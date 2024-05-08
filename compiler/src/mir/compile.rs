//! Compiling MIR down to RV32I-ISA, ILP32-ABI assembly.
//!
//! Note that we don't support floating-point numbers, so keeping track of the
//! ABI and ISA support for them is just so we produce object-files that work
//! with other software.

use core::fmt;
use std::{
    alloc::Layout,
    collections::{HashMap, HashSet, VecDeque},
};

use either::Either;
use indexmap::IndexSet;
use zachs18_stdx::OptionExt;

use crate::{
    ast::ArithmeticOp,
    hir::PointerSized,
    mir::{
        BasicBlockIdx, BasicOperation, CompilationUnit, Constant, ItemKind,
        LocalOrConstant, Operand, Place, PlaceProjection, SlotIdx, Terminator,
        Value,
    },
};

use super::{Body, TypeIdx, TypeKind};

mod const_eval;

#[derive(Debug, Clone, Copy)]
pub struct CompilationState {
    isa: ISA,
    abi: ABI,
}

impl CompilationState {
    pub fn new(isa: ISA, abi: ABI) -> Result<Self, &'static str> {
        match (isa, abi) {
            (ISA::RV32I, ABI::ILP32F | ABI::ILP32D) => {
                Err("cannot use F or D ABI with RV32I")
            }
            (ISA::RV32I | ISA::RV32G, ABI::LP64 | ABI::LP64F | ABI::LP64D) => {
                Err("cannot use 64-bit ABI on RV32")
            }
            (
                ISA::RV64I | ISA::RV64G,
                ABI::ILP32 | ABI::ILP32F | ABI::ILP32D,
            ) => Err("cannot use 32-bit ABI on RV64"),
            (ISA::RV64I, ABI::LP64F | ABI::LP64D) => {
                Err("cannot use F or D ABI on RV64I")
            }
            (ISA::RV32I, ABI::ILP32)
            | (ISA::RV64I, ABI::LP64)
            | (ISA::RV32G, ABI::ILP32 | ABI::ILP32F | ABI::ILP32D)
            | (ISA::RV64G, ABI::LP64 | ABI::LP64F | ABI::LP64D) => {
                Ok(Self { isa, abi })
            }
        }
    }

    fn pointer_size(&self) -> usize {
        match self.abi {
            ABI::ILP32 | ABI::ILP32F | ABI::ILP32D => 4,
            ABI::LP64 | ABI::LP64F | ABI::LP64D => 8,
        }
    }

    fn pointer_layout(&self) -> Layout {
        let size @ align = self.pointer_size();
        Layout::from_size_align(size, align).unwrap()
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ISA {
    RV32I,
    RV32G,
    RV64I,
    RV64G,
}

#[derive(Debug, Clone, Copy)]
pub enum ABI {
    ILP32,
    ILP32F,
    ILP32D,
    LP64,
    LP64F,
    LP64D,
}

const TEMP_REGS: [&str; 7] = ["t0", "t1", "t2", "t3", "t4", "t5", "t6"];

fn emit_static(
    buffer: &mut String, compilation_unit: &CompilationUnit,
    state: &CompilationState, value: &[u8], global: bool, alignment: usize,
    mutable: bool, name: &str,
) -> fmt::Result {
    use std::fmt::Write;
    if global {
        writeln!(buffer, ".global {name}")?;
    }
    let is_bss = value.iter().all(|&b| b == 0);
    if is_bss {
        writeln!(buffer, ".bss {name}, {len}, {alignment}", len = value.len())?;
    } else {
        if mutable {
            writeln!(buffer, ".section .rodata.{name}")?;
        } else {
            writeln!(buffer, ".section .data.{name}")?;
        }
        writeln!(buffer, ".balign {alignment}")?;
        writeln!(buffer, "{name}:")?;
        for b in value {
            writeln!(buffer, ".byte {b}")?;
        }
    }
    Ok(())
}

fn arithmetic_op_instruction(op: &ArithmeticOp) -> &str {
    match op {
        ArithmeticOp::Add => "add",
        ArithmeticOp::Subtract => "sub",
        ArithmeticOp::Multiply => todo!(),
        ArithmeticOp::Divide => todo!(),
        ArithmeticOp::Modulo => todo!(),
        ArithmeticOp::And | ArithmeticOp::BitAnd => "and",
        ArithmeticOp::Or | ArithmeticOp::BitOr => "or",
        ArithmeticOp::BitXor => "xor",
        ArithmeticOp::LeftShift => todo!(),
        ArithmeticOp::RightShift => todo!(),
    }
}

fn emit_function(
    buffer: &mut String, compilation_unit: &CompilationUnit,
    state: &CompilationState, body: &super::Body, global: bool, name: &str,
    new_local_symbol: &mut (impl ?Sized + FnMut() -> String),
) -> fmt::Result {
    use std::fmt::Write;
    if global {
        writeln!(buffer, ".global {name}")?;
    }
    writeln!(buffer, ".type {name},@function")?;
    writeln!(buffer, ".section .text.{name}")?;
    writeln!(buffer, ".balign 4")?;
    writeln!(buffer, "{name}:")?;
    writeln!(buffer, ".cfi_startproc")?;
    eprintln!("TODO: CFI directives");

    let [pointer_load_inst, pointer_store_inst] =
        compilation_unit.pointer_load_store_instructions(state);

    // See if this function is a leaf
    let is_leaf = !body
        .basic_blocks
        .iter()
        .any(|block| matches!(block.terminator, Terminator::Call { .. }));

    // Calculate stack frame layout
    let (stack_layout, slot_locations) =
        compilation_unit.body_stack_layout(body, state);
    // Allocate space for return address on stack (only used if we call another
    // function).
    let (stack_layout, return_address_offset) = if !is_leaf {
        stack_layout.extend(state.pointer_layout()).unwrap()
    } else {
        (stack_layout, usize::MAX)
    };
    // Stack must be 16-byte-aligned
    let stack_layout = stack_layout.align_to(16).unwrap().pad_to_align();

    // Function prologue:
    // 1. Allocate stack frame
    // 2. If not leaf, write return address
    // 3. Copy arguments into stack
    if let stack_size @ 1.. = stack_layout.size() {
        writeln!(buffer, "addi sp, sp, -{}", stack_size)?;
    }
    if !is_leaf {
        writeln!(
            buffer,
            "{pointer_store_inst} ra, {}(sp)",
            return_address_offset
        )?;
    }

    let mut arg_registers_used = 0;
    let mut next_arg_register = || {
        if arg_registers_used >= 8 {
            unimplemented!("more than 8 function arguments");
        }
        let argreg = arg_registers_used;
        arg_registers_used += 1;
        format!("a{argreg}")
    };

    for arg in 1..=body.argc {
        let Some([_load_inst, store_inst]) =
            compilation_unit.load_store_instructions(body.slots[arg], state)
        else {
            continue;
        };
        let reg = next_arg_register();
        let offset = slot_locations[arg];
        writeln!(buffer, "{store_inst} {reg}, {offset}(sp)")?;
    }

    // Determine the order to emit basic blocks.
    // This is optimized by the SortBlocks optimization, so this vec is just for
    // clarity.
    let basic_block_order: Vec<BasicBlockIdx> =
        (0..body.basic_blocks.len()).map(BasicBlockIdx).collect();

    // Function epilogue
    let emit_return = |buffer: &mut String| -> fmt::Result {
        use fmt::Write;
        if !is_leaf {
            writeln!(
                buffer,
                "{pointer_load_inst} ra, {}(sp)",
                return_address_offset
            )?;
        }
        if let Some([load_inst, _store_inst]) =
            compilation_unit.load_store_instructions(body.slots[0], state)
        {
            let offset = slot_locations[0];
            writeln!(buffer, "{load_inst} a0, {offset}(sp)")?;
        }
        if let stack_size @ 1.. = stack_layout.size() {
            writeln!(buffer, "addi sp, sp, {}", stack_size)?;
        }
        writeln!(buffer, "ret")
    };

    // Load local slot into register (should be a temporary register)
    let emit_load_local =
        |buffer: &mut String, local: SlotIdx, dst: &str| -> fmt::Result {
            use fmt::Write;
            let Some([load_inst, _store_inst]) = compilation_unit
                .load_store_instructions(body.slots[local.0], state)
            else {
                return Ok(());
            };
            let offset = slot_locations[local.0];
            writeln!(buffer, "{load_inst} {dst}, {offset}(sp)")
        };

    // Load constant into register (should be a temporary register)
    let emit_load_constant =
        |buffer: &mut String, constant: &Constant, dst: &str| -> fmt::Result {
            use fmt::Write;
            match *constant {
                Constant::Integer { value, .. } => {
                    writeln!(buffer, "li {dst}, {}", value as i64)
                }
                Constant::Bool(value) => {
                    writeln!(buffer, "li {dst}, {}", value as u8)
                }
                Constant::ItemAddress(_) => todo!(),
                Constant::Tuple(_) => unimplemented!("tuples"),
            }
        };

    // Store register into local slot (register should be a temporary register)
    let emit_load_local_or_constant = |buffer: &mut String,
                                       local: &LocalOrConstant,
                                       dst: &str|
     -> fmt::Result {
        match local {
            &LocalOrConstant::Local(local) => {
                emit_load_local(buffer, local, dst)
            }
            LocalOrConstant::Constant(constant) => {
                emit_load_constant(buffer, constant, dst)
            }
        }
    };

    // Store register into local slot (register should be a temporary register)
    let emit_store_local =
        |buffer: &mut String, local: SlotIdx, src: &str| -> fmt::Result {
            use fmt::Write;
            let Some([_load_inst, store_inst]) = compilation_unit
                .load_store_instructions(body.slots[local.0], state)
            else {
                return Ok(());
            };
            let offset = slot_locations[local.0];
            writeln!(buffer, "{store_inst} {src}, {offset}(sp)")
        };

    // Returns Ok((index, load_store_insts)), where `index(dst)` is the actual
    // address after evaluation, and load_store_insts is the load and store
    // instructions to be used for the place.
    let emit_evaluate_place_address =
        |buffer: &mut String,
         place: &Place,
         dst: &str,
         scratch: &[&str]|
         -> Result<(isize, Option<[&'static str; 2]>), fmt::Error> {
            let local = place.local;
            let Some(ref projection) = place.projection else {
                panic!("cannot evaluate address of local place");
            };
            let ptr_ty = body.slots[local.0];
            let pointee_ty = match compilation_unit.types[ptr_ty.0] {
                TypeKind::Pointer { pointee, .. } => pointee,
                _ => unreachable!("cannot deref a non-pointer"),
            };
            let load_store_insts =
                compilation_unit.load_store_instructions(pointee_ty, state);
            let pointee_layout = compilation_unit.layout(pointee_ty, state);
            let pointee_size = pointee_layout.size();
            // Load local into dst, then either const-index using immediate,
            // or add then 0-index
            emit_load_local(buffer, local, dst)?;
            match (projection, 0) {
                (PlaceProjection::Deref, index)
                | (&PlaceProjection::DerefConstantIndex(index), _) => {
                    let index = index * pointee_size as isize;
                    Ok((index, load_store_insts))
                }
                (&PlaceProjection::DerefIndex(index_local), _) => {
                    let (&index_dst, scratch) = scratch
                        .split_first()
                        .expect("have enough scratch registers");
                    emit_load_local(buffer, index_local, index_dst)?;
                    assert!(
                        pointee_size.is_power_of_two(),
                        "cannot load non-power-of-two-sized type using \
                         indexing"
                    );
                    let shift_amt = pointee_size.ilog2();
                    if shift_amt != 0 {
                        writeln!(
                            buffer,
                            "slli {index_dst}, {index_dst}, {shift_amt}"
                        )?;
                    }
                    writeln!(buffer, "add {dst}, {dst}, {index_dst}")?;
                    Ok((0, load_store_insts))
                }
            }
        };

    let emit_evaluate_operand = |buffer: &mut String,
                                 operand: &Operand,
                                 dst: &str,
                                 scratch: &[&str]|
     -> fmt::Result {
        match *operand {
            (Operand::Constant(ref constant)) => {
                emit_load_constant(buffer, constant, dst)
            }
            (Operand::Copy(Place { local, projection: None })) => {
                emit_load_local(buffer, local, dst)
            }
            (Operand::Copy(ref place)) => {
                let (index, load_store_insts) =
                    emit_evaluate_place_address(buffer, place, dst, scratch)?;
                let Some([load_inst, _]) = load_store_insts else {
                    panic!("maybe allow ZST indexing?");
                };
                writeln!(buffer, "{load_inst} {dst}, {index}({dst})")
            }
        }
    };

    let emit_evaluate_value = |buffer: &mut String,
                               value: &Value,
                               dst: &str,
                               scratch: &[&str]|
     -> fmt::Result {
        match value {
            Value::Operand(operand) => {
                emit_evaluate_operand(buffer, operand, dst, scratch)
            }
            Value::BinaryOp(op, lhs, rhs) => {
                emit_evaluate_operand(buffer, lhs, dst, scratch)?;
                let (&rhs_dst, scratch) = scratch
                    .split_first()
                    .expect("have enough scratch registers");
                emit_evaluate_operand(buffer, rhs, rhs_dst, scratch)?;
                match op {
                    crate::ast::BinaryOp::Arithmetic(op) => {
                        let op_inst = arithmetic_op_instruction(op);
                        writeln!(buffer, "{op_inst} {dst}, {dst}, {rhs_dst}")
                    }
                    crate::ast::BinaryOp::Comparison(_) => todo!(),
                    crate::ast::BinaryOp::Assignment
                    | crate::ast::BinaryOp::RangeOp { .. } => unreachable!(
                        "assignment and range ops should not be in MIR"
                    ),
                }
            }
            Value::Not(_) => todo!(),
            Value::Negate(_) => todo!(),
        }
    };

    let mut basic_block_labels: HashMap<BasicBlockIdx, String> = HashMap::new();
    macro_rules! basic_block_label {
        ($block_idx:expr) => {
            basic_block_labels
                .entry($block_idx)
                .or_insert_with(&mut *new_local_symbol)
        };
    }
    let mut emitted_basic_blocks: HashSet<BasicBlockIdx> = HashSet::new();

    for (idx, block_idx) in basic_block_order.iter().copied().enumerate() {
        if !emitted_basic_blocks.insert(block_idx) {
            continue;
        }
        let label = basic_block_label!(block_idx);
        writeln!(buffer, "{label}:")?;
        let block = &body.basic_blocks[block_idx.0];
        for op in &block.operations {
            let BasicOperation::Assign(place, value) = op else {
                continue;
            };

            let (&dst, scratch) = TEMP_REGS.split_first().unwrap();

            // Load value into dst
            emit_evaluate_value(buffer, value, dst, scratch)?;

            // Write value into place
            match place.projection {
                None => {
                    let Some([_, store_inst]) = compilation_unit
                        .load_store_instructions(
                            body.slots[place.local.0],
                            state,
                        )
                    else {
                        return Ok(());
                    };
                    let offset = slot_locations[place.local.0];
                    writeln!(buffer, "{store_inst} {dst}, {offset}(sp)")?;
                }
                Some(_) => {
                    let (index, load_store_insts) =
                        emit_evaluate_place_address(
                            buffer, place, dst, scratch,
                        )?;
                    let Some([load_inst, _]) = load_store_insts else {
                        panic!("maybe allow ZST indexing?");
                    };
                    writeln!(buffer, "{load_inst} {dst}, {index}({dst})")?;
                }
            }
        }

        match block.terminator {
            Terminator::Goto { target } => {
                if basic_block_order
                    .get(idx + 1)
                    .is_none_or(|next_basic_block| *next_basic_block != target)
                {
                    writeln!(buffer, "j {}", basic_block_label!(target))?;
                }
            }
            Terminator::Return => emit_return(buffer)?,
            Terminator::SwitchBool { ref scrutinee, true_dst, false_dst } => {
                let dst = TEMP_REGS[0];
                emit_load_local_or_constant(buffer, scrutinee, dst)?;
                let next_emitted_block =
                    basic_block_order.get(idx + 1).copied();

                if next_emitted_block == Some(true_dst) {
                    // jump to false if false, else fallthrough
                    writeln!(
                        buffer,
                        "beqz {dst}, {}",
                        basic_block_label!(false_dst)
                    )?;
                } else if next_emitted_block == Some(false_dst) {
                    // jump to true if true, else fallthrough
                    writeln!(
                        buffer,
                        "bnez {dst}, {}",
                        basic_block_label!(true_dst)
                    )?;
                } else {
                    // jump to false if false, else jump to true
                    writeln!(
                        buffer,
                        "beqz {dst}, {}",
                        basic_block_label!(false_dst)
                    )?;
                    writeln!(buffer, "j {}", basic_block_label!(true_dst))?;
                }
            }
            Terminator::SwitchCmp {
                ref lhs,
                ref rhs,
                less_dst,
                equal_dst,
                greater_dst,
            } => {
                let lhs_dst = TEMP_REGS[0];
                let rhs_dst = TEMP_REGS[1];
                emit_load_local_or_constant(buffer, lhs, lhs_dst)?;
                emit_load_local_or_constant(buffer, rhs, rhs_dst)?;
                let signed = match *lhs {
                    LocalOrConstant::Local(slot) => {
                        match compilation_unit.types[body.slots[slot.0].0] {
                            TypeKind::Integer { signed, .. } => signed,
                            _ => unreachable!("non-integer in SwitchCmp"),
                        }
                    }
                    LocalOrConstant::Constant(Constant::Integer {
                        signed,
                        ..
                    }) => signed,
                    _ => unreachable!("non-integer in SwitchCmp"),
                };
                eprintln!("TODO: emit better code for SwitchCmp");
                #[cfg(any())]
                match (
                    less_dst == greater_dst,
                    less_dst == equal_dst,
                    equal_dst == greater_dst,
                ) {
                    (true, true, true)
                    | (true, true, false)
                    | (false, true, true)
                    | (true, false, true) => todo!(),
                    // == or !=
                    (true, false, false) => {
                        todo!()
                    }
                    (false, true, false) => todo!(),
                    (false, false, true) => todo!(),
                    (false, false, false) => todo!(),
                }

                if signed {
                    writeln!(
                        buffer,
                        "blt {lhs_dst}, {rhs_dst}, {}",
                        basic_block_label!(less_dst)
                    )?;
                    writeln!(
                        buffer,
                        "bgt {lhs_dst}, {rhs_dst}, {}",
                        basic_block_label!(greater_dst)
                    )?;
                    writeln!(buffer, "j {}", basic_block_label!(equal_dst))?;
                } else {
                    writeln!(
                        buffer,
                        "bltu {lhs_dst}, {rhs_dst}, {}",
                        basic_block_label!(less_dst)
                    )?;
                    writeln!(
                        buffer,
                        "bgtu {lhs_dst}, {rhs_dst}, {}",
                        basic_block_label!(greater_dst)
                    )?;
                    writeln!(buffer, "j {}", basic_block_label!(equal_dst))?;
                }
            }
            Terminator::Unreachable => todo!(),
            Terminator::Call {
                ref func,
                ref args,
                ref return_destination,
                target,
            } => {
                todo!()
            }
            Terminator::Error => todo!(),
        }
    }

    writeln!(buffer, ".cfi_endproc")?;
    writeln!(buffer, ".size {name}, .-{name}")
}

impl CompilationUnit {
    fn layout(&self, ty: TypeIdx, state: &CompilationState) -> Layout {
        let pointer_size = state.pointer_size();
        match self.types[ty.0] {
            TypeKind::Array { element, length } => {
                let element_layout = self.layout(element, state).pad_to_align();
                let alloc_size = element_layout.size() * length;
                Layout::from_size_align(alloc_size, element_layout.align())
                    .expect("array too large")
            }
            TypeKind::Integer { bits: Either::Left(bits), .. } => {
                let size = match bits {
                    8 => 1,
                    16 => 2,
                    32 => 4,
                    64 => 8,
                    _ => unreachable!("unsupported integer width {bits}"),
                };
                Layout::from_size_align(size, size).unwrap()
            }
            TypeKind::Pointer { .. }
            | TypeKind::Integer { bits: Either::Right(PointerSized), .. } => {
                Layout::from_size_align(pointer_size, pointer_size).unwrap()
            }
            TypeKind::Bool => Layout::new::<bool>(),
            TypeKind::Never => Layout::new::<()>(),
            TypeKind::Tuple(ref fields) => {
                fields.iter().fold(Layout::new::<()>(), |layout, &field| {
                    layout.extend(self.layout(field, state)).unwrap().0
                })
            }
            TypeKind::Slice { .. } => unimplemented!("slice types"),
            TypeKind::Function { .. } => {
                unimplemented!("function pointers")
            }
        }
    }

    fn pointer_load_store_instructions(
        &self, state: &CompilationState,
    ) -> [&'static str; 2] {
        match state.abi {
            ABI::ILP32 | ABI::ILP32F | ABI::ILP32D => ["lw", "sw"],
            ABI::LP64 | ABI::LP64F | ABI::LP64D => ["ld", "sd"],
        }
    }

    fn load_store_instructions(
        &self, ty: TypeIdx, state: &CompilationState,
    ) -> Option<[&'static str; 2]> {
        let (pointer_sized_suffix, pointer_bits) = match state.abi {
            ABI::ILP32 | ABI::ILP32F | ABI::ILP32D => (["lw", "sw"], 32),
            ABI::LP64 | ABI::LP64F | ABI::LP64D => (["ld", "sd"], 64),
        };
        Some(match self.types[ty.0] {
            TypeKind::Integer { bits: Either::Right(PointerSized), .. }
            | TypeKind::Pointer { .. } => pointer_sized_suffix,
            TypeKind::Integer { bits: Either::Left(bits), signed } => {
                match (signed, bits, pointer_bits) {
                    (_, 64, 64) => ["ld", "sd"],
                    (_, 32, 32) | (true, 32, _) => ["lw", "sw"],
                    (false, 32, _) => ["lwu", "sw"],
                    (true, 16, _) => ["lh", "sh"],
                    (false, 16, _) => ["lhu", "sh"],
                    (true, 8, _) => ["lb", "sb"],
                    (false, 8, _) => ["lbu", "sb"],
                    (true, _, _) => {
                        unimplemented!("loading i{bits} on RV{pointer_bits}")
                    }
                    (false, _, _) => {
                        unimplemented!("loading u{bits} on RV{pointer_bits}")
                    }
                }
            }
            TypeKind::Bool => ["lbu", "sb"],
            TypeKind::Tuple(ref fields) if fields.len() == 0 => return None,
            ref ty => unimplemented!("loading {ty:?}"),
        })
    }

    /// Returns the Layout required by the stack, and the offsets of all local
    /// slots
    fn body_stack_layout(
        &self, body: &Body, state: &CompilationState,
    ) -> (Layout, Vec<usize>) {
        let mut layout = Layout::new::<()>();
        let mut offets = Vec::with_capacity(body.argc);
        for &slot_ty in &body.slots {
            let slot_layout = self.layout(slot_ty, state);
            offets.push(layout.size());
            layout = layout.extend(slot_layout).expect("too many locals").0;
        }
        (layout, offets)
    }

    pub fn compile(&self, state: CompilationState) -> String {
        let mut buffer = String::new();

        let mut local_symbols: HashMap<usize, String> = HashMap::new();
        let mut local_idx = 0;
        let mut new_local_symbol = || {
            let idx = local_idx;
            local_idx += 1;
            format!(".L{idx}")
        };

        for (idx, item) in self.items.iter().enumerate() {
            match item
                .as_ref()
                .expect_left("No stubs should be left after MIR lowering")
            {
                ItemKind::DeclaredExternStatic { .. } => {
                    // No ASM generated
                }
                ItemKind::DeclaredExternFn { .. } => {
                    // No ASM generated
                }
                ItemKind::DefinedExternStatic {
                    name,
                    mutability,
                    initializer,
                } => {
                    let value = self.const_eval(initializer, &state);
                    let layout = self.layout(initializer.slots[0], &state);
                    emit_static(
                        &mut buffer,
                        self,
                        &state,
                        &value,
                        true,
                        layout.align(),
                        mutability.is_mutable(),
                        name.ident,
                    )
                    .expect("formatting should not fail");
                }
                ItemKind::StringLiteral { data } => {
                    let local_symbol = new_local_symbol();
                    emit_static(
                        &mut buffer,
                        self,
                        &state,
                        data,
                        false,
                        1,
                        false,
                        &local_symbol,
                    )
                    .expect("formatting should not fail");
                    local_symbols.insert(idx, local_symbol);
                }
                ItemKind::LocalStatic { mutability, initializer } => {
                    let value = self.const_eval(initializer, &state);
                    let local_symbol = new_local_symbol();
                    let layout = self.layout(initializer.slots[0], &state);
                    emit_static(
                        &mut buffer,
                        self,
                        &state,
                        &value,
                        false,
                        layout.align(),
                        mutability.is_mutable(),
                        &local_symbol,
                    )
                    .expect("formatting should not fail");
                    local_symbols.insert(idx, local_symbol);
                }
                ItemKind::DefinedExternFn { name, body } => {
                    emit_function(
                        &mut buffer,
                        self,
                        &state,
                        body,
                        true,
                        name.ident,
                        &mut new_local_symbol,
                    )
                    .expect("formatting should not fail");
                }
                ItemKind::LocalFn { body } => {
                    let local_symbol = new_local_symbol();
                    emit_function(
                        &mut buffer,
                        self,
                        &state,
                        body,
                        true,
                        &local_symbol,
                        &mut new_local_symbol,
                    )
                    .expect("formatting should not fail");
                    local_symbols.insert(idx, local_symbol);
                }
            }
        }

        dbg!(&buffer);

        buffer
    }
}
