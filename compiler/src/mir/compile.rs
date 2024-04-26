//! Compiling MIR down to RV32I-ISA, ILP32-ABI assembly.
//!
//! Note that we don't support floating-point numbers, so keeping track of the
//! ABI and ISA support for them is just so we produce object-files that work
//! with other software.

use core::fmt;
use std::{alloc::Layout, collections::HashMap};

use either::Either;

use crate::{
    hir::PointerSized,
    mir::{CompilationUnit, ItemKind},
};

use super::{TypeIdx, TypeKind};

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
            TypeKind::Tuple(_) => todo!(),
            TypeKind::Slice { .. } => unimplemented!("slice types"),
            TypeKind::Function { .. } => {
                unimplemented!("function pointers")
            }
        }
    }

    pub fn compile(&self, state: CompilationState) -> String {
        let is_64 = match state.abi {
            ABI::ILP32 | ABI::ILP32F | ABI::ILP32D => false,
            ABI::LP64 | ABI::LP64F | ABI::LP64D => true,
        };

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
                ItemKind::DefinedExternFn { name, body } => todo!(),
                ItemKind::LocalFn { body } => todo!(),
            }
        }

        dbg!(&buffer);

        buffer
    }
}
