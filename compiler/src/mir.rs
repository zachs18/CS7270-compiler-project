//! Mid-level intermediate representation, appropriate for some optimizations
//! and lowering to assembly.
//!
//! Roughly similar to https://doc.rust-lang.org/stable/nightly-rustc/rustc_middle/mir/index.html
//!
//! Note: Assignments to slots of type `()` may be ignored (since they do
//! nothing).

use std::{collections::HashMap, fmt, mem::ManuallyDrop, sync::Arc};

use either::Either;
use itertools::Itertools;

use crate::{
    ast::BinaryOp,
    hir::{
        self, BlockLabel, HirCtx, Mutability, PointerSized, Symbol, UnaryOp,
    },
    token::Ident,
    util::{FmtSlice, Scope},
};

use self::optimizations::MirOptimization;

pub mod compile;
pub mod optimizations;

/// Lower type-checked hir to mir
pub fn lower_hir_to_mir(items: &[hir::Item], ctx: &HirCtx) -> CompilationUnit {
    let mut compilation_unit = CompilationUnit::new();
    compilation_unit.items.reserve(items.len());
    for (idx, item) in items.iter().enumerate() {
        let ty = compilation_unit.lower_type(item.type_(), ctx);
        assert!(
            compilation_unit
                .globals
                .insert(item.name(), (ItemIdx(idx), ty))
                .is_none(),
            "duplicate item {:?}",
            item.name()
        );
        match item {
            hir::Item::FnItem(_) => {
                compilation_unit.items.push(Either::Right(ItemKindStub::Fn))
            }
            hir::Item::StaticItem(item) => compilation_unit.items.push(
                Either::Right(ItemKindStub::Static {
                    mutability: Mutability::from_bool(item.mut_token.is_some()),
                }),
            ),
        }
    }
    for (idx, item) in items.iter().enumerate() {
        match item {
            hir::Item::FnItem(hir::FnItem {
                name,
                extern_token: None,
                body: None,
                ..
            }) => {
                unreachable!(
                    "fn item {name:?} must be extern, have a body, or both"
                )
            }
            hir::Item::StaticItem(hir::StaticItem {
                name,
                extern_token: None,
                initializer: None,
                ..
            }) => unreachable!(
                "static item {name:?} must be extern, have an initializer, or \
                 both"
            ),
            hir::Item::FnItem(hir::FnItem {
                extern_token: Some(..),
                body: None,
                name,
                ..
            }) => {
                let Symbol::Ident(name) = *name else {
                    panic!("extern fn must have a non-synthetic name");
                };
                let item = ItemKind::DeclaredExternFn { name };
                compilation_unit.items[idx] = Either::Left(item);
            }
            hir::Item::StaticItem(hir::StaticItem {
                extern_token: Some(..),
                initializer: None,
                name,
                mut_token,
                ..
            }) => {
                let Symbol::Ident(name) = *name else {
                    panic!("extern static must have a non-synthetic name");
                };
                let item = ItemKind::DeclaredExternStatic {
                    mutability: Mutability::from_bool(mut_token.is_some()),
                    name,
                };
                compilation_unit.items[idx] = Either::Left(item);
            }
            hir::Item::FnItem(hir::FnItem {
                name,
                body: Some(..),
                is_variadic: true,
                ..
            }) => {
                unimplemented!("defining variadic fn {name:?} is not supported")
            }
            hir::Item::FnItem(hir::FnItem {
                extern_token,
                name,
                params,
                body: Some(body),
                is_variadic: false,
                fn_token,
                return_type,
                signature,
            }) => {
                let body = Body::new_for_fn(
                    body,
                    ctx,
                    params,
                    *return_type,
                    &mut compilation_unit,
                );
                let item = if extern_token.is_none() {
                    ItemKind::LocalFn { body }
                } else {
                    let Symbol::Ident(name) = *name else {
                        panic!("extern fn must have non-synthetic name");
                    };
                    ItemKind::DefinedExternFn { name, body }
                };
                compilation_unit.items[idx] = Either::Left(item);
            }
            hir::Item::StaticItem(hir::StaticItem {
                extern_token,
                name,
                mut_token,
                initializer: Some(initializer),
                ..
            }) => {
                let body = Body::new_for_static(
                    initializer,
                    ctx,
                    &mut compilation_unit,
                );
                let item = if extern_token.is_none() {
                    ItemKind::LocalStatic {
                        mutability: Mutability::from_bool(mut_token.is_some()),
                        initializer: body,
                    }
                } else {
                    let Symbol::Ident(name) = *name else {
                        panic!("extern static must have a non-synthetic name");
                    };
                    ItemKind::DefinedExternStatic {
                        mutability: Mutability::from_bool(mut_token.is_some()),
                        name,
                        initializer: body,
                    }
                };
                compilation_unit.items[idx] = Either::Left(item);
            }
        }
    }
    compilation_unit
}

#[derive(Debug)]
pub struct CompilationUnit {
    types: Vec<TypeKind>,
    /// These should only be `Right` between registering globals and resolving
    /// bodies.
    items: Vec<Either<ItemKind, ItemKindStub>>,
    globals: HashMap<hir::Symbol, (ItemIdx, TypeIdx)>,
}

impl fmt::Display for CompilationUnit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.pretty_print(f)
    }
}

impl CompilationUnit {
    fn pretty_print(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "CompilationUnit {{")?;
        for (name, &(idx, ty)) in &self.globals {
            let Either::Left(ref item) = self.items[idx.0] else {
                unreachable!("items should not be stubs after MIR-building")
            };
            self.pretty_print_global(name, ty, item, f)?;
        }
        writeln!(f, "}}")
    }

    fn display_type(&self, ty: TypeIdx) -> impl fmt::Display + '_ {
        struct FmtType<'a>(&'a CompilationUnit, TypeIdx);

        impl fmt::Display for FmtType<'_> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let FmtType(this, ty) = *self;
                match this.types[ty.0] {
                    TypeKind::Pointer { mutability, pointee } => {
                        write!(
                            f,
                            "*{} {}",
                            mutability,
                            this.display_type(pointee)
                        )
                    }
                    TypeKind::Array { element, length } => {
                        write!(f, "[{}; {length}]", this.display_type(element))
                    }
                    TypeKind::Slice { element } => {
                        write!(f, "[{}", this.display_type(element))
                    }
                    TypeKind::Integer { signed, bits } => {
                        if signed {
                            write!(f, "i")?;
                        } else {
                            write!(f, "u")?;
                        }
                        match bits {
                            Either::Left(bits) => write!(f, "{bits}"),
                            Either::Right(PointerSized) => write!(f, "size"),
                        }
                    }
                    TypeKind::Bool => write!(f, "bool"),
                    TypeKind::Never => write!(f, "!"),
                    TypeKind::Tuple(ref elems) => {
                        let mut elems = elems.iter().copied();
                        match elems.next() {
                            None => write!(f, "()"),
                            Some(first) => {
                                write!(f, "({}", this.display_type(first))?;
                                for elem in elems {
                                    write!(f, ", {}", this.display_type(elem))?;
                                }
                                write!(f, ")")
                            }
                        }
                    }
                    TypeKind::Function {
                        ref params,
                        return_type,
                        is_variadic,
                    } => {
                        let mut params = params.iter().copied();
                        if is_variadic {
                            write!(f, "fn(")?;
                            for param in params {
                                write!(f, "{}, ", this.display_type(param))?;
                            }
                            write!(
                                f,
                                "...) -> {}",
                                this.display_type(return_type)
                            )
                        } else {
                            match params.next() {
                                None => write!(
                                    f,
                                    "fn() -> {}",
                                    this.display_type(return_type)
                                ),
                                Some(first) => {
                                    write!(
                                        f,
                                        "fn({}",
                                        this.display_type(first)
                                    )?;
                                    for param in params {
                                        write!(
                                            f,
                                            ", {}",
                                            this.display_type(param)
                                        )?;
                                    }
                                    write!(
                                        f,
                                        ") -> {}",
                                        this.display_type(return_type)
                                    )
                                }
                            }
                        }
                    }
                }
            }
        }

        FmtType(self, ty)
    }

    fn display_fn_args(&self, ty: TypeIdx) -> impl fmt::Display + '_ {
        struct FmtFnArgs<'a>(&'a CompilationUnit, TypeIdx);

        impl fmt::Display for FmtFnArgs<'_> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let FmtFnArgs(this, ty) = *self;
                let TypeKind::Function { ref params, return_type, is_variadic } =
                    this.types[ty.0]
                else {
                    panic!("fn type is not a function?");
                };

                let mut params = params.iter().copied().enumerate();
                if is_variadic {
                    write!(f, "(")?;
                    for (idx, param) in params {
                        write!(
                            f,
                            "_{}: {}, ",
                            idx + 1,
                            this.display_type(param)
                        )?;
                    }
                    write!(f, "...) -> {}", this.display_type(return_type))
                } else {
                    match params.next() {
                        None => write!(
                            f,
                            "() -> {}",
                            this.display_type(return_type)
                        ),
                        Some((_, first)) => {
                            write!(f, "(_1: {}", this.display_type(first))?;
                            for (idx, param) in params {
                                write!(
                                    f,
                                    ", _{}: {}",
                                    idx + 1,
                                    this.display_type(param)
                                )?;
                            }
                            write!(f, ") -> {}", this.display_type(return_type))
                        }
                    }
                }
            }
        }

        FmtFnArgs(self, ty)
    }

    fn pretty_print_global(
        &self, name: &Symbol, ty: TypeIdx, kind: &ItemKind,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        match *kind {
            ItemKind::DeclaredExternStatic { mutability, .. } => {
                writeln!(
                    f,
                    "    extern static {mutability} {name}: {};",
                    self.display_type(ty)
                )
            }
            ItemKind::DefinedExternStatic {
                mutability,
                ref initializer,
                ..
            } => {
                write!(
                    f,
                    "    extern static {mutability} {name}: {} = ",
                    self.display_type(ty)
                )?;
                self.pretty_print_body(initializer, f)
            }
            ItemKind::LocalStatic { mutability, ref initializer, .. } => {
                write!(
                    f,
                    "    static {mutability} {name}: {} = ",
                    self.display_type(ty)
                )?;
                self.pretty_print_body(initializer, f)
            }
            ItemKind::DeclaredExternFn { .. } => {
                writeln!(f, "    extern fn {name} = {};", self.display_type(ty))
            }
            ItemKind::DefinedExternFn { ref body, .. } => {
                write!(
                    f,
                    "    extern fn {name}{} = ",
                    self.display_fn_args(ty)
                )?;
                self.pretty_print_body(body, f)
            }
            ItemKind::LocalFn { ref body, .. } => {
                write!(f, "    fn {name}{} = ", self.display_fn_args(ty))?;
                self.pretty_print_body(body, f)
            }
            ItemKind::StringLiteral { data } => {
                writeln!(
                    f,
                    "    string literal {name} = \"{}\";",
                    data.escape_ascii()
                )
            }
        }
    }

    fn pretty_print_body(
        &self, body: &Body, f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        writeln!(f, "{{")?;
        for (idx, slot) in body.slots.iter().copied().enumerate() {
            writeln!(f, "        let _{idx}: {};", self.display_type(slot))?;
        }
        writeln!(f)?;
        for (idx, bb) in body.basic_blocks.iter().enumerate() {
            writeln!(f, "        bb{idx}: {{")?;
            for op in &bb.operations {
                writeln!(f, "            {op}")?;
            }
            writeln!(f, "            {}", bb.terminator)?;
            writeln!(f, "        }}")?;
        }
        writeln!(f, "    }}")
    }

    fn new() -> Self {
        // TypeIdx(0) is unit, 1 is bool, 2 is never, 3..13 are integers
        let mut this =
            Self { types: vec![], items: vec![], globals: HashMap::new() };
        this.insert_type(TypeKind::Tuple(Arc::new([])));
        this.insert_type(TypeKind::Bool);
        this.insert_type(TypeKind::Never);
        for b in [8, 16, 32, 64] {
            this.insert_type(TypeKind::Integer {
                signed: true,
                bits: Either::Left(b),
            });
            this.insert_type(TypeKind::Integer {
                signed: false,
                bits: Either::Left(b),
            });
        }
        this.insert_type(TypeKind::Integer {
            signed: true,
            bits: Either::Right(PointerSized),
        });
        this.insert_type(TypeKind::Integer {
            signed: false,
            bits: Either::Right(PointerSized),
        });
        this
    }

    fn unit_type(&self) -> TypeIdx {
        debug_assert!(
            matches!(&self.types[0], TypeKind::Tuple(elems) if elems.is_empty() )
        );
        TypeIdx(0)
    }

    fn bool_type(&self) -> TypeIdx {
        debug_assert!(matches!(&self.types[1], TypeKind::Bool));
        TypeIdx(1)
    }

    fn never_type(&self) -> TypeIdx {
        debug_assert!(matches!(&self.types[2], TypeKind::Never));
        TypeIdx(2)
    }

    fn integer_type(
        &self, signed: bool, bits: Either<u32, PointerSized>,
    ) -> TypeIdx {
        let (idx, _) = self.types[..13].iter().enumerate().find(|(_, tk)| matches!(tk, &&TypeKind::Integer { signed: s, bits: b } if s == signed && b == bits)).expect("types should be regsitered in fn new");
        TypeIdx(idx)
    }

    fn insert_type(&mut self, tk: TypeKind) -> TypeIdx {
        let idx = self.types.len();
        self.types.push(tk);
        TypeIdx(idx)
    }

    fn lower_mutability(
        &mut self, mutability: hir::MutIdx, ctx: &HirCtx,
    ) -> Mutability {
        ctx.resolve_mut(mutability).unwrap_or_else(|| {
            log::error!("types should all be resolved after hir type checking");
            Mutability::Mutable
        })
    }

    fn lower_type(&mut self, ty: hir::TypeIdx, ctx: &HirCtx) -> TypeIdx {
        match ctx
            .resolve_ty(ty)
            .expect("types should all be resolved after hir type checking")
        {
            &hir::TypeKind::Pointer { mutability, pointee } => {
                let tk = TypeKind::Pointer {
                    mutability: self.lower_mutability(mutability, ctx),
                    pointee: self.lower_type(pointee, ctx),
                };
                self.insert_type(tk)
            }
            &hir::TypeKind::Array { element, length } => {
                let tk = TypeKind::Array {
                    element: self.lower_type(element, ctx),
                    length,
                };
                self.insert_type(tk)
            }
            &hir::TypeKind::Slice { .. } => {
                unimplemented!("slice types not implemented")
            }
            &hir::TypeKind::Integer { signed, bits } => {
                self.integer_type(signed, bits)
            }
            hir::TypeKind::Bool => self.bool_type(),
            hir::TypeKind::Tuple(elems) => {
                let tk = TypeKind::Tuple(Arc::from_iter(
                    elems.iter().map(|&ty| self.lower_type(ty, ctx)),
                ));
                self.insert_type(tk)
            }
            hir::TypeKind::Never => self.never_type(),
            &hir::TypeKind::Function {
                ref params,
                return_type,
                is_variadic,
            } => {
                let tk = TypeKind::Function {
                    params: Arc::from_iter(
                        params.iter().map(|&ty| self.lower_type(ty, ctx)),
                    ),
                    return_type: self.lower_type(return_type, ctx),
                    is_variadic,
                };
                self.insert_type(tk)
            }
        }
    }

    fn make_anonymous_static_for_string_literal(
        &mut self, data: &'static [u8],
    ) -> (Symbol, ItemIdx) {
        let idx = self.items.len();
        let symbol = Symbol::new_synthetic();
        self.items.push(Either::Left(ItemKind::StringLiteral { data }));
        let idx = ItemIdx(idx);
        let i8 = self.integer_type(true, Either::Left(8));
        let ty = self
            .insert_type(TypeKind::Array { element: i8, length: data.len() });
        self.globals.insert(symbol, (idx, ty));
        (symbol, idx)
    }

    pub fn apply_optimization(&mut self, opt: impl MirOptimization) -> bool {
        self.items
            .iter_mut()
            .filter_map(|item| item.as_mut().left())
            .map(|item| match item {
                ItemKind::DeclaredExternStatic { .. }
                | ItemKind::StringLiteral { .. }
                | ItemKind::DeclaredExternFn { .. } => false,
                ItemKind::DefinedExternStatic { initializer, .. }
                | ItemKind::LocalStatic { initializer, .. } => {
                    opt.apply(initializer)
                }
                ItemKind::DefinedExternFn { body, .. }
                | ItemKind::LocalFn { body, .. } => opt.apply(body),
            })
            .fold(false, |a, b| a || b)
    }
}

/// Index into `CompilationUnit::types`.
#[derive(Debug, Clone, Copy)]
pub struct TypeIdx(usize);

#[derive(Debug, Clone)]
pub enum TypeKind {
    Pointer { mutability: Mutability, pointee: TypeIdx },
    Array { element: TypeIdx, length: usize },
    Slice { element: TypeIdx },
    Integer { signed: bool, bits: Either<u32, PointerSized> },
    Bool,
    Tuple(Arc<[TypeIdx]>),
    Never,
    Function { params: Arc<[TypeIdx]>, return_type: TypeIdx, is_variadic: bool },
}

/// Index into `CompilationUnit::globals`.
#[derive(Debug, Clone, Copy)]
pub struct ItemIdx(usize);

#[derive(Debug)]
enum ItemKind {
    DeclaredExternStatic {
        name: Ident,
        mutability: Mutability,
    },
    DefinedExternStatic {
        name: Ident,
        mutability: Mutability,
        initializer: Body,
    },
    LocalStatic {
        mutability: Mutability,
        initializer: Body,
    },
    DeclaredExternFn {
        name: Ident,
    },
    DefinedExternFn {
        name: Ident,
        body: Body,
    },
    LocalFn {
        body: Body,
    },
    StringLiteral {
        data: &'static [u8],
    },
}

/// Only used while lowering, so that items being lowered can know how to access
/// another item.
///
/// There are never stubbed string literals.
#[derive(Debug)]
enum ItemKindStub {
    Static { mutability: Mutability },
    Fn,
}

#[derive(Debug)]
pub struct Body {
    /// Local variable/temporary slots.
    ///
    /// The return value is always in slot 0.
    ///
    /// For fn items, the arguments are in slots `1..=argc`.
    slots: Vec<TypeIdx>,
    argc: usize,
    /// Basic blocks in this body. The initial block is index 0.
    basic_blocks: Vec<BasicBlock>,
}

impl Body {
    fn new_for_static(
        initializer: &hir::Expression, ctx: &HirCtx,
        compilation_unit: &mut CompilationUnit,
    ) -> Self {
        let return_type = compilation_unit.lower_type(initializer.type_, ctx);

        // The initial BasicBlock. This will be overwritten with a Goto
        // terminator for the initializer expression's initial block.
        let initial_block = BasicBlock {
            operations: vec![],
            terminator: Terminator::Unreachable,
        };
        // The terminal BasicBlock. This is given as the destimation block when
        // lowering the imitializer expression.
        let terminal_block =
            BasicBlock { operations: vec![], terminator: Terminator::Return };
        let mut this = Body {
            slots: vec![return_type],
            argc: 0,
            basic_blocks: vec![initial_block, terminal_block],
        };

        let mut value_scope: Scope<Symbol, (Mutability, SlotIdx)> =
            Scope::new(None);
        let mut label_scope: Scope<BlockLabel, LabelDestination> =
            Scope::new(None);
        let initial_block = BasicBlockIdx(0);
        let terminal_block = BasicBlockIdx(1);

        // SlotIdx(0) is always the return value
        let body_initial_block = lower_value_expression(
            initializer,
            ctx,
            SlotIdx(0),
            &mut this,
            &mut value_scope,
            &mut label_scope,
            terminal_block,
            compilation_unit,
        );
        this.basic_blocks[initial_block.0].terminator =
            Terminator::Goto { target: body_initial_block };
        this
    }

    fn new_for_fn(
        fn_body: &hir::Block, ctx: &HirCtx, args: &[hir::FnParam],
        return_type: hir::TypeIdx, compilation_unit: &mut CompilationUnit,
    ) -> Self {
        let return_type = compilation_unit.lower_type(return_type, ctx);

        let mut body = Body {
            slots: vec![return_type],
            basic_blocks: vec![],
            argc: args.len(),
        };

        // The initial BasicBlock. This will be overwritten with a Goto
        // terminator for the fn body's initial block.
        let initial_block = body.temp_block();

        // The terminal BasicBlock. This is given as the destination block when
        // lowering the fn body.
        let terminal_block = body.insert_block(BasicBlock {
            operations: vec![],
            terminator: Terminator::Return,
        });

        let mut value_scope: Scope<Symbol, (Mutability, SlotIdx)> =
            Scope::new(None);
        let mut label_scope: Scope<BlockLabel, LabelDestination> =
            Scope::new(None);

        // First, we make slots for parameters
        let param_slots_and_tys = args
            .iter()
            .map(|param| {
                let ty = compilation_unit.lower_type(param.type_, ctx);
                let slot = body.new_slot(ty);
                (slot, ty)
            })
            .collect_vec();

        // Then, we lower the param patterns into locals
        let mut prev_intermediate_block = initial_block;
        for (param, (src_slot, _)) in std::iter::zip(args, param_slots_and_tys)
        {
            let next_intermediate_block = body.temp_block();
            let pattern_block_idx = lower_pattern(
                &param.pattern,
                ctx,
                src_slot,
                &mut body,
                &mut value_scope,
                next_intermediate_block.as_basic_block_idx(),
                compilation_unit,
            );
            prev_intermediate_block.update(
                &mut body,
                vec![],
                Terminator::Goto { target: pattern_block_idx },
            );
            prev_intermediate_block = next_intermediate_block;
        }
        let after_pattern_block = prev_intermediate_block;

        // The we lower the body
        // SlotIdx(0) is always the return value
        let body_initial_block = lower_block(
            fn_body,
            ctx,
            SlotIdx(0),
            &mut body,
            &mut value_scope,
            &mut label_scope,
            terminal_block,
            compilation_unit,
        );

        after_pattern_block.update(
            &mut body,
            vec![],
            Terminator::Goto { target: body_initial_block },
        );
        body
    }

    fn insert_block(&mut self, block: BasicBlock) -> BasicBlockIdx {
        let idx = self.basic_blocks.len();
        self.basic_blocks.push(block);
        BasicBlockIdx(idx)
    }

    /// Used to create a temporary basic block that will be updated later, when
    /// you need to have a destination for something before the destination is
    /// made.
    #[track_caller]
    fn temp_block(&mut self) -> TempBlockIdx {
        let BasicBlockIdx(idx) = self.insert_block(BasicBlock {
            operations: vec![],
            terminator: Terminator::Error,
        });
        // TODO: once we're done, maybe remove the Location field
        TempBlockIdx(std::panic::Location::caller(), idx)
    }

    fn new_slot(&mut self, ty: TypeIdx) -> SlotIdx {
        let idx = self.slots.len();
        self.slots.push(ty);
        SlotIdx(idx)
    }
}

struct TempBlockIdx(&'static std::panic::Location<'static>, usize);

impl Drop for TempBlockIdx {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            panic!(
                "temp block {} (created at {}) dropped without being updated",
                self.1, self.0
            );
        } else {
            eprintln!(
                "temp block {} (created at {}) dropped without being updated \
                 (while panicking)",
                self.1, self.0
            );
        }
    }
}

impl TempBlockIdx {
    fn update(
        self, body: &mut Body, operations: Vec<BasicOperation>,
        terminator: Terminator,
    ) -> BasicBlockIdx {
        let this = ManuallyDrop::new(self);
        body.basic_blocks[this.1] = BasicBlock { operations, terminator };
        BasicBlockIdx(this.1)
    }

    fn as_basic_block_idx(&self) -> BasicBlockIdx {
        BasicBlockIdx(self.1)
    }
}

/// Lowers a block into BasicBlocks which evaluate the block, write the
/// result to `dst`, and then jump to `next_block`.
///
/// Returns the initial BasicBlockIdx.
fn lower_block(
    block: &hir::Block, ctx: &HirCtx, dst: SlotIdx, body: &mut Body,
    value_scope: &mut Scope<'_, Symbol, (Mutability, SlotIdx)>,
    label_scope: &mut Scope<'_, BlockLabel, LabelDestination>,
    next_block: BasicBlockIdx, compilation_unit: &mut CompilationUnit,
) -> BasicBlockIdx {
    // 4 cases:
    // * no statements, no tail: immediately jump to next_block
    // * no statements, with tail: assign tail to dst, jump to next_block
    // * statements, no tail: lower statements, jump to next_block
    // * statements, with tail: lower statements, assign tail to dst, jump to
    //   next_block

    // New value scope since we're in a new block
    let mut value_scope = Scope::new(Some(value_scope));

    match block {
        hir::Block { statements, tail: None } if statements.is_empty() => {
            next_block
        }
        hir::Block { statements, tail: Some(tail) }
            if statements.is_empty() =>
        {
            lower_value_expression(
                tail,
                ctx,
                dst,
                body,
                &mut value_scope,
                label_scope,
                next_block,
                compilation_unit,
            )
        }
        hir::Block { statements, tail: None } => {
            // Put temp blocks between each statement, which are NOPs except
            // jumping to the next  statement. The last temp block is replaced
            // with the _dst = () block, and then jumps to `next_block`.
            let mut prev_intermediate_block = body.temp_block();
            let initial_block = prev_intermediate_block.as_basic_block_idx();
            for stmt in statements {
                let next_intermediate_block = body.temp_block();
                let dst = lower_statement(
                    stmt,
                    ctx,
                    body,
                    &mut value_scope,
                    label_scope,
                    next_intermediate_block.as_basic_block_idx(),
                    compilation_unit,
                );
                prev_intermediate_block.update(
                    body,
                    vec![],
                    Terminator::Goto { target: dst },
                );
                prev_intermediate_block = next_intermediate_block;
            }

            prev_intermediate_block.update(
                body,
                vec![],
                Terminator::Goto { target: next_block },
            );
            initial_block
        }
        hir::Block { statements, tail: Some(tail) } => {
            // Put temp blocks between each statement, which are NOPs except
            // jumping to the next  statement. The last temp block jumps to the
            // expression evaluation, which then jumps to `next_block`.
            let mut prev_intermediate_block = body.temp_block();
            let initial_block = prev_intermediate_block.as_basic_block_idx();
            for stmt in statements {
                let next_intermediate_block = body.temp_block();
                let dst = lower_statement(
                    stmt,
                    ctx,
                    body,
                    &mut value_scope,
                    label_scope,
                    next_intermediate_block.as_basic_block_idx(),
                    compilation_unit,
                );
                prev_intermediate_block.update(
                    body,
                    vec![],
                    Terminator::Goto { target: dst },
                );
                prev_intermediate_block = next_intermediate_block;
            }
            let expr_block = lower_value_expression(
                tail,
                ctx,
                dst,
                body,
                &mut value_scope,
                label_scope,
                next_block,
                compilation_unit,
            );

            prev_intermediate_block.update(
                body,
                vec![],
                Terminator::Goto { target: expr_block },
            );
            initial_block
        }
    }
}

/// Lowers the evaluation of matching a pattern against a source to basic
/// blocks.
///
/// Locals will be inserted for `ident` patterns.
///
/// Returns the initial BasicBlock. If no basic blocks are required to lower the
/// pattern matching (e.g. for wildcard or ident patterns), then `next_block`
/// may be returned.
fn lower_pattern(
    pattern: &hir::Pattern, ctx: &HirCtx, src: SlotIdx, body: &mut Body,
    value_scope: &mut Scope<'_, Symbol, (Mutability, SlotIdx)>,
    next_block: BasicBlockIdx, compilation_unit: &mut CompilationUnit,
) -> BasicBlockIdx {
    let src_ty = body.slots[src.0];
    match pattern {
        hir::Pattern::Wildcard => {
            // Don't actually need to do anything
            next_block
        }
        &hir::Pattern::Ident { mutability, ident } => {
            // Create a new slot for the new variable, and insert an assignment
            // operation
            let new_slot = body.new_slot(src_ty);
            assert!(
                value_scope.insert(ident, (mutability, new_slot)).is_none(),
                "duplicate local {ident}"
            );
            let op = BasicOperation::Assign(
                Place::from(new_slot),
                Value::Operand(Operand::Copy(Place::from(src))),
            );
            body.insert_block(BasicBlock {
                operations: vec![op],
                terminator: Terminator::Goto { target: next_block },
            })
        }
        hir::Pattern::Array(_) => unimplemented!("array-patterns"),
        hir::Pattern::Tuple(_) => unimplemented!("tuple-patterns"),
        hir::Pattern::Alt(_) => unimplemented!("alt-patterns"),
        hir::Pattern::Integer(_) | hir::Pattern::Range { .. } => {
            unimplemented!("non-exhaustive patterns")
        }
    }
}

struct LabelDestination {
    /// Where to jump to after a `break`.
    break_dst: BasicBlockIdx,
    /// Where to write the value to before jumping to `break_dst`.
    break_value_slot: SlotIdx,
    /// Where to jump to after a `continue`.
    continue_dst: Option<BasicBlockIdx>,
}

/// Lower a non-short-circuiting Arithmetic or Comparison BinaryOp expression.
fn lower_normal_binary_op_expression(
    lhs: &hir::Expression, rhs: &hir::Expression, op: BinaryOp, ctx: &HirCtx,
    dst: SlotIdx, body: &mut Body,
    value_scope: &mut Scope<'_, Symbol, (Mutability, SlotIdx)>,
    label_scope: &mut Scope<'_, BlockLabel, LabelDestination>,
    next_block: BasicBlockIdx, compilation_unit: &mut CompilationUnit,
) -> BasicBlockIdx {
    // bb0 {
    //  lhs_slot = evaluate lhs;
    //  goto -> bb1;
    // }
    // bb1 {
    //  goto -> bb2;
    // }
    // bb2 {
    //  rhs_slot = evaluate rhs;
    //  goto -> bb3;
    // }
    // bb3 {
    //  _0 = Add(lhs_slot, rhs_slot); // or whatever op
    //  goto -> next_block;
    // }
    let lhs_slot = body.new_slot(compilation_unit.lower_type(lhs.type_, ctx));
    let rhs_slot = body.new_slot(compilation_unit.lower_type(rhs.type_, ctx));
    let bb1 = body.temp_block();
    let bb3 = body.temp_block();
    let bb0 = lower_value_expression(
        lhs,
        ctx,
        lhs_slot,
        body,
        value_scope,
        label_scope,
        bb1.as_basic_block_idx(),
        compilation_unit,
    );
    let bb2 = lower_value_expression(
        rhs,
        ctx,
        rhs_slot,
        body,
        value_scope,
        label_scope,
        bb3.as_basic_block_idx(),
        compilation_unit,
    );
    bb1.update(body, vec![], Terminator::Goto { target: bb2 });
    bb3.update(
        body,
        vec![BasicOperation::Assign(
            Place::from(dst),
            Value::BinaryOp(
                op,
                Operand::Copy(Place::from(lhs_slot)),
                Operand::Copy(Place::from(rhs_slot)),
            ),
        )],
        Terminator::Goto { target: next_block },
    );

    bb0
}

/// Lowers a value-expression into BasicBlocks which evaluate the expression,
/// write the result to `dst`, and then jump to `next_block`.
///
/// Returns the initial BasicBlockIdx.
fn lower_value_expression(
    expr: &hir::Expression, ctx: &HirCtx, dst_slot: SlotIdx, body: &mut Body,
    value_scope: &mut Scope<'_, Symbol, (Mutability, SlotIdx)>,
    label_scope: &mut Scope<'_, BlockLabel, LabelDestination>,
    next_block: BasicBlockIdx, compilation_unit: &mut CompilationUnit,
) -> BasicBlockIdx {
    let orig_expr = expr;
    let _expr = (); // prevent accidentally stack-overflowing from passing the wrong expression
    match &orig_expr.kind {
        hir::ExpressionKind::Ident(name) => {
            let ops = match value_scope.lookup(name) {
                Some(&(_, local)) => vec![BasicOperation::Assign(
                    Place::from(dst_slot),
                    Value::Operand(Operand::Copy(Place::from(local))),
                )],
                None => match compilation_unit.globals.get(name) {
                    Some((item_idx, type_idx)) => {
                        // for static:
                        //   _tmp = Operand::Constant(Constant::GlobalAddress(global_idx));
                        //   _dst = Operand::Copy(*_tmp);
                        // for fn/string literal:
                        //   _dst = Operand::Constant(Constant::GlobalAddress(global_idx));

                        match compilation_unit.items[item_idx.0].as_ref() {
                            Either::Left(
                                ItemKind::DeclaredExternStatic { .. }
                                | ItemKind::DefinedExternStatic { .. }
                                | ItemKind::LocalStatic { .. },
                            )
                            | Either::Right(ItemKindStub::Static { .. }) => {
                                let addr_ty = compilation_unit.insert_type(
                                    TypeKind::Pointer {
                                        mutability: Mutability::Constant,
                                        pointee: *type_idx,
                                    },
                                );
                                let addr_slot = body.new_slot(addr_ty);
                                vec![
                                    BasicOperation::Assign(
                                        Place::from(addr_slot),
                                        Value::Operand(Operand::Constant(
                                            Constant::ItemAddress(*name),
                                        )),
                                    ),
                                    BasicOperation::Assign(
                                        Place::from(dst_slot),
                                        Value::Operand(Operand::Copy(Place {
                                            local: addr_slot,
                                            projection: Some(
                                                PlaceProjection::Deref,
                                            ),
                                        })),
                                    ),
                                ]
                            }
                            Either::Left(
                                ItemKind::DeclaredExternFn { .. }
                                | ItemKind::DefinedExternFn { .. }
                                | ItemKind::LocalFn { .. }
                                | ItemKind::StringLiteral { .. },
                            )
                            | Either::Right(ItemKindStub::Fn) => {
                                vec![BasicOperation::Assign(
                                    Place::from(dst_slot),
                                    Value::Operand(Operand::Constant(
                                        Constant::ItemAddress(*name),
                                    )),
                                )]
                            }
                        }
                    }
                    None => unreachable!("no value {name} in scope"),
                },
            };
            let block = BasicBlock {
                operations: ops,
                terminator: Terminator::Goto { target: next_block },
            };
            body.insert_block(block)
        }
        hir::ExpressionKind::Integer(value) => {
            let Some(&hir::TypeKind::Integer { signed, bits }) =
                ctx.resolve_ty(orig_expr.type_)
            else {
                unreachable!("integer expression's type is not integral")
            };
            let op = BasicOperation::Assign(
                Place::from(dst_slot),
                Value::Operand(Operand::Constant(Constant::Integer {
                    value: value.value,
                    signed,
                    bits,
                })),
            );
            let block = BasicBlock {
                operations: vec![op],
                terminator: Terminator::Goto { target: next_block },
            };
            body.insert_block(block)
        }
        &hir::ExpressionKind::Bool(value) => {
            let op = BasicOperation::Assign(
                Place::from(dst_slot),
                Value::Operand(Operand::Constant(Constant::Bool(value))),
            );
            let block = BasicBlock {
                operations: vec![op],
                terminator: Terminator::Goto { target: next_block },
            };
            body.insert_block(block)
        }
        hir::ExpressionKind::StringLiteral(literal) => {
            // create an anonymous static, and load its address
            let (anon_global, _) = compilation_unit
                .make_anonymous_static_for_string_literal(literal.data);
            let op = BasicOperation::Assign(
                Place::from(dst_slot),
                Value::Operand(Operand::Constant(Constant::ItemAddress(
                    anon_global,
                ))),
            );
            let block = BasicBlock {
                operations: vec![op],
                terminator: Terminator::Goto { target: next_block },
            };
            body.insert_block(block)
        }
        hir::ExpressionKind::Array(_) => unimplemented!("arrays"),
        hir::ExpressionKind::Tuple(_) => unimplemented!("tuples"),
        hir::ExpressionKind::UnaryOp { op, operand } => match op {
            hir::UnaryOp::Not | hir::UnaryOp::Neg => {
                let operand_slot = body
                    .new_slot(compilation_unit.lower_type(operand.type_, ctx));
                let not_block = body.temp_block();
                let initial_block = lower_value_expression(
                    operand,
                    ctx,
                    operand_slot,
                    body,
                    value_scope,
                    label_scope,
                    not_block.as_basic_block_idx(),
                    compilation_unit,
                );

                let value_constructor = match op {
                    UnaryOp::Not => Value::Not,
                    UnaryOp::Neg => Value::Negate,
                    _ => unreachable!(),
                };

                not_block.update(
                    body,
                    vec![BasicOperation::Assign(
                        Place::from(dst_slot),
                        value_constructor(Box::new(Value::Operand(
                            Operand::Copy(Place::from(operand_slot)),
                        ))),
                    )],
                    Terminator::Goto { target: next_block },
                );
                initial_block
            }
            &hir::UnaryOp::AddrOf { mutable } => {
                log::warn!("TODO: refactor this into a separate function");
                let addr_of_mutability = Mutability::from_bool(mutable);
                match &operand.kind {
                    hir::ExpressionKind::Ident(symbol) => {
                        match value_scope.lookup(symbol) {
                            Some(&(local_mutability, local)) => {
                                assert!(
                                    local_mutability >= addr_of_mutability,
                                    "cannot take the mutable address of \
                                     non-mut local {symbol} (TODO: \
                                     type-checking should have caught this)"
                                );
                                body.insert_block(BasicBlock {
                                    operations: vec![BasicOperation::Assign(
                                        Place::from(dst_slot),
                                        Value::AddressOf(
                                            Mutability::from_bool(mutable),
                                            Place::from(local),
                                        ),
                                    )],
                                    terminator: Terminator::Goto {
                                        target: next_block,
                                    },
                                })
                            }
                            None => match compilation_unit.globals.get(symbol) {
                                Some((item, type_idx)) => {
                                    match compilation_unit.items[item.0] {
                                        Either::Left(
                                            ItemKind::DeclaredExternFn {
                                                ..
                                            }
                                            | ItemKind::DefinedExternFn {
                                                ..
                                            }
                                            | ItemKind::LocalFn { .. },
                                        )
                                        | Either::Right(ItemKindStub::Fn) => {
                                            panic!(
                                                "cannot take address of \
                                                 function {symbol}"
                                            )
                                        }
                                        Either::Left(
                                            ItemKind::StringLiteral { .. },
                                        ) => {
                                            panic!(
                                                "cannot take address of \
                                                 string literal"
                                            )
                                        }
                                        Either::Left(
                                            ItemKind::LocalStatic {
                                                mutability: static_mutability,
                                                ..
                                            }
                                            | ItemKind::DefinedExternStatic {
                                                mutability: static_mutability,
                                                ..
                                            }
                                            | ItemKind::DeclaredExternStatic {
                                                mutability: static_mutability,
                                                ..
                                            },
                                        )
                                        | Either::Right(
                                            ItemKindStub::Static {
                                                mutability: static_mutability,
                                            },
                                        ) => {
                                            assert!(
                                                static_mutability
                                                    >= addr_of_mutability,
                                                "cannot take the mutable \
                                                 address of non-mut local \
                                                 {symbol} (TODO: \
                                                 type-checking should have \
                                                 caught this)"
                                            );
                                            let ops = vec![
                                                BasicOperation::Assign(
                                                    Place::from(dst_slot),
                                                    Value::Operand(Operand::Constant(
                                                        Constant::ItemAddress(*symbol),
                                                    )),
                                                ),
                                            ];
                                            body.insert_block(BasicBlock {
                                                operations: ops,
                                                terminator: Terminator::Goto {
                                                    target: next_block,
                                                },
                                            })
                                        }
                                    }
                                }
                                None => unreachable!(
                                    "unresolved symbol {symbol} \
                                     (type-checking should have caught this)"
                                ),
                            },
                        }
                    }
                    hir::ExpressionKind::Array(_) => {
                        unimplemented!("address of array")
                    }
                    hir::ExpressionKind::Tuple(_) => {
                        unimplemented!("address of tuple")
                    }
                    hir::ExpressionKind::Index { base, index } => {
                        let index_slot = body.new_slot(
                            compilation_unit.lower_type(index.type_, ctx),
                        );

                        let base_ty =
                            compilation_unit.lower_type(base.type_, ctx);
                        let base_tykind = &compilation_unit.types[base_ty.0];

                        match base_tykind {
                            TypeKind::Pointer { .. } => {
                                // Evaluate pointer into new slot, then evaluate
                                // index, then write addr of indexed place into
                                // dst_slot
                                let after_base_before_index_block =
                                    body.temp_block();
                                let ptr_slot = body.new_slot(base_ty);
                                let base_initial_block = lower_value_expression(
                                    base,
                                    ctx,
                                    ptr_slot,
                                    body,
                                    value_scope,
                                    label_scope,
                                    after_base_before_index_block
                                        .as_basic_block_idx(),
                                    compilation_unit,
                                );
                                let after_index_block = body.temp_block();
                                let index_initial_block =
                                    lower_value_expression(
                                        index,
                                        ctx,
                                        index_slot,
                                        body,
                                        value_scope,
                                        label_scope,
                                        after_index_block.as_basic_block_idx(),
                                        compilation_unit,
                                    );
                                after_base_before_index_block.update(
                                    body,
                                    vec![],
                                    Terminator::Goto {
                                        target: index_initial_block,
                                    },
                                );
                                let ops = vec![BasicOperation::Assign(
                                    Place { local: dst_slot, projection: None },
                                    Value::AddressOf(
                                        addr_of_mutability,
                                        Place {
                                            local: ptr_slot,
                                            projection: Some(
                                                PlaceProjection::DerefIndex(
                                                    index_slot,
                                                ),
                                            ),
                                        },
                                    ),
                                )];
                                after_index_block.update(
                                    body,
                                    ops,
                                    Terminator::Goto { target: next_block },
                                );
                                base_initial_block
                            }
                            TypeKind::Array { .. } => {
                                unimplemented!("arrays not implemented")
                            }
                            TypeKind::Slice { .. } => {
                                unimplemented!("slices not implemented")
                            }
                            TypeKind::Tuple(_) => {
                                unimplemented!("tuples not implemented")
                            }
                            _ => unreachable!(
                                "cannot index {base_ty:?} (TODO: \
                                 type-checking should have caught this)"
                            ),
                        }
                    }
                    // &* cancels out
                    hir::ExpressionKind::UnaryOp {
                        op: UnaryOp::Deref,
                        operand,
                    } => {
                        unimplemented!(
                            "assignment to deref (For now, just do ptr[0] = \
                             ...)"
                        )
                    }

                    hir::ExpressionKind::Wildcard
                    | hir::ExpressionKind::UnaryOp { .. }
                    | hir::ExpressionKind::If { .. }
                    | hir::ExpressionKind::Loop { .. }
                    | hir::ExpressionKind::Block { .. }
                    | hir::ExpressionKind::Match { .. }
                    | hir::ExpressionKind::Call { .. }
                    | hir::ExpressionKind::Continue { .. }
                    | hir::ExpressionKind::Break { .. }
                    | hir::ExpressionKind::Return { .. }
                    | hir::ExpressionKind::Integer(_)
                    | hir::ExpressionKind::StringLiteral(_)
                    | hir::ExpressionKind::Bool(_)
                    | hir::ExpressionKind::BinaryOp { .. } => {
                        panic!(
                            "can only take address of local variables, \
                             statics, and pointer-based index expressions \
                             items, not {operand:?}"
                        )
                    }
                }
            }
            hir::UnaryOp::Deref => {
                let operand_slot = body
                    .new_slot(compilation_unit.lower_type(operand.type_, ctx));
                let deref_block = body.temp_block();
                let initial_block = lower_value_expression(
                    operand,
                    ctx,
                    operand_slot,
                    body,
                    value_scope,
                    label_scope,
                    deref_block.as_basic_block_idx(),
                    compilation_unit,
                );

                deref_block.update(
                    body,
                    vec![BasicOperation::Assign(
                        Place::from(dst_slot),
                        Value::Operand(Operand::Copy(Place {
                            local: operand_slot,
                            projection: Some(PlaceProjection::Deref),
                        })),
                    )],
                    Terminator::Goto { target: next_block },
                );
                initial_block
            }
            hir::UnaryOp::AsCast { to_type } => todo!(),
        },
        hir::ExpressionKind::BinaryOp { lhs, op, rhs } => match op {
            crate::ast::BinaryOp::Assignment => lower_assignment_expression(
                lhs,
                rhs,
                ctx,
                body,
                value_scope,
                label_scope,
                next_block,
                compilation_unit,
            ),
            crate::ast::BinaryOp::Arithmetic(arith_op) => {
                if arith_op.is_short_circuit() {
                    todo!("short-circuiting ops");
                } else {
                    lower_normal_binary_op_expression(
                        lhs,
                        rhs,
                        *op,
                        ctx,
                        dst_slot,
                        body,
                        value_scope,
                        label_scope,
                        next_block,
                        compilation_unit,
                    )
                }
            }
            crate::ast::BinaryOp::Comparison(_) => {
                lower_normal_binary_op_expression(
                    lhs,
                    rhs,
                    *op,
                    ctx,
                    dst_slot,
                    body,
                    value_scope,
                    label_scope,
                    next_block,
                    compilation_unit,
                )
            }
            crate::ast::BinaryOp::RangeOp { .. } => unreachable!(
                "range ops are only part of syntax of for loops and should \
                 not be in HIR"
            ),
        },
        hir::ExpressionKind::If { condition, then_block, else_block } => {
            // bb0: {
            //    _1 = evaluate condition;
            //    goto bb1;
            // }
            // bb1: {
            //    switch_bool _1 [true -> then_block, false -> else_block]
            // }
            // then_block: {
            //     _0 = then_block;
            //     goto next_block;
            // }
            // else_block: {
            //     _0 = else_block or () if None;
            //     goto next_block;
            // }
            let switch_block_idx = body.temp_block();
            let condition_slot = body.new_slot(compilation_unit.bool_type());
            let evaluate_condition_block = lower_value_expression(
                condition,
                ctx,
                condition_slot,
                body,
                value_scope,
                label_scope,
                switch_block_idx.as_basic_block_idx(),
                compilation_unit,
            );
            let then_block_idx = lower_block(
                then_block,
                ctx,
                dst_slot,
                body,
                value_scope,
                label_scope,
                next_block,
                compilation_unit,
            );
            // If there is no else block, the SwitchBool should just go to
            // next_block in that case
            let else_block_idx = match else_block {
                Some(else_block) => lower_block(
                    else_block,
                    ctx,
                    dst_slot,
                    body,
                    value_scope,
                    label_scope,
                    next_block,
                    compilation_unit,
                ),
                None => next_block,
            };
            switch_block_idx.update(
                body,
                vec![],
                Terminator::SwitchBool {
                    scrutinee: LocalOrConstant::Local(condition_slot),
                    true_dst: then_block_idx,
                    false_dst: else_block_idx,
                },
            );
            evaluate_condition_block
        }
        hir::ExpressionKind::Loop { label, body: block } => {
            let initial_block = body.temp_block();
            let mut label_scope = Scope::new(Some(label_scope));
            let label = label.expect("Loop should have label");
            label_scope.insert(
                label,
                LabelDestination {
                    break_dst: next_block,
                    break_value_slot: dst_slot,
                    continue_dst: Some(initial_block.as_basic_block_idx()),
                },
            );

            let block_dst = body.new_slot(compilation_unit.unit_type());

            let body_initial_idx = lower_block(
                block,
                ctx,
                block_dst,
                body,
                value_scope,
                &mut label_scope,
                initial_block.as_basic_block_idx(),
                compilation_unit,
            );
            initial_block.update(
                body,
                vec![],
                Terminator::Goto { target: body_initial_idx },
            )
        }
        hir::ExpressionKind::Block { label, body: block } => {
            let mut label_scope = Scope::new(Some(label_scope));
            if let &Some(label) = label {
                label_scope.insert(
                    label,
                    LabelDestination {
                        break_dst: next_block,
                        break_value_slot: dst_slot,
                        continue_dst: None,
                    },
                );
            }
            lower_block(
                block,
                ctx,
                dst_slot,
                body,
                value_scope,
                &mut label_scope,
                next_block,
                compilation_unit,
            )
        }
        hir::ExpressionKind::Match { .. } => {
            unimplemented!("match expressions not implemented")
        }
        hir::ExpressionKind::Wildcard => panic!(
            "wildcard expressions should only happen in the lhs of assignment \
             ops (i.e. place-expressions), which should not use \
             lower_expression"
        ),
        hir::ExpressionKind::Index { base, index } => {
            let index_slot =
                body.new_slot(compilation_unit.lower_type(index.type_, ctx));

            let intermediate_block = body.temp_block();

            let base_ty = compilation_unit.lower_type(base.type_, ctx);
            let base_tykind = &compilation_unit.types[base_ty.0];

            match base_tykind {
                TypeKind::Pointer { .. } => {
                    // Evaluate pointer into new slot, then evalute index into
                    // new slot, then Index into pointer
                    let ptr_slot = body.new_slot(base_ty);
                    let initial_block = lower_value_expression(
                        base,
                        ctx,
                        ptr_slot,
                        body,
                        value_scope,
                        label_scope,
                        intermediate_block.as_basic_block_idx(),
                        compilation_unit,
                    );
                    let after_index_block = body.temp_block();
                    let index_initial_block = lower_value_expression(
                        index,
                        ctx,
                        index_slot,
                        body,
                        value_scope,
                        label_scope,
                        after_index_block.as_basic_block_idx(),
                        compilation_unit,
                    );
                    intermediate_block.update(
                        body,
                        vec![],
                        Terminator::Goto { target: index_initial_block },
                    );
                    let ops = vec![BasicOperation::Assign(
                        Place::from(dst_slot),
                        Value::Operand(Operand::Copy(Place {
                            local: ptr_slot,
                            projection: Some(PlaceProjection::DerefIndex(
                                index_slot,
                            )),
                        })),
                    )];
                    after_index_block.update(
                        body,
                        ops,
                        Terminator::Goto { target: next_block },
                    );
                    initial_block
                }
                TypeKind::Array { element, length } => todo!(),
                TypeKind::Slice { element } => todo!(),
                TypeKind::Tuple(_) => todo!(),
                _ => unreachable!(
                    "cannot index {base_ty:?} (TODO: type-checking should \
                     have caught this)"
                ),
            }
        }
        hir::ExpressionKind::Call { function, args } => {
            // Create slots for the function and each argument, then evaluate
            // the function, then evaluate the arguments, then call the
            // function.

            let func_slot =
                body.new_slot(compilation_unit.lower_type(function.type_, ctx));
            let arg_slots = args
                .iter()
                .map(|expr| {
                    body.new_slot(compilation_unit.lower_type(expr.type_, ctx))
                })
                .collect_vec();

            let mut intermediate_block = body.temp_block();
            let initial_block = lower_value_expression(
                function,
                ctx,
                func_slot,
                body,
                value_scope,
                label_scope,
                intermediate_block.as_basic_block_idx(),
                compilation_unit,
            );

            for (expr, &arg_slot) in std::iter::zip(args, &arg_slots) {
                let next_intermediate_block = body.temp_block();
                let expr_initial_block = lower_value_expression(
                    expr,
                    ctx,
                    arg_slot,
                    body,
                    value_scope,
                    label_scope,
                    next_intermediate_block.as_basic_block_idx(),
                    compilation_unit,
                );
                intermediate_block.update(
                    body,
                    vec![],
                    Terminator::Goto { target: expr_initial_block },
                );
                intermediate_block = next_intermediate_block;
            }

            // This is now the last block
            intermediate_block.update(
                body,
                vec![],
                Terminator::Call {
                    func: Value::Operand(Operand::Copy(Place::from(func_slot))),
                    args: arg_slots
                        .into_iter()
                        .map(|arg_slot| {
                            Value::Operand(Operand::Copy(Place::from(arg_slot)))
                        })
                        .collect_vec(),
                    return_destination: Place::from(dst_slot),
                    target: next_block,
                },
            );

            initial_block
        }
        hir::ExpressionKind::Return { value } => {
            let return_block = body.temp_block();
            match value {
                Some(expr) => {
                    let initial_block = lower_value_expression(
                        expr,
                        ctx,
                        SlotIdx(0),
                        body,
                        value_scope,
                        label_scope,
                        return_block.as_basic_block_idx(),
                        compilation_unit,
                    );
                    return_block.update(body, vec![], Terminator::Return);
                    initial_block
                }
                None => return_block.update(body, vec![], Terminator::Return),
            }
        }
        hir::ExpressionKind::Break { label, value } => {
            let label = label.expect(
                "all break expressions should have labels after type checking",
            );
            let label_destination = label_scope.lookup(&label).expect(
                "all break expressions should have valid labels after type \
                 checking",
            );
            let break_value_slot = label_destination.break_value_slot;
            let break_dst = label_destination.break_dst;
            match value {
                Some(expr) => lower_value_expression(
                    expr,
                    ctx,
                    break_value_slot,
                    body,
                    value_scope,
                    label_scope,
                    break_dst,
                    compilation_unit,
                ),
                None => body.insert_block(BasicBlock {
                    operations: vec![],
                    terminator: Terminator::Goto { target: break_dst },
                }),
            }
        }
        hir::ExpressionKind::Continue { label } => {
            let label = label.expect(
                "all break expressions should have labels after type checking",
            );
            let label_destination = label_scope.lookup(&label).expect(
                "all break expressions should have valid labels after type \
                 checking",
            );
            let continue_dst = label_destination
                .continue_dst
                .expect("cannot continue from non-loop context");
            body.insert_block(BasicBlock {
                operations: vec![],
                terminator: Terminator::Goto { target: continue_dst },
            })
        }
    }
}

/// Lowers an assignment-expression into BasicBlocks which evaluate the
/// assignment and then jump to `next_block`.
///
/// Evaluates the *rhs* first (in contrast to "normal" binary operations)
///
/// Returns the initial BasicBlockIdx.
fn lower_assignment_expression(
    lhs: &hir::Expression, rhs: &hir::Expression, ctx: &HirCtx,
    body: &mut Body,
    value_scope: &mut Scope<'_, Symbol, (Mutability, SlotIdx)>,
    label_scope: &mut Scope<'_, BlockLabel, LabelDestination>,
    next_block: BasicBlockIdx, compilation_unit: &mut CompilationUnit,
) -> BasicBlockIdx {
    let intermediate_block = body.temp_block();
    let intermediate_slot =
        body.new_slot(compilation_unit.lower_type(rhs.type_, ctx));
    let initial_block_idx = lower_value_expression(
        rhs,
        ctx,
        intermediate_slot,
        body,
        value_scope,
        label_scope,
        intermediate_block.as_basic_block_idx(),
        compilation_unit,
    );

    match &lhs.kind {
        hir::ExpressionKind::Wildcard => {
            // Don't need to do assign anything
            intermediate_block.update(
                body,
                vec![],
                Terminator::Goto { target: next_block },
            );
        }
        hir::ExpressionKind::Ident(symbol) => {
            match value_scope.lookup(symbol) {
                Some(&(mutability, local)) => {
                    assert!(
                        mutability == Mutability::Mutable,
                        "cannot assign to non-mut local {symbol} (TODO: \
                         type-checking should have caught this)"
                    );
                    intermediate_block.update(
                        body,
                        vec![BasicOperation::Assign(
                            Place::from(local),
                            Value::Operand(Operand::Copy(Place::from(
                                intermediate_slot,
                            ))),
                        )],
                        Terminator::Goto { target: next_block },
                    );
                }
                None => match compilation_unit.globals.get(symbol) {
                    Some((item, type_idx)) => match compilation_unit.items
                        [item.0]
                    {
                        Either::Left(
                            ItemKind::DeclaredExternFn { .. }
                            | ItemKind::DefinedExternFn { .. }
                            | ItemKind::LocalFn { .. },
                        )
                        | Either::Right(ItemKindStub::Fn) => {
                            panic!("cannot assign to function {symbol}")
                        }
                        Either::Left(ItemKind::StringLiteral { .. }) => {
                            panic!("cannot assign to string literal")
                        }
                        Either::Left(
                            ItemKind::LocalStatic { mutability, .. }
                            | ItemKind::DefinedExternStatic {
                                mutability, ..
                            }
                            | ItemKind::DeclaredExternStatic {
                                mutability, ..
                            },
                        )
                        | Either::Right(ItemKindStub::Static { mutability }) => {
                            assert!(
                                mutability == Mutability::Mutable,
                                "cannot assign to immutable static {symbol} \
                                 (TODO: type-checking should have caught this)"
                            );
                            let addr_ty = compilation_unit.insert_type(
                                TypeKind::Pointer {
                                    mutability: Mutability::Mutable,
                                    pointee: *type_idx,
                                },
                            );
                            let addr_slot = body.new_slot(addr_ty);
                            let ops = vec![
                                BasicOperation::Assign(
                                    Place::from(addr_slot),
                                    Value::Operand(Operand::Constant(
                                        Constant::ItemAddress(*symbol),
                                    )),
                                ),
                                BasicOperation::Assign(
                                    Place {
                                        local: addr_slot,
                                        projection: Some(
                                            PlaceProjection::Deref,
                                        ),
                                    },
                                    Value::Operand(Operand::Copy(Place::from(
                                        intermediate_slot,
                                    ))),
                                ),
                            ];
                            intermediate_block.update(
                                body,
                                ops,
                                Terminator::Goto { target: next_block },
                            );
                        }
                    },
                    None => unreachable!(
                        "unresolved symbol {symbol} (type-checking should \
                         have caught this)"
                    ),
                },
            }
        }
        hir::ExpressionKind::Array(_) => {
            unimplemented!("destructuring assignment of array")
        }
        hir::ExpressionKind::Tuple(_) => {
            unimplemented!("destructuring assignment of tuple")
        }
        hir::ExpressionKind::Index { base, index } => {
            let index_slot =
                body.new_slot(compilation_unit.lower_type(index.type_, ctx));

            let base_ty = compilation_unit.lower_type(base.type_, ctx);
            let base_tykind = &compilation_unit.types[base_ty.0];

            match base_tykind {
                TypeKind::Pointer { .. } => {
                    // Evaluate pointer into new slot, then evaluate index, then
                    // write into indexed pointer
                    let after_base_before_index_block = body.temp_block();
                    let ptr_slot = body.new_slot(base_ty);
                    let base_initial_block = lower_value_expression(
                        base,
                        ctx,
                        ptr_slot,
                        body,
                        value_scope,
                        label_scope,
                        after_base_before_index_block.as_basic_block_idx(),
                        compilation_unit,
                    );
                    intermediate_block.update(
                        body,
                        vec![],
                        Terminator::Goto { target: base_initial_block },
                    );
                    let after_index_block = body.temp_block();
                    let index_initial_block = lower_value_expression(
                        index,
                        ctx,
                        index_slot,
                        body,
                        value_scope,
                        label_scope,
                        after_index_block.as_basic_block_idx(),
                        compilation_unit,
                    );
                    after_base_before_index_block.update(
                        body,
                        vec![],
                        Terminator::Goto { target: index_initial_block },
                    );
                    let ops = vec![BasicOperation::Assign(
                        Place {
                            local: ptr_slot,
                            projection: Some(PlaceProjection::DerefIndex(
                                index_slot,
                            )),
                        },
                        Value::Operand(Operand::Copy(Place::from(
                            intermediate_slot,
                        ))),
                    )];
                    after_index_block.update(
                        body,
                        ops,
                        Terminator::Goto { target: next_block },
                    );
                }
                TypeKind::Array { .. } => {
                    unimplemented!("arrays not implemented")
                }
                TypeKind::Slice { .. } => {
                    unimplemented!("slices not implemented")
                }
                TypeKind::Tuple(_) => unimplemented!("tuples not implemented"),
                _ => unreachable!(
                    "cannot index {base_ty:?} (TODO: type-checking should \
                     have caught this)"
                ),
            }
        }
        hir::ExpressionKind::UnaryOp { op: UnaryOp::Deref, .. } => {
            unimplemented!(
                "assignment to deref (For now, just do ptr[0] = ...)"
            )
        }
        hir::ExpressionKind::UnaryOp { .. }
        | hir::ExpressionKind::If { .. }
        | hir::ExpressionKind::Loop { .. }
        | hir::ExpressionKind::Block { .. }
        | hir::ExpressionKind::Match { .. }
        | hir::ExpressionKind::Call { .. }
        | hir::ExpressionKind::Continue { .. }
        | hir::ExpressionKind::Break { .. }
        | hir::ExpressionKind::Return { .. }
        | hir::ExpressionKind::Integer(_)
        | hir::ExpressionKind::StringLiteral(_)
        | hir::ExpressionKind::Bool(_)
        | hir::ExpressionKind::BinaryOp { .. } => {
            panic!(
                "can only assign to local variables and static items, not \
                 {lhs:?}"
            )
        }
    }

    initial_block_idx
}

/// Lowers a statement into BasicBlocks which evaluate the statement and then
/// jump to `next_block`.
///
/// Returns the initial BasicBlockIdx.
fn lower_statement(
    stmt: &hir::Statement, ctx: &HirCtx, body: &mut Body,
    value_scope: &mut Scope<'_, Symbol, (Mutability, SlotIdx)>,
    label_scope: &mut Scope<'_, BlockLabel, LabelDestination>,
    next_block: BasicBlockIdx, compilation_unit: &mut CompilationUnit,
) -> BasicBlockIdx {
    match stmt {
        hir::Statement::LetStatement { pattern, type_, initializer } => {
            match initializer {
                Some(initializer) => {
                    let intermeidate_block = body.temp_block();
                    let intermediate_slot =
                        body.new_slot(compilation_unit.lower_type(*type_, ctx));
                    let initial_block = lower_value_expression(
                        initializer,
                        ctx,
                        intermediate_slot,
                        body,
                        value_scope,
                        label_scope,
                        intermeidate_block.as_basic_block_idx(),
                        compilation_unit,
                    );
                    let pattern_initial_block = lower_pattern(
                        pattern,
                        ctx,
                        intermediate_slot,
                        body,
                        value_scope,
                        next_block,
                        compilation_unit,
                    );
                    intermeidate_block.update(
                        body,
                        vec![],
                        Terminator::Goto { target: pattern_initial_block },
                    );
                    initial_block
                }
                None => {
                    unimplemented!("uninitalized locals not yet implemented")
                }
            }
        }
        hir::Statement::Expression { expression, .. } => {
            // This slot is not referenced by anything else, so it will be
            // optimized out with dead-local-store elimination enabled (once
            // that is implemented).
            let dst = body
                .new_slot(compilation_unit.lower_type(expression.type_, ctx));
            lower_value_expression(
                expression,
                ctx,
                dst,
                body,
                value_scope,
                label_scope,
                next_block,
                compilation_unit,
            )
        }
    }
}

/// Index into Body::slots
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct SlotIdx(usize);

/// Index into Body::basic_blocks
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct BasicBlockIdx(usize);

#[derive(Debug)]
struct BasicBlock {
    operations: Vec<BasicOperation>,
    terminator: Terminator,
}

#[derive(Debug)]
enum LocalOrConstant {
    Local(SlotIdx),
    Constant(Constant),
}

impl fmt::Display for LocalOrConstant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LocalOrConstant::Local(SlotIdx(slot)) => write!(f, "_{slot}"),
            LocalOrConstant::Constant(constant) => write!(f, "{constant}"),
        }
    }
}

#[derive(Debug)]
enum Terminator {
    Goto {
        target: BasicBlockIdx,
    },
    SwitchBool {
        scrutinee: LocalOrConstant,
        true_dst: BasicBlockIdx,
        false_dst: BasicBlockIdx,
    },
    SwitchCmp {
        lhs: LocalOrConstant,
        rhs: LocalOrConstant,
        less_dst: BasicBlockIdx,
        equal_dst: BasicBlockIdx,
        greater_dst: BasicBlockIdx,
    },
    Return,
    /// This basic block is unreachable.
    Unreachable,
    Call {
        func: Value,
        args: Vec<Value>,
        return_destination: Place,
        target: BasicBlockIdx,
    },
    /// This variant is only used when building MIR, and should not occur after
    /// the MIR is built.
    Error,
}

impl fmt::Display for Terminator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Goto { target } => {
                write!(f, "goto -> bb{}", target.0)
            }
            Self::SwitchBool { scrutinee, true_dst, false_dst } => write!(
                f,
                "switchBool({}) -> [false -> bb{}, true -> bb{}]",
                scrutinee, false_dst.0, true_dst.0
            ),
            Self::SwitchCmp { lhs, rhs, less_dst, equal_dst, greater_dst } => {
                write!(
                    f,
                    "switchCmp({}, {}) [less -> bb{}, equal -> bb{}, greater \
                     -> bb{}]",
                    lhs, rhs, less_dst.0, equal_dst.0, greater_dst.0,
                )
            }
            Self::Return => write!(f, "return"),
            Self::Unreachable => write!(f, "unreachable"),
            Self::Error => write!(f, "{{error}}"),
            Self::Call { func, args, return_destination, target } => {
                write!(
                    f,
                    "{} = call {}({}) -> bb{}",
                    return_destination,
                    func,
                    FmtSlice::new(args, ", "),
                    target.0
                )
            }
        }
    }
}

#[derive(Debug)]
enum BasicOperation {
    Assign(Place, Value),
    Nop,
}

impl fmt::Display for BasicOperation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BasicOperation::Assign(place, value) => {
                write!(f, "{place} = {value};")
            }
            BasicOperation::Nop => write!(f, "Nop;"),
        }
    }
}

#[derive(Debug, Clone)]
struct Place {
    local: SlotIdx,
    projection: Option<PlaceProjection>,
}

impl fmt::Display for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut place = format!("_{}", self.local.0);
        if let Some(projection) = &self.projection {
            match projection {
                PlaceProjection::DerefConstantIndex(idx @ 0..) => {
                    place = format!("*({place} + {idx})");
                }
                PlaceProjection::DerefConstantIndex(idx @ ..=-1) => {
                    place = format!("*({place} - {})", idx.unsigned_abs());
                }
                PlaceProjection::DerefIndex(idx) => {
                    place = format!("*({place} + _{})", idx.0);
                }
                PlaceProjection::Deref => {
                    place = format!("*{place}");
                }
            }
        }
        f.write_str(place.as_str())
    }
}

impl From<SlotIdx> for Place {
    fn from(value: SlotIdx) -> Self {
        Self { local: value, projection: None }
    }
}

#[derive(Debug, Clone)]
enum PlaceProjection {
    /// Used for pointer indexing by a constant
    DerefConstantIndex(isize),
    /// Used for pointer indexing by a value
    DerefIndex(SlotIdx),
    /// Equivalent to DerefConstantIndex(0)
    Deref,
}

#[derive(Debug, Clone)]
enum Operand {
    Copy(Place),
    Constant(Constant),
}

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operand::Copy(place) => write!(f, "Copy({place})"),
            Operand::Constant(constant) => write!(f, "{constant}"),
        }
    }
}

#[derive(Debug, Clone)]
enum Value {
    Operand(Operand),
    /// Must be Arithmetic or Comparison.
    BinaryOp(BinaryOp, Operand, Operand),
    Not(Box<Value>),
    Negate(Box<Value>),
    AddressOf(Mutability, Place),
}

impl From<Operand> for Value {
    fn from(value: Operand) -> Self {
        Value::Operand(value)
    }
}

impl From<Constant> for Value {
    fn from(value: Constant) -> Self {
        Value::Operand(Operand::Constant(value))
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Operand(operand) => write!(f, "{operand}"),
            Value::BinaryOp(op, lhs, rhs) => match op {
                BinaryOp::Assignment => unreachable!(
                    "assignment ops should not be lowered to BinaryOp values"
                ),
                BinaryOp::Arithmetic(op) => write!(f, "{op:?}({lhs}, {rhs})"),
                BinaryOp::Comparison(op) => write!(f, "{op:?}({lhs}, {rhs})"),
                BinaryOp::RangeOp { .. } => unreachable!(
                    "range ops are only allowed as part of for-loop syntax \
                     sugar and should not exist in MIR"
                ),
            },
            Value::Not(inner) => write!(f, "Not({inner})"),
            Value::Negate(inner) => write!(f, "Negate({inner})"),
            Value::AddressOf(mutability, place) => {
                write!(f, "&{mutability} {place}")
            }
        }
    }
}

#[derive(Debug, Clone)]
enum Constant {
    Integer { value: u128, signed: bool, bits: Either<u32, PointerSized> },
    Bool(bool),
    Tuple(Arc<[Constant]>),
    ItemAddress(Symbol),
}

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Constant::Integer { value, signed, bits } => {
                let bits = match bits {
                    Either::Left(ref bits) => bits as &dyn std::fmt::Display,
                    Either::Right(_) => &"size",
                };
                if signed {
                    write!(f, "const {i}_u{bits}", i = value as i128)
                } else {
                    write!(f, "const {i}_u{bits}", i = value)
                }
            }
            Constant::Bool(b) => write!(f, "const {b}"),
            Constant::Tuple(ref elems) => {
                write!(f, "const ({})", FmtSlice::new(elems, ", "))
            }
            Constant::ItemAddress(item) => {
                // TODO: print the name?
                write!(f, "const {{&item {}}}", item)
            }
        }
    }
}
