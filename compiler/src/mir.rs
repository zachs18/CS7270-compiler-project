//! Mid-level intermediate representation, appropriate for some optimizations
//! and lowering to assembly.
//!
//! Roughly similar to https://doc.rust-lang.org/stable/nightly-rustc/rustc_middle/mir/index.html

use std::{collections::HashMap, sync::Arc};

use either::Either;

use crate::{
    hir::{self, HirCtx, PointerSized, Symbol},
    token::Ident,
    util::Scope,
};

/// Lower type-checked hir to mir
pub fn lower_hir_to_mir(items: &[hir::Item], ctx: &HirCtx) -> CompilationUnit {
    let mut compilation_unit = CompilationUnit::new();
    compilation_unit.items.resize_with(items.len(), || None);
    for (idx, item) in items.iter().enumerate() {
        let ty = compilation_unit.lower_type(item.type_(), ctx);
        assert!(
            compilation_unit
                .globals
                .insert(item.name(), (GlobalIdx(idx), ty))
                .is_none(),
            "duplicate item {:?}",
            item.name()
        );
    }
    for (idx, item) in items.iter().enumerate() {
        match item {
            hir::Item::FnItem(hir::FnItem {
                name,
                extern_token: None,
                body: None,
                ..
            }) => unreachable!(
                "fn item {name:?} must be extern, have a body, or both"
            ),
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
                let item = GlobalKind::DeclaredExternFn { name };
                compilation_unit.items[idx] = Some(item);
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
                let item = GlobalKind::DeclaredExternStatic {
                    mutable: mut_token.is_some(),
                    name,
                };
                compilation_unit.items[idx] = Some(item);
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
                ..
            }) => {
                let body =
                    Body::new_for_fn(body, ctx, params, &mut compilation_unit);
                let item = if extern_token.is_none() {
                    GlobalKind::LocalFn { body, todo: () }
                } else {
                    let Symbol::Ident(name) = *name else {
                        panic!("extern fn must have non-synthetic name");
                    };
                    GlobalKind::DefinedExternFn { name, body, todo: () }
                };
                compilation_unit.items[idx] = Some(item);
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
                    GlobalKind::LocalStatic {
                        mutable: mut_token.is_some(),
                        initializer: body,
                    }
                } else {
                    let Symbol::Ident(name) = *name else {
                        panic!("extern static must have a non-synthetic name");
                    };
                    GlobalKind::DefinedExternStatic {
                        mutable: mut_token.is_some(),
                        name,
                        initializer: body,
                    }
                };
                compilation_unit.items[idx] = Some(item);
            }
        }
    }
    compilation_unit
}

#[derive(Debug)]
pub struct CompilationUnit {
    types: Vec<TypeKind>,
    /// These should only be `None` between registering globals and resolving
    /// bodies.
    items: Vec<Option<GlobalKind>>,
    globals: HashMap<hir::Symbol, (GlobalIdx, TypeIdx)>,
}

impl CompilationUnit {
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

    fn lower_type(&mut self, ty: hir::TypeIdx, ctx: &HirCtx) -> TypeIdx {
        match ctx
            .resolve_ty(ty)
            .expect("types should all be resolved after hir type checking")
        {
            &hir::TypeKind::Pointer { mutable, pointee } => {
                let tk = TypeKind::Pointer {
                    mutable,
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
}

/// Index into `CompilationUnit::types`.
#[derive(Debug, Clone, Copy)]
pub struct TypeIdx(usize);

#[derive(Debug, Clone)]
pub enum TypeKind {
    Pointer { mutable: bool, pointee: TypeIdx },
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
pub struct GlobalIdx(usize);

#[derive(Debug)]
enum GlobalKind {
    DeclaredExternStatic { name: Ident, mutable: bool },
    DefinedExternStatic { name: Ident, mutable: bool, initializer: Body },
    LocalStatic { mutable: bool, initializer: Body },
    DeclaredExternFn { name: Ident },
    DefinedExternFn { name: Ident, body: Body, todo: () },
    LocalFn { body: Body, todo: () },
}

#[derive(Debug)]
struct Body {
    /// Local variable/temporary slots.
    ///
    /// The return value is always in slot 0.
    ///
    /// For fn items, the arguments are in slots `1..=argc`.
    slots: Vec<TypeIdx>,
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
            basic_blocks: vec![initial_block, terminal_block],
        };

        let mut values: Scope<Symbol, SlotIdx> = Scope::new(None);
        // SlotIdx(0) is always the return value
        let initial_block_idx = lower_expression(
            initializer,
            ctx,
            SlotIdx(0),
            &mut this,
            &mut values,
            BasicBlockIdx(1),
            compilation_unit,
        );
        this.basic_blocks[0].terminator =
            Terminator::Goto { target: initial_block_idx };
        this
    }

    fn new_for_fn(
        body: &hir::Block, ctx: &HirCtx, args: &[hir::FnParam],
        compilation_unit: &mut CompilationUnit,
    ) -> Self {
        todo!()
    }

    fn insert_block(&mut self, block: BasicBlock) -> BasicBlockIdx {
        let idx = self.basic_blocks.len();
        self.basic_blocks.push(block);
        BasicBlockIdx(idx)
    }

    fn insert_assign_unit_block(
        &mut self, dst: SlotIdx, next_block: BasicBlockIdx,
    ) -> BasicBlockIdx {
        let op = BasicOperation::Assign(
            Place::from(dst),
            Value::Constant(Constant::Tuple(Arc::new([]))),
        );
        self.insert_block(BasicBlock {
            operations: vec![op],
            terminator: Terminator::Goto { target: next_block },
        })
    }

    /// Used to create a temporary basic block that will be updated later, when
    /// you need to have a destination for something before the destination is
    /// made.
    fn temp_block(&mut self) -> BasicBlockIdx {
        self.insert_block(BasicBlock {
            operations: vec![],
            terminator: Terminator::Error,
        })
    }

    fn new_slot(&mut self, ty: TypeIdx) -> SlotIdx {
        let idx = self.slots.len();
        self.slots.push(ty);
        SlotIdx(idx)
    }
}

/// Lowers a block into BasicBlocks which evaluate the block, write the
/// result to `dst`, and then jump to `next_block`.
///
/// Returns the initial BasicBlockIdx.
fn lower_block(
    block: &hir::Block, ctx: &HirCtx, dst: SlotIdx, body: &mut Body,
    value_scope: &mut Scope<'_, Symbol, SlotIdx>, next_block: BasicBlockIdx,
    compilation_unit: &mut CompilationUnit,
) -> BasicBlockIdx {
    // 4 cases:
    // * no statements, no tail: assign () to dst
    // * no statements, with tail: assign tail to dst
    // * statements, no tail: lower statements, assign () to dst
    // * statements, with tail: lower statements, assign tail to dst

    match block {
        hir::Block { statements, tail: None } if statements.is_empty() => {
            body.insert_assign_unit_block(dst, next_block)
        }
        hir::Block { statements, tail: Some(tail) }
            if statements.is_empty() =>
        {
            lower_expression(
                tail,
                ctx,
                dst,
                body,
                value_scope,
                next_block,
                compilation_unit,
            )
        }
        hir::Block { statements, tail: None } => {
            // Put temp blocks between each statement, which are NOPs except
            // jumping to the next  statement. The last temp block is replaced
            // with the _dst = () block, and then jumps to `next_block`.
            let mut temp_block = body.temp_block();
            let initial_block = temp_block;
            for stmt in statements {
                let dst = lower_statement(
                    stmt,
                    ctx,
                    body,
                    value_scope,
                    next_block,
                    compilation_unit,
                );
                body.basic_blocks[temp_block.0].terminator =
                    Terminator::Goto { target: dst };
                temp_block = body.temp_block();
            }
            body.basic_blocks[temp_block.0].operations.push(
                BasicOperation::Assign(
                    Place::from(dst),
                    Value::Constant(Constant::Tuple(Arc::new([]))),
                ),
            );
            body.basic_blocks[temp_block.0].terminator =
                Terminator::Goto { target: next_block };
            initial_block
        }
        hir::Block { statements, tail: Some(tail) } => {
            // Put temp blocks between each statement, which are NOPs except
            // jumping to the next  statement. The last temp block jumps to the
            // expression evaluation, which then jumps to `next_block`.
            let mut temp_block = body.temp_block();
            let initial_block = temp_block;
            for stmt in statements {
                let dst = lower_statement(
                    stmt,
                    ctx,
                    body,
                    value_scope,
                    next_block,
                    compilation_unit,
                );
                body.basic_blocks[temp_block.0].terminator =
                    Terminator::Goto { target: dst };
                temp_block = body.temp_block();
            }
            let expr_block = lower_expression(
                tail,
                ctx,
                dst,
                body,
                value_scope,
                next_block,
                compilation_unit,
            );
            body.basic_blocks[temp_block.0].terminator =
                Terminator::Goto { target: expr_block };
            initial_block
        }
    }
}

/// Lowers an expression into BasicBlocks which evaluate the expression,
/// write the result to `dst`, and then jump to `next_block`.
///
/// Returns the initial BasicBlockIdx.
fn lower_expression(
    expr: &hir::Expression, ctx: &HirCtx, dst: SlotIdx, body: &mut Body,
    value_scope: &mut Scope<'_, Symbol, SlotIdx>, next_block: BasicBlockIdx,
    compilation_unit: &mut CompilationUnit,
) -> BasicBlockIdx {
    match &expr.kind {
        hir::ExpressionKind::Ident(name) => {
            let op = BasicOperation::Assign(
                Place::from(dst),
                Value::Copy(Place::from(
                    *value_scope.lookup(name).expect("value should exist"),
                )),
            );
            let block = BasicBlock {
                operations: vec![op],
                terminator: Terminator::Goto { target: next_block },
            };
            body.insert_block(block)
        }
        hir::ExpressionKind::Integer(value) => {
            let op = BasicOperation::Assign(
                Place::from(dst),
                Value::Constant(Constant::Integer(value.value)),
            );
            let block = BasicBlock {
                operations: vec![op],
                terminator: Terminator::Goto { target: next_block },
            };
            body.insert_block(block)
        }
        &hir::ExpressionKind::Bool(value) => {
            let op = BasicOperation::Assign(
                Place::from(dst),
                Value::Constant(Constant::Bool(value)),
            );
            let block = BasicBlock {
                operations: vec![op],
                terminator: Terminator::Goto { target: next_block },
            };
            body.insert_block(block)
        }
        hir::ExpressionKind::StringLiteral(_) => todo!(),
        hir::ExpressionKind::Array(_) => todo!(),
        hir::ExpressionKind::Tuple(_) => todo!(),
        hir::ExpressionKind::UnaryOp { op, operand } => todo!(),
        hir::ExpressionKind::BinaryOp { lhs, op, rhs } => todo!(),
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
            let evaluate_condition_block = lower_expression(
                &condition,
                ctx,
                condition_slot,
                body,
                value_scope,
                switch_block_idx,
                compilation_unit,
            );
            let then_block_idx = lower_block(
                then_block,
                ctx,
                dst,
                body,
                value_scope,
                next_block,
                compilation_unit,
            );
            // If there is no else block, the SwitchBool should just go to
            // next_block in that case
            let else_block_idx = match else_block {
                Some(else_block) => lower_block(
                    else_block,
                    ctx,
                    dst,
                    body,
                    value_scope,
                    next_block,
                    compilation_unit,
                ),
                None => body.insert_assign_unit_block(dst, next_block),
            };
            body.basic_blocks[switch_block_idx.0].terminator =
                Terminator::SwitchBool {
                    scrutinee: condition_slot,
                    true_dst: then_block_idx,
                    false_dst: else_block_idx,
                };
            evaluate_condition_block
        }
        hir::ExpressionKind::Loop { .. } => todo!(),
        hir::ExpressionKind::Block { .. } => todo!(),
        hir::ExpressionKind::Match { scrutinee, arms } => {
            unimplemented!("match expressions not implemented")
        }
        hir::ExpressionKind::Wildcard => panic!(
            "wildcard expressions should only happen in the lhs of assignment \
             ops, which should not use lower_expression"
        ),
        hir::ExpressionKind::Index { base, index } => todo!(),
        hir::ExpressionKind::Call { function, args } => todo!(),
        hir::ExpressionKind::Break { label, value } => todo!(),
        hir::ExpressionKind::Return { value } => todo!(),
        &hir::ExpressionKind::Continue { label } => todo!(),
    }
}

/// Lowers a statement into BasicBlocks which evaluate the statement and then
/// jump to `next_block`.
///
/// Returns the initial BasicBlockIdx.
fn lower_statement(
    stmt: &hir::Statement, ctx: &HirCtx, body: &mut Body,
    value_scope: &mut Scope<'_, Symbol, SlotIdx>, next_block: BasicBlockIdx,
    compilation_unit: &mut CompilationUnit,
) -> BasicBlockIdx {
    todo!()
}

/// Index into Body::slots
#[derive(Debug, Clone, Copy)]
struct SlotIdx(usize);

/// Index into Body::basic_blocks
#[derive(Debug, Clone, Copy)]
struct BasicBlockIdx(usize);

#[derive(Debug)]
struct BasicBlock {
    operations: Vec<BasicOperation>,
    terminator: Terminator,
}

#[derive(Debug)]
enum Terminator {
    Goto {
        target: BasicBlockIdx,
    },
    SwitchBool {
        scrutinee: SlotIdx,
        true_dst: BasicBlockIdx,
        false_dst: BasicBlockIdx,
    },
    SwitchCmp {
        lhs: SlotIdx,
        rhs: SlotIdx,
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

#[derive(Debug)]
enum BasicOperation {
    Assign(Place, Value),
}

#[derive(Debug)]
struct Place {
    local: SlotIdx,
    projections: Vec<PlaceProjection>,
}

impl From<SlotIdx> for Place {
    fn from(value: SlotIdx) -> Self {
        Self { local: value, projections: vec![] }
    }
}

#[derive(Debug)]
enum PlaceProjection {
    /// Used for arrays and tuples (pointer indexing is lowered to addition and
    /// deref)
    ConstantIndex(usize),
    /// Used for arrays (pointer indexing is lowered to addition and deref,
    /// tuples cannot be runtime-indexed)
    Index(SlotIdx),
    Deref,
}

#[derive(Debug)]
enum Value {
    Copy(Place),
    Constant(Constant),
}

#[derive(Debug)]
enum Constant {
    Integer(u128),
    Bool(bool),
    Tuple(Arc<[Constant]>),
    GlobalAddress(GlobalIdx),
}
