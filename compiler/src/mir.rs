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
                extern_token: None,
                body: None,
                ..
            }) => unreachable!("fn item must be extern, have a body, or both"),
            hir::Item::StaticItem(hir::StaticItem {
                extern_token: None,
                initializer: None,
                ..
            }) => unreachable!(
                "static item must be extern, have an initializer, or both"
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
                ..
            }) => {
                let Symbol::Ident(name) = *name else {
                    panic!("extern static must have a non-synthetic name");
                };
                let item = GlobalKind::DeclaredExternStatic { name };
                compilation_unit.items[idx] = Some(item);
            }
            hir::Item::FnItem(hir::FnItem {
                extern_token,
                fn_token,
                name,
                params,
                return_type,
                signature,
                body: Some(body),
                is_variadic,
            }) => todo!(),
            hir::Item::StaticItem(hir::StaticItem {
                extern_token,
                static_token,
                mut_token,
                name,
                type_,
                initializer: Some(initializer),
            }) => {
                let body = Body::new_for_static(
                    initializer,
                    ctx,
                    &mut compilation_unit,
                );
                let item = if extern_token.is_none() {
                    GlobalKind::LocalStatic { initializer: body }
                } else {
                    let Symbol::Ident(name) = *name else {
                        panic!("extern static must have a non-synthetic name");
                    };
                    GlobalKind::DefinedExternStatic { name, initializer: body }
                };
                compilation_unit.items[idx] = Some(item);
            }
        }
    }
    dbg!(&compilation_unit);
    todo!()
}

#[derive(Debug)]
pub struct CompilationUnit {
    types: Vec<TypeKind>,
    /// These should only be `None` between registering globals and resolving
    /// bodies.
    items: Vec<Option<GlobalKind>>,
    globals: HashMap<hir::Symbol, (GlobalIdx, TypeIdx)>,
    todo: (),
}

impl CompilationUnit {
    fn new() -> Self {
        // TypeIdx(0) is unit, 1 is never, 2 is bool, 3..13 are integers
        let mut this = Self {
            types: vec![],
            items: vec![],
            todo: (),
            globals: HashMap::new(),
        };
        this.insert_type(TypeKind::Tuple(Arc::new([])));
        this.insert_type(TypeKind::Never);
        this.insert_type(TypeKind::Bool);
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
            &hir::TypeKind::Slice { element } => todo!(),
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
    DeclaredExternStatic { name: Ident },
    DefinedExternStatic { name: Ident, initializer: Body },
    LocalStatic { initializer: Body },
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
        todo!()
    }
    fn new_for_fn(
        body: &hir::Expression, ctx: &HirCtx, args: &[hir::FnParam],
        compilation_unit: &mut CompilationUnit,
    ) -> Self {
        todo!()
    }
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
    Return,
    Unreachable,
    Call {
        func: Value,
        args: Vec<Value>,
        return_destination: Place,
        target: BasicBlockIdx,
    },
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
    GlobalAddress(GlobalIdx),
}
