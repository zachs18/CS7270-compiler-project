//! Like [`ast`](crate::ast), but type-checked, and with things desugared to
//! simpler constructs:
//!
//! * `while` and `for` desugared to `loop`s with `let`, `if`, and `match`
//! * `if` conditions are not chained
//! * parenthesized around patterns/expressions/types are removed (the "order of
//!   operations" is maintained by the tree structure anyway)
//! * alt-patterns are combined (i.e. `(a | b) | c` is lowered to `a | b | c`).
//! * todo
//!
//! After type-checking, some additional invariants hold:
//!
//! * `Expression::{Break, Loop, Continue}::label` are `Some`
//! * todo

use std::{
    collections::{HashMap, VecDeque},
    hash::Hash,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    },
};

use either::Either;
use once_cell::sync::Lazy;

use crate::{
    ast::{self, BinaryOp, ComparisonOp},
    token::{Ident, Integer, Label, StringLiteral},
    util::{MaybeOwned, Scope, UnionFind},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BlockLabel {
    Label(Label),
    Synthetic(usize),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LabeledBlockKind {
    /// A labeled `for`, `while`, or `loop` loop.
    ///
    /// Can be `break`'d or `continue`'d.
    Loop,
    /// A labeled `{}` block.
    ///
    /// Can be `break`'d but *not* `continue`'d.
    Block,
}

impl BlockLabel {
    fn new_synthetic() -> Self {
        static COUNTER: AtomicUsize = AtomicUsize::new(0);
        Self::Synthetic(COUNTER.fetch_add(1, Ordering::Relaxed))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TypeVarKind {
    Normal,
    Integer,
}

struct TyCtx {
    /// Type unification constraints.
    ///
    /// Type vars which must be the same type.
    constraints: UnionFind,
    /// Type vars
    ///
    /// Map from type var to actual type, if an index is `None`, that type var
    /// has not been resolved yet.
    substitutions: Vec<Either<TypeKind, TypeVarKind>>,
}

static EMPTY_TYPE_LIST: Lazy<Arc<[TypeIdx]>> = Lazy::new(|| Arc::new([]));

impl TyCtx {
    pub fn new() -> (Self, Scope<'static, Symbol, TypeIdx>) {
        // Unit is 0, Bool is 1, Never is 2, integers are 3..11
        let mut this = Self {
            constraints: UnionFind::new(),
            substitutions: Vec::with_capacity(11),
        };
        let mut type_scope = Scope::new(None);
        let unit_idx =
            this.insert_type(TypeKind::Tuple(EMPTY_TYPE_LIST.clone()));
        assert_eq!(unit_idx.0, 0);
        let bool_idx = this.insert_type(TypeKind::Bool);
        assert_eq!(bool_idx.0, 1);
        type_scope
            .insert(Symbol::Ident(Ident::new_unspanned("bool")), bool_idx);
        let never_idx = this.insert_type(TypeKind::Never);
        assert_eq!(never_idx.0, 2);
        macro_rules! bit_integers {
            ($($bits:literal),*) => {
                $(
                    let signed_ident =
                        Symbol::Ident(Ident::new_unspanned(concat!("i", $bits)));
                    let signed_idx = this
                        .insert_type(TypeKind::Integer { signed: true, bits: Either::Left($bits) });
                    type_scope.insert(signed_ident, signed_idx);
                    let unsigned_ident =
                        Symbol::Ident(Ident::new_unspanned(concat!("u", $bits)));
                    let unsigned_idx = this
                        .insert_type(TypeKind::Integer { signed: false, bits: Either::Left($bits) });
                    type_scope.insert(unsigned_ident, unsigned_idx);
                )*
            };
        }
        bit_integers!(8, 16, 32, 64);

        let isize_ident = Symbol::Ident(Ident::new_unspanned("isize"));
        let isize_idx = this.insert_type(TypeKind::Integer {
            signed: true,
            bits: Either::Right(PointerSized),
        });
        type_scope.insert(isize_ident, isize_idx);
        let usize_ident = Symbol::Ident(Ident::new_unspanned("usize"));
        let usize_idx = this.insert_type(TypeKind::Integer {
            signed: false,
            bits: Either::Right(PointerSized),
        });
        type_scope.insert(usize_ident, usize_idx);

        (this, type_scope)
    }

    fn insert_type(&mut self, kind: TypeKind) -> TypeIdx {
        let idx = self.substitutions.len();
        self.substitutions.push(Either::Left(kind));
        self.constraints.insert(idx);
        TypeIdx(idx)
    }

    fn new_var(&mut self) -> TypeIdx {
        let idx = self.substitutions.len();
        self.substitutions.push(Either::Right(TypeVarKind::Normal));
        TypeIdx(idx)
    }

    fn new_integer_var(&mut self) -> TypeIdx {
        let idx = self.substitutions.len();
        self.substitutions.push(Either::Right(TypeVarKind::Integer));
        TypeIdx(idx)
    }

    fn unit_type(&self) -> TypeIdx {
        let type_idx = TypeIdx(0);
        debug_assert!(matches!(
            self.substitutions[type_idx.0].as_ref().left().unwrap(),
            TypeKind::Tuple(types) if types.len() == 0,
        ));
        type_idx
    }

    fn bool_type(&self) -> TypeIdx {
        let type_idx = TypeIdx(1);
        debug_assert!(matches!(
            self.substitutions[type_idx.0].as_ref().left().unwrap(),
            TypeKind::Bool,
        ));
        type_idx
    }

    /// can't use this easily because we don't have coercions, so `something ==
    /// Never` will fail instead of coercing.
    #[cfg(any())]
    fn never_type(&self) -> TypeIdx {
        let type_idx = TypeIdx(2);
        debug_assert!(matches!(
            self.substitutions[type_idx.0].as_ref().left().unwrap(),
            TypeKind::Never,
        ));
        type_idx
    }
}

pub struct HirCtx<'a> {
    /// The types in a scope.
    type_scope: Scope<'a, Symbol, TypeIdx>,
    /// The type of values in a scope.
    ///
    /// HIR does not have a way to say anything about the *values* of such
    /// values.
    value_scope: Scope<'a, Symbol, TypeIdx>,
    ty_ctx: MaybeOwned<'a, TyCtx>,
    /// If we are currently checking a `FnItem`, this is the `FnItem`'s return
    /// type (i.e. the type of `a` in `return a`)
    return_type: Option<TypeIdx>,
    /// If we are currently inside a `Loop`, the last element of this vector is
    /// the `Loop`'s label.
    ///
    /// Used to ensure that `break` and `continue` expressions always have a
    /// label, as this makes mir-building easier.
    nested_loop_labels: MaybeOwned<'a, Vec<BlockLabel>>,
    /// The types of all currently-entered labeled loops or blocks.
    ///
    /// Used to type-check the `value` in that `break 'label value`
    /// expressions, as well as to check that `continue 'label` expressions are
    /// valid.
    labeled_block_types:
        MaybeOwned<'a, HashMap<BlockLabel, (TypeIdx, LabeledBlockKind)>>,
}

impl<'a> HirCtx<'a> {
    fn prelude() -> Self {
        let (ty_ctx, type_scope) = TyCtx::new();
        let value_scope = Scope::new(None);
        Self {
            type_scope,
            value_scope,
            ty_ctx: ty_ctx.into(),
            return_type: None,
            nested_loop_labels: vec![].into(),
            labeled_block_types: HashMap::new().into(),
        }
    }

    /// Returns `None` if the given `TypeIdx` is not a concrete type.
    pub fn resolve_ty(&self, ty: TypeIdx) -> Option<&TypeKind> {
        self.ty_ctx.substitutions.get(ty.0).and_then(|e| e.as_ref().left())
    }

    fn new_parent(parent: &'a mut HirCtx<'_>) -> Self {
        Self {
            type_scope: Scope::new(Some(&parent.type_scope)),
            value_scope: Scope::new(Some(&parent.value_scope)),
            ty_ctx: parent.ty_ctx.borrowed(),
            return_type: parent.return_type,
            nested_loop_labels: parent.nested_loop_labels.borrowed(),
            labeled_block_types: parent.labeled_block_types.borrowed(),
        }
    }

    fn register_globals(&mut self, hir: &[Item]) {
        for item in hir {
            let name = item.name();
            let type_ = item.type_();
            assert!(type_.is_concrete(self), "item type must be concrete");
            if self.value_scope.insert_noreplace(name, type_).is_some() {
                panic!("duplicate item {:?}", item);
            }
        }
    }

    fn register_local(&mut self, name: Symbol, type_: TypeIdx) {
        if self.value_scope.insert_noreplace(name, type_).is_some() {
            panic!("duplicate local {:?}", name);
        }
    }

    /// Returns `true` if a new substitution or constraint was added.
    fn constrain_eq(&mut self, t1: TypeIdx, t2: TypeIdx) -> bool {
        let t1 = TypeIdx(self.ty_ctx.constraints.root_of(t1.0));
        let t2 = TypeIdx(self.ty_ctx.constraints.root_of(t2.0));
        if t1.0 == t2.0 {
            return false;
        }
        let [t1k, t2k] =
            self.ty_ctx.substitutions.get_many_mut([t1.0, t2.0]).unwrap();
        match (&mut *t1k, &mut *t2k) {
            (
                Either::Right(TypeVarKind::Normal),
                Either::Right(TypeVarKind::Normal),
            ) => self.ty_ctx.constraints.union(t1.0, t2.0),

            (
                Either::Right(TypeVarKind::Integer),
                Either::Right(TypeVarKind::Integer),
            ) => self.ty_ctx.constraints.union(t1.0, t2.0),
            (Either::Right(t1k), Either::Right(t2k)) => {
                *t1k = TypeVarKind::Integer;
                *t2k = TypeVarKind::Integer;
                self.ty_ctx.constraints.union(t1.0, t2.0)
            }
            (
                Either::Left(TypeKind::Integer { .. }),
                Either::Right(TypeVarKind::Integer),
            )
            | (Either::Left(..), Either::Right(TypeVarKind::Normal)) => {
                *t2k = t1k.clone();
                self.ty_ctx.constraints.union(t1.0, t2.0)
            }
            (
                Either::Right(TypeVarKind::Integer),
                Either::Left(TypeKind::Integer { .. }),
            )
            | (Either::Right(TypeVarKind::Normal), Either::Left(..)) => {
                *t1k = t2k.clone();
                self.ty_ctx.constraints.union(t1.0, t2.0)
            }
            (Either::Left(ref tk), Either::Right(TypeVarKind::Integer))
            | (Either::Right(TypeVarKind::Integer), Either::Left(ref tk)) => {
                panic!("cannot resolve {{integer}} == {tk:?}");
            }
            (Either::Left(tk1), Either::Left(tk2)) => match (&*tk1, &*tk2) {
                (
                    &TypeKind::Pointer { mutable: m1, pointee: p1 },
                    &TypeKind::Pointer { mutable: m2, pointee: p2 },
                ) => {
                    if m1 != m2 {
                        let mutability = |b| if b { "mut" } else { "const" };
                        panic!(
                            "cannot resolve *{} _ == *{} _",
                            mutability(m1),
                            mutability(m2)
                        );
                    }
                    self.constrain_eq(p1, p2)
                }
                (
                    &TypeKind::Slice { element: e1 },
                    &TypeKind::Slice { element: e2 },
                ) => self.constrain_eq(e1, e2),
                (
                    &TypeKind::Integer { signed: s1, bits: b1 },
                    &TypeKind::Integer { signed: s2, bits: b2 },
                ) => {
                    if s1 != s2 || b1 != b2 {
                        panic!("cannot resolve {t1k:?} == {t2k:?}");
                    }
                    false
                }
                (TypeKind::Tuple(t1s), TypeKind::Tuple(t2s)) => {
                    if t1s.len() != t2s.len() {
                        panic!(
                            "cannot resolve {}-length tuple == {}-length tuple",
                            t1s.len(),
                            t2s.len()
                        );
                    }
                    let t1s = t1s.clone();
                    let t2s = t2s.clone();
                    let mut changed = false;
                    for (&t1, &t2) in std::iter::zip(t1s.iter(), t2s.iter()) {
                        changed |= self.constrain_eq(t1, t2);
                    }
                    changed
                }
                (TypeKind::Never, TypeKind::Never) => false,
                (_, TypeKind::Never) | (TypeKind::Never, _) => {
                    log::warn!("TODO: coercions in a non-hacky way");
                    false
                }
                (
                    &TypeKind::Function {
                        params: ref p1s,
                        return_type: r1,
                        ..
                    },
                    &TypeKind::Function {
                        params: ref p2s,
                        return_type: r2,
                        ..
                    },
                ) => {
                    if p1s.len() != p2s.len() {
                        panic!(
                            "cannot resolve {}-arg fn == {}-arg fn",
                            p1s.len(),
                            p2s.len()
                        );
                    }
                    let p1s = p1s.clone();
                    let p2s = p2s.clone();
                    let mut changed = false;
                    for (&p1, &p2) in std::iter::zip(p1s.iter(), p2s.iter()) {
                        changed |= self.constrain_eq(p1, p2);
                    }
                    changed |= self.constrain_eq(r1, r2);
                    changed
                }
                (TypeKind::Bool, TypeKind::Bool) => false,

                (_, _) => panic!(
                    "cannot resolve {t1:?} == {t2:?}, because {t1k:?} != \
                     {t2k:?}"
                ),
            },
        }
    }

    /// Returns `true` if a new substitution or constraint was added.
    fn constrain_integer(&mut self, ty: TypeIdx) -> bool {
        match self.ty_ctx.substitutions[ty.0] {
            Either::Left(TypeKind::Integer { .. }) => false,
            Either::Left(ref tk) => {
                panic!("cannot resolve {{integer}} == {tk:?}")
            }
            Either::Right(ref mut tv) => {
                let changed = *tv != TypeVarKind::Integer;
                *tv = TypeVarKind::Integer;
                changed
            }
        }
    }

    /// Returns `true` in the first tuple element if a new constraint was added.
    ///
    /// Returns the `TypeIdx` of the pointee type in the second tuple
    /// element.
    fn constrain_pointer(
        &mut self, ty: TypeIdx, mutable: bool,
    ) -> (bool, TypeIdx) {
        match self.ty_ctx.substitutions[ty.0] {
            Either::Left(TypeKind::Pointer { pointee, mutable: m }) => {
                assert_eq!(mutable, m, "cannot resolve *const _ == *mut _");
                (false, pointee)
            }
            Either::Left(ref tk) => {
                panic!("cannot resolve {tk:?} == pointer")
            }
            Either::Right(TypeVarKind::Integer) => {
                panic!("cannot resolve {{integer}} == pointer")
            }
            Either::Right(TypeVarKind::Normal) => {
                let pointee = self.ty_ctx.new_var();
                let tk = TypeKind::Pointer { mutable, pointee };
                self.ty_ctx.substitutions[ty.0] = Either::Left(tk);
                (true, pointee)
            }
        }
    }

    /// Returns `true` in the first tuple element if a new constraint was added.
    ///
    /// Returns the `TypeIdx` of the array element type in the second tuple
    /// element.
    fn constrain_array(
        &mut self, ty: TypeIdx, length: usize,
    ) -> (bool, TypeIdx) {
        match self.ty_ctx.substitutions[ty.0] {
            Either::Right(TypeVarKind::Normal) => {
                let element = self.ty_ctx.new_var();
                self.ty_ctx.substitutions[ty.0] =
                    Either::Left(TypeKind::Array { element, length });
                (true, element)
            }
            Either::Left(TypeKind::Array { element, length: actual_len }) => {
                assert_eq!(
                    length, actual_len,
                    "cannot resolve [_; {length}] == [_; {actual_len}"
                );
                (false, element)
            }
            ref t => {
                panic!("cannot resolve [_; {length}] == {t:?}")
            }
        }
    }

    /// Returns `true` in the first tuple element if a new constraint was added.
    ///
    /// Returns the `TypeIdx`s of the tuple element types in the second tuple
    /// element.
    fn constrain_tuple(
        &mut self, ty: TypeIdx, length: usize,
    ) -> (bool, Arc<[TypeIdx]>) {
        match self.ty_ctx.substitutions[ty.0] {
            Either::Right(TypeVarKind::Normal) => {
                let elements = Arc::from_iter(
                    std::iter::repeat_with(|| self.ty_ctx.new_var())
                        .take(length),
                );
                self.ty_ctx.substitutions[ty.0] =
                    Either::Left(TypeKind::Tuple(elements.clone()));
                (true, elements)
            }
            Either::Left(TypeKind::Tuple(ref elements)) => {
                assert_eq!(
                    length,
                    elements.len(),
                    "cannot resolve {length}-length tuple == {}-length tuple",
                    elements.len()
                );
                (false, elements.clone())
            }
            ref t => {
                panic!("cannot resolve {length}-length tuple == {t:?}")
            }
        }
    }

    /// Returns `true` if a new constraint or substitution was added.
    fn constrain_bool(&mut self, ty: TypeIdx) -> bool {
        match self.ty_ctx.substitutions[ty.0] {
            Either::Right(TypeVarKind::Normal) => {
                self.ty_ctx.substitutions[ty.0] = Either::Left(TypeKind::Bool);
                true
            }
            Either::Left(TypeKind::Bool) => false,
            ref t => panic!("cannot resolve bool == {t:?}"),
        }
    }

    /// Returns `true` if a new constraint or substitution was added.
    ///
    /// Returns the argument types and return type. Note that the argument types
    /// may be shorter than `argc` if the fn is variadic.
    ///
    /// Note: issues may occur if inference decides that a fn is not variadic
    /// when it should be, but hypothetically this shouldn't happen.
    fn constrain_fn(
        &mut self, ty: TypeIdx, argc: usize,
    ) -> (bool, Arc<[TypeIdx]>, TypeIdx) {
        match self.ty_ctx.substitutions[ty.0] {
            Either::Right(TypeVarKind::Normal) => {
                let args = Arc::from_iter(
                    std::iter::repeat_with(|| self.ty_ctx.new_var()).take(argc),
                );
                let return_type = self.ty_ctx.new_var();
                self.ty_ctx.substitutions[ty.0] =
                    Either::Left(TypeKind::Function {
                        params: args.clone(),
                        return_type,
                        is_variadic: false,
                    });
                (true, args, return_type)
            }
            Either::Left(TypeKind::Function {
                ref params,
                return_type,
                is_variadic,
            }) if params.len() == argc
                || (params.len() <= argc && is_variadic) =>
            {
                (false, params.clone(), return_type)
            }
            ref t => {
                panic!("cannot resolve fn({argc} args) -> {{unknown}} == {t:?}")
            }
        }
    }

    /// Returns `true` if a new constraint or substitution was added.
    fn constrain_unit(&mut self, ty: TypeIdx) -> bool {
        match self.ty_ctx.substitutions[ty.0] {
            Either::Right(TypeVarKind::Normal) => {
                self.ty_ctx.substitutions[ty.0] =
                    Either::Left(TypeKind::Tuple(EMPTY_TYPE_LIST.clone()));
                true
            }
            Either::Left(TypeKind::Tuple(ref types)) if types.is_empty() => {
                false
            }
            ref t => panic!("cannot resolve bool == {t:?}"),
        }
    }

    fn type_check_pattern_and_insert_locals(
        &mut self, pattern: &Pattern, type_: TypeIdx,
    ) -> bool {
        match pattern {
            Pattern::Wildcard => false,
            Pattern::Integer(_) | Pattern::Range { .. } => {
                unimplemented!(
                    "non-exhaustive patterns and match expressions not \
                     implemented"
                );
                // self.constrain_integer(type_)
            }
            Pattern::Ident { ident, .. } => {
                self.value_scope.insert_noreplace(*ident, type_);
                false
            }
            Pattern::Alt(_) => unimplemented!("alt patterns not implemented"),
            Pattern::Array(elems) => {
                let (mut changed, elem_ty) =
                    self.constrain_array(type_, elems.len());
                for elem in elems {
                    changed |= self
                        .type_check_pattern_and_insert_locals(elem, elem_ty);
                }
                changed
            }
            Pattern::Tuple(elems) => {
                let (mut changed, elem_tys) =
                    self.constrain_tuple(type_, elems.len());
                for (elem, &elem_ty) in std::iter::zip(elems, elem_tys.iter()) {
                    changed |= self
                        .type_check_pattern_and_insert_locals(elem, elem_ty);
                }
                changed
            }
        }
    }

    /// Constrain `lhs + rhs` expression types.
    ///
    /// Allowed cases:
    ///
    /// * `iN + iN -> iN` (or `uN`)
    /// * `ptr + iN -> ptr` (or `uN`)
    /// * `iN + ptr -> ptr` (or `uN`)
    fn constrain_add(
        &mut self, lhs: TypeIdx, rhs: TypeIdx, result: TypeIdx,
    ) -> bool {
        let mut changed = false;
        let lhs = TypeIdx(self.ty_ctx.constraints.root_of(lhs.0));
        let rhs = TypeIdx(self.ty_ctx.constraints.root_of(rhs.0));
        let result = TypeIdx(self.ty_ctx.constraints.root_of(result.0));
        if lhs.0 == rhs.0
            || (lhs.is_integer(self).unwrap_or(false)
                && rhs.is_integer(self).unwrap_or(false))
        {
            // If lhs and rhs are the same, they must be integers.
            // If lhs and rhs are both integers, they must be the same type.

            // Only integers can be added to themselves, not pointers.
            changed |= self.constrain_integer(lhs);
            // Only same-type integers can be added.
            changed |= self.constrain_eq(lhs, rhs);
            // Adding integers produces the same type;
            changed |= self.constrain_eq(lhs, result);
        } else if lhs.is_pointer(self).unwrap_or(false) {
            // Can only add pointer to integer. lhs is pointer, rhs is integer
            changed |= self.constrain_integer(rhs);
            // `ptr + int -> ptr`
            changed |= self.constrain_eq(lhs, result);
        } else if rhs.is_pointer(self).unwrap_or(false) {
            // Can only add pointer to integer. rhs is pointer, lhs is integer
            changed |= self.constrain_integer(lhs);
            // `int + ptr -> ptr`
            changed |= self.constrain_eq(rhs, result);
        } else {
            // Either lhs or rhs *could* be a poitner
            log::warn!("TODO: type check additions");
        }
        changed
    }

    /// Constrain `lhs - rhs` expression types
    ///
    /// Allowed cases:
    ///
    /// * `iN - iN -> iN` (or `uN`)
    /// * `ptr - isize -> ptr`
    /// * `ptr - usize -> ptr`
    /// * `ptr - ptr -> isize` (same pointee)
    fn constrain_subtract(
        &mut self, lhs: TypeIdx, rhs: TypeIdx, result: TypeIdx,
    ) -> bool {
        let mut changed = false;
        if lhs.is_integer(self).unwrap_or(false) {
            // Can only subtract integer from integer
            // Only same-type integers can be subtracted.
            changed |= self.constrain_eq(lhs, rhs);
            // Subtracting integers produces the same type;
            changed |= self.constrain_eq(lhs, result);
        } else {
            log::warn!("TODO: type check subtractions");
        }
        changed
    }

    /// Constrain `base[index]` expression types.
    ///
    /// Allowed cases:
    ///
    /// * `pointer[iN]` (or `uN`)
    /// * `array[iN]` (or `uN`)
    fn constrain_index(
        &mut self, base: TypeIdx, index: TypeIdx, result: TypeIdx,
    ) -> bool {
        let mut changed = false;
        let base = TypeIdx(self.ty_ctx.constraints.root_of(base.0));
        let index = TypeIdx(self.ty_ctx.constraints.root_of(index.0));
        let result = TypeIdx(self.ty_ctx.constraints.root_of(result.0));

        self.constrain_integer(index);

        match self.ty_ctx.substitutions[base.0] {
            Either::Right(TypeVarKind::Integer) => {
                panic!("cannot index into an integer")
            }
            Either::Right(TypeVarKind::Normal) => {
                log::warn!("TODO: constrain_index");
            }
            Either::Left(TypeKind::Pointer { pointee, .. }) => {
                changed |= self.constrain_eq(pointee, result);
            }
            Either::Left(TypeKind::Array { element, .. }) => {
                changed |= self.constrain_eq(element, result);
            }
            Either::Left(ref t) => panic!("cannot index into a {t:?}"),
        }

        changed
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Symbol {
    Ident(Ident),
    Synthetic(usize),
}

impl std::fmt::Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Ident(ident) => ident.fmt(f),
            Self::Synthetic(idx) => write!(f, "synthetic#{idx}"),
        }
    }
}

impl Symbol {
    pub fn new_synthetic() -> Self {
        static COUNTER: AtomicUsize = AtomicUsize::new(0);
        Self::Synthetic(COUNTER.fetch_add(1, Ordering::Relaxed))
    }
}

#[derive(Debug)]
pub enum Item {
    FnItem(FnItem),
    StaticItem(StaticItem),
}

impl Item {
    pub fn type_(&self) -> TypeIdx {
        match self {
            Item::StaticItem(static_item) => static_item.type_,
            Item::FnItem(fn_item) => fn_item.signature,
        }
    }

    pub fn name(&self) -> Symbol {
        match self {
            Item::FnItem(fn_item) => fn_item.name,
            Item::StaticItem(static_item) => static_item.name,
        }
    }
}

#[derive(Debug)]
pub struct FnItem {
    pub extern_token: Option<Ident>,
    pub fn_token: Ident,
    pub name: Symbol,
    pub params: Vec<FnParam>,
    pub return_type: TypeIdx,
    pub signature: TypeIdx,
    pub body: Option<Block>,
    pub is_variadic: bool,
}

#[derive(Debug)]
pub struct StaticItem {
    pub extern_token: Option<Ident>,
    pub static_token: Ident,
    pub mut_token: Option<Ident>,
    pub name: Symbol,
    pub type_: TypeIdx,
    pub initializer: Option<Expression>,
}

/// An index into `TyCtx`'s vector of types
#[derive(Debug, Clone, Copy)]
pub struct TypeIdx(usize);

#[derive(Debug)]
pub struct FnParam {
    pub pattern: Pattern,
    pub type_: TypeIdx,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PointerSized;

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

impl TypeIdx {
    fn is_concrete(&self, ctx: &HirCtx) -> bool {
        match ctx.ty_ctx.substitutions[self.0] {
            Either::Right(_) => false,
            Either::Left(ref type_kind) => match type_kind {
                TypeKind::Pointer { pointee, .. } => pointee.is_concrete(ctx),
                TypeKind::Array { element, .. } => element.is_concrete(ctx),
                TypeKind::Slice { element } => element.is_concrete(ctx),
                TypeKind::Integer { .. } => true,
                TypeKind::Bool => true,
                TypeKind::Tuple(types) => {
                    types.iter().all(|type_idx| type_idx.is_concrete(ctx))
                }
                TypeKind::Never => true,
                TypeKind::Function { params, return_type, .. } => {
                    return_type.is_concrete(ctx)
                        && params
                            .iter()
                            .all(|type_idx| type_idx.is_concrete(ctx))
                }
            },
        }
    }

    fn is_integer(&self, ctx: &HirCtx) -> Option<bool> {
        match ctx.ty_ctx.substitutions[self.0] {
            Either::Right(TypeVarKind::Integer) => Some(true),
            Either::Right(TypeVarKind::Normal) => None,
            Either::Left(TypeKind::Integer { .. }) => Some(true),
            Either::Left(..) => Some(false),
        }
    }

    fn is_pointer(&self, ctx: &HirCtx) -> Option<bool> {
        match ctx.ty_ctx.substitutions[self.0] {
            Either::Right(TypeVarKind::Integer) => Some(false),
            Either::Right(TypeVarKind::Normal) => None,
            Either::Left(TypeKind::Pointer { .. }) => Some(true),
            Either::Left(..) => Some(false),
        }
    }
}

#[derive(Debug)]
pub enum Pattern {
    Wildcard,
    Ident { mutable: bool, ident: Symbol },
    Integer(Integer),
    Alt(Vec<Self>),
    Array(Vec<Self>),
    Tuple(Vec<Self>),
    Range { start: Integer, inclusive: bool, end: Integer },
}

#[derive(Debug)]
pub struct Expression {
    pub kind: ExpressionKind,
    pub type_: TypeIdx,
}
macro_rules! make_expr_wrappers {
    ($( $fn_name:ident( $($arg:ident : $argty:ty),* $(,)? ) -> $variant_value:expr ;)*) => {
        $(
            fn $fn_name( $($arg : $argty,)* ctx: &mut HirCtx) -> Self {
                Self {
                    kind: $variant_value,
                    type_: ctx.ty_ctx.new_var(),
                }
            }
        )*
    };
}

impl Expression {
    make_expr_wrappers! {
        ident(sym: Symbol) -> ExpressionKind::Ident(sym);
        array(exprs: Vec<Expression>) -> ExpressionKind::Array(exprs);
        tuple(exprs: Vec<Expression>) -> ExpressionKind::Tuple(exprs);
        unary_op(op: UnaryOp, operand: Box<Expression>) -> ExpressionKind::UnaryOp {
            op,
            operand
        };
        binary_op(lhs: Box<Expression>, op: BinaryOp, rhs: Box<Expression>) -> ExpressionKind::BinaryOp {
            lhs,
            op,
            rhs,
        };
        if_block(
            condition: Box<Expression>,
            then_block: Block,
            else_block: Option<Block>,
        ) -> ExpressionKind::If { condition, then_block, else_block };
        loop_expr(label: Option<BlockLabel>, body: Block) -> ExpressionKind::Loop { label, body };
        block(label: Option<BlockLabel>, block: Block) -> ExpressionKind::Block { label, body: block };
        wildcard() -> ExpressionKind::Wildcard;
        match_expr(scrutinee: Box<Expression>, arms: Vec<MatchArm>) -> ExpressionKind::Match {
            scrutinee, arms,
        };
        index(base: Box<Expression>, index: Box<Expression>) -> ExpressionKind::Index {
            base, index,
        };
        call(function: Box<Expression>, args: Vec<Expression>) -> ExpressionKind::Call {
            function, args,
        };
    }
    fn integer(int: Integer, ctx: &mut HirCtx) -> Expression {
        Expression {
            kind: ExpressionKind::Integer(int),
            type_: ctx.ty_ctx.new_integer_var(),
        }
    }
    fn bool(b: bool, ctx: &mut HirCtx) -> Expression {
        Expression {
            kind: ExpressionKind::Bool(b),
            type_: ctx.ty_ctx.bool_type(),
        }
    }
    fn string_literal(string: StringLiteral, ctx: &mut HirCtx) -> Expression {
        let i8 = ctx.ty_ctx.insert_type(TypeKind::Integer {
            signed: true,
            bits: Either::Left(8),
        });
        let const_i8_ptr = TypeKind::Pointer { mutable: false, pointee: i8 };
        let type_ = ctx.ty_ctx.insert_type(const_i8_ptr);
        Expression { kind: ExpressionKind::StringLiteral(string), type_ }
    }
    fn break_expr(
        label: Option<BlockLabel>, value: Option<Box<Expression>>,
        ctx: &mut HirCtx,
    ) -> Expression {
        Expression {
            kind: ExpressionKind::Break { label, value },
            type_: ctx.ty_ctx.new_var(),
        }
    }
    fn return_expr(
        value: Option<Box<Expression>>, ctx: &mut HirCtx,
    ) -> Expression {
        Expression {
            kind: ExpressionKind::Return { value },
            type_: ctx.ty_ctx.new_var(),
        }
    }
    fn continue_expr(
        label: Option<BlockLabel>, ctx: &mut HirCtx,
    ) -> Expression {
        Expression {
            kind: ExpressionKind::Continue { label },
            type_: ctx.ty_ctx.new_var(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum UnaryOp {
    Not,
    Neg,
    AddrOf { mutable: bool },
    Deref,
    AsCast { to_type: TypeIdx },
}

#[derive(Debug)]
pub enum ExpressionKind {
    Ident(Symbol),
    Integer(Integer),
    StringLiteral(StringLiteral),
    Bool(bool),
    Array(Vec<Expression>),
    Tuple(Vec<Expression>),
    UnaryOp {
        op: UnaryOp,
        operand: Box<Expression>,
    },
    BinaryOp {
        lhs: Box<Expression>,
        op: BinaryOp,
        rhs: Box<Expression>,
    },
    If {
        condition: Box<Expression>,
        then_block: Block,
        else_block: Option<Block>,
    },
    Loop {
        label: Option<BlockLabel>,
        body: Block,
    },
    Block {
        label: Option<BlockLabel>,
        body: Block,
    },
    Match {
        scrutinee: Box<Expression>,
        arms: Vec<MatchArm>,
    },
    Wildcard,
    Index {
        base: Box<Expression>,
        index: Box<Expression>,
    },
    Call {
        function: Box<Expression>,
        args: Vec<Expression>,
    },
    Continue {
        label: Option<BlockLabel>,
    },
    Break {
        label: Option<BlockLabel>,
        value: Option<Box<Expression>>,
    },
    Return {
        value: Option<Box<Expression>>,
    },
}

#[derive(Debug)]
pub struct Block {
    /// The last statement cannot be a `Statement::Expression` if `self.tail`
    /// is `None`
    pub statements: Vec<Statement>,
    pub tail: Option<Box<Expression>>,
}
impl Block {
    fn type_(&self, ctx: &mut HirCtx) -> TypeIdx {
        self.tail.as_ref().map_or(ctx.ty_ctx.unit_type(), |expr| expr.type_)
    }
}

#[derive(Debug)]
pub enum Statement {
    LetStatement {
        pattern: Pattern,
        type_: TypeIdx,
        initializer: Option<Expression>,
    },
    Expression {
        expression: Expression,
        has_semicolon: bool,
    },
}

#[derive(Debug)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub expression: Expression,
}

/// Lower ast to hir and type-check it.
pub fn lower_ast_to_hir(ast: Vec<ast::Item>) -> (Vec<Item>, HirCtx<'static>) {
    let mut ctx = HirCtx::prelude();
    let mut hir = ast.lower(&mut ctx);
    ctx.register_globals(&hir);

    // Keep type checking until no changes occur, then resolve integer variables
    // to `i32`, then resolve unbound type vars to unit.

    loop {
        while hir.type_check(&mut ctx) {}

        // Resolve integer type vars to i32
        for t in &mut ctx.ty_ctx.substitutions {
            if matches!(t, Either::Right(TypeVarKind::Integer)) {
                *t = Either::Left(TypeKind::Integer {
                    signed: true,
                    bits: Either::Left(32),
                });
            }
        }

        // If resolving integer type vars caused more inference to be possible,
        // start the loop over.
        if hir.type_check(&mut ctx) {
            continue;
        }

        // Resolve unknown type vars to i32
        for t in &mut ctx.ty_ctx.substitutions {
            if matches!(t, Either::Right(TypeVarKind::Normal)) {
                *t = Either::Left(TypeKind::Tuple(EMPTY_TYPE_LIST.clone()));
            }
        }

        // If resolving unknown type vars caused more inference to be possible,
        // start the loop over, else break
        if !hir.type_check(&mut ctx) {
            break;
        }
    }

    hir.assert_concrete(&ctx);

    (hir, ctx)
}

trait Lower {
    type Output;
    fn lower(self, ctx: &mut HirCtx) -> Self::Output;
}

impl<T: Lower> Lower for Option<T> {
    type Output = Option<T::Output>;

    fn lower(self, ctx: &mut HirCtx) -> Self::Output {
        self.map(|t| t.lower(ctx))
    }
}

impl<T: Lower> Lower for Vec<T> {
    type Output = Vec<T::Output>;

    fn lower(self, ctx: &mut HirCtx) -> Self::Output {
        self.into_iter().map(|t| t.lower(ctx)).collect()
    }
}

impl<T: Lower> Lower for Box<T> {
    type Output = Box<T::Output>;

    fn lower(self, ctx: &mut HirCtx) -> Self::Output {
        Box::new((*self).lower(ctx))
    }
}

impl Lower for ast::Item {
    type Output = Item;

    fn lower(self, ctx: &mut HirCtx) -> Self::Output {
        match self {
            ast::Item::FnItem(item) => Item::FnItem(item.lower(ctx)),
            ast::Item::StaticItem(item) => Item::StaticItem(item.lower(ctx)),
        }
    }
}

impl Lower for ast::FnItem {
    type Output = FnItem;

    fn lower(self, ctx: &mut HirCtx) -> Self::Output {
        let params = self.params.lower(ctx);
        let return_type = self.return_type.lower(ctx);
        let body = self.body.lower(ctx);
        let param_idxs = params.iter().map(|param| param.type_).collect();
        let return_type = return_type.unwrap_or(ctx.ty_ctx.unit_type());
        let signature = TypeKind::Function {
            params: param_idxs,
            return_type,
            is_variadic: self.is_variadic,
        };
        let signature = ctx.ty_ctx.insert_type(signature);
        FnItem {
            extern_token: self.extern_token,
            fn_token: self.fn_token,
            name: Symbol::Ident(self.name),
            is_variadic: self.is_variadic,
            params,
            return_type,
            body,
            signature,
        }
    }
}

impl Lower for ast::FnParam {
    type Output = FnParam;

    fn lower(self, ctx: &mut HirCtx) -> Self::Output {
        FnParam {
            pattern: self.pattern.lower(ctx),
            type_: self.type_.lower(ctx),
        }
    }
}

impl Lower for ast::StaticItem {
    type Output = StaticItem;

    fn lower(self, ctx: &mut HirCtx) -> Self::Output {
        StaticItem {
            extern_token: self.extern_token,
            static_token: self.static_token,
            mut_token: self.mut_token,
            name: Symbol::Ident(self.name),
            type_: self.type_.lower(ctx),
            initializer: self.initializer.lower(ctx),
        }
    }
}

impl Lower for ast::Type {
    type Output = TypeIdx;

    fn lower(self, ctx: &mut HirCtx) -> Self::Output {
        match self {
            ast::Type::Pointer { mutable, pointee } => {
                let pointee = (*pointee).lower(ctx);
                ctx.ty_ctx.insert_type(TypeKind::Pointer { mutable, pointee })
            }
            ast::Type::Array { element, length } => {
                let element = (*element).lower(ctx);
                ctx.ty_ctx.insert_type(TypeKind::Array { element, length })
            }
            ast::Type::Slice { element } => {
                let element = (*element).lower(ctx);
                ctx.ty_ctx.insert_type(TypeKind::Slice { element })
            }
            ast::Type::Ident(ident) => *ctx
                .type_scope
                .lookup(&Symbol::Ident(ident))
                .expect("unknown type"),
            ast::Type::Tuple(types) => {
                let types =
                    types.into_iter().map(|type_| type_.lower(ctx)).collect();
                ctx.ty_ctx.insert_type(TypeKind::Tuple(types))
            }
            ast::Type::Parenthesized(type_) => (*type_).lower(ctx),
            // TODO: since we don't have coercions, we can't use never_type
            // here, since otherwise it would try to check
            // `something == Never` and fail.
            ast::Type::Never => ctx.ty_ctx.new_var(),
        }
    }
}

impl Lower for ast::UnaryOp {
    type Output = UnaryOp;

    fn lower(self, ctx: &mut HirCtx) -> Self::Output {
        match self {
            ast::UnaryOp::Not => UnaryOp::Not,
            ast::UnaryOp::Neg => UnaryOp::Neg,
            ast::UnaryOp::AddrOf { mutable } => UnaryOp::AddrOf { mutable },
            ast::UnaryOp::Deref => UnaryOp::Deref,
            ast::UnaryOp::AsCast { to_type } => {
                UnaryOp::AsCast { to_type: to_type.lower(ctx) }
            }
        }
    }
}

impl Lower for ast::Expression {
    type Output = Expression;

    fn lower(self, ctx: &mut HirCtx) -> Self::Output {
        match self {
            ast::Expression::Ident(ident) => {
                Expression::ident(Symbol::Ident(ident), ctx)
            }
            ast::Expression::Integer(integer) => {
                Expression::integer(integer, ctx)
            }
            ast::Expression::StringLiteral(string_literal) => {
                Expression::string_literal(string_literal, ctx)
            }
            ast::Expression::Bool(b) => Expression::bool(b, ctx),
            ast::Expression::Array(exprs) => {
                Expression::array(exprs.lower(ctx), ctx)
            }
            ast::Expression::Tuple(exprs) => {
                Expression::tuple(exprs.lower(ctx), ctx)
            }
            ast::Expression::Parenthesized(expr) => (*expr).lower(ctx),
            ast::Expression::UnaryOp { op, operand } => {
                Expression::unary_op(op.lower(ctx), operand.lower(ctx), ctx)
            }
            ast::Expression::BinaryOp { lhs, op, rhs } => {
                Expression::binary_op(lhs.lower(ctx), op, rhs.lower(ctx), ctx)
            }
            ast::Expression::If { conditions, blocks } => {
                let mut conditions = VecDeque::from(conditions.lower(ctx));
                let mut blocks = VecDeque::from(blocks.lower(ctx));
                let mut expr = Expression::if_block(
                    Box::new(conditions.pop_front().unwrap()),
                    blocks.pop_front().unwrap(),
                    None,
                    ctx,
                );

                let ExpressionKind::If { else_block, .. } = &mut expr.kind
                else {
                    unreachable!();
                };

                let mut next = else_block;
                while let Some(block) = blocks.pop_front() {
                    if let Some(condition) = conditions.pop_front() {
                        // else if
                        let block = Block {
                            statements: vec![],
                            tail: Some(Box::new(Expression::if_block(
                                Box::new(condition),
                                block,
                                None,
                                ctx,
                            ))),
                        };
                        *next = Some(block);
                        let Some(Expression {
                            kind: ExpressionKind::If { else_block, .. },
                            ..
                        }) = next.as_mut().unwrap().tail.as_deref_mut()
                        else {
                            unreachable!();
                        };
                        next = else_block;
                    } else {
                        // else
                        *next = Some(block);
                        debug_assert!(blocks.is_empty());
                    }
                }
                expr
            }
            ast::Expression::While { label, condition, body } => {
                let label = label
                    .map_or_else(BlockLabel::new_synthetic, BlockLabel::Label);
                // 'label: loop {
                //     if condition { break 'label } else body
                // }
                Expression::loop_expr(
                    Some(label),
                    Block {
                        statements: vec![Statement::Expression {
                            expression: Expression::if_block(
                                condition.lower(ctx),
                                Block {
                                    statements: vec![],
                                    tail: Some(Box::new(
                                        Expression::break_expr(
                                            Some(label),
                                            None,
                                            ctx,
                                        ),
                                    )),
                                },
                                Some(body.lower(ctx)),
                                ctx,
                            ),
                            has_semicolon: false,
                        }],
                        tail: None,
                    },
                    ctx,
                )
            }
            ast::Expression::For { label, pattern, iterable, body } => {
                // {
                //     let start = start;
                //     let end = end;
                //     if start <= end {
                //         let mut i = start;
                //         'label: loop {
                //             // if end_inclusive is false the break is before
                // the body             if i >= end { break 'label }
                //             let pattern = i;
                //             body
                //             // if end_inclusive is true, the break is after
                // the body             if i >= end { break 'label }
                //             i = i + 1;
                //         };
                //     };
                // }
                let label = label
                    .map_or_else(BlockLabel::new_synthetic, BlockLabel::Label);
                let (start, inclusive, end) = match *iterable {
                    ast::Expression::BinaryOp {
                        lhs,
                        op: BinaryOp::RangeOp { end_inclusive },
                        rhs,
                    } => ((*lhs).lower(ctx), end_inclusive, (*rhs).lower(ctx)),
                    _ => panic!(
                        "only range expressions can be used as `for` loop \
                         iterables"
                    ),
                };
                let pattern = pattern.lower(ctx);
                let body = (*body).lower(ctx);
                let start_ident = Symbol::new_synthetic();
                let end_ident = Symbol::new_synthetic();
                let iter_ident = Symbol::new_synthetic();
                let entry_condition = Expression::binary_op(
                    Box::new(Expression::ident(start_ident, ctx)),
                    BinaryOp::Comparison(ComparisonOp::LessEq),
                    Box::new(Expression::ident(end_ident, ctx)),
                    ctx,
                );
                let exit_condition = Expression::binary_op(
                    Box::new(Expression::ident(iter_ident, ctx)),
                    BinaryOp::Comparison(ComparisonOp::GreaterEq),
                    Box::new(Expression::ident(end_ident, ctx)),
                    ctx,
                );

                let let_start_stmt = Statement::LetStatement {
                    pattern: Pattern::Ident {
                        mutable: false,
                        ident: start_ident,
                    },
                    type_: start.type_,
                    initializer: Some(start),
                };
                let let_end_stmt = Statement::LetStatement {
                    pattern: Pattern::Ident {
                        mutable: false,
                        ident: end_ident,
                    },
                    type_: end.type_,
                    initializer: Some(end),
                };
                let let_i_stmt = Statement::LetStatement {
                    pattern: Pattern::Ident {
                        mutable: true,
                        ident: iter_ident,
                    },
                    type_: ctx.ty_ctx.new_var(),
                    initializer: Some(Expression::ident(start_ident, ctx)),
                };
                let let_pattern_stmt = Statement::LetStatement {
                    pattern,
                    type_: ctx.ty_ctx.new_var(),
                    initializer: Some(Expression::ident(iter_ident, ctx)),
                };

                let exit_break_stmt = Statement::Expression {
                    expression: Expression::if_block(
                        Box::new(exit_condition),
                        Block {
                            statements: vec![],
                            tail: Some(Box::new(Expression::break_expr(
                                Some(label),
                                None,
                                ctx,
                            ))),
                        },
                        None,
                        ctx,
                    ),
                    has_semicolon: true,
                };
                let body_stmt = Statement::Expression {
                    expression: body,
                    has_semicolon: true,
                };
                let i_plus_one_expr = Expression::binary_op(
                    Box::new(Expression::ident(iter_ident, ctx)),
                    BinaryOp::Arithmetic(ast::ArithmeticOp::Add),
                    Box::new(Expression::integer(
                        Integer::new_unspanned(1),
                        ctx,
                    )),
                    ctx,
                );
                let increment_i_stmt = Statement::Expression {
                    expression: Expression::binary_op(
                        Box::new(Expression::ident(iter_ident, ctx)),
                        BinaryOp::Assignment,
                        Box::new(i_plus_one_expr),
                        ctx,
                    ),
                    has_semicolon: true,
                };

                let loop_statements = if inclusive {
                    vec![
                        let_pattern_stmt,
                        body_stmt,
                        exit_break_stmt,
                        increment_i_stmt,
                    ]
                } else {
                    vec![
                        let_pattern_stmt,
                        exit_break_stmt,
                        body_stmt,
                        increment_i_stmt,
                    ]
                };
                let loop_stmt = Statement::Expression {
                    expression: Expression::loop_expr(
                        Some(label),
                        Block { statements: loop_statements, tail: None },
                        ctx,
                    ),
                    has_semicolon: true,
                };
                Expression::block(
                    None,
                    Block {
                        statements: vec![
                            let_start_stmt,
                            let_end_stmt,
                            Statement::Expression {
                                expression: Expression::if_block(
                                    Box::new(entry_condition),
                                    Block {
                                        statements: vec![let_i_stmt, loop_stmt],
                                        tail: None,
                                    },
                                    None,
                                    ctx,
                                ),
                                has_semicolon: true,
                            },
                        ],
                        tail: None,
                    },
                    ctx,
                )
            }
            ast::Expression::Loop { label, body } => Expression::loop_expr(
                label.map(BlockLabel::Label),
                body.lower(ctx),
                ctx,
            ),
            ast::Expression::Block { label, body } => Expression::block(
                label.map(BlockLabel::Label),
                body.lower(ctx),
                ctx,
            ),
            ast::Expression::Match { scrutinee, arms } => {
                Expression::match_expr(
                    scrutinee.lower(ctx),
                    arms.lower(ctx),
                    ctx,
                )
            }
            ast::Expression::Wildcard => Expression::wildcard(ctx),
            ast::Expression::Index { base, index } => {
                Expression::index(base.lower(ctx), index.lower(ctx), ctx)
            }
            ast::Expression::Call { function, args } => {
                Expression::call(function.lower(ctx), args.lower(ctx), ctx)
            }
            ast::Expression::Break { label, value } => Expression::break_expr(
                label.map(BlockLabel::Label),
                value.lower(ctx),
                ctx,
            ),
            ast::Expression::Return { value } => {
                Expression::return_expr(value.lower(ctx), ctx)
            }
            ast::Expression::Continue { label } => {
                Expression::continue_expr(label.map(BlockLabel::Label), ctx)
            }
        }
    }
}

impl Lower for ast::Block {
    type Output = Block;

    fn lower(self, ctx: &mut HirCtx) -> Self::Output {
        let mut statements = self.statements.lower(ctx);
        let mut tail = self.tail.lower(ctx);
        // If there's no syntactic tail expression, but the last statement is an
        // expression-statement without a semicolon, make it the tail
        // expression.
        if tail.is_none()
            && statements.last().is_some_and(|stmt| {
                matches!(
                    stmt,
                    Statement::Expression { has_semicolon: false, .. }
                )
            })
        {
            let Statement::Expression { expression, .. } =
                statements.pop().unwrap()
            else {
                unreachable!()
            };
            tail = Some(Box::new(expression));
        }
        Block { statements, tail }
    }
}

impl Lower for ast::Pattern {
    type Output = Pattern;

    fn lower(self, ctx: &mut HirCtx) -> Self::Output {
        match self {
            ast::Pattern::Wildcard => Pattern::Wildcard,
            ast::Pattern::Ident { mutable, ident } => {
                Pattern::Ident { mutable, ident: Symbol::Ident(ident) }
            }
            ast::Pattern::Integer(integer) => Pattern::Integer(integer),
            ast::Pattern::Alt(orig_patterns) => {
                // Collapse parenthesized alt patterns.
                // `(a | b) | (c | d)` -> `a | b | c | d``
                let mut patterns = Vec::with_capacity(orig_patterns.len());
                for pattern in orig_patterns {
                    let pattern = pattern.lower(ctx);
                    match pattern {
                        Pattern::Alt(inner) => patterns.extend(inner),
                        _ => patterns.push(pattern),
                    }
                }
                Pattern::Alt(patterns)
            }
            ast::Pattern::Array(patterns) => {
                Pattern::Array(patterns.lower(ctx))
            }
            ast::Pattern::Tuple(patterns) => {
                Pattern::Tuple(patterns.lower(ctx))
            }
            ast::Pattern::Parenthesized(inner) => (*inner).lower(ctx),
            ast::Pattern::Range { start, inclusive, end } => {
                Pattern::Range { start, inclusive, end }
            }
        }
    }
}

impl Lower for ast::MatchArm {
    type Output = MatchArm;

    fn lower(self, ctx: &mut HirCtx) -> Self::Output {
        MatchArm {
            pattern: self.pattern.lower(ctx),
            expression: self.expression.lower(ctx),
        }
    }
}

impl Lower for ast::Statement {
    type Output = Statement;

    fn lower(self, ctx: &mut HirCtx) -> Self::Output {
        match self {
            ast::Statement::LetStatement { pattern, type_, initializer } => {
                Statement::LetStatement {
                    pattern: pattern.lower(ctx),
                    type_: type_
                        .lower(ctx)
                        .unwrap_or_else(|| ctx.ty_ctx.new_var()),
                    initializer: initializer.lower(ctx),
                }
            }
            ast::Statement::Expression { expression, has_semicolon } => {
                Statement::Expression {
                    expression: expression.lower(ctx),
                    has_semicolon,
                }
            }
        }
    }
}

trait TypeCheck {
    /// Returns `true` if anything in this node changed.
    fn type_check(&mut self, ctx: &mut HirCtx) -> bool;

    /// Panics with a message if self is not type-checked to concreteness.
    fn assert_concrete(&self, ctx: &HirCtx);
}

impl<T: TypeCheck> TypeCheck for Option<T> {
    fn type_check(&mut self, ctx: &mut HirCtx) -> bool {
        self.as_mut().map_or(false, |t| t.type_check(ctx))
    }

    fn assert_concrete(&self, ctx: &HirCtx) {
        if let Some(this) = self {
            this.assert_concrete(ctx);
        }
    }
}

impl<T: TypeCheck> TypeCheck for Vec<T> {
    fn type_check(&mut self, ctx: &mut HirCtx) -> bool {
        // Intentionally not short-circuiting
        let result = self
            .iter_mut()
            .map(|t| t.type_check(ctx))
            .fold(false, |a, b| a || b);
        result
    }

    fn assert_concrete(&self, ctx: &HirCtx) {
        for t in self {
            t.assert_concrete(ctx);
        }
    }
}

impl<T: TypeCheck> TypeCheck for Box<T> {
    fn type_check(&mut self, ctx: &mut HirCtx) -> bool {
        (**self).type_check(ctx)
    }

    fn assert_concrete(&self, ctx: &HirCtx) {
        (**self).assert_concrete(ctx)
    }
}

impl TypeCheck for Item {
    fn type_check(&mut self, ctx: &mut HirCtx) -> bool {
        match self {
            Item::FnItem(item) => item.type_check(ctx),
            Item::StaticItem(item) => item.type_check(ctx),
        }
    }

    fn assert_concrete(&self, ctx: &HirCtx) {
        match self {
            Item::FnItem(item) => item.assert_concrete(ctx),
            Item::StaticItem(item) => item.assert_concrete(ctx),
        }
    }
}

impl TypeCheck for FnItem {
    fn type_check(&mut self, ctx: &mut HirCtx) -> bool {
        let mut ctx = HirCtx::new_parent(ctx);
        ctx.return_type = Some(self.return_type);
        let mut changed = false;
        for param in &self.params {
            changed |= ctx.type_check_pattern_and_insert_locals(
                &param.pattern,
                param.type_,
            );
        }
        changed |= self.body.type_check(&mut ctx);

        changed
    }

    fn assert_concrete(&self, ctx: &HirCtx) {
        assert!(
            self.signature.is_concrete(ctx),
            "fn item {:?}'s signature is not concrete",
            self.name
        );
        self.body.assert_concrete(ctx);
    }
}

impl TypeCheck for StaticItem {
    fn type_check(&mut self, ctx: &mut HirCtx) -> bool {
        let mut changed = self.initializer.type_check(ctx);
        if let Some(expr) = &self.initializer {
            changed |= ctx.constrain_eq(self.type_, expr.type_);
        }
        changed
    }

    fn assert_concrete(&self, ctx: &HirCtx) {
        assert!(
            self.type_.is_concrete(ctx),
            "static {:?}'s type is not concrete",
            self.name
        );
        self.initializer.assert_concrete(ctx);
    }
}

impl TypeCheck for Expression {
    fn type_check(&mut self, ctx: &mut HirCtx) -> bool {
        match &mut self.kind {
            ExpressionKind::Ident(ident) => {
                let Some(type_) = ctx.value_scope.lookup(ident) else {
                    panic!("undefined variable {ident:?}");
                };
                ctx.constrain_eq(*type_, self.type_)
            }
            ExpressionKind::StringLiteral(_) => {
                // string literal expressions should already be created as
                // `*const i8` type
                assert!(self.type_.is_pointer(ctx).is_some_and(|is| is));
                false
            }
            ExpressionKind::Integer(_) => {
                // integer expressions should already be created as integer type
                // var
                assert!(self.type_.is_integer(ctx).is_some_and(|is| is));
                false
            }
            ExpressionKind::Bool(_) => {
                debug_assert!(matches!(self.kind, ExpressionKind::Bool(..)));
                false
            }
            ExpressionKind::Array(elems) => {
                let (mut changed, elem_ty) =
                    ctx.constrain_array(self.type_, elems.len());
                for elem in elems.iter() {
                    changed |= ctx.constrain_eq(elem.type_, elem_ty);
                }
                changed
            }
            ExpressionKind::Tuple(elems) => {
                let mut changed = elems.type_check(ctx);
                let (c, elem_tys) =
                    ctx.constrain_tuple(self.type_, elems.len());
                changed |= c;
                for (elem, &elem_ty) in std::iter::zip(elems, elem_tys.iter()) {
                    changed |= ctx.constrain_eq(elem.type_, elem_ty);
                }
                changed
            }
            ExpressionKind::UnaryOp { op, operand } => {
                let mut changed = operand.type_check(ctx);
                match op {
                    UnaryOp::Not => todo!("bool or integer"),
                    UnaryOp::Neg => {
                        changed |= ctx.constrain_integer(operand.type_);
                    }
                    UnaryOp::AddrOf { .. } => {}
                    UnaryOp::Deref => {
                        todo!(
                            "constrain pointer without constraining \
                             mutability?"
                        );
                        // let (c, pointee) =
                        // ctx.constrain_pointer(operand.type_);
                        // changed |= c;
                        // changed |= ctx.constrain_eq(pointee, self.type_);
                    }
                    UnaryOp::AsCast { to_type } => {
                        changed |= ctx.constrain_eq(*to_type, self.type_);
                        log::warn!(
                            "TODO:changed |= ctx.constrain_as_castable(src, \
                             dst);"
                        );
                    }
                }
                changed
            }
            ExpressionKind::BinaryOp { lhs, op, rhs } => {
                let mut changed = lhs.type_check(ctx);
                changed |= rhs.type_check(ctx);
                match *op {
                    BinaryOp::Assignment => {
                        changed |= ctx.constrain_eq(lhs.type_, rhs.type_);
                        changed |= ctx.constrain_unit(self.type_);
                    }
                    BinaryOp::Arithmetic(op) => {
                        use ast::ArithmeticOp as A;
                        match op {
                            A::And | A::Or => {
                                changed |= ctx.constrain_bool(lhs.type_);
                                changed |= ctx.constrain_bool(rhs.type_);
                                changed |= ctx.constrain_bool(self.type_);
                            }
                            A::BitAnd | A::BitOr | A::BitXor => {
                                log::warn!("TODO: maybe allow bitops on bool?");
                                changed |= ctx.constrain_integer(lhs.type_);
                                changed |=
                                    ctx.constrain_eq(lhs.type_, rhs.type_);
                                changed |=
                                    ctx.constrain_eq(lhs.type_, self.type_);
                            }
                            A::Modulo
                            | A::Multiply
                            | A::Divide
                            | A::LeftShift
                            | A::RightShift => {
                                changed |= ctx.constrain_integer(lhs.type_);
                                changed |= ctx.constrain_integer(rhs.type_);
                                changed |=
                                    ctx.constrain_eq(lhs.type_, self.type_);
                            }
                            A::Add => {
                                changed |= ctx.constrain_add(
                                    lhs.type_, rhs.type_, self.type_,
                                )
                            }
                            A::Subtract => {
                                changed |= ctx.constrain_subtract(
                                    lhs.type_, rhs.type_, self.type_,
                                )
                            }
                        };
                    }
                    BinaryOp::Comparison(_) => {
                        changed |= ctx
                            .constrain_eq(self.type_, ctx.ty_ctx.bool_type());
                    }
                    BinaryOp::RangeOp { .. } => todo!(),
                }
                changed
            }
            ExpressionKind::If { condition, then_block, else_block } => {
                let mut changed = condition.type_check(ctx);
                changed |= then_block.type_check(ctx);
                changed |= else_block.type_check(ctx);
                let then_block_ty_idx = then_block.type_(ctx);
                if let Some(else_block) = else_block {
                    let else_block_ty_idx = else_block.type_(ctx);
                    changed |=
                        ctx.constrain_eq(then_block_ty_idx, else_block_ty_idx);
                } else {
                    changed |= ctx.constrain_unit(then_block_ty_idx);
                }
                changed
            }
            ExpressionKind::Loop { label, body } => {
                // Note that we generate a synthetic label if this loop does not
                // have an explicit label, so that we can ensure
                // that every `break`/`continue` has a label, which makes
                // mir-building easier.
                let label =
                    *label.get_or_insert_with(BlockLabel::new_synthetic);
                ctx.nested_loop_labels.push(label);
                assert!(
                    ctx.labeled_block_types
                        .insert(label, (self.type_, LabeledBlockKind::Loop))
                        .is_none(),
                    "cannot shadow label {label:?}"
                );
                let changed = body.type_check(ctx);
                ctx.labeled_block_types.remove(&label);
                ctx.nested_loop_labels.pop();
                changed
            }
            ExpressionKind::Block { label, body } => {
                // Note that we don't push to `ctx.nested_loop_labels` because
                // an unlabeled `break` will never break from a
                // block-expression. Also note that we don't add
                // a synthetic label, since unlabeled blocks
                // don't matter for break or continue.
                if let Some(label) = *label {
                    assert!(
                        ctx.labeled_block_types
                            .insert(
                                label,
                                (self.type_, LabeledBlockKind::Block)
                            )
                            .is_none(),
                        "cannot shadow label {label:?}"
                    );
                }
                let changed = body.type_check(ctx);
                if let Some(label) = *label {
                    ctx.labeled_block_types.remove(&label);
                }
                changed
            }
            ExpressionKind::Match { .. } => {
                unimplemented!("match expressions not implemented")
            }
            ExpressionKind::Wildcard => todo!(),
            ExpressionKind::Index { base, index } => {
                let mut changed = base.type_check(ctx);
                changed |= index.type_check(ctx);
                changed |=
                    ctx.constrain_index(base.type_, index.type_, self.type_);
                changed
            }
            ExpressionKind::Call { function, args } => {
                let mut changed = function.type_check(ctx);
                changed |= args.type_check(ctx);

                let (c, param_tys, ret_ty) =
                    ctx.constrain_fn(function.type_, args.len());
                changed |= c;

                changed |= ctx.constrain_eq(ret_ty, self.type_);
                for (&param_ty, arg) in
                    std::iter::zip(param_tys.iter(), args.iter())
                {
                    changed |= ctx.constrain_eq(param_ty, arg.type_);
                }

                changed
            }
            ExpressionKind::Break { label, value } => {
                let mut changed = value.type_check(ctx);
                let label = *label.get_or_insert_with(|| {
                    *ctx.nested_loop_labels
                        .last()
                        .expect("unlabeled break expr in non-loop context")
                });
                let expected = ctx
                    .labeled_block_types
                    .get(&label)
                    .expect("break label undeclared")
                    .0;
                match value {
                    Some(value) => {
                        changed |= ctx.constrain_eq(expected, value.type_)
                    }
                    None => changed |= ctx.constrain_unit(expected),
                }
                changed
            }
            ExpressionKind::Return { value } => {
                let mut changed = value.type_check(ctx);
                let expected =
                    ctx.return_type.expect("return expr in non-fn context");
                match value {
                    Some(value) => {
                        changed |= ctx.constrain_eq(expected, value.type_)
                    }
                    None => changed |= ctx.constrain_unit(expected),
                }
                changed
            }
            ExpressionKind::Continue { label } => {
                // We don't need to do type-checking as such, but we do need to
                // check that there is a loop to continue.
                let label = label.get_or_insert_with(|| {
                    *ctx.nested_loop_labels
                        .last()
                        .expect("continue expr in non-loop context")
                });
                match ctx.labeled_block_types.get(label) {
                    None => {
                        panic!("invalid `continue`: no label {label:?}");
                    }
                    Some((_, LabeledBlockKind::Block)) => {
                        panic!("invalid `continue` from labeled block");
                    }
                    Some((_, LabeledBlockKind::Loop)) => {}
                }
                false
            }
        }
    }

    fn assert_concrete(&self, ctx: &HirCtx) {
        assert!(
            self.type_.is_concrete(ctx),
            "expression's type is not concrete: {self:?}"
        );
        match &self.kind {
            ExpressionKind::Ident(..)
            | ExpressionKind::Integer(..)
            | ExpressionKind::StringLiteral(..)
            | ExpressionKind::Bool(..) => {}
            ExpressionKind::Array(elems) => elems.assert_concrete(ctx),
            ExpressionKind::Tuple(elems) => elems.assert_concrete(ctx),
            ExpressionKind::UnaryOp { operand, .. } => {
                operand.assert_concrete(ctx)
            }
            ExpressionKind::BinaryOp { lhs, rhs, .. } => {
                lhs.assert_concrete(ctx);
                rhs.assert_concrete(ctx);
            }
            ExpressionKind::If { condition, then_block, else_block } => {
                condition.assert_concrete(ctx);
                then_block.assert_concrete(ctx);
                else_block.assert_concrete(ctx);
            }
            ExpressionKind::Loop { body, .. } => body.assert_concrete(ctx),
            ExpressionKind::Block { body, .. } => body.assert_concrete(ctx),
            ExpressionKind::Match { .. } => {
                unimplemented!("match expressions not implemented");
            }
            ExpressionKind::Wildcard => {}
            ExpressionKind::Index { base, index } => {
                base.assert_concrete(ctx);
                index.assert_concrete(ctx);
            }
            ExpressionKind::Call { function, args } => {
                function.assert_concrete(ctx);
                args.assert_concrete(ctx);
            }
            ExpressionKind::Break { value, .. } => value.assert_concrete(ctx),
            ExpressionKind::Return { value } => value.assert_concrete(ctx),
            ExpressionKind::Continue { .. } => {}
        }
    }
}

impl TypeCheck for Block {
    fn type_check(&mut self, ctx: &mut HirCtx) -> bool {
        let stmts_changed = self.statements.type_check(ctx);
        let tail_changed = self.tail.type_check(ctx);
        stmts_changed || tail_changed
    }

    fn assert_concrete(&self, ctx: &HirCtx) {
        for stmt in &self.statements {
            stmt.assert_concrete(ctx);
        }
        self.tail.assert_concrete(ctx);
    }
}

impl TypeCheck for Statement {
    fn type_check(&mut self, ctx: &mut HirCtx) -> bool {
        match self {
            Statement::LetStatement { pattern, type_, initializer } => {
                let mut changed = initializer.type_check(ctx);
                if let Some(expr) = initializer {
                    changed |= ctx.constrain_eq(*type_, expr.type_);
                }
                ctx.type_check_pattern_and_insert_locals(&*pattern, *type_);
                changed
            }
            Statement::Expression { expression, has_semicolon } => {
                let mut changed = expression.type_check(ctx);
                if !*has_semicolon {
                    // Must be unit type
                    changed |= ctx.constrain_unit(expression.type_);
                }
                changed
            }
        }
    }

    fn assert_concrete(&self, ctx: &HirCtx) {
        match self {
            Statement::LetStatement { type_, initializer, .. } => {
                assert!(
                    type_.is_concrete(ctx),
                    "let statement's type is not concrete"
                );
                initializer.assert_concrete(ctx);
            }
            Statement::Expression { expression, .. } => {
                expression.assert_concrete(ctx)
            }
        }
    }
}
