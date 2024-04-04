use crate::token::{Ident, Integer};

#[derive(Debug)]
pub enum Item {
    ExternBlock { extern_token: (), items: Vec<Item> },
    FnItem(FnItem),
    StaticItem(StaticItem),
}

#[derive(Debug)]
pub struct FnItem {
    extern_token: Option<()>,
    fn_token: (),
    name: Ident,
    args: Vec<FnArg>,
    return_type: Option<Type>,
    body: Option<Block>,
}

#[derive(Debug)]
pub struct StaticItem {
    static_token: (),
    mut_token: Option<()>,
    name: Ident,
    initializer: Option<Expression>,
}

#[derive(Debug)]
pub struct FnArg {
    pattern: Pattern,
    type_: Type,
}

#[derive(Debug)]
pub enum Type {
    Pointer { mutable: bool, inner: Box<Type> },
    Array { inner: Box<Type>, length: usize },
    Ident(Ident),
}

#[derive(Debug)]
pub enum Pattern {
    Wildcard,
    Ident(Ident),
}

#[derive(Debug)]
pub enum Expression {
    Ident(Ident),
    Integer(Integer),
    Bool(bool),
    Array(Vec<Expression>),
    Derev(Box<Expression>),
    Parenthesized(Box<Expression>),
    Neg(Box<Expression>),
    Add(Box<Expression>, Box<Expression>),
    Sub(Box<Expression>, Box<Expression>),
    Mul(Box<Expression>, Box<Expression>),
    Div(Box<Expression>, Box<Expression>),
    Mod(Box<Expression>, Box<Expression>),
    BoolAnd(Box<Expression>, Box<Expression>),
    BoolOr(Box<Expression>, Box<Expression>),
    BitAnd(Box<Expression>, Box<Expression>),
    BitOr(Box<Expression>, Box<Expression>),
    BitXor(Box<Expression>, Box<Expression>),
    LeftShift(Box<Expression>, Box<Expression>),
    RightShift(Box<Expression>, Box<Expression>),
    Assign(Box<Expression>, Box<Expression>),
    /// `if cond1 { block1 } else if cond2 { block2 } else { block3 }`
    ///
    /// `conditions.len()` is always `>= 1`, and is always equal to or one less
    /// than `blocks.len()`.
    If {
        conditions: Vec<Expression>,
        blocks: Vec<Block>,
    },
    While {
        condition: Box<Expression>,
        body: Block,
    },
    Block(Block),
    Return(Option<Box<Expression>>),
}

#[derive(Debug)]
pub struct Block {
    statements: Vec<Statement>,
    tail: Option<Box<Expression>>,
}

#[derive(Debug)]
pub enum Statement {
    LetStatement { mutable: bool, name: Ident, initializer: Option<Expression> },
    Expression(Expression),
}
