use crate::token::{Ident, Integer};

#[derive(Debug)]
pub enum Item {
    FnItem(FnItem),
    StaticItem(StaticItem),
}

#[derive(Debug)]
pub struct FnItem {
    pub extern_token: Option<()>,
    pub fn_token: (),
    pub name: Ident,
    pub args: Vec<FnArg>,
    pub return_type: Option<Type>,
    pub body: Option<Block>,
}

#[derive(Debug)]
pub struct StaticItem {
    pub extern_token: Option<()>,
    pub static_token: (),
    pub mut_token: Option<()>,
    pub name: Ident,
    pub type_: Type,
    pub initializer: Option<Expression>,
}

#[derive(Debug)]
pub struct FnArg {
    pub pattern: Pattern,
    pub type_: Type,
}

#[derive(Debug)]
pub enum Type {
    Pointer { mutable: bool, inner: Box<Type> },
    Array { inner: Box<Type>, length: usize },
    Ident(Ident),
    Tuple(Vec<Type>),
}

#[derive(Debug)]
pub enum Pattern {
    Wildcard,
    Ident { mutable: bool, ident: Ident },
}

#[derive(Debug)]
pub enum Expression {
    Ident(Ident),
    Integer(Integer),
    Bool(bool),
    Array(Vec<Expression>),
    Tuple(Vec<Expression>),
    Deref(Box<Expression>),
    AddrOf(Box<Expression>),
    Parenthesized(Box<Expression>),
    /// TODO: remove this
    BinOpChain {
        operands: Vec<Expression>,
        operators: Vec<&'static str>,
    },
    Neg(Box<Expression>),
    Not(Box<Expression>),
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
    Loop(Block),
    Block(Block),
    Return(Option<Box<Expression>>),
    Match {
        scrutinee: Box<Expression>,
        arms: Vec<MatchArm>,
    },
    Wildcard,
}

#[derive(Debug)]
pub struct Block {
    pub statements: Vec<Statement>,
    pub tail: Option<Box<Expression>>,
}

#[derive(Debug)]
pub enum Statement {
    LetStatement {
        pattern: Pattern,
        type_: Option<Type>,
        initializer: Option<Expression>,
    },
    Expression(Expression),
}

#[derive(Debug)]
pub struct MatchArm {
    todo_: (),
}
