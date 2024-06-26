use crate::token::{Ident, Integer, Label, StringLiteral};

#[derive(Debug)]
pub enum Item {
    FnItem(FnItem),
    StaticItem(StaticItem),
}

#[derive(Debug)]
pub struct FnItem {
    pub extern_token: Option<Ident>,
    pub fn_token: Ident,
    pub name: Ident,
    pub params: Vec<FnParam>,
    pub return_type: Option<Type>,
    pub body: Option<Block>,
    pub is_variadic: bool,
}

#[derive(Debug)]
pub struct StaticItem {
    pub extern_token: Option<Ident>,
    pub static_token: Ident,
    pub mut_token: Option<Ident>,
    pub name: Ident,
    pub type_: Type,
    pub initializer: Option<Expression>,
}

#[derive(Debug)]
pub struct FnParam {
    pub pattern: Pattern,
    pub type_: Type,
}

#[derive(Debug, Clone)]
pub enum Type {
    Pointer { mutable: bool, pointee: Box<Type> },
    Array { element: Box<Type>, length: usize },
    Slice { element: Box<Type> },
    Ident(Ident),
    Tuple(Vec<Type>),
    Parenthesized(Box<Type>),
    Never,
}

#[derive(Debug)]
pub enum Pattern {
    Wildcard,
    Ident { mutable: bool, ident: Ident },
    Integer(Integer),
    Alt(Vec<Self>),
    Array(Vec<Self>),
    Tuple(Vec<Self>),
    Parenthesized(Box<Pattern>),
    Range { start: Integer, inclusive: bool, end: Integer },
}

#[derive(Debug, Clone)]
pub enum UnaryOp {
    Not,
    Neg,
    AddrOf { mutable: bool },
    Deref,
    AsCast { to_type: Type },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArithmeticOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
    BitAnd,
    BitOr,
    BitXor,
    And,
    Or,
    LeftShift,
    RightShift,
}

impl ArithmeticOp {
    pub fn is_short_circuit(&self) -> bool {
        match self {
            ArithmeticOp::Add
            | ArithmeticOp::Subtract
            | ArithmeticOp::Multiply
            | ArithmeticOp::Divide
            | ArithmeticOp::Modulo
            | ArithmeticOp::BitAnd
            | ArithmeticOp::BitOr
            | ArithmeticOp::BitXor
            | ArithmeticOp::LeftShift
            | ArithmeticOp::RightShift => false,
            ArithmeticOp::And | ArithmeticOp::Or => true,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ComparisonOp {
    Equal,
    NotEqual,
    Less,
    Greater,
    LessEq,
    GreaterEq,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    Arithmetic(ArithmeticOp),
    Assignment,
    Comparison(ComparisonOp),
    RangeOp { end_inclusive: bool },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Associativity {
    /// Left-associative, e.g. `x - y - z` is equivalent to `(x - y) - z`.
    ///
    /// Left-associative operators with the same precedence can be mixed
    /// without parentheses, e.g. `x + y - z + w` is equivalent to `((x + y) -
    /// z) + w`
    Left,
    /// Right-associative, e.g. `x - y - z` is equivalent to `x - (y - z)`.
    ///
    /// Right-associative operators with the same precedence can be mixed
    /// without parentheses.
    Right,
    /// Non-associative, e.g. `x == y == z` is not allowed.
    None,
}

impl BinaryOp {
    pub fn precedence_and_associativity(&self) -> (u8, Associativity) {
        use ArithmeticOp as A;
        use BinaryOp as B;
        match self {
            // Assignment operators have the lowest precedence, and cannot be
            // chained.
            B::Assignment { .. } => (0, Associativity::None),
            // Range operators have the lowest precedence other than assignment,
            // and cannot be chained.
            B::RangeOp { .. } => (1, Associativity::None),
            // Boolean or has lower precedence than boolean and, e.g. `a && b ||
            // c` parses as `(a && b) || c`.
            B::Arithmetic(A::Or) => (2, Associativity::Right),
            B::Arithmetic(A::And) => (3, Associativity::Right),
            // Comparison operators have lower precedence than boolean
            // operators, and cannot be chained. e.g. `x == y && a < b` parses
            // as `(x == y) && (a < b)`.
            B::Comparison(..) => (4, Associativity::None),
            // The rest of these are mostly copied from Rust, with some
            // restrictions (like making shift operators non-associative).
            B::Arithmetic(A::BitOr) => (5, Associativity::Left),
            B::Arithmetic(A::BitXor) => (6, Associativity::Left),
            B::Arithmetic(A::BitAnd) => (7, Associativity::Left),
            B::Arithmetic(A::LeftShift | A::RightShift) => {
                (8, Associativity::None)
            }
            B::Arithmetic(A::Add | A::Subtract) => (9, Associativity::Left),
            B::Arithmetic(A::Multiply | A::Divide | A::Modulo) => {
                (10, Associativity::Left)
            }
        }
    }
}

#[derive(Debug)]
pub enum Expression {
    Ident(Ident),
    Integer(Integer),
    StringLiteral(StringLiteral),
    Bool(bool),
    Array(Vec<Expression>),
    Tuple(Vec<Expression>),
    Parenthesized(Box<Expression>),
    UnaryOp {
        op: UnaryOp,
        operand: Box<Expression>,
    },
    BinaryOp {
        lhs: Box<Expression>,
        op: BinaryOp,
        rhs: Box<Expression>,
    },
    /// `if cond1 { block1 } else if cond2 { block2 } else { block3 }`
    ///
    /// `conditions.len()` is always `>= 1`, and is always equal to or one less
    /// than `blocks.len()`.
    If {
        conditions: Vec<Expression>,
        blocks: Vec<Block>,
    },
    While {
        label: Option<Label>,
        condition: Box<Expression>,
        body: Block,
    },
    For {
        label: Option<Label>,
        pattern: Pattern,
        iterable: Box<Expression>,
        body: Box<Expression>,
    },
    Loop {
        label: Option<Label>,
        body: Block,
    },
    Block {
        label: Option<Label>,
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
        label: Option<Label>,
    },
    Break {
        label: Option<Label>,
        value: Option<Box<Expression>>,
    },
    Return {
        value: Option<Box<Expression>>,
    },
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
