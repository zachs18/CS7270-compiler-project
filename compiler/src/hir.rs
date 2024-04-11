//! Like [`ast`](crate::ast), but with things desugared to simpler constructs:
//!
//! * `while` and `for` desugared to `loop`s with `let`, `if`, and `match`
//! * `if` conditions are not chained
//! * parenthesized around patterns/expressions/types are removed (the "order of
//!   operations" is maintained by the tree structure anyway)
//! * alt-patterns are combined (i.e. `(a | b) | c` is lowered to `a | b | c`).

use std::{
    collections::VecDeque,
    sync::atomic::{AtomicUsize, Ordering},
};

use crate::{
    ast::{self, BinaryOp, ComparisonOp, UnaryOp},
    span::Span,
    token::{self, Ident},
};

#[derive(Clone, Copy)]
pub enum Symbol {
    Ident(Ident),
    Synthetic(usize),
}

#[derive(Debug, Clone, Copy)]
pub struct Integer {
    pub value: u128,
    pub span: Option<Span>,
}

impl Integer {
    pub fn new(value: u128) -> Self {
        Self { value, span: None }
    }
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

#[derive(Debug)]
pub struct FnItem {
    pub extern_token: Option<Ident>,
    pub fn_token: Ident,
    pub name: Symbol,
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
    pub name: Symbol,
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
    Array { element: Box<Type>, length: u128 },
    Slice { element: Box<Type> },
    Ident(Ident),
    Tuple(Vec<Type>),
    Never,
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
pub enum Expression {
    Ident(Symbol),
    Integer(Integer),
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
    Loop(Block),
    Block(Block),
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
    Break {
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

pub fn lower_ast_to_hir(ast: Vec<ast::Item>) -> Vec<Item> {
    ast.lower()
}

trait Lower {
    type Output;
    fn lower(self) -> Self::Output;
}

impl<T: Lower> Lower for Option<T> {
    type Output = Option<T::Output>;

    fn lower(self) -> Self::Output {
        self.map(T::lower)
    }
}

impl<T: Lower> Lower for Vec<T> {
    type Output = Vec<T::Output>;

    fn lower(self) -> Self::Output {
        self.into_iter().map(T::lower).collect()
    }
}

impl<T: Lower> Lower for Box<T> {
    type Output = Box<T::Output>;

    fn lower(self) -> Self::Output {
        Box::new((*self).lower())
    }
}

impl Lower for ast::Item {
    type Output = Item;

    fn lower(self) -> Self::Output {
        match self {
            ast::Item::FnItem(item) => Item::FnItem(item.lower()),
            ast::Item::StaticItem(item) => Item::StaticItem(item.lower()),
        }
    }
}

impl Lower for ast::FnItem {
    type Output = FnItem;

    fn lower(self) -> Self::Output {
        FnItem {
            extern_token: self.extern_token,
            fn_token: self.fn_token,
            name: Symbol::Ident(self.name),
            is_variadic: self.is_variadic,
            params: self.params.lower(),
            return_type: self.return_type.lower(),
            body: self.body.lower(),
        }
    }
}

impl Lower for ast::FnParam {
    type Output = FnParam;

    fn lower(self) -> Self::Output {
        FnParam { pattern: self.pattern.lower(), type_: self.type_.lower() }
    }
}

impl Lower for ast::StaticItem {
    type Output = StaticItem;

    fn lower(self) -> Self::Output {
        StaticItem {
            extern_token: self.extern_token,
            static_token: self.static_token,
            mut_token: self.mut_token,
            name: Symbol::Ident(self.name),
            type_: self.type_.lower(),
            initializer: self.initializer.lower(),
        }
    }
}

impl Lower for ast::Type {
    type Output = Type;

    fn lower(self) -> Self::Output {
        match self {
            ast::Type::Pointer { mutable, pointee } => {
                Type::Pointer { mutable, pointee: pointee.lower() }
            }
            ast::Type::Array { element, length } => {
                Type::Array { element: element.lower(), length }
            }
            ast::Type::Slice { element } => {
                Type::Slice { element: element.lower() }
            }
            ast::Type::Ident(ident) => Type::Ident(ident),
            ast::Type::Tuple(types) => Type::Tuple(types.lower()),
            ast::Type::Parenthesized(type_) => (*type_).lower(),
            ast::Type::Never => Type::Never,
        }
    }
}

impl Lower for ast::Expression {
    type Output = Expression;

    fn lower(self) -> Self::Output {
        match self {
            ast::Expression::Ident(ident) => {
                Expression::Ident(Symbol::Ident(ident))
            }
            ast::Expression::Integer(integer) => {
                Expression::Integer(integer.lower())
            }
            ast::Expression::Bool(b) => Expression::Bool(b),
            ast::Expression::Array(exprs) => Expression::Array(exprs.lower()),
            ast::Expression::Tuple(exprs) => Expression::Tuple(exprs.lower()),
            ast::Expression::Parenthesized(expr) => (*expr).lower(),
            ast::Expression::UnaryOp { op, operand } => {
                Expression::UnaryOp { op, operand: operand.lower() }
            }
            ast::Expression::BinaryOp { lhs, op, rhs } => {
                Expression::BinaryOp { lhs: lhs.lower(), op, rhs: rhs.lower() }
            }
            ast::Expression::If { conditions, blocks } => {
                let mut conditions = VecDeque::from(conditions.lower());
                let mut blocks = VecDeque::from(blocks.lower());
                let mut expr = Expression::If {
                    condition: Box::new(conditions.pop_front().unwrap()),
                    then_block: blocks.pop_front().unwrap(),
                    else_block: None,
                };

                let Expression::If { else_block, .. } = &mut expr else {
                    unreachable!();
                };

                let mut next = else_block;
                while let Some(block) = blocks.pop_front() {
                    if let Some(condition) = conditions.pop_front() {
                        // else if
                        let block = Block {
                            statements: vec![],
                            tail: Some(Box::new(Expression::If {
                                condition: Box::new(condition),
                                then_block: block,
                                else_block: None,
                            })),
                        };
                        *next = Some(block);
                        let Some(Expression::If { else_block, .. }) =
                            next.as_mut().unwrap().tail.as_deref_mut()
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
            ast::Expression::While { condition, body } => {
                // loop {
                //     if condition { break } else body
                // }
                Expression::Loop(Block {
                    statements: vec![Statement::Expression {
                        expression: Expression::If {
                            condition: condition.lower(),
                            then_block: Block {
                                statements: vec![],
                                tail: Some(Box::new(Expression::Break {
                                    value: None,
                                })),
                            },
                            else_block: Some(body.lower()),
                        },
                        has_semicolon: false,
                    }],
                    tail: None,
                })
            }
            ast::Expression::For { pattern, iterable, body } => {
                // {
                //     let start = start;
                //     let end = end;
                //     if start <= end {
                //         let mut i = start;
                //         loop {
                //             // if end_inclusive is false the break is before
                // the body             if i >= end { break }
                //             let pattern = i;
                //             body
                //             // if end_inclusive is true, the break is after
                // the body             if i >= end { break }
                //             i += 1;
                //         };
                //     };
                // }
                let (start, inclusive, end) = match *iterable {
                    ast::Expression::BinaryOp {
                        lhs,
                        op: BinaryOp::RangeOp { end_inclusive },
                        rhs,
                    } => ((*lhs).lower(), end_inclusive, (*rhs).lower()),
                    _ => panic!(
                        "only range expressions can be used as `for` loop \
                         iterables"
                    ),
                };
                let pattern = pattern.lower();
                let body = (*body).lower();
                let start_ident = Symbol::new_synthetic();
                let end_ident = Symbol::new_synthetic();
                let iter_ident = Symbol::new_synthetic();
                let entry_condition = Expression::BinaryOp {
                    lhs: Box::new(Expression::Ident(start_ident)),
                    op: BinaryOp::Comparison(ComparisonOp::LessEq),
                    rhs: Box::new(Expression::Ident(end_ident)),
                };
                let exit_condition = Expression::BinaryOp {
                    lhs: Box::new(Expression::Ident(iter_ident)),
                    op: BinaryOp::Comparison(ComparisonOp::GreaterEq),
                    rhs: Box::new(Expression::Ident(end_ident)),
                };

                let let_start_stmt = Statement::LetStatement {
                    pattern: Pattern::Ident {
                        mutable: false,
                        ident: start_ident,
                    },
                    type_: None,
                    initializer: Some(start),
                };
                let let_end_stmt = Statement::LetStatement {
                    pattern: Pattern::Ident {
                        mutable: false,
                        ident: end_ident,
                    },
                    type_: None,
                    initializer: Some(end),
                };
                let let_i_stmt = Statement::LetStatement {
                    pattern,
                    type_: None,
                    initializer: Some(Expression::Ident(iter_ident)),
                };

                let exit_break_stmt = Statement::Expression {
                    expression: Expression::If {
                        condition: Box::new(exit_condition),
                        then_block: Block {
                            statements: vec![],
                            tail: Some(Box::new(Expression::Break {
                                value: None,
                            })),
                        },
                        else_block: None,
                    },
                    has_semicolon: true,
                };
                let body_stmt = Statement::Expression {
                    expression: body,
                    has_semicolon: true,
                };
                let increment_i_stmt = Statement::Expression {
                    expression: Expression::BinaryOp {
                        lhs: Box::new(Expression::Ident(iter_ident)),
                        op: BinaryOp::Assignment {
                            augment: Some(ast::ArithmeticOp::Add),
                        },
                        rhs: Box::new(Expression::Integer(Integer::new(1))),
                    },
                    has_semicolon: true,
                };

                let loop_statements = if inclusive {
                    vec![body_stmt, exit_break_stmt, increment_i_stmt]
                } else {
                    vec![exit_break_stmt, body_stmt, increment_i_stmt]
                };
                let loop_stmt = Statement::Expression {
                    expression: Expression::Loop(Block {
                        statements: loop_statements,
                        tail: None,
                    }),
                    has_semicolon: true,
                };
                Expression::Block(Block {
                    statements: vec![
                        let_start_stmt,
                        let_end_stmt,
                        Statement::Expression {
                            expression: Expression::If {
                                condition: Box::new(entry_condition),
                                then_block: Block {
                                    statements: vec![let_i_stmt, loop_stmt],
                                    tail: None,
                                },
                                else_block: None,
                            },
                            has_semicolon: true,
                        },
                    ],
                    tail: None,
                })
            }
            ast::Expression::Loop(body) => Expression::Loop(body.lower()),
            ast::Expression::Block(block) => Expression::Block(block.lower()),
            ast::Expression::Match { scrutinee, arms } => Expression::Match {
                scrutinee: scrutinee.lower(),
                arms: arms.lower(),
            },
            ast::Expression::Wildcard => Expression::Wildcard,
            ast::Expression::Index { base, index } => {
                Expression::Index { base: base.lower(), index: index.lower() }
            }
            ast::Expression::Call { function, args } => Expression::Call {
                function: function.lower(),
                args: args.lower(),
            },
            ast::Expression::Break { value } => {
                Expression::Break { value: value.lower() }
            }
            ast::Expression::Return { value } => {
                Expression::Return { value: value.lower() }
            }
        }
    }
}

impl Lower for ast::Block {
    type Output = Block;

    fn lower(self) -> Self::Output {
        let mut statements = self.statements.lower();
        let mut tail = self.tail.lower();
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

    fn lower(self) -> Self::Output {
        match self {
            ast::Pattern::Wildcard => Pattern::Wildcard,
            ast::Pattern::Ident { mutable, ident } => {
                Pattern::Ident { mutable, ident: Symbol::Ident(ident) }
            }
            ast::Pattern::Integer(integer) => Pattern::Integer(integer.lower()),
            ast::Pattern::Alt(orig_patterns) => {
                // Collapse parenthesized alt patterns.
                // `(a | b) | (c | d)` -> `a | b | c | d``
                let mut patterns = Vec::with_capacity(orig_patterns.len());
                for pattern in orig_patterns {
                    let pattern = pattern.lower();
                    match pattern {
                        Pattern::Alt(inner) => patterns.extend(inner),
                        _ => patterns.push(pattern),
                    }
                }
                Pattern::Alt(patterns)
            }
            ast::Pattern::Array(patterns) => Pattern::Array(patterns.lower()),
            ast::Pattern::Tuple(patterns) => Pattern::Tuple(patterns.lower()),
            ast::Pattern::Parenthesized(inner) => (*inner).lower(),
            ast::Pattern::Range { start, inclusive, end } => Pattern::Range {
                start: start.lower(),
                inclusive,
                end: end.lower(),
            },
        }
    }
}

impl Lower for token::Integer {
    type Output = Integer;

    fn lower(self) -> Self::Output {
        Integer { value: self.value, span: Some(self.span) }
    }
}

impl Lower for ast::MatchArm {
    type Output = MatchArm;

    fn lower(self) -> Self::Output {
        MatchArm {
            pattern: self.pattern.lower(),
            expression: self.expression.lower(),
        }
    }
}

impl Lower for ast::Statement {
    type Output = Statement;

    fn lower(self) -> Self::Output {
        match self {
            ast::Statement::LetStatement { pattern, type_, initializer } => {
                Statement::LetStatement {
                    pattern: pattern.lower(),
                    type_: type_.lower(),
                    initializer: initializer.lower(),
                }
            }
            ast::Statement::Expression { expression, has_semicolon } => {
                Statement::Expression {
                    expression: expression.lower(),
                    has_semicolon,
                }
            }
        }
    }
}
