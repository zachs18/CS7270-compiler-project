use std::{backtrace::Backtrace, collections::VecDeque, fmt};

use either::Either;
use itertools::{Itertools, Position};
use nom::{
    branch::alt,
    combinator::{all_consuming, cut, eof, map_opt, not, opt, verify},
    error::{ErrorKind, ParseError},
    multi::{fold_many0, many0, separated_list1},
    sequence::{pair, preceded, terminated, tuple},
    Finish, Parser,
};
use zachs18_stdx::OptionExt;

use crate::{
    ast::{
        ArithmeticOp, Associativity, BinaryOp, Block, ComparisonOp, Expression,
        FnItem, FnParam, Item, MatchArm, Pattern, Statement, StaticItem, Type,
        UnaryOp,
    },
    lexer::{self, is_keyword},
    token::{Delimiter, Group, Ident, Integer, Punct, TokenTree},
};

struct ParseError_<'a> {
    backtrace: Backtrace,
    expected: Option<&'static str>,
    found: Option<&'a TokenTree>,
    caused_by: Vec<Self>,
}

impl<'a> fmt::Debug for ParseError_<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl fmt::Display for ParseError_<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\ncreated at {}: ", self.backtrace)?;
        if let Some(expected) = self.expected {
            write!(f, "expected {expected}, ")?;
        }
        write!(f, "found ")?;
        match self.found {
            None => write!(f, "<eof>")?,
            Some(TokenTree::Group(Group { delimiter, .. })) => {
                write!(f, "`{}`", delimiter.opening())?
            }
            Some(TokenTree::Ident(Ident { ident, .. }))
                if is_keyword(ident) =>
            {
                write!(f, "keyword `{ident}`")?
            }
            Some(TokenTree::Ident(Ident { ident, .. })) => {
                write!(f, "identifier `{ident}`")?
            }
            Some(TokenTree::Integer(_)) => write!(f, "integer literal")?,
            Some(&TokenTree::Punct(Punct { c, .. })) => {
                write!(f, "`{}`", c as char)?
            }
        }
        if let Some(found) = self.found {
            write!(f, " at {:?}", found.span())?;
        }
        write!(f, " caused by: {:?}", self.caused_by)?;
        Ok(())
    }
}

impl<'a> ParseError<&'a [TokenTree]> for ParseError_<'a> {
    fn from_error_kind(input: &'a [TokenTree], _kind: ErrorKind) -> Self {
        Self {
            expected: None,
            found: input.first(),
            backtrace: Backtrace::force_capture(),
            caused_by: vec![],
        }
    }

    fn append(
        input: &'a [TokenTree], kind: ErrorKind, mut other: Self,
    ) -> Self {
        other.caused_by.push(Self::from_error_kind(input, kind));
        other
    }
}

pub fn separated_list<I, O, O2, E, F, G>(
    sep: G, f: F,
) -> impl FnMut(I) -> nom::IResult<I, Vec<O>, E>
where
    I: Clone + nom::InputLength,
    F: Parser<I, O, E>,
    G: Parser<I, O2, E> + Clone,
    E: ParseError<I>,
{
    let mut inner = opt(terminated(separated_list1(sep.clone(), f), opt(sep)))
        .map(Option::unwrap_or_default);
    move |input| inner.parse(input)
}

/// Rust-style comma-separated lists, allowing a trailing comma, but not
/// allowing a comma with nothing before it.
fn comma_separated_list<'input, O, F>(
    f: F,
) -> impl FnMut(&'input [TokenTree]) -> IResult<'input, Vec<O>>
where
    F: for<'a> Parser<&'input [TokenTree], O, ParseError_<'input>>,
{
    fn sep(input: &[TokenTree]) -> IResult<'_, ()> {
        parse_joint_puncts(",")(input)
    }
    let mut inner = opt(terminated(separated_list1(sep, f), opt(sep)))
        .map(Option::unwrap_or_default);
    move |input| inner.parse(input)
}

fn either<I, O1, O2, E, P1, P2>(
    p1: P1, p2: P2,
) -> impl FnMut(I) -> nom::IResult<I, Either<O1, O2>, E>
where
    I: Clone,
    P1: Parser<I, O1, E>,
    P2: Parser<I, O2, E>,
    E: ParseError<I>,
{
    let p1 = p1.map(Either::Left);
    let p2 = p2.map(Either::Right);
    alt((p1, p2))
}

trait IResultExt: Sized {
    fn or_expected(self, expected: &'static str) -> Self;
}

impl<'a, T> IResultExt for Result<T, nom::Err<ParseError_<'a>>> {
    fn or_expected(mut self, expected: &'static str) -> Self {
        if let Some(nom::Err::Error(err) | nom::Err::Failure(err)) =
            self.as_mut().err()
        {
            err.expected = Some(expected);
        }
        self
    }
}

// type IResult<'a, O, E = nom::error::VerboseError<&'a [TokenTree]>> =
//     nom::IResult<&'a [TokenTree], O, E>;
type IResult<'a, O, E = ParseError_<'a>> = nom::IResult<&'a [TokenTree], O, E>;

pub fn parse(tokens: &[TokenTree]) -> Vec<Item> {
    let (_, items) = parse_items_full(tokens).finish().unwrap();
    items
}

fn parse_items_full(input: &[TokenTree]) -> IResult<'_, Vec<Item>> {
    all_consuming(many0(parse_item))(input)
}

/// A [fn item](parse_fn_item) or a [static item](parse_static_item).
///
/// ```text
/// | FN_ITEM
/// | STATIC_ITEM
/// ```
fn parse_item(input: &[TokenTree]) -> IResult<'_, Item> {
    nom::branch::alt((
        parse_fn_item.map(Item::FnItem),
        parse_static_item.map(Item::StaticItem),
    ))(input)
}

fn parse_group<
    'a,
    E: ParseError<&'a [TokenTree]>,
    O,
    P: Parser<&'a [TokenTree], O, E>,
>(
    expected_delimiter: Delimiter, inner: P,
) -> impl FnMut(&'a [TokenTree]) -> IResult<'a, O, E> {
    let mut inner = all_consuming(inner);
    move |input: &'a [TokenTree]| -> IResult<'a, O, E> {
        let Some((TokenTree::Group(group), rest)) = input.split_first() else {
            return Err(nom::Err::Error(
                nom::error::ParseError::from_error_kind(input, ErrorKind::IsA),
            ));
        };
        if group.delimiter != expected_delimiter {
            return Err(nom::Err::Error(
                nom::error::ParseError::from_error_kind(input, ErrorKind::IsA),
            ));
        }
        inner.parse(&group.inner).map(|(_, output)| (rest, output))
    }
}

/// A function item.
///
/// ```text
/// 'extern'? 'fn' ident '(' list[TYPED_PATTERN] ')' ( BLOCK | ';' )
/// ```
///
/// If `extern` is not present, then `BLOCK` must be present, and this defines
/// an internal, non-exported function.
///
/// If `extern` is present and `BLOCK` is present, this defines an
/// exported function.
///
/// If `extern` is present and `BLOCK` is not present, this declares an
/// external function that is defined elsewhere.
///
/// Examples:
///
/// ```text
/// extern fn memcpy(dst: *mut void, src: *const void, n: usize) -> *mut void;
/// extern fn main(argc: i32, argv: *mut *mut i8) -> i32 {
///     let x = 4 + 3;
/// }
/// fn foobar(x: *mut [u32; 10]) {
///     x[4] = 3;
/// }
/// ```
fn parse_fn_item(input: &[TokenTree]) -> IResult<'_, FnItem> {
    let (input, extern_token) =
        nom::combinator::opt(parse_ident("extern"))(input)?;
    let (input, fn_token) = parse_ident("fn")(input)?;
    let rest = move |input| {
        let (input, name) = parse_non_kw_ident(input)?;
        let (input, args) = parse_fn_params(input)?;
        let (input, return_type) =
            opt(preceded(parse_joint_puncts("->"), parse_type))(input)?;
        if let Ok((input, ())) = parse_joint_puncts(";")(input) {
            Ok((
                input,
                FnItem {
                    extern_token,
                    fn_token,
                    name,
                    args,
                    return_type,
                    body: None,
                },
            ))
        } else {
            let (input, body) = parse_block(input)?;
            Ok((
                input,
                FnItem {
                    extern_token,
                    fn_token,
                    name,
                    args,
                    return_type,
                    body: Some(body),
                },
            ))
        }
    };
    cut(rest)(input)
}

#[test]
fn atom_expr() {
    let tokens = crate::lexer::lex(b"a");
    assert!(parse_expression(&tokens).is_ok());

    let tokens = crate::lexer::lex(b"{while b < c {} a}");
    assert!(parse_block(&tokens).is_ok());
}

/// A block containing [statements](parse_statement) and an optional trailing
/// [expression](parse_expression).
///
/// ```text
/// '{' STATEMENT* EXPRESSION? '}'
/// ```
fn parse_block(input: &[TokenTree]) -> IResult<'_, Block> {
    let inner =
        pair(many0(parse_statement), opt(parse_expression.map(Box::new)))
            .map(|(statements, expr)| Block { statements, tail: expr });
    parse_group(Delimiter::Brace, inner)(input)
}

/// A statment is either an [expression statement](parse_expression_statement).
/// or a [`let` statement](parse_let_statement).
///
/// ```text
/// | EXPRESSION_STATEMENT
/// | LET_STATEMENT
/// ```
fn parse_statement(input: &[TokenTree]) -> IResult<'_, Statement> {
    alt((parse_expression_statement, parse_let_statement))(input)
}

/// An expression statement is either a [non-block
/// expression](parse_no_block_expression) followed by a semicolon, or a [block
/// expression](parse_block_expression) optionally followed by a semicolon.
///
/// ```text
/// | NO_BLOCK_EXPRESSION ';'
/// | BLOCK_EXPRESSION ';'?
/// ```
fn parse_expression_statement(input: &[TokenTree]) -> IResult<'_, Statement> {
    alt((
        terminated(parse_no_block_expression, parse_joint_puncts(";"))
            .map(|expr| Statement::Expression(expr)),
        terminated(parse_block_expression, opt(parse_joint_puncts(";")))
            .map(|expr| Statement::Expression(expr)),
    ))(input)
}

fn parse_let_statement(input: &[TokenTree]) -> IResult<'_, Statement> {
    tuple((
        parse_ident("let"),
        parse_pattern,
        opt(preceded(parse_joint_puncts(":"), parse_type)),
        opt(preceded(parse_joint_puncts("="), parse_expression)),
        parse_joint_puncts(";"),
    ))
    .map(|(_, pattern, type_, initializer, _)| Statement::LetStatement {
        pattern,
        type_,
        initializer,
    })
    .parse(input)
}

fn parse_expression(input: &[TokenTree]) -> IResult<'_, Expression> {
    alt((parse_block_expression, parse_no_block_expression))(input)
}

/// An expression that is a block.
///
/// Can be a [(normal) block](parse_block), an [if
/// expression](parse_if_expression), a [loop
/// expression](parse_loop_expression), or a [match
/// expression](parse_match_expression).
fn parse_block_expression(input: &[TokenTree]) -> IResult<'_, Expression> {
    alt((
        parse_block.map(Expression::Block),
        parse_if_expression,
        parse_loop_expression,
        parse_match_expression,
    ))(input)
}

/// An `if` expression.
///
/// ```text
/// 'if' EXPR_NO_BLOCK BLOCK ( 'else' 'if' EXPR_NO_BLOCK BLOCK )* ('else' BLOCK)?
/// ```
///
/// TODO: docs
fn parse_if_expression(input: &[TokenTree]) -> IResult<'_, Expression> {
    let (input, _if) = parse_ident("if")(input)?;
    let (input, condition) = parse_no_block_expression(input)?;
    let mut conditions = Some(vec![condition]);
    let (input, block) = parse_block(input)?;
    let mut blocks = Some(vec![block]);
    let elseif = tuple((
        parse_ident("else"),
        parse_ident("if"),
        parse_no_block_expression,
        parse_block,
    ));
    let (input, (conditions, mut blocks)) = fold_many0(
        elseif,
        || (conditions.take().unwrap(), blocks.take().unwrap()),
        |(mut conditions, mut blocks), (_, _, condition, block)| {
            conditions.push(condition);
            blocks.push(block);
            (conditions, blocks)
        },
    )(input)?;
    let (input, else_block) =
        opt(preceded(parse_ident("else"), parse_block))(input)?;
    blocks.extend(else_block);
    Ok((input, Expression::If { conditions, blocks }))
}

/// A `match` expression.
///
/// TODO: docs
fn parse_match_expression(input: &[TokenTree]) -> IResult<'_, Expression> {
    let (input, _match) = parse_ident("match")(input)?;
    let (input, scrutinee) = parse_no_block_expression(input)?;
    let inner = comma_separated_list(parse_match_arm);
    let (input, arms) = parse_group(Delimiter::Brace, inner)(input)?;
    Ok((input, Expression::Match { scrutinee: Box::new(scrutinee), arms }))
}

/// An arm of a [`match` expression](parse_match_expression).
///
/// TODO: docs
fn parse_match_arm(input: &[TokenTree]) -> IResult<'_, MatchArm> {
    tuple((parse_pattern_with_alt, parse_joint_puncts("=>"), parse_expression))
        .map(|(pattern, _, expression)| MatchArm { pattern, expression })
        .parse(input)
}

/// A loop expression.
///
/// Can be a [while loop](parse_while_loop), a [for loop](parse_for_loop), or an
/// [infinite loop](parse_loop_loop).
fn parse_loop_expression(input: &[TokenTree]) -> IResult<'_, Expression> {
    alt((parse_while_loop, parse_for_loop, parse_loop_loop))(input)
}

/// A while loop.
///
/// ```text
/// 'while' EXPR_NO_BLOCK BLOCK
/// ```
///
/// The condition must be of type `bool`, and the block must
/// evaluate to `()`.
///
/// # Examples:
///
/// ```text
/// while true {}
/// while i < 42 { i += 1; }
/// ```
fn parse_while_loop(input: &[TokenTree]) -> IResult<'_, Expression> {
    let (input, _) = parse_ident("while")(input)?;
    let tail = tuple((parse_no_block_expression, parse_block)).map(
        |(condition, body)| Expression::While {
            condition: Box::new(condition),
            body,
        },
    );
    // Cut because we already saw a `while` token, so we know this is a while
    // loop.
    cut(tail)(input)
}

/// A for loop.
///
/// ```text
/// 'for' PATTERN 'in' EXPR_NO_BLOCK BLOCK
/// ```
///
/// The pattern must be infallible and of the same type as the
/// iterable's element, and the block must evaluate to `()`.
///
/// The iterable must be a range expression, i.e. `a..b` or `a..=b` for some
/// `a`, `b`.
///
/// # Examples:
///
/// ```text
/// for i in 0..10 {}
/// ```
fn parse_for_loop(input: &[TokenTree]) -> IResult<'_, Expression> {
    let (input, _) = parse_ident("for")(input)?;
    let tail = tuple((
        parse_pattern,
        parse_ident("in"),
        parse_no_block_expression,
        parse_block,
    ))
    .map(|(pattern, _, iterable, body)| Expression::For {
        pattern,
        iterable: Box::new(iterable),
        body: Box::new(Expression::Block(body)),
    });
    // Cut because we already saw a `for` token, so we know this is a for
    // loop.
    cut(tail)(input)
}

/// An infinite loop.
///
/// ```text
/// 'loop' BLOCK
/// ```
///
/// The block must evaluate to `()`.
///
/// # Examples:
///
/// ```text
/// loop {}
/// loop {
///     if i == 42 { break; } // TODO: break expressions
/// }
/// ```
fn parse_loop_loop(input: &[TokenTree]) -> IResult<'_, Expression> {
    let (input, _) = parse_ident("loop")(input)?;
    let tail = parse_block.map(Expression::Loop);
    // Cut because we already saw a `loop` token, so we know this is a loop.
    cut(tail)(input)
}

// TODO: use shunting-yard algorithm maybe?
// This algorithm is not optimal, but the compiler doesn't need to be fast lol.
// Also unless we observe a bottleneck of parsing long expressions, this should
// be fine.
/// Given an alternating sequence of operands and binary operators, use operator
/// precedence and associativity to produce the resulting expression.
///
/// Currently implemented as:
///
/// 1. If there's only one operand, return it.
/// 2. If there's only two operands, return the binary operator expression with
///    them.
/// 3. If there's more than two operands:
///     1. Go through the list of operators and find the lowest-precedence ones
///     2. Split the input into chunks between the lowest-precedence operators.
///     3. Recursively fixup those chunks into single expressions.
///     4. Reduce the fixed-up expressions into a single expression using the
///        lowest-precedence operators, based on the associativity of the
///        lowest-precedence operators.
fn fixup_binary_operators(
    mut operands: Vec<Expression>, mut operators: Vec<BinaryOp>,
) -> Result<Expression, &'static str> {
    match operands.len() {
        0 => unreachable!(),
        1 => Ok(operands.pop().unwrap()),
        2 => {
            let operands: [Expression; 2] = operands.try_into().unwrap();
            let [lhs, rhs] = operands.map(Box::new);
            Ok(Expression::BinaryOp { lhs, op: operators[0], rhs })
        }
        _ => {
            let mut lowest_precedence = u8::MAX;
            let mut associativity = Associativity::None;
            let mut lowest_precedence_operator_indices = vec![];
            for (i, op) in operators.iter().enumerate() {
                let (precedence, assoc) = op.precedence_and_associativity();
                if precedence == lowest_precedence {
                    lowest_precedence_operator_indices.push(i);
                    if assoc != associativity {
                        return Err("operators with the same precedence but \
                                    different associativities cannot be \
                                    chained");
                    }
                } else if precedence < lowest_precedence {
                    lowest_precedence = precedence;
                    lowest_precedence_operator_indices.clear();
                    lowest_precedence_operator_indices.push(i);
                    associativity = assoc;
                }
            }
            if associativity == Associativity::None
                && lowest_precedence_operator_indices.len() > 1
            {
                return Err("operator cannot be chained");
            }

            let n = lowest_precedence_operator_indices.len();
            // These are all stored in reverse order, since it's easier to take
            // from the end of the vec since that doesn't affect indices.
            let mut operand_chunks: Vec<Vec<Expression>> =
                Vec::with_capacity(n + 1);
            let mut operator_chunks: Vec<Vec<BinaryOp>> =
                Vec::with_capacity(n + 1);
            let mut lowest_precedence_operators: VecDeque<BinaryOp> =
                VecDeque::with_capacity(n);
            for &n in lowest_precedence_operator_indices.iter().rev() {
                operand_chunks.push(operands.split_off(n + 1));
                operator_chunks.push(operators.split_off(n + 1));
                lowest_precedence_operators.push_back(operators.pop().unwrap());
            }
            operand_chunks.push(operands);
            operator_chunks.push(operators);

            let mut operators = lowest_precedence_operators;

            // As above, these are in reverse order.
            let mut operands = std::iter::zip(operand_chunks, operator_chunks)
                .map(|(operands, operators)| {
                    fixup_binary_operators(operands, operators)
                })
                .collect::<Result<VecDeque<_>, _>>()?;

            // Because the above are in reverse order, left-associativity will
            // take from the back, and right-associativity will take from the
            // front
            match associativity {
                Associativity::Left | Associativity::None => {
                    let mut expr = operands.pop_back().unwrap();
                    while let Some(lhs) = operands.pop_back() {
                        let op = operators.pop_back().unwrap();
                        expr = Expression::BinaryOp {
                            lhs: Box::new(lhs),
                            op,
                            rhs: Box::new(expr),
                        };
                    }
                    debug_assert!(operators.is_empty());
                    Ok(expr)
                }
                Associativity::Right => {
                    let mut expr = operands.pop_front().unwrap();
                    while let Some(rhs) = operands.pop_front() {
                        let op = operators.pop_front().unwrap();
                        expr = Expression::BinaryOp {
                            lhs: Box::new(expr),
                            op,
                            rhs: Box::new(rhs),
                        };
                    }
                    debug_assert!(operators.is_empty());
                    Ok(expr)
                }
            }
        }
    }
}

/// A expression that is not a block.
///
/// TODO: docs
fn parse_no_block_expression(input: &[TokenTree]) -> IResult<'_, Expression> {
    alt((
        preceded(parse_ident("break"), opt(parse_no_block_expression))
            .map(|expr| Expression::Break { value: expr.map(Box::new) }),
        preceded(parse_ident("return"), opt(parse_no_block_expression))
            .map(|expr| Expression::Return { value: expr.map(Box::new) }),
        parse_operator_expression,
    ))(input)
}

/// An expression containing unary and binary operators.
///
/// TODO: docs
fn parse_operator_expression(input: &[TokenTree]) -> IResult<'_, Expression> {
    let (input, (mut operands, operators)) = fold_many0(
        tuple((parse_cast_expression, parse_binop)),
        || (vec![], vec![]),
        |mut vs, items| {
            vs.extend([items]);
            vs
        },
    )(input)?;
    let (input, last_operand) = parse_cast_expression(input)?;
    if operands.is_empty() {
        Ok((input, last_operand))
    } else {
        operands.push(last_operand);
        let expr = fixup_binary_operators(operands, operators).unwrap();
        Ok((input, expr))
    }
}

/// A type-cast expression.
///
/// ```text
/// PREFIX_UNARY_EXPR ( 'as' TYPE )*
/// ```
///
/// Examples:
///
/// ```text
/// 42 as u8
/// 42 as *mut u8
/// &X as usize
/// ```
fn parse_cast_expression(input: &[TokenTree]) -> IResult<'_, Expression> {
    let (input, mut expr) = parse_prefix_unary_expression(input)?;
    let (input, tails) = many0(preceded(parse_ident("as"), parse_type))(input)?;
    for to_type in tails {
        expr = Expression::UnaryOp {
            op: UnaryOp::AsCast { to_type },
            operand: Box::new(expr),
        };
    }
    Ok((input, expr))
}

/// An expression containing no top-level binary operators (there can be
/// binary operators in parentheses, arrays, function call arguments, etc).
///
/// ```text
/// | '-' PREFIX_UNARY_EXPR
/// | '!' PREFIX_UNARY_EXPR
/// | '*' PREFIX_UNARY_EXPR
/// | '&' PREFIX_UNARY_EXPR
/// | POSTFIX_UNARY_EXPR
/// ```
///
/// Examples:
///
/// ```text
/// 42
/// &hello
/// (43 + 7)
/// my_function(42, 7 + 3)
/// !my_function(X, 42)
/// &(*get_ptr(42))[3]
/// ```
fn parse_prefix_unary_expression(
    input: &[TokenTree],
) -> IResult<'_, Expression> {
    let prefix_unary_op = |op: &'static str, unary_op: UnaryOp| {
        preceded(parse_joint_puncts(op), parse_prefix_unary_expression).map(
            move |operand| Expression::UnaryOp {
                op: unary_op.clone(),
                operand: Box::new(operand),
            },
        )
    };

    alt((
        parse_postfix_unary_expression,
        prefix_unary_op("-", UnaryOp::Neg),
        prefix_unary_op("!", UnaryOp::Not),
        prefix_unary_op("*", UnaryOp::Deref),
        pair(
            preceded(parse_joint_puncts("&"), opt(parse_ident("mut"))),
            parse_prefix_unary_expression,
        )
        .map(|(mutable, operand)| Expression::UnaryOp {
            op: UnaryOp::AddrOf { mutable: mutable.is_some() },
            operand: Box::new(operand),
        }),
    ))(input)
}

/// An expression containing no top-level binary operators, prefix unary
/// operators, or type casts (there can be such operators in parentheses,
/// arrays, function call arguments, etc).
///
/// ```text
/// | integer
/// | ident
/// | 'true'
/// | 'false'
/// | '_'
/// | '(' list[EXPRESSION] ')'
/// | '[' list[EXPRESSION] ']'
/// | POSTFIX_UNARY_EXPR '[' EXPRESSION ']'
/// | POSTFIX_UNARY_EXPR '(' list[EXPRESSION] ')'
/// ```
///
/// Examples:
///
/// ```text
/// 42
/// hello
/// (43 + 7)
/// my_function(42, 7 + 3)
/// my_function(X, 42)
/// (*get_ptr(42))[3]
/// ```
fn parse_postfix_unary_expression(
    input: &[TokenTree],
) -> IResult<'_, Expression> {
    let (input, mut expr) = alt((
        parse_integer.map(Expression::Integer),
        parse_non_kw_ident.map(Expression::Ident),
        parse_ident("_").map(|_| Expression::Wildcard),
        parse_ident("true").map(|_| Expression::Bool(true)),
        parse_ident("false").map(|_| Expression::Bool(false)),
        parse_group(
            Delimiter::Parenthesis,
            comma_separated_list(parse_expression).map(Expression::Tuple),
        ),
        parse_group(
            Delimiter::Bracket,
            comma_separated_list(parse_expression).map(Expression::Array),
        ),
    ))(input)?;
    let index = parse_group(Delimiter::Bracket, parse_expression);
    let call = parse_group(
        Delimiter::Parenthesis,
        comma_separated_list(parse_expression),
    );
    let (input, tails) = many0(either(index, call))(input)?;
    for tail in tails {
        expr = match tail {
            Either::Left(index) => Expression::Index {
                base: Box::new(expr),
                index: Box::new(index),
            },
            Either::Right(args) => {
                Expression::Call { function: Box::new(expr), args }
            }
        };
    }
    Ok((input, expr))
}

#[test]
fn test_unary_expressions() {
    use crate::lexer::lex;
    let tokens = lex("!&*&!*&a[42](37) as u32".as_bytes());
    let ast = all_consuming(parse_expression)(&tokens).finish().unwrap();
}

const fn sorted_by_length_decreasing<const N: usize, T: Copy>(
    mut ops: [(&'static str, T); N],
) -> [(&'static str, T); N] {
    let mut i = N;
    while i > 0 {
        let mut j = 0;
        while j < i - 1 {
            if ops[j].0.len() < ops[j + 1].0.len() {
                (ops[j], ops[j + 1]) = (ops[j + 1], ops[j]);
            }
            j += 1;
        }
        i -= 1;
    }
    ops
}

/// Parse a binary operator, e.g. `+`, `||=`, `<<`.
fn parse_binop(input: &[TokenTree]) -> IResult<'_, BinaryOp> {
    use ArithmeticOp as A;
    use BinaryOp as B;
    use ComparisonOp as C;
    // sorted longest first to avoid parsing ambiguity
    static BINOPS: [(&str, BinaryOp); 33] = sorted_by_length_decreasing([
        ("+", B::Arithmetic(A::Add)),
        ("-", B::Arithmetic(A::Subtract)),
        ("*", B::Arithmetic(A::Multiply)),
        ("/", B::Arithmetic(A::Divide)),
        ("%", B::Arithmetic(A::Modulo)),
        ("&&", B::Arithmetic(A::And)),
        ("||", B::Arithmetic(A::Or)),
        ("&", B::Arithmetic(A::BitAnd)),
        ("|", B::Arithmetic(A::BitOr)),
        ("^", B::Arithmetic(A::BitXor)),
        (">>", B::Arithmetic(A::RightShift)),
        ("<<", B::Arithmetic(A::LeftShift)),
        ("==", B::Comparison(C::Equal)),
        ("<=", B::Comparison(C::LessEq)),
        (">=", B::Comparison(C::GreaterEq)),
        ("!=", B::Comparison(C::NotEqual)),
        ("<", B::Comparison(C::Less)),
        (">", B::Comparison(C::Greater)),
        ("=", B::Assignment { augment: None }),
        ("+=", B::Assignment { augment: Some(A::Add) }),
        ("-=", B::Assignment { augment: Some(A::Subtract) }),
        ("*=", B::Assignment { augment: Some(A::Multiply) }),
        ("/=", B::Assignment { augment: Some(A::Divide) }),
        ("%=", B::Assignment { augment: Some(A::Modulo) }),
        ("&&=", B::Assignment { augment: Some(A::And) }),
        ("||=", B::Assignment { augment: Some(A::Or) }),
        ("&=", B::Assignment { augment: Some(A::BitAnd) }),
        ("|=", B::Assignment { augment: Some(A::BitOr) }),
        ("^=", B::Assignment { augment: Some(A::BitXor) }),
        (">>=", B::Assignment { augment: Some(A::RightShift) }),
        ("<<=", B::Assignment { augment: Some(A::LeftShift) }),
        ("..", B::RangeOp { end_inclusive: false }),
        ("..=", B::RangeOp { end_inclusive: true }),
    ]);
    for (puncts, binop) in BINOPS {
        if let Ok((input, ())) = parse_joint_puncts(puncts)(input) {
            return Ok((input, binop));
        }
    }
    return Err(nom::Err::Error(ParseError::from_error_kind(
        input,
        ErrorKind::IsA,
    )))
    .or_expected("a binary operator");
}

/// A [`fn` parameter](parse_fn_param) list.
///
/// ```text
/// '(' list[TYPED_PATTERN] ')'
/// ```
fn parse_fn_params(input: &[TokenTree]) -> IResult<'_, Vec<FnParam>> {
    let inner = comma_separated_list(parse_fn_param);
    parse_group(Delimiter::Parenthesis, inner)(input)
}

/// A parameter argument in a `fn` item: a [pattern](parse_pattern) followed by
/// a colon and a [type](parse_type).
///
/// ```text
/// PATTERN ':' TYPE
/// ```
fn parse_fn_param(input: &[TokenTree]) -> IResult<'_, FnParam> {
    tuple((parse_pattern, parse_joint_puncts(":"), parse_type))
        .map(|(pattern, _, type_)| FnParam { pattern, type_ })
        .parse(input)
}

/// Any identifier, including keywords.
fn parse_any_ident(input: &[TokenTree]) -> IResult<'_, Ident> {
    let Some((&TokenTree::Ident(ident), rest)) = input.split_first() else {
        return Err(nom::Err::Error(ParseError::from_error_kind(
            input,
            ErrorKind::IsA,
        )));
    };
    Ok((rest, ident))
}

/// Non-keyword identifiers.
fn parse_non_kw_ident(input: &[TokenTree]) -> IResult<'_, Ident> {
    verify(parse_any_ident, |ident: &Ident| !lexer::is_keyword(&ident.ident))(
        input,
    )
}

/// Parse a specific identifier. May be a keyword.
fn parse_ident<'expected>(
    expected: &'expected str,
) -> impl for<'a> Fn(&'a [TokenTree]) -> IResult<'a, ()> + 'expected {
    move |input| {
        nom::combinator::verify(parse_any_ident, |ident: &Ident| {
            ident.ident == expected
        })
        .map(|_| ())
        .parse(input)
    }
}

/// Any integer token.
fn parse_integer(input: &[TokenTree]) -> IResult<'_, Integer> {
    let Some((TokenTree::Integer(integer), rest)) = input.split_first() else {
        return Err(nom::Err::Error(ParseError::from_error_kind(
            input,
            ErrorKind::IsA,
        )));
    };
    Ok((rest, *integer))
}

/// Parse a specific sequence of punctuation characters not separated by
/// whitespace.
///
/// For example, `parse_joint_puncts(">>=")` will match `>>=` but not `>> =`.
fn parse_joint_puncts<'expected>(
    expected: &'expected str,
) -> impl for<'a> Fn(&'a [TokenTree]) -> IResult<'a, ()> + 'expected + Copy {
    let expected = expected.as_bytes();
    move |input: &[TokenTree]| -> IResult<'_, ()> {
        if input.len() < expected.len() {
            return Err(nom::Err::Error(ParseError::from_error_kind(
                input,
                ErrorKind::IsA,
            )));
        }
        let (puncts, rest) = input.split_at(expected.len());
        for (position, (expected, punct)) in
            expected.iter().copied().zip(puncts).with_position()
        {
            if punct.as_punct().is_none_or(|punct| {
                punct.c != expected
                    || !(punct.joint_with_next
                        || matches!(position, Position::Last | Position::Only))
            }) {
                return Err(nom::Err::Error(ParseError::from_error_kind(
                    input,
                    ErrorKind::IsA,
                )));
            }
        }
        Ok((rest, ()))
    }
}

/// `const` (false) or `mut` (true)
fn parse_pointer_mutability(input: &[TokenTree]) -> IResult<'_, bool> {
    map_opt(parse_any_ident, |ident: Ident| match ident.ident {
        "const" => Some(false),
        "mut" => Some(true),
        _ => None,
    })(input)
}

/// A type.
///
/// ```text
/// | ident
/// | '!'
/// | '[' TYPE (';' integer)? ']'
/// | '(' list[TYPE] ')'
/// | '*' ('const' | 'mut') TYPE
/// ```
///
/// Can be:
///
/// * a named type
/// * the never type (`!`)
/// * an array or slice type
/// * a tuple type or a parenthesized type
/// * a pointer type
fn parse_type(input: &[TokenTree]) -> IResult<'_, Type> {
    let named_type = parse_non_kw_ident.map(Type::Ident);
    let never_type = parse_joint_puncts("!").map(|_| Type::Never);
    let pointer_type =
        tuple((parse_joint_puncts("*"), parse_pointer_mutability, parse_type))
            .map(|(_, mutable, pointee)| Type::Pointer {
                mutable,
                pointee: Box::new(pointee),
            });
    let array_or_slice_type = parse_group(
        Delimiter::Bracket,
        tuple((
            parse_type,
            opt(preceded(parse_joint_puncts(";"), parse_integer)),
        ))
        .map(|(element, length)| match length {
            Some(length) => {
                Type::Array { element: Box::new(element), length: length.value }
            }
            None => Type::Slice { element: Box::new(element) },
        }),
    );
    // We can't just do `separated_list(',', parse_type)`, since that would
    // treat `(u32)` as `(u32,)`.
    let tuple_or_parenthesized_type = parse_group(
        Delimiter::Parenthesis,
        alt((
            terminated(parse_type, eof),
            comma_separated_list(parse_type).map(|types| Type::Tuple(types)),
        )),
    );

    alt((
        named_type,
        never_type,
        pointer_type,
        tuple_or_parenthesized_type,
        array_or_slice_type,
    ))(input)
}

/// A static item.
///
/// ```text
/// 'extern'? 'static' 'mut'? ident ':' TYPE ( '=' EXPRESSION )? ';'
/// ```
///
/// If `mut` is present, the item is mutable. If `mut` is not present, the item
/// is not mutable (including by external code!).
///
/// If `extern` is not present, then `EXPRESSION` must be present, and this
/// defines an internal, non-exported static item.
///
/// If `extern` is present and `EXPRESSION` is present, this defines an
/// exported static item.
///
/// If `extern` is present and `EXPRESSION` is not present, this declares an
/// external static item that is defined elsewhere.
///
/// Examples:
///
/// ```text
/// extern static mut errno: i32;
/// extern static MY_VAR: u64 = 42;
/// static mut COUNTER: u64 = 0;
/// ```
fn parse_static_item(input: &[TokenTree]) -> IResult<'_, StaticItem> {
    let (input, extern_token) = opt(parse_ident("static"))(input)?;
    let (input, static_token) = parse_ident("static")(input)?;
    let (input, mut_token) = opt(parse_ident("mut"))(input)?;
    let (input, name) = parse_non_kw_ident(input)?;
    let (input, type_) = preceded(parse_joint_puncts(":"), parse_type)(input)?;
    let (input, initializer) =
        opt(preceded(parse_joint_puncts("="), parse_expression))(input)?;
    let (input, _semi) = parse_joint_puncts(";")(input)?;
    Ok((
        input,
        StaticItem {
            extern_token,
            static_token,
            mut_token,
            name,
            type_,
            initializer,
        },
    ))
}

/// A pattern, as used in `let` bindings, `fn` arguments, and `match` arms.
///
/// ```text
/// | '_'
/// | 'mut' ident
/// | ident
/// | '(' list[PATTERN_WITH_ALT] ')'
/// | '[' list[PATTERN_WITH_ALT] ']'
/// ```
fn parse_pattern(input: &[TokenTree]) -> IResult<'_, Pattern> {
    // TODO: remove once todo!() is implmented below;
    // this way we don't panic if there's nothing to parse anyway
    let (input, _) = not(eof)(input)?;
    let wildcard_pattern = parse_ident("_").map(|_| Pattern::Wildcard);
    let ident_pattern = pair(opt(parse_ident("mut")), parse_non_kw_ident).map(
        |(mutable, ident)| Pattern::Ident { mutable: mutable.is_some(), ident },
    );
    let integer_pattern = parse_integer.map(Pattern::Integer);
    let array_pattern = parse_group(
        Delimiter::Bracket,
        comma_separated_list(parse_pattern_with_alt),
    )
    .map(|patterns| Pattern::Array(patterns));
    let tuple_or_parenthesized_pattern = parse_group(
        Delimiter::Parenthesis,
        alt((
            terminated(parse_pattern_with_alt, eof),
            comma_separated_list(parse_pattern_with_alt)
                .map(|patterns| Pattern::Tuple(patterns)),
        )),
    );
    alt((
        wildcard_pattern,
        ident_pattern,
        integer_pattern,
        array_pattern,
        tuple_or_parenthesized_pattern,
    ))(input)
}

/// A pattern that matches if any of its alternatives match.
///
/// ```text
/// '|'? PATTERN ('|' PATTERN)*
/// // equivalently
/// '|'? (PATTERN '|')* PATTERN
/// ```
fn parse_pattern_with_alt(input: &[TokenTree]) -> IResult<'_, Pattern> {
    fn alt(input: &[TokenTree]) -> IResult<'_, ()> {
        parse_joint_puncts("|")(input)
    }
    let base =
        tuple((opt(alt), many0(terminated(parse_pattern, alt)), parse_pattern));
    let mut mapped = base.map(|(_, mut patterns, last_pattern)| {
        if patterns.is_empty() {
            last_pattern
        } else {
            patterns.push(last_pattern);
            Pattern::Alt(patterns)
        }
    });
    mapped.parse(input)
}

#[test]
fn test_comma_separated() {
    for src in ["", "42", "42,", "42,42"] {
        let tokens = crate::lexer::lex(src.as_bytes());
        let res = comma_separated_list(parse_integer)(&tokens).finish();
        let (tokens, _) = res.unwrap();
        assert!(tokens.is_empty(), "{src:?}: {tokens:?}");
    }
    for src in ["", "x: u32", "x: *mut u32,", "x: *mut u32, y: u64"] {
        let tokens = crate::lexer::lex(src.as_bytes());
        let res = comma_separated_list(parse_fn_param)(&tokens).finish();
        let (tokens, _) = res.unwrap();
        assert!(tokens.is_empty(), "{src:?}: {tokens:?}");
    }
    for src in ["()", "(x: u32)", "(x: *mut u32,)", "(x: *mut u32, y: u64)"] {
        let tokens = crate::lexer::lex(src.as_bytes());
        let res = parse_fn_params(&tokens).finish();
        let (tokens, _) = res.unwrap();
        assert!(tokens.is_empty(), "{src:?}: {tokens:?}");
    }
}
