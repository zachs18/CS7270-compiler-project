use std::{backtrace::Backtrace, fmt};

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
        Block, Expression, FnArg, FnItem, Item, Pattern, Statement, StaticItem,
        Type,
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
        write!(f, "at {}: ", self.backtrace)?;
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
        parse_joint_puncts(";")(input)
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

/// ```ignore
/// 'extern'? 'fn' ident '(' list[TYPED_PATTERN] ')' ( BLOCK | ';' )
/// ```
///
/// A function item.
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
/// ```ignore
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
        let (input, args) = parse_fn_args(input)?;
        let (input, return_type) =
            opt(preceded(parse_joint_puncts("->"), parse_type))(input)?;
        if let Ok((input, ())) = parse_joint_puncts(";")(input) {
            Ok((
                input,
                FnItem {
                    extern_token,
                    fn_token,
                    name: name.clone(),
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
                    name: name.clone(),
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

fn parse_block(input: &[TokenTree]) -> IResult<'_, Block> {
    let inner = pair(parse_statements, opt(parse_expression.map(Box::new)));
    parse_group(Delimiter::Brace, inner)
        .map(|(statements, expr)| Block { statements, tail: expr })
        .parse(input)
}

fn parse_statements(input: &[TokenTree]) -> IResult<'_, Vec<Statement>> {
    many0(parse_statement)(input)
}

fn parse_statement(input: &[TokenTree]) -> IResult<'_, Statement> {
    alt((
        terminated(parse_no_block_expression, parse_joint_puncts(";"))
            .map(|expr| Statement::Expression(expr)),
        terminated(parse_block_expression, opt(parse_joint_puncts(";")))
            .map(|expr| Statement::Expression(expr)),
        parse_let_statement,
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

fn parse_block_expression(input: &[TokenTree]) -> IResult<'_, Expression> {
    alt((
        parse_block.map(Expression::Block),
        parse_if_expression,
        parse_loop_expression,
        parse_match_expression,
    ))(input)
}

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

fn parse_match_expression(input: &[TokenTree]) -> IResult<'_, Expression> {
    let (input, _match) = parse_ident("match")(input)?;
    let (input, scrutinee) = parse_no_block_expression(input)?;
    let inner = |_input| todo!("parsing match expressions");
    let (input, arms) = parse_group(Delimiter::Brace, inner)(input)?;
    Ok((input, Expression::Match { scrutinee: Box::new(scrutinee), arms }))
}

fn parse_loop_expression(input: &[TokenTree]) -> IResult<'_, Expression> {
    alt((
        tuple((
            parse_ident("while"),
            parse_no_block_expression.map(|a| dbg!(a)),
            parse_block,
        ))
        .map(|(_, condition, body)| Expression::While {
            condition: Box::new(condition),
            body,
        }),
        tuple((parse_ident("for"), |_input| todo!("for loop")))
            .map(|(_, ())| todo!()),
        tuple((parse_ident("loop"), parse_block))
            .map(|(_, body)| Expression::Loop(body)),
    ))(input)
}

fn parse_no_block_expression(input: &[TokenTree]) -> IResult<'_, Expression> {
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
        Ok((input, Expression::BinOpChain { operands, operators }))
    }
}

/// ```ignore
///  | integer
///  | ident
///  | '_'
///  | '(' list[EXPRESSION] ')'
///  | '[' list[EXPRESSION] ']'
///  | '-' UNARY_EXPR
///  | '!' UNARY_EXPR
///  | '*' UNARY_EXPR
///  | '&' UNARY_EXPR
///  | UNARY_EXPR '[' EXPRESSION ']'
///  | UNARY_EXPR '(' list[EXPRESSION] ')'
/// ```
///
/// An expression containing no top-level binary operators (there can be
/// binary operators in parentheses, arrays, function call arguments, etc).
///
/// Examples:
///
/// ```ignore
/// 42
/// &hello
/// (43 + 7)
/// my_function(42, 7 + 3)
/// !my_function(X, 42)
/// &(*get_ptr(42))[3]
/// ```
fn parse_unary_expression(input: &[TokenTree]) -> IResult<'_, Expression> {
    let (input, unary_expression) = alt((
        parse_integer.map(Expression::Integer),
        parse_non_kw_ident.map(|ident| Expression::Ident(ident.clone())),
        parse_ident("_").map(|_| Expression::Wildcard),
        parse_group(
            Delimiter::Parenthesis,
            comma_separated_list(parse_expression).map(Expression::Tuple),
        ),
        parse_group(
            Delimiter::Bracket,
            comma_separated_list(parse_expression).map(Expression::Array),
        ),
        tuple((parse_joint_puncts("-"), parse_unary_expression))
            .map(|(_, expr)| Expression::Neg(Box::new(expr))),
        tuple((parse_joint_puncts("!"), parse_unary_expression))
            .map(|(_, expr)| Expression::Not(Box::new(expr))),
        tuple((parse_joint_puncts("*"), parse_unary_expression))
            .map(|(_, expr)| Expression::Deref(Box::new(expr))),
        tuple((parse_joint_puncts("&"), parse_unary_expression))
            .map(|(_, expr)| Expression::AddrOf(Box::new(expr))),
    ))(input)?;
    let index = parse_group(Delimiter::Bracket, parse_expression);
    let call = parse_group(
        Delimiter::Parenthesis,
        comma_separated_list(parse_expression),
    );
    let (input, tails) = many0(either(index, call))(input)?;
    if tails.is_empty() {
        // There were only prefix operators, don't need to do precedence stuff
        Ok((input, unary_expression))
    } else {
        // Need to do precedence stuff
        todo!()
    }
}

/// ```ignore
/// UNARY_EXPR ( 'as' TYPE )*
/// ```
///
/// A type-cast expression.
///
/// Examples:
///
/// ```ignore
/// 42 as u8
/// 42 as *mut u8
/// &X as usize
/// ```
fn parse_cast_expression(input: &[TokenTree]) -> IResult<'_, Expression> {
    let (input, unary_expression) = parse_unary_expression(input)?;
    let (input, tails) = many0(preceded(parse_ident("as"), parse_type))(input)?;
    if tails.is_empty() {
        // There were no casts, don't need to do precedence stuff
        Ok((input, unary_expression))
    } else {
        // Need to do precedence stuff
        todo!()
    }
}

#[test]
fn test_unary_expressions() {
    use crate::lexer::lex;
    let tokens = lex("!&*&!*&a".as_bytes());
    let ast = parse_unary_expression(&tokens);
    assert!(ast.is_ok());
}

const fn sorted_by_length_decreasing<const N: usize>(
    mut strs: [&'static str; N],
) -> [&'static str; N] {
    let mut i = N;
    while i > 0 {
        let mut j = 0;
        while j < i - 1 {
            if strs[j].len() < strs[j + 1].len() {
                (strs[j], strs[j + 1]) = (strs[j + 1], strs[j]);
            }
            j += 1;
        }
        i -= 1;
    }
    strs
}

fn parse_binop(input: &[TokenTree]) -> IResult<'_, &'static str> {
    // sorted longest first to avoid parsing ambiguity
    static BINOPS: [&str; 33] = sorted_by_length_decreasing([
        "+", "-", "*", "/", "%", "&&", "||", "&", "|", "^", ">>", "<<", "==",
        "<=", ">=", "!=", "<", ">", "=", "+=", "-=", "*=", "/=", "%=", "&&=",
        "||=", "&=", "|=", "^=", ">>=", "<<=", "..", "..=",
    ]);
    for binop in BINOPS {
        if let Ok((input, ())) = parse_joint_puncts(binop)(input) {
            return Ok((input, binop));
        }
    }
    return Err(nom::Err::Error(ParseError::from_error_kind(
        input,
        ErrorKind::IsA,
    )))
    .or_expected("a binary operator");
}

/// ```ignore
/// '(' list[TYPED_PATTERN] ')'
/// ```
fn parse_fn_args(input: &[TokenTree]) -> IResult<'_, Vec<FnArg>> {
    let inner = comma_separated_list(parse_fn_arg);
    parse_group(Delimiter::Parenthesis, inner)(input)
}

/// ```ignore
/// PATTERN ':' TYPE
/// ```
fn parse_fn_arg(input: &[TokenTree]) -> IResult<'_, FnArg> {
    tuple((parse_pattern, parse_joint_puncts(":"), parse_type))
        .map(|(pattern, _, type_)| FnArg { pattern, type_ })
        .parse(input)
}

/// Any identifier, including keywords.
fn parse_any_ident(input: &[TokenTree]) -> IResult<'_, &Ident> {
    let Some((TokenTree::Ident(ident), rest)) = input.split_first() else {
        return Err(nom::Err::Error(ParseError::from_error_kind(
            input,
            ErrorKind::IsA,
        )));
    };
    Ok((rest, ident))
}

/// Non-keyword identifiers.
fn parse_non_kw_ident(input: &[TokenTree]) -> IResult<'_, &Ident> {
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
    map_opt(parse_any_ident, |ident: &Ident| match ident.ident.as_str() {
        "const" => Some(false),
        "mut" => Some(true),
        _ => None,
    })(input)
}

/// ```ignore
/// | ident
/// | '[' TYPE (';' integer)? ']'
/// | '(' list[TYPE] ')'
/// | '*' ('const' | 'mut') TYPE
/// ```
///
/// A type. Can be:
///
/// * a named type
/// * an array or slice type
/// * a tuple type or a parenthesized type
/// * a pointer type
fn parse_type(input: &[TokenTree]) -> IResult<'_, Type> {
    let named_type = parse_non_kw_ident.map(|ident| Type::Ident(ident.clone()));
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
    let tuple_type = parse_group(
        Delimiter::Parenthesis,
        alt((
            terminated(parse_type, eof),
            comma_separated_list(parse_type).map(|types| Type::Tuple(types)),
        )),
    );

    alt((named_type, pointer_type, tuple_type, array_or_slice_type))(input)
}

/// ```ignore
/// 'extern'? 'static' 'mut'? ident ':' TYPE ( '=' EXPRESSION )? ';'
/// ```
///
/// A static item.
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
/// ```ignore
/// extern fn memcpy(dst: *mut void, src: *const void, n: usize) -> *mut void;
/// extern fn main(argc: i32, argv: *mut *mut i8) -> i32 {
///     let x = 4 + 3;
/// }
/// fn foobar(x: *mut [u32; 10]) {
///     x[4] = 3;
/// }
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
            name: name.clone(),
            type_,
            initializer,
        },
    ))
}

fn parse_pattern(input: &[TokenTree]) -> IResult<'_, Pattern> {
    // TODO: remove once todo!() is implmented below;
    // this way we don't panic if there's nothing to parse anyway
    let (input, _) = not(eof)(input)?;
    let mut basic = alt((
        parse_ident("_").map(|_| Pattern::Wildcard),
        pair(opt(parse_ident("mut")), parse_non_kw_ident).map(
            |(mutable, ident)| Pattern::Ident {
                mutable: mutable.is_some(),
                ident: ident.clone(),
            },
        ),
    ));
    if let Ok((input, pattern)) = basic(input) {
        return Ok((input, pattern));
    } else {
        todo!()
    }
}
