use crate::{
    ast::{self, Block, ExternBlock, FnItem, Item, Pattern, Type},
    token::{Delimiter, Punct, TokenTree},
};

pub fn parse(tokens: &[TokenTree]) -> Vec<ast::Item> {
    let (items, end) = parse_items(tokens, 0);
    assert_eq!(end, tokens.len());
    items
}

fn parse_items(tokens: &[TokenTree], start: usize) -> (Vec<ast::Item>, usize) {
    let mut idx = start;
    let mut items = vec![];
    while idx < tokens.len() {
        let Some((item, end)) = parse_item(tokens, idx) else {
            break;
        };
        items.push(item);
        idx = end;
    }
    (items, idx)
}

fn map<
    I,
    O,
    F: FnOnce(&[TokenTree], usize) -> Option<(I, usize)>,
    M: FnOnce(I) -> O,
>(
    f: F, m: M,
) -> impl FnOnce(&[TokenTree], usize) -> Option<(O, usize)> {
    move |tokens, start| match f(tokens, start) {
        Some((ast, end)) => Some((m(ast), end)),
        None => todo!(),
    }
}

fn chain<
    O1,
    O2,
    P1: FnOnce(&[TokenTree], usize) -> Option<(O1, usize)>,
    P2: FnOnce(&[TokenTree], usize) -> Option<(O2, usize)>,
>(
    p1: P1, p2: P2,
) -> impl FnOnce(&[TokenTree], usize) -> Option<((O1, O2), usize)> {
    move |tokens, start| {
        let (o1, mid) = p1(tokens, start)?;
        let (o2, end) = p2(tokens, mid)?;
        Some(((o1, o2), end))
    }
}

fn opt<O, F: FnOnce(&[TokenTree], usize) -> Option<(O, usize)>>(
    f: F,
) -> impl FnOnce(&[TokenTree], usize) -> Option<(Option<O>, usize)> {
    move |tokens, start| match f(tokens, start) {
        Some((result, end)) => Some((Some(result), end)),
        None => Some((None, start)),
    }
}

fn separated_opt_trailing<
    O1,
    O2,
    P1: FnMut(&[TokenTree], usize) -> Option<(O1, usize)>,
    P2: FnMut(&[TokenTree], usize) -> Option<(O2, usize)>,
>() {
}

fn expect_punct(
    expected: u8,
) -> impl Fn(&[TokenTree], usize) -> Option<((), usize)> {
    move |tokens, start| {
        let token = tokens.get(start)?;
        let punct = token.as_punct()?;
        if expected == punct.c {
            Some(((), start + 1))
        } else {
            None
        }
    }
}

fn expect_joint_puncts(
    expected: &[u8],
) -> impl Fn(&[TokenTree], usize) -> Option<((), usize)> + '_ {
    move |tokens, start| {
        let puncts = tokens.get(start..)?.get(..expected.len())?;
        for (expected, punct) in expected.iter().copied().zip(puncts) {
            let punct = punct.as_punct()?;
            if !punct.joint_with_next || punct.c != expected {
                return None;
            }
        }
        Some(((), start + expected.len()))
    }
}

fn parse_item(
    tokens: &[TokenTree], start: usize,
) -> Option<(ast::Item, usize)> {
    map(parse_fn_item, Item::FnItem)(tokens, start)
        .or_else(|| map(parse_static_item, Item::StaticItem)(tokens, start))
        .or_else(|| map(parse_extern_block, Item::ExternBlock)(tokens, start))
}

fn parse_fn_item(
    tokens: &[TokenTree], start: usize,
) -> Option<(ast::FnItem, usize)> {
    let mut idx = start;
    let mut extern_token = None;
    let fn_token: ();
    loop {
        let token = tokens.get(idx)?;
        match token.as_ident()?.ident.as_str() {
            "extern" => {
                if extern_token.is_some() {
                    return None;
                } else {
                    extern_token = Some(());
                    idx += 1
                }
            }
            "fn" => {
                fn_token = ();
                idx += 1;
                break;
            }
            _ => return None,
        }
    }
    let name = tokens.get(idx)?.as_ident()?.clone();
    idx += 1;
    let args = tokens.get(idx)?.as_group()?;
    if args.delimiter != Delimiter::Parenthesis {
        return None;
    }
    eprintln!("TODO: parse fn args");

    let return_type;
    (return_type, idx) = opt(parse_return_type)(tokens, start)?;

    if let Some((semicolon, end)) = expect_punct(b';')(tokens, idx) {
        Some((
            FnItem {
                extern_token,
                fn_token,
                name,
                args: todo!(),
                return_type,
                body: None,
            },
            end,
        ))
    } else {
        let (body, end) = parse_block(tokens, idx)?;
        Some((
            FnItem {
                extern_token,
                fn_token,
                name,
                args: todo!(),
                return_type,
                body: Some(body),
            },
            end,
        ))
    }
}

fn parse_typed_pattern(
    tokens: &[TokenTree], idx: usize,
) -> Option<((Pattern, Type), usize)> {
    todo!()
}

fn parse_block(tokens: &[TokenTree], idx: usize) -> Option<(Block, usize)> {
    todo!()
}

fn parse_type(
    tokens: &[TokenTree], start: usize,
) -> Option<(ast::Type, usize)> {
    match tokens.get(start)? {
        TokenTree::Ident(ident) => {
            Some((Type::Ident(ident.clone()), start + 1))
        }
        TokenTree::Group(group) => match group.delimiter {
            Delimiter::Parenthesis => todo!("tuple"),
            Delimiter::Brace => return None,
            Delimiter::Bracket => todo!("array/slice"),
        },
        TokenTree::Integer(_) => None,
        TokenTree::Punct(punct) => match punct.c {
            b'*' => todo!("pointer"),
            _ => None,
        },
    }
}

fn parse_return_type(
    tokens: &[TokenTree], start: usize,
) -> Option<(ast::Type, usize)> {
    let ((), mid) = expect_joint_puncts(b"->")(tokens, start)?;
    parse_type(tokens, mid)
}

fn parse_static_item(
    tokens: &[TokenTree], start: usize,
) -> Option<(ast::StaticItem, usize)> {
    todo!()
}

/// `extern` followed by a `Brace` group containing items
fn parse_extern_block(
    tokens: &[TokenTree], start: usize,
) -> Option<(ast::ExternBlock, usize)> {
    if tokens.get(start)?.as_ident()?.ident.as_str() != "extern" {
        return None;
    }
    let group = tokens.get(start + 1)?.as_group()?;
    if group.delimiter != Delimiter::Brace {
        return None;
    }
    let inner = &group.inner;
    let (items, end) = parse_items(inner, 0);
    assert_eq!(end, inner.len());
    Some((ExternBlock { extern_token: (), items }, start + 2))
}
