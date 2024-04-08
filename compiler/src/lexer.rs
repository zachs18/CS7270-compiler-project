use crate::token::{Delimiter, Group, Ident, Integer, Punct, TokenTree};

pub fn lex(src: &'static [u8]) -> Vec<TokenTree> {
    let (tokens, end) = lex_until_closing_delimiter(src, 0);
    if end != src.len() {
        panic!("unmatched closing delimiter at {end}");
    }
    tokens
}

fn is_ident_start(b: u8) -> bool {
    match b {
        b'a'..=b'z' => true,
        b'A'..=b'Z' => true,
        b'_' => true,
        _ => false,
    }
}

fn is_ident_continue(b: u8) -> bool {
    match b {
        b'a'..=b'z' => true,
        b'A'..=b'Z' => true,
        b'_' => true,
        b'0'..=b'9' => true,
        _ => false,
    }
}

fn is_punct(b: u8) -> bool {
    match b {
        b'.' | b':' | b';' | b'<' | b'>' | b'+' | b'-' | b'%' | b'*' | b'/'
        | b'!' | b'&' | b'|' | b'=' | b'^' | b',' => true,
        _ => false,
    }
}

fn delimiter(b: u8) -> Option<(Delimiter, u8)> {
    match b {
        b'(' => Some((Delimiter::Parenthesis, b')')),
        b'{' => Some((Delimiter::Brace, b'}')),
        b'[' => Some((Delimiter::Bracket, b']')),
        _ => None,
    }
}

fn lex_until_closing_delimiter(
    src: &'static [u8], start: usize,
) -> (Vec<TokenTree>, usize) {
    let mut tokens = vec![];
    let mut idx = start;
    let mut prev_byte_was_punct = false;
    loop {
        match src.get(idx) {
            None | Some(b']' | b'}' | b')') => break,
            Some(b'/') if src.get(idx + 1) == Some(&b'/') => {
                idx += 2;
                while src.get(idx).is_some_and(|&b| b != b'\r' && b != b'\n') {
                    idx += 1;
                }
            }
            Some(&c) if is_ident_start(c) => {
                let start = idx;
                idx += 1;
                while src.get(idx).is_some_and(|&c| is_ident_continue(c)) {
                    idx += 1;
                }
                tokens.push(TokenTree::Ident(Ident {
                    ident: std::str::from_utf8(&src[start..idx])
                        .expect("valid UTF-8 source"),
                    span: (start..idx).into(),
                }));
                prev_byte_was_punct = false;
            }
            Some(&c) if c.is_ascii_digit() => {
                // TODO: hexadecimal etc
                let start = idx;
                idx += 1;
                while src.get(idx).is_some_and(|&c| c.is_ascii_digit()) {
                    idx += 1;
                }
                if src.get(idx).is_some_and(|&c| is_ident_continue(c)) {
                    panic!("invalid integer literal at {start}..");
                }
                let s = std::str::from_utf8(&src[start..idx])
                    .expect("valid UTF-8 source");
                let value: u128 =
                    s.parse().expect("overflowing integer literal");
                tokens.push(TokenTree::Integer(Integer {
                    value,
                    span: (start..idx).into(),
                }));
                prev_byte_was_punct = false;
            }
            Some(&c) if is_punct(c) => {
                if prev_byte_was_punct {
                    if let Some(TokenTree::Punct(prev_punct)) =
                        tokens.last_mut()
                    {
                        prev_punct.joint_with_next = true;
                    }
                }
                tokens.push(TokenTree::Punct(Punct {
                    c,
                    joint_with_next: false,
                    span: (idx..idx + 1).into(),
                }));
                prev_byte_was_punct = true;
                idx += 1;
            }
            Some(&c) if c.is_ascii_whitespace() => {
                prev_byte_was_punct = false;
                idx += 1;
            }
            Some(&c @ (b'(' | b'{' | b'[')) => {
                let (delimiter, closing) = delimiter(c).unwrap();
                let (inner, end) = lex_until_closing_delimiter(src, idx + 1);
                if src.get(end).copied() != Some(closing) {
                    panic!("mismatched closing delimiter");
                }
                tokens.push(TokenTree::Group(Group {
                    delimiter,
                    inner,
                    span: (idx..end + 1).into(),
                }));
                idx = end + 1;
            }
            Some(&c) => {
                prev_byte_was_punct = false;
                panic!("invalid character: {}", std::ascii::escape_default(c));
            }
        }
    }
    (tokens, idx)
}

pub fn is_keyword(s: &str) -> bool {
    // copied from the Rust Reference for simplicity;
    // we don't use all of these
    match s {
        "as" | "break" | "const" | "continue" | "crate" | "else" | "enum"
        | "extern" | "false" | "fn" | "for" | "if" | "impl" | "in" | "let"
        | "loop" | "match" | "mod" | "move" | "mut" | "pub" | "ref"
        | "return" | "self" | "Self" | "static" | "struct" | "super"
        | "trait" | "true" | "type" | "unsafe" | "use" | "where" | "while"
        | "async" | "await" | "dyn" | "abstract" | "become" | "box" | "do"
        | "final" | "macro" | "override" | "priv" | "typeof" | "unsized"
        | "virtual" | "yield" | "try" | "union" | "_" => true,
        _ => false,
    }
}
