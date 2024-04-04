use crate::span::Span;

pub enum TokenTree {
    Ident(Ident),
    Group(Group),
    Integer(Integer),
    Punct(Punct),
}

impl std::fmt::Debug for TokenTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Ident(arg0) => arg0.fmt(f),
            Self::Group(arg0) => arg0.fmt(f),
            Self::Integer(arg0) => arg0.fmt(f),
            Self::Punct(arg0) => arg0.fmt(f),
        }
    }
}

#[derive(Debug)]
pub struct Ident {
    pub ident: String,
    pub span: Span,
}

#[derive(Debug)]
pub struct Group {
    pub delimiter: Delimiter,
    pub inner: Vec<TokenTree>,
    pub span: Span,
}

#[derive(Debug)]
pub enum Delimiter {
    Parenthesis,
    Brace,
    Bracket,
}

#[derive(Debug)]
pub struct Integer {
    pub value: u128,
    pub span: Span,
}

pub struct Punct {
    pub c: u8,
    pub joint_with_next: bool,
    pub span: Span,
}

impl std::fmt::Debug for Punct {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Punct")
            .field("c", &format_args!("b'{}'", self.c.escape_ascii()))
            .field("joint_with_next", &self.joint_with_next)
            .field("span", &self.span)
            .finish()
    }
}
