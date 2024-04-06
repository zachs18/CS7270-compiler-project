use crate::span::Span;

#[derive(Clone)]
pub enum TokenTree {
    Ident(Ident),
    Group(Group),
    Integer(Integer),
    Punct(Punct),
}

impl TokenTree {
    pub fn as_ident(&self) -> Option<&Ident> {
        match self {
            TokenTree::Ident(ident) => Some(ident),
            _ => None,
        }
    }

    pub(crate) fn as_group(&self) -> Option<&Group> {
        match self {
            TokenTree::Group(group) => Some(group),
            _ => None,
        }
    }

    pub(crate) fn as_punct(&self) -> Option<&Punct> {
        match self {
            TokenTree::Punct(punct) => Some(punct),
            _ => None,
        }
    }

    pub(crate) fn span(&self) -> Span {
        match self {
            TokenTree::Ident(ident) => ident.span,
            TokenTree::Group(group) => group.span,
            TokenTree::Integer(integer) => integer.span,
            TokenTree::Punct(punct) => punct.span,
        }
    }
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

#[derive(Debug, Clone)]
pub struct Ident {
    pub ident: String,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Group {
    pub delimiter: Delimiter,
    pub inner: Vec<TokenTree>,
    pub span: Span,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum Delimiter {
    Parenthesis,
    Brace,
    Bracket,
}

impl Delimiter {
    pub fn opening(self) -> char {
        match self {
            Delimiter::Parenthesis => '(',
            Delimiter::Brace => '{',
            Delimiter::Bracket => '[',
        }
    }

    pub fn closing(self) -> char {
        match self {
            Delimiter::Parenthesis => ')',
            Delimiter::Brace => '}',
            Delimiter::Bracket => ']',
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Integer {
    pub value: u128,
    pub span: Span,
}

#[derive(Clone, Copy)]
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
