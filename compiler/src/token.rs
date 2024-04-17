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

    pub(crate) fn span(&self) -> Option<Span> {
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

#[derive(Debug, Clone, Copy)]
pub struct Ident {
    pub ident: &'static str,
    pub span: Option<Span>,
}

impl Ident {
    pub fn new_unspanned(ident: &'static str) -> Self {
        Self { ident, span: None }
    }
}

impl PartialEq for Ident {
    fn eq(&self, other: &Self) -> bool {
        self.ident == other.ident
    }
}

impl Eq for Ident {}

impl PartialOrd for Ident {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.ident.partial_cmp(&other.ident)
    }
}

impl Ord for Ident {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.ident.cmp(other.ident)
    }
}

impl std::hash::Hash for Ident {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.ident.hash(state);
    }
}

#[derive(Debug, Clone)]
pub struct Group {
    pub delimiter: Delimiter,
    pub inner: Vec<TokenTree>,
    pub span: Option<Span>,
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
    pub span: Option<Span>,
}
impl Integer {
    pub fn new_unspanned(value: u128) -> Integer {
        Self { value, span: None }
    }
}

#[derive(Clone, Copy)]
pub struct Punct {
    pub c: u8,
    pub joint_with_next: bool,
    pub span: Option<Span>,
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
