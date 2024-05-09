use crate::span::Span;

#[derive(Clone)]
pub enum TokenTree {
    Ident(Ident),
    Group(Group),
    Integer(Integer),
    Punct(Punct),
    StringLiteral(StringLiteral),
    Label(Label),
}

impl TokenTree {
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
            TokenTree::StringLiteral(string) => string.span,
            TokenTree::Label(label) => Some(label.span),
        }
    }
}

impl std::fmt::Debug for TokenTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TokenTree::Ident(arg0) => arg0.fmt(f),
            TokenTree::Group(arg0) => arg0.fmt(f),
            TokenTree::Integer(arg0) => arg0.fmt(f),
            TokenTree::Punct(arg0) => arg0.fmt(f),
            TokenTree::StringLiteral(arg0) => arg0.fmt(f),
            TokenTree::Label(arg0) => arg0.fmt(f),
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
        Some(self.cmp(other))
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

#[derive(Debug, Clone, Copy)]
pub struct Label {
    pub label: &'static str,
    pub span: Span,
}

impl PartialEq for Label {
    fn eq(&self, other: &Self) -> bool {
        self.label == other.label
    }
}

impl Eq for Label {}

impl PartialOrd for Label {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Label {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.label.cmp(other.label)
    }
}

impl std::hash::Hash for Label {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.label.hash(state);
    }
}

#[derive(Debug, Clone)]
pub struct Group {
    pub delimiter: Delimiter,
    pub inner: Vec<TokenTree>,
    pub span: Option<Span>,
}

#[derive(Debug, Clone, Copy)]
pub struct StringLiteral {
    /// NUL-terminated
    pub data: &'static [u8],
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
