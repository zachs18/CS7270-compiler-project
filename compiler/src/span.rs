use std::ops::Range;

pub struct Span {
    span: copy_range::CopyRange<usize>,
}

impl From<Range<usize>> for Span {
    fn from(range: Range<usize>) -> Self {
        Self { span: range.into() }
    }
}

impl std::fmt::Debug for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}..{}", self.span.start, self.span.end)
    }
}
