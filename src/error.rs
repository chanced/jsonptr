use core::iter::once;

use crate::Token;

/// Data structures utilized in errors

/// Represents a span of text within a JSON Pointer
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub offset: usize,
    pub len: usize,
}

impl Span {
    pub fn for_token(token: &Token, offset: usize) -> Self {
        Self {
            offset,
            len: token.encoded().len(),
        }
    }
}

/// An error that pertains to a specific span of text within a JSON Pointer
#[derive(Debug, PartialEq, Eq)]
pub struct Spanned<E> {
    span: Span,
    source: E,
}

impl<E> Spanned<E> {
    pub const fn new(span: Span, source: E) -> Self {
        Self { span, source }
    }

    pub const fn span(&self) -> Span {
        self.span
    }

    pub const fn offset(&self) -> usize {
        self.span.offset
    }

    pub const fn len(&self) -> usize {
        self.span.len
    }

    pub const fn is_empty(&self) -> bool {
        self.span.len == 0
    }

    pub const fn source(&self) -> &E {
        &self.source
    }
}

impl<E: core::fmt::Display> core::fmt::Display for Spanned<E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.source.fmt(f)
    }
}

#[cfg(feature = "std")]
impl<E> std::error::Error for Spanned<E>
where
    E: std::error::Error + 'static,
{
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        Some(&self.source)
    }
}

#[cfg(feature = "miette")]
impl<E> miette::Diagnostic for Spanned<E>
where
    E: 'static + miette::Diagnostic,
{
    fn code<'a>(&'a self) -> Option<Box<dyn core::fmt::Display + 'a>> {
        self.source.code()
    }

    fn severity(&self) -> Option<miette::Severity> {
        self.source.severity()
    }

    fn help<'a>(&'a self) -> Option<Box<dyn core::fmt::Display + 'a>> {
        self.source.help()
    }

    fn url<'a>(&'a self) -> Option<Box<dyn core::fmt::Display + 'a>> {
        self.source.url()
    }

    fn source_code(&self) -> Option<&dyn miette::SourceCode> {
        self.source.source_code()
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = miette::LabeledSpan> + '_>> {
        Some(Box::new(once(miette::LabeledSpan::new(
            None,
            self.offset(),
            self.len(),
        ))))
    }

    fn related<'a>(&'a self) -> Option<Box<dyn Iterator<Item = &'a dyn miette::Diagnostic> + 'a>> {
        self.source.related()
    }

    fn diagnostic_source(&self) -> Option<&dyn miette::Diagnostic> {
        self.source.diagnostic_source()
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Positioned<E> {
    position: usize,
    source: Spanned<E>,
}

impl<E> Positioned<E> {
    pub const fn new(source: E, position: usize, span: Span) -> Self {
        Self {
            position,
            source: Spanned::new(span, source),
        }
    }

    pub const fn position(&self) -> usize {
        self.position
    }

    pub const fn span(&self) -> Span {
        self.source.span
    }

    pub const fn offset(&self) -> usize {
        self.source.offset()
    }

    pub const fn len(&self) -> usize {
        self.source.len()
    }

    pub const fn is_empty(&self) -> bool {
        self.source.is_empty()
    }

    pub const fn source(&self) -> &Spanned<E> {
        &self.source
    }
}

impl<E: core::fmt::Display> core::fmt::Display for Positioned<E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.source.fmt(f)
    }
}

#[cfg(feature = "std")]
impl<E> std::error::Error for Positioned<E>
where
    E: std::error::Error + 'static,
{
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        Some(&self.source)
    }
}

#[cfg(feature = "miette")]
impl<E> miette::Diagnostic for Positioned<E>
where
    E: 'static + miette::Diagnostic,
{
    fn code<'a>(&'a self) -> Option<Box<dyn core::fmt::Display + 'a>> {
        self.source.code()
    }

    fn severity(&self) -> Option<miette::Severity> {
        self.source.severity()
    }

    fn help<'a>(&'a self) -> Option<Box<dyn core::fmt::Display + 'a>> {
        self.source.help()
    }

    fn url<'a>(&'a self) -> Option<Box<dyn core::fmt::Display + 'a>> {
        self.source.url()
    }

    fn source_code(&self) -> Option<&dyn miette::SourceCode> {
        self.source.source_code()
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = miette::LabeledSpan> + '_>> {
        self.source.labels()
    }

    fn related<'a>(&'a self) -> Option<Box<dyn Iterator<Item = &'a dyn miette::Diagnostic> + 'a>> {
        self.source.related()
    }

    fn diagnostic_source(&self) -> Option<&dyn miette::Diagnostic> {
        self.source.diagnostic_source()
    }
}
