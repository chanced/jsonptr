use core::{fmt, iter::once, ops::Deref};

use crate::{pointer::Validator, report::Label, EncodingError};

/// The structure of a `ParseError`.
pub trait Structure: core::fmt::Debug {
    type Cause: Causative;
    type Subject: core::fmt::Debug + for<'a> From<&'a str> + From<String>;
}

/// [`Structure`] for a [`ParseError`] which contains the first encountered [`Cause`]
/// but does not contain the input string as `subject`.
#[derive(Debug)]
pub struct WithoutInput;
impl Structure for WithoutInput {
    type Cause = Cause;
    type Subject = Empty;
}

/// [`Structure`] for a [`ParseError`] which contains the first encountered
/// [`Cause`] along with the input string as `subject`.
#[derive(Debug)]
pub struct WithInput;
impl Structure for WithInput {
    type Cause = Cause;
    type Subject = String;
}

/// [`Structure`] for a [`ParseError`] which contains all encountered [`Cause`]s
/// along with the input string as `subject`.
#[derive(Debug)]
pub struct Complete;
impl Structure for Complete {
    type Cause = Causes;
    type Subject = String;
}

#[cfg(feature = "miette")]
/// A cause of a `ParseError`.
pub trait Causative:
    PartialEq + Sized + std::error::Error + fmt::Display + fmt::Debug + miette::Diagnostic
{
    fn try_new(cause: impl Iterator<Item = Cause>) -> Option<Self>;
    fn labels(&self, value: &str) -> impl Iterator<Item = Label>;
    fn first(&self) -> &Cause;
}

#[cfg(all(feature = "std", not(feature = "miette")))]
/// A cause of a `ParseError`.
pub trait Causative:
    Sized + std::error::Error + fmt::Display + fmt::Debug + miette::Diagnostic
{
    fn try_new(cause: impl Iterator<Item = Cause>) -> Option<Self>;
    fn labels(&self, value: &str) -> impl Iterator<Item = Label>;
    fn first(&self) -> &Cause;
}

#[cfg(not(feature = "miette"))]
/// A cause of a `ParseError`.
pub trait Causative: Sized + fmt::Display + fmt::Debug {
    fn try_new(cause: impl Iterator<Item = Cause>) -> Option<Self>;
    fn labels(&self, value: &str) -> impl Iterator<Item = Label>;
    fn first(&self) -> &Cause;
}

/// Cause of a [`ParseError`].
#[derive(Debug, PartialEq, Eq)]
pub enum Cause {
    /// `Pointer` did not start with a backslash (`'/'`).
    NoLeadingBackslash,

    /// `Pointer` contained invalid encoding (e.g. `~` not followed by `0` or
    /// `1`).
    InvalidEncoding {
        /// Offset of the partial pointer starting with the token that contained
        /// the invalid encoding
        offset: usize,
        /// The source `InvalidEncodingError`
        source: EncodingError,
    },
}
impl<S> From<ParseError<S>> for Cause
where
    S: Structure<Cause = Cause>,
{
    fn from(err: ParseError<S>) -> Self {
        err.cause
    }
}

impl Cause {
    fn create_labels(&self, subject: &str) -> Box<dyn Iterator<Item = Label>> {
        let offset = self.complete_offset();
        let len = self.invalid_encoding_len(subject);
        let text = match self {
            Self::NoLeadingBackslash { .. } => "must start with a slash ('/')",
            Self::InvalidEncoding { .. } => "'~' must be followed by '0' or '1'",
        }
        .to_string();
        let text = Some(text);
        Box::new(once(Label { text, offset, len }))
    }
    /// Returns `true` if this error is `NoLeadingBackslash`
    pub fn is_no_leading_backslash(&self) -> bool {
        matches!(self, Cause::NoLeadingBackslash { .. })
    }

    /// Returns `true` if this error is `InvalidEncoding`    
    pub fn is_invalid_encoding(&self) -> bool {
        matches!(self, Cause::InvalidEncoding { .. })
    }

    pub fn invalid_encoding_len(&self, subject: &str) -> usize {
        match self {
            Self::NoLeadingBackslash => 0,
            Self::InvalidEncoding { offset, .. } => {
                if *offset < subject.len() - 1 {
                    2
                } else {
                    1
                }
            }
        }
    }
    /// Offset of the partial pointer starting with the token which caused the error.
    ///
    /// ```text
    /// "/foo/invalid~tilde/invalid"
    ///      ↑
    /// ```
    ///
    /// ```
    /// # use jsonptr::PointerBuf;
    /// let err = PointerBuf::parse("/foo/invalid~tilde/invalid").unwrap_err();
    /// assert_eq!(err.pointer_offset(), 4)
    /// ```
    pub fn pointer_offset(&self) -> usize {
        match self {
            Cause::NoLeadingBackslash { .. } => 0,
            Cause::InvalidEncoding { offset, .. } => *offset,
        }
    }

    /// Offset of the character index from within the first token of
    /// [`Self::pointer_offset`])
    ///
    /// ```text
    /// "/foo/invalid~tilde/invalid"
    ///              ↑
    ///              8
    /// ```
    /// ```
    /// # use jsonptr::PointerBuf;
    /// let err = PointerBuf::parse("/foo/invalid~tilde/invalid").unwrap_err();
    /// assert_eq!(err.source_offset(), 8)
    /// ```
    pub fn source_offset(&self) -> usize {
        match &self {
            Cause::NoLeadingBackslash { .. } => 0,
            Cause::InvalidEncoding { source, .. } => source.offset,
        }
    }

    /// Offset of the first invalid encoding from within the pointer.
    /// ```text
    /// "/foo/invalid~tilde/invalid"
    ///              ↑
    ///             12
    /// ```
    /// ```
    /// use jsonptr::PointerBuf;
    /// let err = PointerBuf::parse("/foo/invalid~tilde/invalid").unwrap_err();
    /// assert_eq!(err.complete_offset(), 12)
    /// ```
    pub fn complete_offset(&self) -> usize {
        self.source_offset() + self.pointer_offset()
    }
}
#[cfg(feature = "std")]
impl std::error::Error for Cause {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Cause::InvalidEncoding { source, .. } => Some(source),
            Cause::NoLeadingBackslash => None,
        }
    }
}

#[cfg(feature = "miette")]
impl miette::Diagnostic for Cause {
    fn code<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        None
    }

    fn severity(&self) -> Option<miette::Severity> {
        None
    }

    fn help<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        None
    }

    fn url<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        None
    }

    fn source_code(&self) -> Option<&dyn miette::SourceCode> {
        None
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = miette::LabeledSpan> + '_>> {
        None
    }

    fn related<'a>(&'a self) -> Option<Box<dyn Iterator<Item = &'a dyn miette::Diagnostic> + 'a>> {
        None
    }

    fn diagnostic_source(&self) -> Option<&dyn miette::Diagnostic> {
        None
    }
}

impl Causative for Cause {
    fn try_new(mut iter: impl Iterator<Item = Cause>) -> Option<Self> {
        iter.next()
    }

    fn labels(&self, subject: &str) -> impl Iterator<Item = Label> {
        self.create_labels(subject)
    }

    fn first(&self) -> &Cause {
        self
    }
}

impl fmt::Display for Cause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoLeadingBackslash { .. } => {
                write!(f, "missing leading slash ('/') for non-empty pointer")
            }
            Self::InvalidEncoding { offset, .. } => {
                write!(
                    f,
                    "token starting at offset {offset} contains invalid encoding"
                )
            }
        }
    }
}

impl<S> PartialEq<ParseError<S>> for Cause
where
    S: Structure<Cause = Cause>,
{
    fn eq(&self, other: &ParseError<S>) -> bool {
        *self == other.cause
    }
}

#[derive(Debug, PartialEq)]
pub struct Causes(Box<[Cause]>);
impl Causes {
    pub fn new(iter: impl IntoIterator<Item = Cause>) -> Option<Self> {
        let causes: Box<[Cause]> = iter.into_iter().collect();
        if causes.is_empty() {
            None
        } else {
            Some(Causes(causes))
        }
    }
}

#[cfg(feature = "miette")]
impl miette::Diagnostic for Causes {
    fn labels(&self) -> Option<Box<dyn Iterator<Item = miette::LabeledSpan> + '_>> {
        Some(Box::new(
            self.iter().filter_map(miette::Diagnostic::labels).flatten(),
        ))
    }

    fn related<'a>(&'a self) -> Option<Box<dyn Iterator<Item = &'a dyn miette::Diagnostic> + 'a>> {
        Some(Box::new(
            self.iter().map(|cause| cause as &dyn miette::Diagnostic),
        ))
    }

    fn diagnostic_source(&self) -> Option<&dyn miette::Diagnostic> {
        None
    }
}

impl std::error::Error for Causes {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        self[0].source()
    }
}

impl fmt::Display for Causes {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "failed to parse json schema due to {} encoding errors",
            self.0.len()
        )
    }
}

impl Deref for Causes {
    type Target = [Cause];
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Causative for Causes {
    fn try_new(cause: impl Iterator<Item = Cause>) -> Option<Self> {
        let v: Box<[Cause]> = cause.collect();
        if v.is_empty() {
            None
        } else {
            Some(Self(v))
        }
    }

    fn labels(&self, value: &str) -> impl Iterator<Item = Label> {
        self.0.iter().flat_map(|cause| cause.labels(value))
    }

    fn first(&self) -> &Cause {
        &self[0]
    }
}

/// An empty type used as a `subject` in a `ParseError` to indicate that the
/// error does not contain the subject.
#[derive(Debug, PartialEq, Eq)]
pub struct Empty;
impl From<&str> for Empty {
    fn from(_: &str) -> Self {
        Empty
    }
}
impl From<String> for Empty {
    fn from(_: String) -> Self {
        Empty
    }
}
impl PartialEq<String> for Empty {
    fn eq(&self, _: &String) -> bool {
        true
    }
}
impl PartialEq<str> for Empty {
    fn eq(&self, _: &str) -> bool {
        true
    }
}
impl PartialEq<&str> for Empty {
    fn eq(&self, _: &&str) -> bool {
        true
    }
}

/// Indicates that a `Pointer` was malformed and unable to be parsed.
#[derive(Debug, Eq)]
pub struct ParseError<S: Structure = WithoutInput> {
    cause: S::Cause,
    subject: S::Subject,
}
impl<S> ParseError<S>
where
    S: Structure<Cause = Cause>,
{
    /// Returns `true` if this error is `NoLeadingBackslash`
    pub fn is_no_leading_backslash(&self) -> bool {
        matches!(&self.cause, Cause::NoLeadingBackslash { .. })
    }

    /// Returns `true` if this error is `InvalidEncoding`    
    pub fn is_invalid_encoding(&self) -> bool {
        matches!(self.cause, Cause::InvalidEncoding { .. })
    }

    /// Offset of the partial pointer starting with the token which caused the error.
    ///
    /// ```text
    /// "/foo/invalid~tilde/invalid"
    ///      ↑
    /// ```
    ///
    /// ```
    /// # use jsonptr::PointerBuf;
    /// let err = PointerBuf::parse("/foo/invalid~tilde/invalid").unwrap_err();
    /// assert_eq!(err.pointer_offset(), 4)
    /// ```
    pub fn pointer_offset(&self) -> usize {
        self.cause.pointer_offset()
    }

    /// Offset of the character index from within the first token of
    /// [`Self::pointer_offset`])
    ///
    /// ```text
    /// "/foo/invalid~tilde/invalid"
    ///              ↑
    ///              8
    /// ```
    /// ```
    /// # use jsonptr::PointerBuf;
    /// let err = PointerBuf::parse("/foo/invalid~tilde/invalid").unwrap_err();
    /// assert_eq!(err.source_offset(), 8)
    /// ```
    pub fn source_offset(&self) -> usize {
        self.cause.source_offset()
    }

    /// Offset of the first invalid encoding from within the pointer.
    /// ```text
    /// "/foo/invalid~tilde/invalid"
    ///              ↑
    ///             12
    /// ```
    /// ```
    /// use jsonptr::PointerBuf;
    /// let err = PointerBuf::parse("/foo/invalid~tilde/invalid").unwrap_err();
    /// assert_eq!(err.complete_offset(), 12)
    /// ```
    pub fn complete_offset(&self) -> usize {
        self.cause.complete_offset()
    }
}

impl<S, O> PartialEq<ParseError<O>> for ParseError<S>
where
    S: Structure,
    O: Structure,
    S::Cause: PartialEq<O::Cause>,
    S::Subject: PartialEq<O::Subject>,
{
    fn eq(&self, other: &ParseError<O>) -> bool {
        todo!()
    }
}
impl<S> ParseError<S>
where
    S: Structure,
{
    pub fn new(cause: S::Cause, subject: impl Into<S::Subject>) -> Self {
        ParseError {
            cause,
            subject: subject.into(),
        }
    }
}

impl<S: Structure> ParseError<S> {
    pub fn cause(&self) -> &Cause {
        self.cause.first()
    }
}

impl<S> ParseError<S>
where
    S: Structure<Cause = Causes>,
{
    pub fn causes(&self) -> &[Cause] {
        &self.cause
    }
}
impl<S> ParseError<S>
where
    S: Structure<Subject = String>,
{
    pub fn subject(&self) -> &str {
        &self.subject
    }
}
impl<S> PartialEq<Cause> for ParseError<S>
where
    S: Structure<Cause = Cause>,
{
    fn eq(&self, other: &Cause) -> bool {
        self.cause == *other
    }
}

impl<S> fmt::Display for ParseError<S>
where
    S: Structure,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.cause, f)
    }
}
impl From<ParseError<WithInput>> for ParseError<WithoutInput> {
    fn from(err: ParseError<WithInput>) -> Self {
        ParseError {
            cause: err.cause,
            subject: Empty,
        }
    }
}

impl<S> From<Cause> for ParseError<S>
where
    S: Structure<Cause = Cause, Subject = Empty>,
{
    fn from(cause: Cause) -> Self {
        ParseError {
            cause,
            subject: Empty,
        }
    }
}

#[cfg(feature = "std")]
impl<S: Structure> std::error::Error for ParseError<S> {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        self.cause.source()
    }
}

#[cfg(feature = "miette")]
impl miette::Diagnostic for ParseError<WithInput> {
    fn code<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        None
    }

    fn severity(&self) -> Option<miette::Severity> {
        None
    }

    fn help<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        None
    }

    fn url<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        None
    }

    fn source_code(&self) -> Option<&dyn miette::SourceCode> {
        Some(&self.subject)
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = miette::LabeledSpan> + '_>> {
        Some(Box::new(Causative::labels(&self.cause, &self.subject).map(
            |label| miette::LabeledSpan::new(label.text, label.offset, label.len),
        )))
    }

    fn related<'a>(&'a self) -> Option<Box<dyn Iterator<Item = &'a dyn miette::Diagnostic> + 'a>> {
        None
    }

    fn diagnostic_source(&self) -> Option<&dyn miette::Diagnostic> {
        None
    }
}

#[cfg(feature = "miette")]
impl miette::Diagnostic for ParseError<Complete> {
    fn code<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        None
    }

    fn severity(&self) -> Option<miette::Severity> {
        None
    }

    fn help<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        None
    }

    fn url<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        None
    }

    fn source_code(&self) -> Option<&dyn miette::SourceCode> {
        Some(&self.subject)
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = miette::LabeledSpan> + '_>> {
        Some(Box::new(Causative::labels(&self.cause, &self.subject).map(
            |label| miette::LabeledSpan::new(label.text, label.offset, label.len),
        )))
    }

    fn related<'a>(&'a self) -> Option<Box<dyn Iterator<Item = &'a dyn miette::Diagnostic> + 'a>> {
        Some(Box::new(
            self.cause
                .iter()
                .map(|cause| cause as &dyn miette::Diagnostic),
        ))
    }

    fn diagnostic_source(&self) -> Option<&dyn miette::Diagnostic> {
        None
    }
}

impl From<ParseError<WithInput>> for ParseError<Complete> {
    fn from(err: ParseError<WithInput>) -> Self {
        let causes: Causes = Validator::validate(&err.subject).unwrap_err();
        ParseError {
            cause: causes,
            subject: err.subject,
        }
    }
}
