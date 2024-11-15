//! Error reporting data structures and miette integration.

use crate::{Pointer, PointerBuf, Token};

/// Implemented by errors which can be converted into a [`Report`].
pub trait Diagnostic: Sized {
    /// The value which caused the error.
    type Subject;

    /// Convert the error into a [`Report`].
    fn into_report(self, subject: Self::Subject) -> Report<Self>;

    /// The docs.rs URL for this error
    fn url() -> &'static str;

    /// Returns the label for the given [`Subject`] if applicable.
    fn labels(&self, subject: &Subject) -> Option<Box<dyn Iterator<Item = Label>>>;
}

/// A label for a span within a json pointer or malformed string.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Label {
    /// The text for the label.
    pub text: String,
    /// The offset of the label.
    pub offset: usize,
    /// The length of the label.
    pub len: usize,
}

impl Label {
    #[cfg(feature = "miette")]
    pub fn into_miette_labeled_span(self) -> miette::LabeledSpan {
        miette::LabeledSpan::new(Some(self.text), self.offset, self.len)
    }
}

#[cfg(feature = "miette")]
impl From<Label> for miette::LabeledSpan {
    fn from(label: Label) -> Self {
        label.into_miette_labeled_span()
    }
}

/// An error wrapper which includes the [`String`] which failed to parse or the
/// [`PointerBuf`] being used.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Report<E> {
    /// The error which occurred.
    source: E,
    /// The value which caused the error.
    subject: Subject,
}

impl<E: Diagnostic> Report<E> {
    /// Create a new `Report` with the given subject and error.
    pub fn new(error: E, subject: Subject) -> Self {
        Self {
            source: error,
            subject,
        }
    }

    pub fn labels(&self) -> Option<Box<dyn Iterator<Item = Label>>> {
        self.source.labels(&self.subject)
    }

    pub fn subject(&self) -> &Subject {
        &self.subject
    }

    pub fn source(&self) -> &E {
        &self.source
    }
}

impl<E: Diagnostic> Report<E> {
    /// The docs.rs URL for the error of this [`Report`].
    fn url() -> &'static str {
        E::url()
    }
}

impl<E> std::fmt::Display for Report<E>
where
    E: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.source, f)
    }
}

impl<E> std::error::Error for Report<E> where E: std::error::Error {}

#[cfg(feature = "miette")]
impl<E> miette::Diagnostic for Report<E>
where
    E: Diagnostic + std::error::Error,
{
    fn url<'a>(&'a self) -> Option<Box<dyn core::fmt::Display + 'a>> {
        Some(Box::new(Self::url()))
    }

    fn source_code(&self) -> Option<&dyn miette::SourceCode> {
        Some(&self.subject)
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = miette::LabeledSpan> + '_>> {
        Some(Box::new(self.labels()?.map(Into::into)))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Subject {
    String(String),
    PointerBuf(PointerBuf),
}

impl Subject {
    pub fn as_str(&self) -> &str {
        match self {
            Self::String(s) => s.as_str(),
            Self::PointerBuf(p) => p.as_str(),
        }
    }
    /// Returns a reference to the string if this `Subject` is a `String`.
    /// Returns `None` if  is a `PointerBuf`.
    pub fn as_string(&self) -> Option<&String> {
        match self {
            Self::String(s) => Some(s),
            Self::PointerBuf(_) => None,
        }
    }

    /// Returns a reference to the [`PointerBuf`] if this `Subject` is a `PointerBuf`.
    pub fn as_pointer_buf(&self) -> Option<&PointerBuf> {
        match self {
            Self::PointerBuf(p) => Some(p),
            Self::String(_) => None,
        }
    }

    /// If this `Source` is a `PointerBuf`, returns the offset of the given
    /// token position (index).
    pub fn offset_for_position(&self, position: usize) -> Option<usize> {
        let ptr = self.as_pointer_buf()?;
        ptr.get(0..position).map(|s| s.as_str().len())
    }

    /// If this `Source` is a `PointerBuf`, returns the token at
    /// the given position (index), if it exists.
    pub fn token(&self, position: usize) -> Option<Token> {
        self.as_pointer_buf().and_then(|ptr| ptr.get(position))
    }

    /// Returns `true` if the subject is [`String`].
    ///
    /// [`String`]: Subject::String
    #[must_use]
    pub fn is_string(&self) -> bool {
        matches!(self, Self::String(..))
    }

    /// Returns `true` if the subject is [`PointerBuf`].
    ///
    /// [`PointerBuf`]: Subject::PointerBuf
    #[must_use]
    pub fn is_pointer_buf(&self) -> bool {
        matches!(self, Self::PointerBuf(..))
    }

    /// ## Errors
    /// Returns `Self` if the [`Subject`] is not a `String`.
    pub fn try_into_string(self) -> Result<String, Self> {
        if let Self::String(v) = self {
            Ok(v)
        } else {
            Err(self)
        }
    }
    /// ## Errors
    /// Returns `Self` if the [`Subject`] is not a `PointerBuf`.
    pub fn try_into_pointer_buf(self) -> Result<PointerBuf, Self> {
        if let Self::PointerBuf(v) = self {
            Ok(v)
        } else {
            Err(self)
        }
    }
}

#[cfg(feature = "miette")]
impl miette::SourceCode for Subject {
    fn read_span<'a>(
        &'a self,
        span: &miette::SourceSpan,
        context_lines_before: usize,
        context_lines_after: usize,
    ) -> Result<Box<dyn miette::SpanContents<'a> + 'a>, miette::MietteError> {
        self.as_str()
            .read_span(span, context_lines_before, context_lines_after)
    }
}

impl PartialEq<str> for Subject {
    fn eq(&self, other: &str) -> bool {
        match self {
            Self::String(this) => this == other,
            Self::PointerBuf(this) => this.as_str() == other,
        }
    }
}
impl PartialEq<Subject> for str {
    fn eq(&self, other: &Subject) -> bool {
        other == self
    }
}
impl PartialEq<Pointer> for Subject {
    fn eq(&self, other: &Pointer) -> bool {
        self == other.as_str()
    }
}
impl PartialEq<Subject> for String {
    fn eq(&self, other: &Subject) -> bool {
        self == other.as_str()
    }
}
impl PartialEq<String> for Subject {
    fn eq(&self, other: &String) -> bool {
        self == other.as_str()
    }
}
impl PartialEq<Subject> for Pointer {
    fn eq(&self, other: &Subject) -> bool {
        self.as_str() == other
    }
}
impl From<&str> for Subject {
    fn from(value: &str) -> Self {
        Self::String(value.to_string())
    }
}
impl From<&Pointer> for Subject {
    fn from(value: &Pointer) -> Self {
        Self::PointerBuf(value.to_buf())
    }
}
impl From<PointerBuf> for Subject {
    fn from(value: PointerBuf) -> Self {
        Self::PointerBuf(value)
    }
}
impl From<String> for Subject {
    fn from(value: String) -> Self {
        Self::String(value)
    }
}

pub trait Diagnose<T> {
    type Error: Diagnostic;

    #[allow(clippy::missing_errors_doc)]
    fn diagnose(
        self,
        subject: impl Into<<Self::Error as Diagnostic>::Subject>,
    ) -> Result<T, Report<Self::Error>>;

    #[allow(clippy::missing_errors_doc)]
    fn diagnose_with<F, S>(self, f: F) -> Result<T, Report<Self::Error>>
    where
        F: FnOnce() -> S,
        S: Into<<Self::Error as Diagnostic>::Subject>;
}

impl<T, E> Diagnose<T> for Result<T, E>
where
    E: Diagnostic,
{
    type Error = E;

    fn diagnose(
        self,
        subject: impl Into<<Self::Error as Diagnostic>::Subject>,
    ) -> Result<T, Report<Self::Error>> {
        self.map_err(|error| error.into_report(subject.into()))
    }

    fn diagnose_with<F, S>(self, f: F) -> Result<T, Report<Self::Error>>
    where
        F: FnOnce() -> S,
        S: Into<<Self::Error as Diagnostic>::Subject>,
    {
        self.diagnose(f())
    }
}

macro_rules! impl_diagnostic_url {
    (enum $type:ident) => {
        crate::report::impl_diagnostic_url!("enum", "", $type);
    };
    (struct $type:ident) => {
        crate::report::impl_diagnostic_url!("struct", "", $type);
    };
    (enum $mod:ident::$type:ident) => {
        crate::report::impl_diagnostic_url!("enum", concat!("/", stringify!($mod)), $type);
    };
    (struct $mod:ident::$type:ident) => {
        crate::report::impl_diagnostic_url!("struct", concat!("/", stringify!($mod)), $type);
    };
    ($kind:literal, $mod:expr, $type:ident) => {
        impl $type {
            #[doc = "The docs.rs URL for this error"]
            pub const fn url() -> &'static str {
                concat!(
                    "https://docs.rs/jsonptr/",
                    env!("CARGO_PKG_VERSION"),
                    "/jsonptr",
                    $mod,
                    "/",
                    $kind,
                    ".",
                    stringify!($type),
                    ".html",
                )
            }
        }
    };
}
pub(crate) use impl_diagnostic_url;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg(all(
        feature = "assign",
        feature = "miette",
        feature = "serde",
        feature = "json"
    ))]
    fn assign_error() {
        use crate::assign::Error;

        let ptr = PointerBuf::parse("/foo/bar/invalid/cannot/reach").unwrap();
        let mut v = serde_json::json!({"foo": {"bar": ["0"]}});
        let report = ptr.assign(&mut v, "qux").diagnose(ptr).unwrap_err();
        println!("{:?}", miette::Report::from(report));

        let ptr = PointerBuf::parse("/foo/bar/3/cannot/reach").unwrap();
        let report = ptr.assign(&mut v, "qux").diagnose(ptr).unwrap_err();
        println!("{:?}", miette::Report::from(report));
    }

    #[test]
    fn parse_error() {
        let invalid = "/foo/bar/invalid~3~encoding/cannot/reach";
        let report = Pointer::parse(invalid).diagnose(invalid).unwrap_err();

        println!("{:?}", miette::Report::from(report));

        // TODO: impl `miette::Diagnostic` for `RichParseError`
        let report = PointerBuf::parse("/foo/bar/invalid~3~encoding/cannot/reach")
            .diagnose(())
            .unwrap_err();

        let report = miette::Report::from(report);
        println!("{report:?}");
    }
}
