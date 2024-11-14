//! Error reporting data structures and miette integration.

use core::iter::once;

use crate::{Pointer, PointerBuf};

/// Implemented by errors which can be converted into a [`Report`].
pub trait IntoReport: Sized {
    /// The value which caused the error.
    ///
    /// Depending on the error, this may be either [`String`] or [`PointerBuf`]
    type Subject;
    /// Convert the error into a [`Report`].
    fn into_report(self, value: Self::Subject) -> Report<Self>;
}

/// An error wrapper which includes the [`String`] which failed to parse or the
/// [`PointerBuf`] being used.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Report<E> {
    /// The error which occurred.
    pub error: E,
    /// The value which caused the error.
    pub subject: Subject,
}

impl<E> Report<E> {
    /// Create a new `Report` with the given subject and error.
    pub fn new(subject: Subject, error: E) -> Self {
        Self { error, subject }
    }
}

impl<E: Reportable> Report<E> {
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
        std::fmt::Display::fmt(&self.error, f)
    }
}
impl<E> std::error::Error for Report<E> where E: std::error::Error {}

#[cfg(feature = "miette")]
impl<E> miette::Diagnostic for Report<E>
where
    E: Reportable + IntoReport + std::error::Error,
{
    fn url<'a>(&'a self) -> Option<Box<dyn core::fmt::Display + 'a>> {
        Some(Box::new(Self::url()))
    }

    fn source_code(&self) -> Option<&dyn miette::SourceCode> {
        Some(&self.subject)
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan> + '_>> {
        match &self.subject {
            Subject::String {
                string,
                offset,
                len,
            } => {
                let span = LabeledSpan::new(Some(string.to_string()), *offset, *len);
                Some(Box::new(once(span)))
            }
            Subject::PointerBuf { pointer, position } => {
                let offset = pointer.get(0..*position).unwrap().as_str().len();
                let token = pointer.get(*position).unwrap();
                let decoded = token.decoded();
                let len = decoded.len();
                let span = LabeledSpan::new(Some(decoded.to_string()), offset, len);
                Some(Box::new(once(span)))
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Subject {
    String {
        string: String,
        offset: usize,
        len: usize,
    },
    PointerBuf {
        pointer: PointerBuf,
        position: usize,
    },
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

impl Subject {
    pub(crate) fn string(value: String, offset: usize, len: usize) -> Self {
        Self::String {
            string: value,
            offset,
            len,
        }
    }
    pub(crate) fn pointer(value: PointerBuf, position: usize) -> Self {
        Self::PointerBuf {
            pointer: value,
            position,
        }
    }
    pub fn as_str(&self) -> &str {
        match self {
            Self::String { string: value, .. } => value,
            Self::PointerBuf { pointer: value, .. } => value.as_str(),
        }
    }
}
impl PartialEq<str> for Subject {
    fn eq(&self, other: &str) -> bool {
        match self {
            Self::String { string: value, .. } => value == other,
            Self::PointerBuf { pointer: value, .. } => value.as_str() == other,
        }
    }
}
impl PartialEq<Pointer> for Subject {
    fn eq(&self, other: &Pointer) -> bool {
        match self {
            Self::String { string: value, .. } => other.as_str() == value,
            Self::PointerBuf { pointer: value, .. } => value == other,
        }
    }
}
impl From<&str> for Subject {
    fn from(value: &str) -> Self {
        Self::String {
            string: value.to_string(),
            offset: 0,
            len: value.len(),
        }
    }
}

pub trait ReportErr<T> {
    type Error: IntoReport;
    #[allow(clippy::missing_errors_doc)]
    fn report_err(
        self,
        value: impl Into<<Self::Error as IntoReport>::Subject>,
    ) -> Result<T, Report<Self::Error>>;
}

impl<T, E> ReportErr<T> for Result<T, E>
where
    E: IntoReport,
{
    type Error = E;

    fn report_err(
        self,
        value: impl Into<<Self::Error as IntoReport>::Subject>,
    ) -> Result<T, Report<Self::Error>> {
        self.map_err(|error| error.into_report(value.into()))
    }
}
pub trait Reportable {
    /// The docs.rs URL for this error
    fn url() -> &'static str;
}

macro_rules! reportable {
    (enum $type:ident) => {
        crate::report::reportable!("enum", "", $type);
    };
    (struct $type:ident) => {
        crate::report::reportable!("struct", "", $type);
    };
    (enum $mod:ident::$type:ident) => {
        crate::report::reportable!("enum", concat!("/", stringify!($mod)), $type);
    };
    (struct $mod:ident::$type:ident) => {
        crate::report::reportable!("struct", concat!("/", stringify!($mod)), $type);
    };
    ($kind:literal, $mod:expr, $type:ident) => {
        impl $type {
            #[doc = "The docs.rs URL for this error"]
            pub const fn url() -> &'static str {
                // https://docs.rs/jsonptr/{VERSION}/jsonptr{}/{}.{}.html
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
        impl crate::report::Reportable for $type {
            fn url() -> &'static str {
                $type::url()
            }
        }
    };
}

use miette::LabeledSpan;
pub(crate) use reportable;

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
        use miette::Diagnostic;
        use serde_json::json;
        let ptr = PointerBuf::parse("/3").unwrap();
        let mut value = json!(["baz"]);
        let error = ptr.assign(&mut value, json!("qux")).unwrap_err();
        let report = error.into_report(ptr);
        println!("{report}");
    }
}
