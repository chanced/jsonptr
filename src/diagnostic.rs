//! Error reporting data structures and miette integration.

use core::{convert::Infallible, fmt, ops::Deref};
use std::sync::OnceLock;

/// Implemented by errors which can be converted into a [`Report`].
pub trait Diagnostic: Sized {
    /// The value which caused the error.
    type Subject: Deref;

    /// Optional type of related errors for miette reporting.
    ///
    /// This is required as this trait is not object safe. Implementations which
    /// do not have related errors should use
    /// [`Infallible`](core::convert::Infallible) and simply not implement
    /// `related`.
    type Related;

    /// Combine the error with its subject to generate a [`Report`].
    fn into_report(self, subject: impl Into<Self::Subject>) -> Report<Self> {
        Report::new(self, subject.into())
    }

    /// The docs.rs URL for this error
    fn url() -> &'static str;

    /// Returns the label for the given [`Subject`] if applicable.
    fn labels(&self, subject: &Self::Subject) -> Option<Box<dyn Iterator<Item = Label>>>;

    /// Returns the related errors if applicable.
    fn related(&self, subject: &Self::Subject) -> Vec<Self::Related> {
        _ = subject;
        vec![]
    }
}
impl Diagnostic for () {
    type Subject = String;
    type Related = ();

    fn url() -> &'static str {
        ""
    }

    fn labels(&self, _: &Self::Subject) -> Option<Box<dyn Iterator<Item = Label>>> {
        None
    }
}

impl Diagnostic for Infallible {
    type Subject = String;
    type Related = ();

    fn url() -> &'static str {
        "https://doc.rust-lang.org/std/convert/enum.Infallible.html"
    }

    fn labels(&self, _: &Self::Subject) -> Option<Box<dyn Iterator<Item = Label>>> {
        None
    }
}

/// A label for a span within a json pointer or malformed string.
///
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Label {
    text: String,
    offset: usize,
    len: usize,
}

impl Label {
    /// Creates a new instance of a [`Label`] from its parts
    pub fn new(text: String, offset: usize, len: usize) -> Self {
        Self { text, offset, len }
    }
}

#[cfg(feature = "miette")]
impl From<Label> for miette::LabeledSpan {
    fn from(value: Label) -> Self {
        miette::LabeledSpan::new(Some(value.text), value.offset, value.len)
    }
}

/// An error wrapper which includes the subject of the failure.
#[derive(Debug, Clone)]
pub struct Report<D: Diagnostic> {
    source: D,
    subject: D::Subject,
    related: OnceLock<Vec<D::Related>>,
}

impl<D: Diagnostic> Report<D> {
    fn new(source: D, subject: D::Subject) -> Self {
        Self {
            source,
            subject,
            related: OnceLock::new(),
        }
    }

    /// The value which caused the error.
    pub fn subject(&self) -> &<D::Subject as Deref>::Target {
        &self.subject
    }

    /// The error which occurred.
    pub fn original(&self) -> &D {
        &self.source
    }

    /// The original parts of the [`Report`].
    pub fn decompose(self) -> (D, D::Subject) {
        (self.source, self.subject)
    }

    pub fn related(&self) -> &[D::Related] {
        self.related
            .get_or_init(|| self.source.related(&self.subject))
    }
}

impl<D: Diagnostic> core::ops::Deref for Report<D> {
    type Target = D;

    fn deref(&self) -> &Self::Target {
        &self.source
    }
}

impl<D: Diagnostic + fmt::Display> fmt::Display for Report<D> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        fmt::Display::fmt(&self.source, f)
    }
}

#[cfg(feature = "std")]
impl<D> std::error::Error for Report<D>
where
    D: Diagnostic + fmt::Debug + std::error::Error + 'static,
    D::Related: fmt::Debug,
    D::Subject: fmt::Debug,
{
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        Some(&self.source)
    }
}

#[cfg(feature = "miette")]
impl<D> miette::Diagnostic for Report<D>
where
    D: Diagnostic + fmt::Debug + std::error::Error + 'static,
    D::Subject: fmt::Debug + miette::SourceCode,
    D::Related: Diagnostic + fmt::Debug + std::error::Error + 'static,
{
    fn url<'a>(&'a self) -> Option<Box<dyn core::fmt::Display + 'a>> {
        Some(Box::new(D::url()))
    }

    fn source_code(&self) -> Option<&dyn miette::SourceCode> {
        Some(&self.subject)
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = miette::LabeledSpan> + '_>> {
        Some(Box::new(D::labels(self, &self.subject)?.map(Into::into)))
    }
}

macro_rules! impl_diagnostic_url {
    (enum $type:ident) => {
        $crate::diagnostic::impl_diagnostic_url!("enum", "", $type)
    };
    (struct $type:ident) => {
        $crate::diagnostic::impl_diagnostic_url!("struct", "", $type)
    };
    (enum $mod:ident::$type:ident) => {
        $crate::diagnostic::impl_diagnostic_url!("enum", concat!("/", stringify!($mod)), $type)
    };
    (struct $mod:ident::$type:ident) => {
        $crate::diagnostic::impl_diagnostic_url!("struct", concat!("/", stringify!($mod)), $type)
    };
    ($kind:literal, $mod:expr, $type:ident) => {
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
    };
}
pub(crate) use impl_diagnostic_url;

#[cfg(feature = "miette")]
struct Borrowed<'a, D: Diagnostic> {
    source: &'a D,
    subject: &'a D::Subject,
}
#[cfg(feature = "miette")]
impl<'a, D: Diagnostic> miette::Diagnostic for Borrowed<'a, D> {
    fn url<'b>(&'b self) -> Option<Box<dyn core::fmt::Display + 'b>> {
        Some(Box::new(D::url()))
    }

    fn source_code(&self) -> Option<&dyn miette::SourceCode> {
        Some(self.subject)
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = miette::LabeledSpan> + '_>> {
        Diagnostic::labels(&self, self.subject)
    }
    fn related<'b>(&'b self) -> Option<Box<dyn Iterator<Item = &'b dyn miette::Diagnostic> + 'b>> {
        Some(Box::new(
            self.source.related(self.subject).iter().map(|r| r as _),
        ))
    }
}

mod private {
    pub trait Sealed {}
    impl Sealed for crate::pointer::ParseError {}
    impl Sealed for crate::assign::Error {}
}

pub trait Diagnose<'s, T> {
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

impl<'s, T, E> Diagnose<'s, T> for Result<T, E>
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Pointer, PointerBuf};

    #[test]
    #[cfg(all(
        feature = "assign",
        feature = "miette",
        feature = "serde",
        feature = "json"
    ))]
    fn assign_error() {
        let mut v = serde_json::json!({"foo": {"bar": ["0"]}});
        use miette::Diagnostic;
        let ptr = PointerBuf::parse("/foo/bar/invalid/cannot/reach").unwrap();
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

        let report = PointerBuf::parse("/foo/bar/invalid~3~encoding/cannot/reach").unwrap_err();

        let report = miette::Report::from(report);
        println!("{report:?}");
    }

    #[test]
    fn into_owned() {
        // creating owned string to ensure its lifetime is local
        // (could also coerce a static reference, but this is less brittle)
        let invalid = "/foo/bar/invalid~3~encoding/cannot/reach".to_string();
        let report = Pointer::parse(&invalid)
            .diagnose(invalid.as_str())
            .unwrap_err();

        println!("{report}");
    }
}
