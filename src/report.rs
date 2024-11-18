//! Error reporting data structures and miette integration.

use core::fmt;

/// Implemented by errors which can be converted into a [`Report`].
pub trait Enrich<'s>: Sized + private::Sealed {
    /// The value which caused the error.
    type Subject;

    /// Enrich the error with its subject.
    fn enrich(self, subject: impl Into<Self::Subject>) -> Enriched<'s, Self> {
        Enriched::new(self, subject)
    }

    /// The docs.rs URL for this error
    fn url() -> &'static str;

    /// Returns the label for the given [`Subject`] if applicable.
    fn labels(&self, subject: &Self::Subject) -> Option<Box<dyn Iterator<Item = Label>>>;
}

/// A label for a span within a json pointer or malformed string.
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

/// An error wrapper which includes the [`String`] which failed to parse or the
/// [`PointerBuf`] being used.
#[derive(Clone, PartialEq, Eq)]
pub struct Enriched<'s, S: Enrich<'s>> {
    source: S,
    subject: S::Subject,
}

impl<'s, S: Enrich<'s>> Enriched<'s, S> {
    /// Create a new `Report` with the given subject and error.
    fn new(source: S, subject: impl Into<S::Subject>) -> Self {
        Self {
            source,
            subject: subject.into(),
        }
    }

    /// Returns labels associated with spans where the error occurs.
    pub fn labels(&self) -> Option<Box<dyn Iterator<Item = Label>>> {
        self.source.labels(&self.subject)
    }

    /// The value which caused the error.
    pub fn subject(&self) -> &S::Subject {
        &self.subject
    }

    /// The error which occurred.
    pub fn source(&self) -> &S {
        &self.source
    }

    /// The docs.rs URL for the error of this [`Report`].
    pub fn url() -> &'static str {
        S::url()
    }
}

impl<'s, S> fmt::Display for Enriched<'s, S>
where
    S: Enrich<'s> + fmt::Display,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        fmt::Display::fmt(&self.source, f)
    }
}

impl<'s, S> fmt::Debug for Enriched<'s, S>
where
    S: Enrich<'s> + fmt::Debug,
    S::Subject: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Enriched")
            .field("source", &self.source)
            .field("subject", &self.subject)
            .finish()
    }
}

#[cfg(feature = "std")]
impl<'s, S> std::error::Error for Enriched<'s, S>
where
    S: Enrich<'s> + fmt::Debug + std::error::Error + 'static,
    S::Subject: fmt::Debug,
{
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        Some(&self.source)
    }
}

#[cfg(feature = "miette")]
impl<'s, S> miette::Diagnostic for Enriched<'s, S>
where
    S: Enrich<'s> + fmt::Debug + std::error::Error + 'static,
    S::Subject: fmt::Debug + miette::SourceCode,
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

macro_rules! impl_diagnostic_url {
    (enum $type:ident) => {
        $crate::report::impl_diagnostic_url!("enum", "", $type)
    };
    (struct $type:ident) => {
        $crate::report::impl_diagnostic_url!("struct", "", $type)
    };
    (enum $mod:ident::$type:ident) => {
        $crate::report::impl_diagnostic_url!("enum", concat!("/", stringify!($mod)), $type)
    };
    (struct $mod:ident::$type:ident) => {
        $crate::report::impl_diagnostic_url!("struct", concat!("/", stringify!($mod)), $type)
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

mod private {
    pub trait Sealed {}
    impl Sealed for crate::pointer::ParseError {}
    impl Sealed for crate::assign::Error {}
}

pub trait Diagnose<'s, T> {
    type Error: Enrich<'s>;

    #[allow(clippy::missing_errors_doc)]
    fn diagnose(
        self,
        subject: impl Into<<Self::Error as Enrich<'s>>::Subject>,
    ) -> Result<T, Enriched<'s, Self::Error>>;

    #[allow(clippy::missing_errors_doc)]
    fn diagnose_with<F, S>(self, f: F) -> Result<T, Enriched<'s, Self::Error>>
    where
        F: FnOnce() -> S,
        S: Into<<Self::Error as Enrich<'s>>::Subject>;
}

impl<'s, T, E> Diagnose<'s, T> for Result<T, E>
where
    E: Enrich<'s>,
{
    type Error = E;

    fn diagnose(
        self,
        subject: impl Into<<Self::Error as Enrich<'s>>::Subject>,
    ) -> Result<T, Enriched<'s, Self::Error>> {
        self.map_err(|error| error.enrich(subject.into()))
    }

    fn diagnose_with<F, S>(self, f: F) -> Result<T, Enriched<'s, Self::Error>>
    where
        F: FnOnce() -> S,
        S: Into<<Self::Error as Enrich<'s>>::Subject>,
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
}
