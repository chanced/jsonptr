//! Error reporting data structures and miette integration.
//!

use alloc::{boxed::Box, string::String};
use core::{fmt, ops::Deref};

/// Implemented by errors which can be converted into a [`Report`].
pub trait Diagnostic: Sized {
    /// The value which caused the error.
    type Subject: Deref;

    /// Combine the error with its subject to generate a [`Report`].
    fn into_report(self, subject: impl Into<Self::Subject>) -> Report<Self> {
        Report::new(self, subject.into())
    }

    /// The docs.rs URL for this error
    fn url() -> &'static str;

    /// Returns the label for the given [`Subject`] if applicable.
    fn labels(&self, subject: &Self::Subject) -> Option<Box<dyn Iterator<Item = Label>>>;
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

/// An enriched error wrapper which captures the original error and the subject
/// (`String` or `PointerBuf`) which caused it, for reporting purposes.
///
/// This type serves two roles:
///
/// 1. **[`PointerBuf::parse`]**: Captures the [`ParseError`] along with the
///    input `String`.
///
/// 2. **Reporting:** Provides enriched reporting capabilities, including
///    (optional) `miette` integration, for `ParseError` and associated  errors
///    of `assign::Assign` and `resolve::Resolve` implementations
#[derive(Debug, Clone)]
pub struct Report<T: Diagnostic> {
    source: T,
    subject: T::Subject,
}

impl<T: Diagnostic> Report<T> {
    fn new(source: T, subject: T::Subject) -> Self {
        Self { source, subject }
    }

    /// The value which caused the error.
    pub fn subject(&self) -> &<T::Subject as Deref>::Target {
        &self.subject
    }

    /// The error which occurred.
    pub fn original(&self) -> &T {
        &self.source
    }

    /// The original parts of the [`Report`].
    pub fn decompose(self) -> (T, T::Subject) {
        (self.source, self.subject)
    }

    /// Consumes the [`Report`] and returns the original error `T`.
    pub fn into_original(self) -> T {
        self.source
    }
}

impl<T: Diagnostic> core::ops::Deref for Report<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.source
    }
}

impl<T: Diagnostic + fmt::Display> fmt::Display for Report<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        fmt::Display::fmt(&self.source, f)
    }
}

#[cfg(feature = "std")]
impl<T> std::error::Error for Report<T>
where
    T: Diagnostic + fmt::Debug + std::error::Error + 'static,
    T::Subject: fmt::Debug,
{
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.source.source()
    }
}

#[cfg(feature = "miette")]
impl<T> miette::Diagnostic for Report<T>
where
    T: Diagnostic + fmt::Debug + std::error::Error + 'static,
    T::Subject: fmt::Debug + miette::SourceCode,
{
    fn url<'a>(&'a self) -> Option<Box<dyn core::fmt::Display + 'a>> {
        Some(Box::new(T::url()))
    }

    fn source_code(&self) -> Option<&dyn miette::SourceCode> {
        Some(&self.subject)
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = miette::LabeledSpan> + '_>> {
        Some(Box::new(T::labels(self, &self.subject)?.map(Into::into)))
    }
}

macro_rules! diagnostic_url {
    (enum $type:ident) => {
        $crate::diagnostic::diagnostic_url!("enum", "", $type)
    };
    (struct $type:ident) => {
        $crate::diagnostic::diagnostic_url!("struct", "", $type)
    };
    (enum $mod:ident::$type:ident) => {
        $crate::diagnostic::diagnostic_url!("enum", concat!("/", stringify!($mod)), $type)
    };
    (struct $mod:ident::$type:ident) => {
        $crate::diagnostic::diagnostic_url!("struct", concat!("/", stringify!($mod)), $type)
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
pub(crate) use diagnostic_url;

/// An extension trait for `Result<_, E>`, where `E` is an implementation of
/// [`Diagnostic`], that converts `E` into [`Report<E>`](`Report`), yielding
/// `Result<_, Report<E>>`.
pub trait Diagnose<'s, T> {
    /// The error type returned from `diagnose` and `diagnose_with`.
    type Error: Diagnostic;

    /// If the `Result` is an `Err`, converts the error into a [`Report`] with
    /// the supplied `subject`.
    ///
    /// ## Example
    /// ```
    /// use core::any::{Any, TypeId};
    /// use jsonptr::{Pointer, ParseError, Diagnose, Report};
    /// let subj = "invalid/pointer";
    /// let err = Pointer::parse(subj).diagnose(subj).unwrap_err();
    /// assert_eq!(err.type_id(),TypeId::of::<Report<ParseError>>());
    /// ```
    #[allow(clippy::missing_errors_doc)]
    fn diagnose(
        self,
        subject: impl Into<<Self::Error as Diagnostic>::Subject>,
    ) -> Result<T, Report<Self::Error>>;

    /// If the `Result` is an `Err`, converts the error into a [`Report`] with
    /// the subject returned from `f`
    ///
    /// ## Example
    /// ```
    /// use core::any::{Any, TypeId};
    /// use jsonptr::{Pointer, ParseError, Diagnose, Report};
    /// let subj = "invalid/pointer";
    /// let err = Pointer::parse(subj).diagnose_with(|| subj).unwrap_err();
    ///
    /// assert_eq!(err.type_id(),TypeId::of::<Report<ParseError>>());
    #[allow(clippy::missing_errors_doc)]
    fn diagnose_with<F, S>(self, f: F) -> Result<T, Report<Self::Error>>
    where
        F: FnOnce() -> S,
        S: Into<<Self::Error as Diagnostic>::Subject>;
}

impl<T, E> Diagnose<'_, T> for Result<T, E>
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
        let ptr = PointerBuf::parse("/foo/bar/invalid/cannot/reach").unwrap();
        let report = ptr.assign(&mut v, "qux").diagnose(ptr).unwrap_err();
        println!("{:?}", miette::Report::from(report));

        let ptr = PointerBuf::parse("/foo/bar/3/cannot/reach").unwrap();
        let report = ptr.assign(&mut v, "qux").diagnose(ptr).unwrap_err();
        println!("{:?}", miette::Report::from(report));
    }

    #[test]
    #[cfg(all(
        feature = "resolve",
        feature = "miette",
        feature = "serde",
        feature = "json"
    ))]
    fn resolve_error() {
        let v = serde_json::json!({"foo": {"bar": ["0"]}});
        let ptr = PointerBuf::parse("/foo/bar/invalid/cannot/reach").unwrap();
        let report = ptr.resolve(&v).diagnose(ptr).unwrap_err();
        println!("{:?}", miette::Report::from(report));

        let ptr = PointerBuf::parse("/foo/bar/3/cannot/reach").unwrap();
        let report = ptr.resolve(&v).diagnose(ptr).unwrap_err();
        println!("{:?}", miette::Report::from(report));
    }

    #[test]
    #[cfg(feature = "miette")]
    fn parse_error() {
        let invalid = "/foo/bar/invalid~3~encoding/cannot/reach";
        let report = Pointer::parse(invalid).diagnose(invalid).unwrap_err();

        println!("{:?}", miette::Report::from(report));

        let report = PointerBuf::parse("/foo/bar/invalid~3~encoding/cannot/reach").unwrap_err();

        let report = miette::Report::from(report);
        println!("{report:?}");
    }
}
