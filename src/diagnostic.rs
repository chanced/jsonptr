//! Error reporting data structures and miette integration.

use core::fmt;

/// Implemented by errors which can be converted into a [`Report`].
pub trait Diagnostic<'s>: Sized + private::Sealed {
    /// The value which caused the error.
    type Subject: private::IntoOwned;

    /// Combine the error with its subject to generate a [`Report`].
    fn into_report(self, subject: impl Into<Self::Subject>) -> Report<'s, Self> {
        Report::new(self, subject)
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

/// An error wrapper which includes the subject of the failure.
#[derive(Clone, PartialEq, Eq)]
pub struct Report<'s, S: Diagnostic<'s>> {
    source: S,
    subject: S::Subject,
}

impl<'s, S: Diagnostic<'s>> Report<'s, S> {
    /// Create a new `Report` with the given subject and error.
    fn new(source: S, subject: impl Into<S::Subject>) -> Self {
        Self {
            source,
            subject: subject.into(),
        }
    }

    /// The value which caused the error.
    pub fn subject(&self) -> &S::Subject {
        &self.subject
    }

    /// The error which occurred.
    pub fn original(&self) -> &S {
        &self.source
    }

    /// The original parts of the [`Report`].
    pub fn decompose(self) -> (S, S::Subject) {
        (self.source, self.subject)
    }
}

impl<'s, S> Report<'s, S>
where
    S: Diagnostic<'s>,
{
    /// Converts the Report into an owned instance (generally by cloning the subject).
    pub fn into_owned<O>(self) -> Report<'static, O>
    where
        S: Into<O>,
        O: Diagnostic<'static, Subject = <S::Subject as private::IntoOwned>::Owned>,
    {
        use private::IntoOwned;

        Report {
            // TODO: is there a way to avoid the `Into` here? We really want `S == O`,
            // but I'm strugggling to express that without a bound predicate cycle
            source: self.source.into(),
            subject: self.subject.into_owned(),
        }
    }
}

impl<'s, S> core::ops::Deref for Report<'s, S>
where
    S: Diagnostic<'s>,
{
    type Target = S;

    fn deref(&self) -> &Self::Target {
        &self.source
    }
}

impl<'s, S> fmt::Display for Report<'s, S>
where
    S: Diagnostic<'s> + fmt::Display,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        fmt::Display::fmt(&self.source, f)
    }
}

impl<'s, S> fmt::Debug for Report<'s, S>
where
    S: Diagnostic<'s> + fmt::Debug,
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
impl<'s, S> std::error::Error for Report<'s, S>
where
    S: Diagnostic<'s> + fmt::Debug + std::error::Error + 'static,
    S::Subject: fmt::Debug,
{
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        Some(&self.source)
    }
}

#[cfg(feature = "miette")]
impl<'s, S> miette::Diagnostic for Report<'s, S>
where
    S: Diagnostic<'s> + fmt::Debug + std::error::Error + 'static,
    S::Subject: fmt::Debug + miette::SourceCode,
{
    fn url<'a>(&'a self) -> Option<Box<dyn core::fmt::Display + 'a>> {
        Some(Box::new(S::url()))
    }

    fn source_code(&self) -> Option<&dyn miette::SourceCode> {
        Some(&self.subject)
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = miette::LabeledSpan> + '_>> {
        Some(Box::new(S::labels(self, &self.subject)?.map(Into::into)))
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

mod private {
    use crate::Pointer;
    use alloc::borrow::Cow;

    pub trait Sealed {}
    impl Sealed for crate::pointer::ParseError {}
    impl Sealed for crate::assign::Error {}

    pub trait IntoOwned {
        type Owned: 'static;

        fn into_owned(self) -> Self::Owned;
    }

    impl<'s> IntoOwned for Cow<'s, str> {
        type Owned = Cow<'static, str>;

        fn into_owned(self) -> Cow<'static, str> {
            Cow::Owned(self.into_owned())
        }
    }

    impl<'s> IntoOwned for Cow<'s, Pointer> {
        type Owned = Cow<'static, Pointer>;

        fn into_owned(self) -> Cow<'static, Pointer> {
            Cow::Owned(self.into_owned())
        }
    }
}

pub trait Diagnose<'s, T> {
    type Error: Diagnostic<'s>;

    #[allow(clippy::missing_errors_doc)]
    fn diagnose(
        self,
        subject: impl Into<<Self::Error as Diagnostic<'s>>::Subject>,
    ) -> Result<T, Report<'s, Self::Error>>;

    #[allow(clippy::missing_errors_doc)]
    fn diagnose_with<F, S>(self, f: F) -> Result<T, Report<'s, Self::Error>>
    where
        F: FnOnce() -> S,
        S: Into<<Self::Error as Diagnostic<'s>>::Subject>;
}

impl<'s, T, E> Diagnose<'s, T> for Result<T, E>
where
    E: Diagnostic<'s>,
{
    type Error = E;

    fn diagnose(
        self,
        subject: impl Into<<Self::Error as Diagnostic<'s>>::Subject>,
    ) -> Result<T, Report<'s, Self::Error>> {
        self.map_err(|error| error.into_report(subject.into()))
    }

    fn diagnose_with<F, S>(self, f: F) -> Result<T, Report<'s, Self::Error>>
    where
        F: FnOnce() -> S,
        S: Into<<Self::Error as Diagnostic<'s>>::Subject>,
    {
        self.diagnose(f())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ParseError, Pointer, PointerBuf};

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

    #[test]
    fn into_owned() {
        // NOTE: the type has to be fully specified here because of the `S: Into<O>` bound
        // in `Report::into_owned`. Ideally we'd express `S == O` so that the output can
        // be automatically inferred.
        let owned_report: Report<'static, ParseError> = {
            // creating owned string to ensure its lifetime is local
            // (could also coerce a static reference, but this is less brittle)
            let invalid = "/foo/bar/invalid~3~encoding/cannot/reach".to_string();
            let report = Pointer::parse(&invalid)
                .diagnose(invalid.as_str())
                .unwrap_err();
            report.into_owned()
        };

        println!("{owned_report}");
    }
}
