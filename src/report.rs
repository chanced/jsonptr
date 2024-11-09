//! Error reporting data structures and miette integration.

use crate::PointerBuf;

pub trait IntoReport: Sized {
    type Value;
    fn into_report(self, value: Self::Value) -> Report<Self>;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Report<E> {
    pub subject: Subject,
    pub error: E,
}

impl<E> Report<E> {
    pub fn new(subject: Subject, error: E) -> Self {
        Self { subject, error }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Subject {
    String {
        value: String,
        offset: usize,
        len: usize,
    },
    Pointer {
        value: PointerBuf,
        position: usize,
    },
}
impl Subject {
    pub(crate) fn string(value: String, offset: usize, len: usize) -> Self {
        Self::String { value, offset, len }
    }
    pub(crate) fn pointer(value: PointerBuf, position: usize) -> Self {
        Self::Pointer { value, position }
    }
}
impl From<&str> for Subject {
    fn from(value: &str) -> Self {
        Self::String {
            value: value.to_string(),
            offset: 0,
            len: value.len(),
        }
    }
}

pub trait ReportErr<T> {
    type Error: IntoReport;
    fn report_err(
        self,
        value: impl Into<<Self::Error as IntoReport>::Value>,
    ) -> Result<T, Report<Self::Error>>;
}

impl<T, E> ReportErr<T> for Result<T, E>
where
    E: IntoReport,
{
    type Error = E;

    fn report_err(
        self,
        value: impl Into<<Self::Error as IntoReport>::Value>,
    ) -> Result<T, Report<Self::Error>> {
        self.map_err(|error| error.into_report(value.into()))
    }
}
