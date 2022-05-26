use crate::{JsonPointer, Token};
use std::{
    error::Error as StdError,
    fmt::{Debug, Display, Formatter},
    num::ParseIntError,
};
pub enum Error {
    IndexError(IndexError),
    Serde(serde_json::Error),
    Unresolvable(UnresolvableError),
}

impl From<IndexError> for Error {
    fn from(err: IndexError) -> Self {
        Error::IndexError(err)
    }
}

impl From<serde_json::Error> for Error {
    fn from(err: serde_json::Error) -> Self {
        Error::Serde(err)
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::IndexError(err) => Display::fmt(err, f),
            Error::Serde(err) => Display::fmt(err, f),
            Error::Unresolvable(_) => todo!(),
        }
    }
}

impl Debug for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IndexError(err) => f.debug_tuple("IndexError").field(err).finish(),
            Self::Serde(err) => f.debug_tuple("Serde").field(err).finish(),
            Self::Unresolvable(err) => f.debug_tuple("Unresolvable").field(err).finish(),
        }
    }
}
impl StdError for Error {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::IndexError(err) => Some(err),
            Self::Serde(err) => Some(err),
            Error::Unresolvable(_) => None,
        }
    }
}

#[derive(Clone)]
pub struct UnresolvableError {
    pub unresolved: JsonPointer,
    pub terminated_at: serde_json::Value,
}

impl Debug for UnresolvableError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("UnresolvableError")
            .field("unresolved", &self.unresolved)
            .field("terminated_at", &self.terminated_at)
            .finish()
    }
}
impl Display for UnresolvableError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} is not capable of being resolved due to {} being a leaf node",
            self.unresolved,
            self.unresolved.front().map_or("/", |t| t.as_str())
        )
    }
}
#[derive(Clone, PartialEq)]
pub enum IndexError {
    Parse(ParseError<ParseIntError>),
    OutOfBounds(OutOfBoundsError),
}
impl Display for IndexError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            IndexError::Parse(err) => Display::fmt(&err, f),
            IndexError::OutOfBounds(err) => Display::fmt(&err, f),
        }
    }
}
impl Debug for IndexError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self, f)
    }
}
impl std::error::Error for IndexError {}

#[derive(Clone, PartialEq)]
pub struct ParseError<T> {
    pub source: T,
    pub token: Token,
}

impl<E> Display for ParseError<E>
where
    E: StdError,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.source)
    }
}
impl<E> Debug for ParseError<E>
where
    E: StdError + 'static,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ParseError")
            .field("source", &self.source)
            .field("token", &self.token)
            .finish()
    }
}
impl<E> StdError for ParseError<E>
where
    E: StdError + 'static + Send + Sync,
{
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        Some(&self.source)
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct OutOfBoundsError {
    pub len: usize,
    pub index: usize,
    pub token: Token,
}
impl StdError for OutOfBoundsError {}

impl Display for OutOfBoundsError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "index {} out of bounds", self.index)
    }
}
impl Debug for OutOfBoundsError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OutOfBoundsError")
            .field("len", &self.len)
            .field("index", &self.index)
            .finish()
    }
}
