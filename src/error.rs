use serde_json::value::Index;

use crate::{Pointer, Token};
use std::{
    error::Error as StdError,
    fmt::{Debug, Display, Formatter},
    num::ParseIntError,
};
#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    IndexError(IndexError),
    Unresolvable(UnresolvableError),
    NotFound(NotFoundError),
    MalformedPointer(MalformedError),
}

impl From<IndexError> for Error {
    fn from(err: IndexError) -> Self {
        Error::IndexError(err)
    }
}
impl From<NotFoundError> for Error {
    fn from(err: NotFoundError) -> Self {
        Error::NotFound(err)
    }
}

impl From<OutOfBoundsError> for Error {
    fn from(err: OutOfBoundsError) -> Self {
        Error::IndexError(IndexError::from(err))
    }
}

// impl From<serde_json::Error> for Error {
//     fn from(err: serde_json::Error) -> Self {
//         Error::Serde(err)
//     }
// }
impl From<UnresolvableError> for Error {
    fn from(err: UnresolvableError) -> Self {
        Error::Unresolvable(err)
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::IndexError(err) => Display::fmt(err, f),
            Error::Unresolvable(err) => Display::fmt(err, f),
            Error::NotFound(err) => Display::fmt(err, f),
            Error::MalformedPointer(err) => Display::fmt(err, f),
        }
    }
}

impl StdError for Error {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::IndexError(err) => Some(err),
            Error::Unresolvable(_) => None,
            Error::NotFound(_) => None,
            Error::MalformedPointer(_) => todo!(),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct UnresolvableError {
    pub unresolvable: Pointer,
}
impl UnresolvableError {
    pub fn new(unresolvable: Pointer) -> Self {
        Self { unresolvable }
    }
}

impl Display for UnresolvableError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "can not resolve \"{}\" due to \"{}\" being a leaf node",
            self.unresolvable,
            self.unresolvable
                .front()
                .map_or("/".to_string(), |t| t.to_string())
        )
    }
}
#[derive(PartialEq, Eq)]
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

impl From<OutOfBoundsError> for IndexError {
    fn from(err: OutOfBoundsError) -> Self {
        IndexError::OutOfBounds(err)
    }
}

#[derive(PartialEq, Eq)]
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

#[derive(Debug, PartialEq, Eq)]
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

/// Indicates that a Pointer was malformed.
#[derive(Debug, PartialEq, Eq)]
pub enum MalformedError {
    NoLeadingSlash(String),
    InvalidEncoding(String),
}

impl Display for MalformedError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            MalformedError::NoLeadingSlash(s) => {
                write!(
                    f,
                    "json pointer \"{}\" is malformed due to missing starting slash",
                    s
                )
            }
            MalformedError::InvalidEncoding(s) => {
                write!(f, "json pointer \"{}\" is improperly encoded", s)
            }
        }
    }
}

impl StdError for MalformedError {}

#[derive(Debug, PartialEq, Eq)]
pub struct NotFoundError {
    pub pointer: Pointer,
}
impl NotFoundError {
    pub fn new(pointer: Pointer) -> Self {
        NotFoundError { pointer }
    }
}
impl Display for NotFoundError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "the resource at json pointer \"{}\" was not found",
            self.pointer
        )
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ReplaceTokenError {
    pub index: usize,
    pub count: usize,
    pub pointer: Pointer,
}
impl StdError for ReplaceTokenError {}
impl Display for ReplaceTokenError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "index {} is out of bounds ({}) for the pointer {}",
            self.index, self.count, self.pointer
        )
    }
}
