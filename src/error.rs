use crate::{Pointer, Token};
use std::{
    error::Error as StdError,
    fmt::{Debug, Display, Formatter},
    num::ParseIntError,
};

/// An enum representing possible errors that can occur when resolving or
/// mutating by a JSON Pointer.
#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    Index(IndexError),
    Unresolvable(UnresolvableError),
    NotFound(NotFoundError),
    MalformedPointer(MalformedPointerError),
}

impl Error {
    /// Returns `true` if the error is `Error::IndexError`.
    pub fn is_index(&self) -> bool {
        matches!(self, Error::Index(_))
    }
    /// Returns `true` if the error is `Error::UnresolvableError`.
    pub fn is_unresolvable(&self) -> bool {
        matches!(self, Error::Unresolvable(_))
    }
    /// Returns `true` if the error is `Error::NotFoundError`.
    pub fn is_not_found(&self) -> bool {
        matches!(self, Error::NotFound(_))
    }
    /// Returns `true` if the error is `Error::MalformedPointerError`.
    pub fn is_malformed_pointer(&self) -> bool {
        matches!(self, Error::MalformedPointer(_))
    }
}
impl From<MalformedPointerError> for Error {
    fn from(err: MalformedPointerError) -> Self {
        Error::MalformedPointer(err)
    }
}
impl From<IndexError> for Error {
    fn from(err: IndexError) -> Self {
        Error::Index(err)
    }
}
impl From<NotFoundError> for Error {
    fn from(err: NotFoundError) -> Self {
        Error::NotFound(err)
    }
}

impl From<OutOfBoundsError> for Error {
    fn from(err: OutOfBoundsError) -> Self {
        Error::Index(IndexError::from(err))
    }
}

impl From<UnresolvableError> for Error {
    fn from(err: UnresolvableError) -> Self {
        Error::Unresolvable(err)
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Index(err) => Display::fmt(err, f),
            Error::Unresolvable(err) => Display::fmt(err, f),
            Error::NotFound(err) => Display::fmt(err, f),
            Error::MalformedPointer(err) => Display::fmt(err, f),
        }
    }
}

impl StdError for Error {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Index(err) => Some(err),
            Error::Unresolvable(_) => None,
            Error::NotFound(_) => None,
            Error::MalformedPointer(_) => todo!(),
        }
    }
}

/// Represents an error that occurs when attempting to resolve a `Pointer` that
/// encounters a leaf node (i.e. a scalar / null value) which is not the root
/// of the `Pointer`.
///
/// ## Example
/// ```rust
/// use serde_json::json;
/// use jsonptr::{Pointer, ResolveMut, Resolve, UnresolvableError};
/// let mut data = json!({ "foo": "bar" });
/// let ptr = Pointer::try_from("/foo/unreachable").unwrap();
/// let err = data.resolve_mut(&ptr).unwrap_err();
/// assert_eq!(err, UnresolvableError::new(ptr.clone()).into());
/// ```
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct UnresolvableError {
    pub pointer: Pointer,
    pub leaf: Option<Token>,
}
impl UnresolvableError {
    pub fn new(pointer: Pointer) -> Self {
        let leaf = if pointer.count() >= 2 {
            Some(pointer.get(pointer.count() - 2).unwrap())
        } else {
            None
        };
        Self { pointer, leaf }
    }
}

impl Display for UnresolvableError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "can not resolve \"{}\" due to {} being a scalar value",
            self.pointer,
            self.leaf
                .as_deref()
                .map_or_else(|| "the root value".to_string(), |l| format!("\"{}\"", l))
        )
    }
}

/// Indicates an error occurred while parsing a `usize` (`ParseError`) or the
/// parsed value was out of bounds for the targeted array.
#[derive(PartialEq, Eq)]
pub enum IndexError {
    Parse(ParseError),
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

/// ParseError represents an that an error occurred when parsing an index.
#[derive(PartialEq, Eq)]
pub struct ParseError {
    pub source: ParseIntError,
    pub token: Token,
}

impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.source)
    }
}
impl Debug for ParseError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ParseError")
            .field("source", &self.source)
            .field("token", &self.token)
            .finish()
    }
}
impl StdError for ParseError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        Some(&self.source)
    }
}

/// Indicates that the `Pointer` contains an index of an array that is out of
/// bounds.
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
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum MalformedPointerError {
    NoLeadingSlash(String),
    InvalidEncoding(String),
}

impl Display for MalformedPointerError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            MalformedPointerError::NoLeadingSlash(s) => {
                write!(
                    f,
                    "json pointer \"{}\" is malformed due to missing starting slash",
                    s
                )
            }
            MalformedPointerError::InvalidEncoding(s) => {
                write!(f, "json pointer \"{}\" is improperly encoded", s)
            }
        }
    }
}

impl StdError for MalformedPointerError {}

/// NotFoundError indicates that a Pointer was not found in the data.
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

/// ReplaceTokenError is returned from `Pointer::replace_token` when the
/// provided index is out of bounds.
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
