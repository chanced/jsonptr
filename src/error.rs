use alloc::{
    format,
    string::{FromUtf8Error, String, ToString},
    vec::Vec,
};

use crate::{Pointer, Token};
use core::{
    // error::Error as StdError,
    fmt::{Debug, Display, Formatter},
    num::ParseIntError,
};

/// An enum representing possible errors that can occur when resolving or
/// mutating by a JSON Pointer.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Error {
    /// Indicates an error occurred while parsing a `usize` (`ParseError`) or the
    /// parsed value was out of bounds for the targeted array.
    Index(IndexError),
    /// Represents an error that occurs when attempting to resolve a `Pointer` that
    /// encounters a leaf node (i.e. a scalar / null value) which is not the root
    /// of the `Pointer`.
    Unresolvable(UnresolvableError),
    /// Indicates that a Pointer was not found in the data.
    NotFound(NotFoundError),
    // /// Indicates that a Pointer was malformed.
    // MalformedPointer(MalformedPointerError),
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
    // /// Returns `true` if the error is `Error::MalformedPointerError`.
    // pub fn is_malformed_pointer(&self) -> bool {
    //     matches!(self, Error::MalformedPointer(_))
    // }
}
// impl From<MalformedPointerError> for Error {
//     fn from(err: MalformedPointerError) -> Self {
//         Error::MalformedPointer(err)
//     }
// }
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
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            Error::Index(err) => Display::fmt(err, f),
            Error::Unresolvable(err) => Display::fmt(err, f),
            Error::NotFound(err) => Display::fmt(err, f),
            // Error::MalformedPointer(err) => Display::fmt(err, f),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}

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
    /// The unresolved `Pointer`.
    pub pointer: Pointer,
    /// The leaf node, if applicable, which was expected to be either an
    /// `Object` or an `Array`.
    pub leaf: Option<Token>,
}

#[cfg(feature = "std")]
impl std::error::Error for UnresolvableError {}

impl UnresolvableError {
    /// Creates a new `UnresolvableError` with the given `Pointer`.
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
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "can not resolve \"{}\" due to {} being a scalar value",
            self.pointer,
            self.leaf
                .as_deref()
                .map_or_else(|| "the root value".to_string(), |l| format!("\"{l}\""))
        )
    }
}

/// Indicates an error occurred while parsing a `usize` (`ParseError`) or the
/// parsed value was out of bounds for the targeted array.
#[derive(PartialEq, Eq, Clone)]
pub enum IndexError {
    /// Represents an that an error occurred when parsing an index.
    Parse(ParseError),
    /// Indicates that the Pointer contains an index of an array that is out of
    /// bounds.
    OutOfBounds(OutOfBoundsError),
}
impl Display for IndexError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            IndexError::Parse(err) => Display::fmt(&err, f),
            IndexError::OutOfBounds(err) => Display::fmt(&err, f),
        }
    }
}
impl Debug for IndexError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        Display::fmt(self, f)
    }
}
#[cfg(feature = "std")]
impl std::error::Error for IndexError {}

impl From<OutOfBoundsError> for IndexError {
    fn from(err: OutOfBoundsError) -> Self {
        IndexError::OutOfBounds(err)
    }
}

/// ParseError represents an that an error occurred when parsing an index.
#[derive(PartialEq, Eq, Clone)]
pub struct ParseError {
    /// The source `ParseIntError`
    pub source: ParseIntError,
    /// The `Token` which was unable to be parsed as an index.
    pub token: Token,
}

impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.source)
    }
}
impl Debug for ParseError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ParseError")
            .field("source", &self.source)
            .field("token", &self.token)
            .finish()
    }
}
#[cfg(feature = "std")]
impl std::error::Error for ParseError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.source)
    }
}

/// Indicates that the `Pointer` contains an index of an array that is out of
/// bounds.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct OutOfBoundsError {
    /// The length of the array.
    pub len: usize,
    /// The index of the array that was out of bounds.
    pub index: usize,
    /// The `Token` which was out of bounds.
    pub token: Token,
}
#[cfg(feature = "std")]
impl std::error::Error for OutOfBoundsError {}

impl Display for OutOfBoundsError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "index {} out of bounds", self.index)
    }
}

/// Pointer was not in UTF-8 format.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct NotUtf8Error {
    /// Underlying `std::str::Utf8Error`.
    pub source: FromUtf8Error,
    /// Byte slice that was not in UTF-8 format.
    pub path: Vec<u8>,
}

impl core::fmt::Display for NotUtf8Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "not utf8: {}", self.source)
    }
}
#[cfg(feature = "std")]
impl std::error::Error for NotUtf8Error {}

/// Indicates that a Pointer was malformed.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum MalformedPointerError {
    /// Indicates that the Pointer was malformed because it did not contain a
    /// leading slash (`'/'`).
    NoLeadingSlash(String),
    /// Indicates that the Pointer was malformed because it contained invalid
    /// encoding.
    InvalidEncoding(String),
    /// NonUTF8
    NotUtf8(NotUtf8Error),
}
impl From<NotUtf8Error> for MalformedPointerError {
    fn from(err: NotUtf8Error) -> Self {
        MalformedPointerError::NotUtf8(err)
    }
}

impl From<FromUtf8Error> for MalformedPointerError {
    fn from(err: FromUtf8Error) -> Self {
        MalformedPointerError::NotUtf8(NotUtf8Error {
            source: err,
            path: Vec::new(),
        })
    }
}
impl Display for MalformedPointerError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            MalformedPointerError::NoLeadingSlash(s) => {
                write!(
                    f,
                    "json pointer \"{s}\" is malformed due to missing starting slash",
                )
            }
            MalformedPointerError::InvalidEncoding(s) => {
                write!(f, "json pointer \"{s}\" is improperly encoded")
            }
            MalformedPointerError::NotUtf8(err) => {
                write!(f, "json pointer is not UTF-8: {}", err.source)
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for MalformedPointerError {}

/// NotFoundError indicates that a Pointer was not found in the data.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct NotFoundError {
    /// The `Pointer` which could not be resolved.
    pub pointer: Pointer,
}
impl NotFoundError {
    /// Creates a new `NotFoundError` with the given `Pointer`.
    pub fn new(pointer: Pointer) -> Self {
        NotFoundError { pointer }
    }
}
impl Display for NotFoundError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "the resource at json pointer \"{}\" was not found",
            self.pointer
        )
    }
}
#[cfg(feature = "std")]
impl std::error::Error for NotFoundError {}

/// Returned from `Pointer::replace_token` when the provided index is out of
/// bounds.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ReplaceTokenError {
    /// The index of the token that was out of bounds.
    pub index: usize,
    /// The number of tokens in the `Pointer`.
    pub count: usize,
    /// The subject `Pointer`.
    pub pointer: Pointer,
}
#[cfg(feature = "std")]
impl std::error::Error for ReplaceTokenError {}

impl Display for ReplaceTokenError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "index {} is out of bounds ({}) for the pointer {}",
            self.index, self.count, self.pointer
        )
    }
}
