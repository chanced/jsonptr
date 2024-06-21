#![doc = include_str!("../README.md")]
#![warn(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]
extern crate alloc;

use core::{fmt, num::ParseIntError};

mod pointer;

pub use pointer::*;
mod token;
pub use token::*;
pub mod index;
pub use index::Index;

mod assign;
pub use assign::*;
mod delete;
pub use delete::*;
mod resolve;
pub use resolve::*;

pub mod prelude;

mod tokens;
pub use tokens::*;

#[cfg(test)]
mod arbitrary;

/// Indicates that a `Pointer` was malformed and unable to be parsed.
#[derive(Debug)]
pub enum ParseError {
    /// `Pointer` did not start with a backslash (`'/'`).
    NoLeadingBackslash,

    /// `Pointer` contained invalid encoding (e.g. `~` not followed by `0` or
    /// `1`).
    InvalidEncoding {
        offset: usize,
        source: InvalidEncodingError,
    },
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoLeadingBackslash { .. } => {
                write!(
                    f,
                    "json pointer is malformed as it does not start with a backslash ('/')"
                )
            }
            Self::InvalidEncoding { source, .. } => write!(f, "{}", source),
        }
    }
}
impl ParseError {
    pub fn is_no_leading_backslash(&self) -> bool {
        matches!(self, Self::NoLeadingBackslash { .. })
    }
    pub fn is_invalid_encoding(&self) -> bool {
        matches!(self, Self::InvalidEncoding { .. })
    }
    pub fn offset(&self) -> usize {
        match *self {
            Self::NoLeadingBackslash { .. } => 0,
            Self::InvalidEncoding { offset, .. } => offset,
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::InvalidEncoding { source, .. } => Some(source),
            _ => None,
        }
    }
}

/// Indicates that the `Token` could not be parsed as valid RFC 6901 index.
#[derive(Debug)]
pub struct ParseIndexError {
    pub source: ParseIntError,
}
impl From<ParseIntError> for ParseIndexError {
    fn from(source: ParseIntError) -> Self {
        Self { source }
    }
}
impl fmt::Display for ParseIndexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "failed to parse token as an integer")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseIndexError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.source)
    }
}

/// A token within a json pointer contained invalid encoding (`~` not followed
/// by `0` or `1`).
///
#[derive(Debug)]
pub struct InvalidEncodingError {
    /// offset of the erroneous `~` from within the `Token`
    pub offset: usize,
}
impl InvalidEncodingError {
    /// The byte offset of the first invalid `~`.
    pub fn offset(&self) -> usize {
        self.offset
    }
}
impl fmt::Display for InvalidEncodingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "json pointer is malformed due to invalid encoding ('~' not followed by '0' or '1')"
        )
    }
}

#[cfg(feature = "std")]
impl std::error::Error for InvalidEncodingError {}

/// Indicates that the `Token` could not be parsed as valid RFC 6901 index.
#[derive(Debug)]
pub struct IndexError {
    source: ParseIntError,
}

impl core::fmt::Display for IndexError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "failed to parse token as an integer")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for IndexError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.source)
    }
}

/// Indicates that an `Index` is not within the given bounds.
#[derive(Debug)]
pub struct OutOfBoundsError {
    /// The provided array length.
    ///
    /// If the range is inclusive, the resolved numerical index will be strictly
    /// less than this value, otherwise it could be equal to it.
    pub length: usize,

    /// The resolved numerical index.
    ///
    /// Note that [`Index::Next`] always resolves to the given array length,
    /// so it is only valid when the range is inclusive.
    pub index: usize,
}

impl fmt::Display for OutOfBoundsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "index {} out of bounds (limit: {})",
            self.index, self.length
        )
    }
}
#[cfg(feature = "std")]
impl std::error::Error for OutOfBoundsError {}

/// NotFoundError indicates that a Pointer's path was not found in the data.
#[derive(Debug)]
pub struct NotFoundError {
    /// The starting offset of the `Token` within the `Pointer` which could not
    /// be resolved.
    pub offset: usize,
}

impl fmt::Display for NotFoundError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "path starting at offset {} not found", self.offset)
    }
}
#[cfg(feature = "std")]
impl std::error::Error for NotFoundError {}

/// Returned from `Pointer::replace_token` when the provided index is out of
/// bounds.
#[derive(Debug)]
pub struct ReplaceTokenError {
    /// The index of the token that was out of bounds.
    pub index: usize,
    /// The number of tokens in the `Pointer`.
    pub count: usize,
}
impl fmt::Display for ReplaceTokenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "index {} is out of bounds ({})", self.index, self.count)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ReplaceTokenError {}
