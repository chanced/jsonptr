use crate::PointerBuf;
use core::num::ParseIntError;
use snafu::{Backtrace, Snafu};

#[derive(Debug, Snafu)]
#[snafu(visibility(pub(crate)), module)]
pub enum ResolveError {
    /// `Pointer` could not be resolved because a `Token` for an array index is
    /// not a valid integer or dash (`"-"`).
    ///
    /// ## Example
    /// ```rust
    /// # use serde_json::json;
    /// # use jsonptr::Pointer;
    /// let data = json!({ "foo": ["bar"] });
    /// let ptr = Pointer::from_static("/foo/invalid");
    /// assert!(ptr.resolve(&data).unwrap_err().is_failed_to_parse_index());
    /// ```
    #[snafu(display("failed to parse index at offset {offset}"))]
    FailedToParseIndex {
        offset: usize,
        source: ParseIndexError,
        backtrace: Backtrace,
    },
    /// `Pointer` could not be resolved due to an index being out of bounds
    /// within an array.
    ///
    /// ## Example
    /// ```rust
    /// # use serde_json::json;
    /// # use jsonptr::Pointer;
    /// let data = json!({ "foo": ["bar"] });
    /// let ptr = Pointer::from_static("/foo/1");
    /// assert!(ptr.resolve(&data).unwrap_err().is_out_of_bounds());
    #[snafu(display("index at offset {offset} out of bounds"))]
    OutOfBounds {
        /// Offset of the pointer starting with the out of bounds index.
        offset: usize,
        #[snafu(backtrace)]
        source: OutOfBoundsError,
    },

    /// `Pointer` could not be resolved as a segment of the path was not found.
    ///
    /// ## Example
    /// ```rust
    /// # use serde_json::json;
    /// # use jsonptr::{Pointer};
    /// let mut data = json!({ "foo": "bar" });
    /// let ptr = Pointer::from_static("/bar");
    /// assert!(ptr.resolve(&data).unwrap_err().is_not_found());
    /// ```
    #[snafu(display("pointer starting at offset {offset} not found"))]
    NotFound {
        /// Offset of the pointer starting with the `Token` which was not found.
        offset: usize,
        /// The backtrace of the error.
        backtrace: Backtrace,
    },

    /// `Pointer` could not be resolved as the path contains a scalar value
    /// before fully exhausting the path.
    ///
    /// ## Example
    /// ```rust
    /// # use serde_json::json;
    /// # use jsonptr::Pointer;
    /// let mut data = json!({ "foo": "bar" });
    /// let ptr = Pointer::from_static("/foo/unreachable");
    /// assert!(ptr.resolve(&data).unwrap_err(), err.is_unreachable());
    /// ```
    Unreachable {
        /// Offset of the pointer which was unreachable.
        offset: usize,
        /// The backtrace of the error.
        backtrace: Backtrace,
    },
}
impl ResolveError {
    pub fn offset(&self) -> usize {
        match self {
            Self::FailedToParseIndex { offset, .. }
            | Self::OutOfBounds { offset, .. }
            | Self::NotFound { offset, .. }
            | Self::Unreachable { offset, .. } => *offset,
        }
    }
    pub fn is_unreachable(&self) -> bool {
        matches!(self, Self::Unreachable { .. })
    }
    pub fn is_not_found(&self) -> bool {
        matches!(self, Self::NotFound { .. })
    }
    pub fn is_out_of_bounds(&self) -> bool {
        matches!(self, Self::OutOfBounds { .. })
    }
    pub fn is_failed_to_parse_index(&self) -> bool {
        matches!(self, Self::FailedToParseIndex { .. })
    }
}

/// Indicates error occurred during an assignment
#[derive(Debug, Snafu)]
#[snafu(visibility(pub(crate)), module)]
pub enum AssignError {
    #[snafu(display("failed to parse index at offset {offset}"))]
    FailedToParseIndex {
        offset: usize,
        source: ParseIndexError,
        backtrace: Backtrace,
    },
    #[snafu(display("index at offset {offset} out of bounds"))]
    OutOfBounds {
        offset: usize,
        #[snafu(backtrace)]
        source: OutOfBoundsError,
    },
}

/// Indicates that the `Token` could not be parsed as valid RFC 6901 index.
#[derive(Debug, Snafu)]
#[snafu(display("failed to parse token as an integer"))]
pub struct IndexError {
    source: ParseIntError,
    backtrace: Backtrace,
}

/// Indicates that an `Index` is not within the given bounds.
#[derive(Debug, Snafu)]
#[snafu(
    visibility(pub(crate)),
    display("index {index} out of bounds (limit: {length})")
)]
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

    /// The backtrace of the error.
    pub backtrace: Backtrace,
}

/// Indicates that a `Pointer` was malformed and unable to be parsed.
#[derive(Debug, Snafu)]
#[snafu(visibility(pub(crate)), module)]
pub enum ParseError {
    /// `Pointer` did not start with a backslash (`'/'`).
    #[snafu(display("json pointer is malformed as it does not start with a backslash ('/')"))]
    NoLeadingBackslash { backtrace: Backtrace },

    /// `Pointer` contained invalid encoding (e.g. `~` not followed by `0` or
    /// `1`).
    #[snafu(transparent)]
    InvalidEncoding { source: InvalidEncodingError },
}

impl ParseError {
    pub fn is_no_leading_backslash(&self) -> bool {
        matches!(self, Self::NoLeadingBackslash { .. })
    }
    pub fn is_invalid_encoding(&self) -> bool {
        matches!(self, Self::InvalidEncoding { .. })
    }
    pub fn offset(&self) -> usize {
        match self {
            Self::NoLeadingBackslash { .. } => 0,
            Self::InvalidEncoding { source } => source.offset(),
        }
    }
}
/// NotFoundError indicates that a Pointer's path was not found in the data.
#[derive(Debug, Snafu)]
#[snafu(display("the resource at json pointer \"{pointer}\" was not found"))]
pub struct NotFoundError {
    /// The path which could not be resolved.
    pub pointer: PointerBuf,
    pub backtrace: Backtrace,
}

/// Returned from `Pointer::replace_token` when the provided index is out of
/// bounds.
#[derive(Debug, Snafu)]
#[snafu(display("index {index} is out of bounds ({count})"))]
pub struct ReplaceTokenError {
    /// The index of the token that was out of bounds.
    pub index: usize,
    /// The number of tokens in the `Pointer`.
    pub count: usize,
}

/// A token within a json pointer contained invalid encoding (`~` not followed
/// by `0` or `1`).
///
#[derive(Debug, Snafu)]
#[snafu(
    visibility(pub(crate)),
    display("json pointer is malformed due to invalid encoding ('~' not followed by '0' or '1')")
)]
pub struct InvalidEncodingError {
    /// offset of the erroneous `~`
    offset: usize,
    backtrace: Backtrace,
}
impl InvalidEncodingError {
    /// The byte offset of the first invalid `~`.
    pub fn offset(&self) -> usize {
        self.offset
    }
}

/// Indicates that the `Token` could not be parsed as valid RFC 6901 index.
#[derive(Debug, Snafu)]
#[snafu(transparent)]
pub struct ParseIndexError {
    source: ParseIntError,
    backtrace: Backtrace,
}

#[derive(Debug, Snafu)]
pub enum DeleteError {
    /// `Value` at `Pointer` could not be because a `Token` for an array index
    /// is not a valid integer or dash (`"-"`).
    ///
    /// ## Example
    /// ```rust
    /// # use serde_json::json;
    /// # use jsonptr::Pointer;
    /// let data = json!({ "foo": ["bar"] });
    /// let ptr = Pointer::from_static("/foo/invalid");
    /// assert!(ptr.resolve(&data).unwrap_err().is_failed_to_parse_index());
    /// ```
    #[snafu(display("failed to parse index at offset {offset}"))]
    FailedToParseIndex {
        offset: usize,
        source: ParseIndexError,
        backtrace: Backtrace,
    },
}
