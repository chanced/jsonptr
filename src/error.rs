use core::{
    fmt::{self, Display, Formatter},
    num::ParseIntError,
};

#[derive(Debug)]
// #[snafu(visibility(pub(crate)), module)]
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
    FailedToParseIndex {
        offset: usize,
        source: ParseIndexError,
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
    OutOfBounds {
        /// Offset of the pointer starting with the out of bounds index.
        offset: usize,
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
    NotFound {
        /// Offset of the pointer starting with the `Token` which was not found.
        offset: usize,
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
impl Display for ResolveError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::FailedToParseIndex { offset, .. } => {
                write!(f, "failed to parse index at offset {}", offset)
            }
            Self::OutOfBounds { offset, .. } => {
                write!(f, "index at offset {} out of bounds", offset)
            }
            Self::NotFound { offset, .. } => {
                write!(f, "pointer starting at offset {} not found", offset)
            }
            Self::Unreachable { offset, .. } => {
                write!(f, "pointer starting at offset {} is unreachable", offset)
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ResolveError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::FailedToParseIndex { source, .. } => Some(source),
            Self::OutOfBounds { source, .. } => Some(source),
            _ => None,
        }
    }
}

/// Indicates error occurred during an assignment
#[derive(Debug)]
pub enum AssignError {
    FailedToParseIndex {
        offset: usize,
        source: ParseIndexError,
    },
    OutOfBounds {
        offset: usize,
        source: OutOfBoundsError,
    },
}
impl Display for AssignError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::FailedToParseIndex { offset, .. } => {
                write!(f, "failed to parse index at offset {}", offset)
            }
            Self::OutOfBounds { offset, .. } => {
                write!(f, "index at offset {} out of bounds", offset)
            }
        }
    }
}

/// Indicates that the `Token` could not be parsed as valid RFC 6901 index.
#[derive(Debug)]
pub struct IndexError {
    source: ParseIntError,
}

impl Display for IndexError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
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

impl Display for OutOfBoundsError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "index {} out of bounds (limit: {})",
            self.index, self.length
        )
    }
}
#[cfg(feature = "std")]
impl std::error::Error for OutOfBoundsError {}

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

impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
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
/// NotFoundError indicates that a Pointer's path was not found in the data.
#[derive(Debug)]
pub struct NotFoundError {
    /// The starting offset of the `Token` within the `Pointer` which could not
    /// be resolved.
    pub offset: usize,
}

impl Display for NotFoundError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
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
impl Display for ReplaceTokenError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "index {} is out of bounds ({})", self.index, self.count)
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
impl Display for InvalidEncodingError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
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
pub struct ParseIndexError {
    pub source: ParseIntError,
}
impl From<ParseIntError> for ParseIndexError {
    fn from(source: ParseIntError) -> Self {
        Self { source }
    }
}
impl Display for ParseIndexError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "failed to parse token as an integer")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseIndexError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.source)
    }
}

#[derive(Debug)]
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
    FailedToParseIndex {
        offset: usize,
        source: ParseIndexError,
    },
}

impl Display for DeleteError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::FailedToParseIndex { offset, .. } => {
                write!(f, "failed to parse index at offset {}", offset)
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for DeleteError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::FailedToParseIndex { source, .. } => Some(source),
        }
    }
}
