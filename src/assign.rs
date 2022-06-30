use std::borrow::Cow;

use serde_json::Value;

use crate::{Error, Pointer};

/// Assign is implemented by types which can internally assign a
/// `serde_json::Value` by a JSON Pointer.
pub trait Assign {
    /// Error associated with `Assign`
    type Error: std::error::Error + Send + Sync + 'static;
    /// Assign a value of based on the path provided by a JSON Pointer.
    fn assign(&mut self, ptr: &Pointer, value: Value) -> Result<Assignment, Self::Error>;
}

impl Assign for Value {
    type Error = Error;
    fn assign(&mut self, ptr: &Pointer, value: Value) -> Result<Assignment, Error> {
        ptr.assign(self, value)
    }
}
#[derive(Debug)]
/// The data structure returned from a successful call to `assign`.
pub struct Assignment<'a> {
    /// The value that was assigned.
    ///
    /// In the event a path is created, this will be the `serde_json::Value`
    /// encompassing the new branch.
    pub assigned: Cow<'a, Value>,

    /// The value that was replaced.
    ///
    /// Note: `serde_json::Value::Null` is utilized if the value did not
    /// previously exist.
    pub replaced: Value,
    /// The path which was created or replaced.
    ///
    /// For example, if you had the json:
    /// ```json
    /// { "foo": { "bar": "baz" } }
    /// ```
    /// and you assigned `"new_value"` to `"/foo/qux/quux"`, then
    /// `created_or_mutated` would be `Some("/foo/qux")` as `"qux"` is the
    /// top-level value assigned.
    ///
    /// The resulting json would have the following structure:
    /// ```json
    /// {
    ///     "foo": {
    ///        "bar": "baz",
    ///         "qux": {
    ///             "quux": "new_value"
    ///         }
    ///     }
    /// }
    /// ```
    ///
    /// Note: if a portion of the path contains a leaf node that is to be
    /// overridden by an object or an array, then the path will be the from the
    /// leaf that is replaced.
    ///
    /// For example, if you had the json:
    /// ```json
    /// { "foo:" "bar" }
    /// ```
    /// and you assigned `"new_value"` to `"/foo/bar/baz"`, then `created` would
    /// be `Some("/foo/bar")` as `"/foo/bar"` is the new path object.
    pub created_or_mutated: Pointer,
    /// A `Pointer` consisting of the path which was assigned.
    ///
    /// ## Example
    /// ```rust
    /// use serde_json::json;
    /// use jsonptr::{Pointer, Assign};
    /// let mut data = json!({ "foo": ["zero"] });
    /// let mut ptr = Pointer::try_from("/foo/-").unwrap();
    /// let assignment = data.assign(&mut ptr, "one".into()).unwrap();
    /// assert_eq!(assignment.assigned_to, Pointer::try_from("/foo/1").unwrap());
    /// ```
    pub assigned_to: Pointer,
}
