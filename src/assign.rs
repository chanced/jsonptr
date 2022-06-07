use std::borrow::Cow;

use serde_json::Value;

use crate::{Error, Pointer};

/// Assign is implemented by types which can internally mutate data based on a
/// `serde_json::Value`.
pub trait Assign {
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
    pub assigned_to: Pointer,
}
