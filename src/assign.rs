// use std::{borrow::Cow, ops::Deref};

// use serde_json::Value;

// use crate::{tokens, try_resolve_mut, Error, Pointer, Token};

// /// Assign is implemented by types which can internally mutate data based on a
// /// `serde_json::Value`.
// pub trait Assign {
//     /// Assign a value of based on the path provided by a JSON Pointer.
//     fn assign(&mut self, ptr: &Pointer, value: Value) -> Result<Assignment, Error>;
// }

// pub struct Assignment<'a> {
//     /// The value that was assigned.
//     pub assigned_value: Cow<'a, Value>,
//     /// The value that was replaced, if it exists.
//     pub previous_value: Cow<'a, Value>,
//     /// If the assignment requires that a path be created, this is that path.
//     ///
//     /// For example, if you had the json:
//     /// ```json
//     /// { "foo": { "bar": "baz" } }
//     /// ```
//     /// and you assigned `"new_value"` to `"/foo/qux/quux"`, then `created_path`
//     /// would be `Some("/qux/quux")` and the json would have the structure:
//     /// ```json
//     /// {
//     ///     "foo": {
//     ///        "bar": "baz",
//     ///         "qux": {
//     ///             "quux": "new_value"
//     ///         }
//     ///     }
//     /// }
//     /// ```
//     ///
//     pub created_path: Option<Pointer>,
// }
