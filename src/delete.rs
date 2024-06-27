//! # Delete values based on JSON Pointers
//!
//! This module provides the [`Delete`] trait which is implemented by types that
//! can internally remove a value based on a JSON Pointer.
//!
//! ## Provided implementations
//! | Lang  |       value type      | feature flag |
//! | ----- |: ------------------- :|: ---------- :|
//! | JSON  | [`serde_json::Value`] |   `"json"`   |
//! | TOML  |     `toml::Value`     |   `"toml"`   |
//!
//! The rules of deletion are determined by the implementation, with the
//! provided implementations (`"json"` & `"toml"`) operating as follows:
//! - If the [`Pointer`] can be resolved, then the [`Value`](`Delete::Value`) is
//!   deleted and returned as `Some(value)`.
//! - If the [`Pointer`] fails to resolve for any reason, `Ok(None)` is
//!   returned.
//! - If the [`Pointer`] is root, `value` is replaced:
//!     - `"json"`: `serde_json::Value::Null`
//!     - `"toml`: `toml::Value::Table::Default`
//!
//! ## Examples
//! ### Deleting a resolved pointer:
//! ```rust
//! use jsonptr::{Pointer, delete::Delete};
//! use serde_json::json;
//!
//! let mut data = json!({ "foo": { "bar": { "baz": "qux" } } });
//! let ptr = Pointer::from_static("/foo/bar/baz");
//! assert_eq!(data.delete(&ptr), Some("qux".into()));
//! assert_eq!(data, json!({ "foo": { "bar": {} } }));
//! ```
//! ### Deleting a non-existent Pointer returns `None`:
//! ```rust
//! use jsonptr::{ Pointer, delete::Delete };
//! use serde_json::json;
//!
//! let mut data = json!({});
//! let ptr = Pointer::from_static("/foo/bar/baz");
//! assert_eq!(ptr.delete(&mut data), None);
//! assert_eq!(data, json!({}));
//! ```
//! ### Deleting a root pointer replaces the value with `Value::Null`:
//! ```rust
//! use jsonptr::{Pointer, delete::Delete};
//! use serde_json::json;
//!
//! let mut data = json!({ "foo": { "bar": "baz" } });
//! let ptr = Pointer::root();
//! assert_eq!(data.delete(&ptr), Some(json!({ "foo": { "bar": "baz" } })));
//! assert!(data.is_null());
//! ```
use crate::Pointer;

/// Delete is implemented by types which can internally remove a value based on
/// a JSON Pointer
///
/// Provided implementations include:
///
/// | Language  | Feature Flag |
/// | --------- | ------------ |
/// |   JSON    |   `"json"`   |
/// |   TOML    |   `"toml"`   |
pub trait Delete {
    /// The type of value that this implementation can operate on.
    ///
    /// Provided implementations include:
    ///
    /// | Lang  |     value type      | feature flag |
    /// | ----- |: ----------------- :|: ---------- :|
    /// | JSON  | `serde_json::Value` |   `"json"`   |
    /// | TOML  |    `toml::Value`    |   `"toml"`   |
    type Value;

    /// Attempts to internally delete a value based upon a [Pointer].
    fn delete(&mut self, ptr: &Pointer) -> Option<Self::Value>;
}

mod json {
    use super::Delete;
    use crate::Pointer;
    use core::mem;
    use serde_json::Value;

    impl Delete for Value {
        type Value = Value;
        fn delete(&mut self, ptr: &Pointer) -> Option<Self::Value> {
            let Some((parent_ptr, last)) = ptr.split_back() else {
                // deleting at root
                return Some(mem::replace(self, Value::Null));
            };
            parent_ptr
                .resolve_mut(self)
                .ok()
                .and_then(|parent| match parent {
                    Value::Array(children) => {
                        let idx = last.to_index().ok()?.for_len_incl(children.len()).ok()?;
                        children.remove(idx).into()
                    }
                    Value::Object(children) => children.remove(last.decoded().as_ref()),
                    _ => None,
                })
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use serde_json::json;
        #[test]
        fn test_delete_value() {
            let tests = [
                (json!({"foo": "bar"}), "/foo", json!({}), Some(json!("bar"))),
                (
                    json!({"foo": "bar"}), // data
                    "/foo/bar",            // ptr
                    json!({"foo": "bar"}), // expected_data
                    None,                  // expected_deleted
                ),
                (
                    json!({"foo": {"bar": "baz"}}), // data
                    "/foo/bar",                     // ptr
                    json!({"foo": {}}),             // expected_data
                    Some(json!("baz")),             // expected_deleted
                ),
                (
                    json!({"foo": {"bar": ["baz", "qux"]}}), // data
                    "/foo/bar/0",                            // ptr
                    json!({"foo": {"bar": ["qux"]}}),        // expected_data
                    Some(json!("baz")),                      // expected_deleted
                ),
                (json!({"foo": "bar"}), "/foo/0", json!({"foo": "bar"}), None),
                (
                    json!({"foo": { "bar": [{"baz": "qux", "remaining": "field"}]}}),
                    "/foo/bar/0/baz",
                    json!({"foo": { "bar": [{"remaining": "field"}]}}),
                    Some(json!("qux")),
                ),
            ];
            for (mut data, ptr, expected_data, expected_deleted) in tests {
                let ptr = Pointer::from_static(ptr);
                let deleted = ptr.delete(&mut data);
                assert_eq!(
                    expected_data,
                    data,
                    "\ndata not as expected
                \nptr: \"{ptr}\"
                \ndata:\n{}
                \nexpected:\n{}
                \nactual:\n{}\n\n",
                    to_string_pretty(&data),
                    to_string_pretty(&expected_data),
                    to_string_pretty(&data)
                );
                assert_eq!(
                    expected_deleted,
                    deleted,
                    "\ndeleted value not as expected
                \nexpected:{}\n\nactual:{}\n\n",
                    expected_deleted
                        .as_ref()
                        .map_or_else(|| "None".to_string(), to_string_pretty),
                    deleted
                        .as_ref()
                        .map_or_else(|| "None".to_string(), to_string_pretty)
                );
            }
        }

        #[test]
        fn test_issue_18() {
            let mut data = json!({
                "Example": 21,
                "test": "test"
            });
            let pointer = Pointer::from_static("/Example");
            pointer.delete(&mut data);
            assert_eq!(json!({"test": "test"}), data);
        }

        fn to_string_pretty(value: &Value) -> String {
            serde_json::to_string_pretty(value).unwrap()
        }
    }
}

#[cfg(feature = "toml")]
mod toml {
    use super::Delete;
    use crate::Pointer;
    use core::mem;
    use toml::{Table, Value};

    impl Delete for Value {
        type Value = Value;
        fn delete(&mut self, ptr: &Pointer) -> Option<Self::Value> {
            let Some((parent_ptr, last)) = ptr.split_back() else {
                // deleting at root
                return Some(mem::replace(self, Table::default().into()));
            };
            parent_ptr
                .resolve_mut(self)
                .ok()
                .and_then(|parent| match parent {
                    Value::Array(children) => {
                        let idx = last.to_index().ok()?.for_len_incl(children.len()).ok()?;
                        children.remove(idx).into()
                    }
                    Value::Table(children) => children.remove(last.decoded().as_ref()),
                    _ => None,
                })
        }
    }

    #[cfg(test)]
    mod tests {
        use toml::{toml, Table, Value};

        use crate::Pointer;

        struct Test {
            data: Value,
            ptr: &'static str,
            expected_data: Value,
            expected_deleted: Option<Value>,
        }

        #[test]
        fn test_delete_value() {
            let tests = [
                Test {
                    data: toml! {"foo" = "bar"}.into(),
                    ptr: "/foo",
                    expected_data: Table::new().into(),
                    expected_deleted: Some("bar".into()),
                },
                Test {
                    data: toml! {"foo" = "bar"}.into(),
                    ptr: "/foo/bar",
                    expected_data: toml! {"foo" = "bar"}.into(),
                    expected_deleted: None,
                },
                Test {
                    data: toml! {"foo" = {"bar" = "baz"}}.into(),
                    ptr: "/foo/bar",
                    expected_data: toml! {"foo" = {}}.into(),
                    expected_deleted: Some("baz".into()),
                },
                Test {
                    data: toml! {"foo" = {"bar" = ["baz", "qux"]}}.into(),
                    ptr: "/foo/bar/0",
                    expected_data: toml! {"foo"={"bar"=["qux"]}}.into(),
                    expected_deleted: Some("baz".into()),
                },
                Test {
                    data: toml! {"foo" = "bar"}.into(),
                    ptr: "/foo/0",
                    expected_data: toml! {"foo"="bar"}.into(),
                    expected_deleted: None,
                },
                Test {
                    data: toml! {"foo"={"bar"=[{"baz"="qux","remaining"="field"}]}}.into(),
                    ptr: "/foo/bar/0/baz",
                    expected_data: toml! {"foo"={"bar"=[{"remaining"="field"}]}}.into(),
                    expected_deleted: Some("qux".into()),
                },
            ];
            for Test {
                mut data,
                ptr,
                expected_data,
                expected_deleted,
            } in tests
            {
                let ptr = Pointer::from_static(ptr);
                let deleted = ptr.delete(&mut data);
                assert_eq!(
                    expected_data,
                    data,
                    "\ndata not as expected
                \nptr: \"{ptr}\"
                \ndata:\n{}
                \nexpected:\n{}
                \nactual:\n{}\n\n",
                    to_string_pretty(&data),
                    to_string_pretty(&expected_data),
                    to_string_pretty(&data)
                );
                assert_eq!(
                    expected_deleted,
                    deleted,
                    "\ndeleted value not as expected
                \nexpected:{}\n\nactual:{}\n\n",
                    expected_deleted
                        .as_ref()
                        .map_or_else(|| "None".to_string(), to_string_pretty),
                    deleted
                        .as_ref()
                        .map_or_else(|| "None".to_string(), to_string_pretty)
                );
            }
        }

        fn to_string_pretty(value: &Value) -> String {
            toml::to_string_pretty(value).unwrap()
        }
    }
}
