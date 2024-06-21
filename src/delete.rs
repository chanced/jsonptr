use core::{fmt, mem};

use serde_json::Value;

use crate::{ParseIndexError, Pointer};

/// Delete is implemented by types which can internally remove a value based on
/// a JSON Pointer
pub trait Delete {
    /// Attempts to internally delete a value based upon a [Pointer].
    fn delete(&mut self, ptr: &Pointer) -> Option<Value>;
}

impl Delete for Value {
    fn delete(&mut self, ptr: &Pointer) -> Option<Value> {
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
                    .map(to_string_pretty)
                    .unwrap_or_else(|| "None".to_string()),
                deleted
                    .as_ref()
                    .map(to_string_pretty)
                    .unwrap_or_else(|| "None".to_string())
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
