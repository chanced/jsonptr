use crate::{Error, JsonPointer, Token, UnresolvableError};
use serde_json::Value;
use std::{cell::RefCell, mem};

pub trait Resolve {}

/// `resolve_mut` resolves a pointer as far as possible. If it encounters an an
/// array without the given index, an object without the given key, or a null
/// value then the pointer is returned at the last resolved location along with
/// the last resolved value.
///
/// If a leaf node is found (`String`, `Number`, `Boolean`) then an error is
/// returned.
///
/// If the resolution is successful, the pointer will be empty.
pub(crate) fn resolve_mut(
    mut value: &mut Value,
    mut ptr: JsonPointer,
) -> Result<(&mut Value, JsonPointer), Error> {
    while let Some(token) = ptr.pop_front() {
        let v = match value {
            Value::Null => Ok(None),
            Value::Number(_) | Value::String(_) | Value::Bool(_) => {
                Err(Error::Unresolvable(UnresolvableError {
                    terminated_at: value.clone(),
                    unresolved: ptr.clone(),
                }))
            }
            Value::Array(arr) => {
                let idx = token.as_index(arr.len(), None)?;
                if let Some(val) = arr.get_mut(idx) {
                    Ok(Some(val))
                } else {
                    Ok(None)
                }
            }
            Value::Object(obj) => {
                if let Some(val) = obj.get_mut(token.as_str()) {
                    Ok(Some(val))
                } else {
                    Ok(None)
                }
            }
        }?;

        match v {
            Some(v) => value = v,
            None => {
                ptr.push_front(token);
                break;
            }
        };
    }
    Ok((value, ptr))
}
