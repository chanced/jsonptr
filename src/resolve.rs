use crate::{Error, JsonPointer, Token, UnresolvableError};
use serde_json::Value;
use std::{cell::RefCell, mem};

pub trait Resolve {}

fn resolve_token<'v, 't>(
    value: &'v mut Value,
    token: &'t Token,
    ptr: &JsonPointer,
) -> Result<Option<&'v mut Value>, Error> {
    match value {
        Value::Null => Ok(None),
        Value::Number(_) | Value::String(_) | Value::Bool(_) => {
            Err(Error::Unresolvable(UnresolvableError {
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
    }
}
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
    loop {
        if let Some(token) = ptr.pop_front() {
            match resolve_token(value, &token, &ptr) {
                Ok(Some(v)) => value = v,
                Ok(None) => {
                    ptr.push_front(token);
                    break;
                }
                Err(err) => return Err(err),
            };
        } else {
            break;
        }
    }

    Ok((value, ptr))
}
