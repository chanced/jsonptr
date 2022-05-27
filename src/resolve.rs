use crate::{Error, Pointer, Token, UnresolvableError};
use serde_json::Value;
use std::ops::ControlFlow;
use std::{cell::RefCell, mem};
pub trait Resolve {}

fn resolve_token<'v, 't>(
    value: &'v mut Value,
    token: &'t Token,
    ptr: &Pointer,
) -> Result<Option<&'v mut Value>, Error> {
    match value {
        Value::Null => Ok(None),
        Value::Number(_) | Value::String(_) | Value::Bool(_) => {
            if ptr.is_root() {
                Err(Error::Unresolvable(UnresolvableError {
                    unresolved: ptr.clone(),
                }))
            } else {
                Ok(Some(value))
            }
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

fn resolve_ptr_mut<'a>(
    acc: Result<(&'a mut Value, Pointer), Error>,
    token: Token,
) -> ControlFlow<
    Result<(&'a mut serde_json::Value, Pointer), Error>,
    Result<(&'a mut serde_json::Value, Pointer), Error>,
> {
    let (cur_val, mut cur_ptr) = acc.unwrap();

    match cur_val {
        Value::Null => {
            cur_ptr.push_back(token);
            ControlFlow::Break(Ok((cur_val, cur_ptr)))
        }

        Value::Number(_) | Value::String(_) | Value::Bool(_) => {
            ControlFlow::Break(Err(Error::Unresolvable(UnresolvableError {
                unresolved: cur_ptr.clone(),
            })))
        }
        Value::Array(_) => {
            let idx = match token.as_index(cur_val.as_array_mut().unwrap().len(), None) {
                Ok(idx) if idx < cur_val.as_array_mut().unwrap().len() => idx,
                Ok(_) => {
                    cur_ptr.push_back(token);
                    return ControlFlow::Break(Ok((cur_val, cur_ptr)));
                }
                Err(e) => return ControlFlow::Break(Err(Error::from(e))),
            };
            cur_ptr.push_back(token);
            ControlFlow::Continue(Ok((
                cur_val.as_array_mut().unwrap().get_mut(idx).unwrap(),
                cur_ptr,
            )))
        }
        Value::Object(_) => {
            if cur_val.as_object_mut().unwrap().contains_key(&*token) {
                cur_ptr.push_back(token.clone());
                ControlFlow::Continue(Ok((
                    cur_val.as_object_mut().unwrap().get_mut(&*token).unwrap(),
                    cur_ptr,
                )))
            } else {
                ControlFlow::Break(Ok((cur_val, cur_ptr)))
            }
        }
    }
}

/// `resolve_mut` resolves a pointer as far as possible. If it encounters an an
/// array without the given index, an object without the given key, or a null
/// value then the pointer is returned at the last resolved location along with
/// the last resolved value.
///
/// If a leaf node is found (`String`, `Number`, `Boolean`) and the pointer is
/// not at the root, an error is returned.
///
/// If the resolution is successful, the pointer will be empty.
pub(crate) fn resolve_mut<'v, 'p>(
    value: &'v mut Value,
    ptr: &'p Pointer,
) -> Result<(&'v mut Value, Pointer), Error> {
    let mut tokens = ptr.tokens();
    tokens.try_fold(Ok((value, Pointer::default())), resolve_ptr_mut);
    todo!()

    // loop {
}
