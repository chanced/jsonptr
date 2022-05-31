use crate::{Error, Pointer, Token, UnresolvableError};
use serde_json::Value;
use std::ops::ControlFlow;
pub trait Resolve {}

/// `resolve_mut` resolves a pointer as far as possible. If it encounters an an
/// array without the given index, an object without the given key, or a null
/// value then the pointer is returned at the last resolved location along with
/// the last resolved value.
///
/// If a leaf node is found (`String`, `Number`, `Boolean`) and the pointer is
/// not at the root, an error is returned.
///
/// If the resolution is successful, the pointer will be empty.
pub(crate) fn try_resolve_mut<'v, 'p>(
    value: &'v mut Value,
    pointer: &'p Pointer,
) -> Result<(&'v mut Value, Pointer), Error> {
    let mut tokens = pointer.tokens();
    let res = tokens.try_fold((value, pointer.clone()), |(v, mut p), token| match v {
        Value::Null => ControlFlow::Break((v, p)),
        Value::Number(_) | Value::String(_) | Value::Bool(_) => ControlFlow::Break((v, p)),
        Value::Array(_) => match token.as_index(v.as_array_mut().unwrap().len()) {
            Ok(idx) => {
                if idx < v.as_array_mut().unwrap().len() {
                    p.pop_front();
                    ControlFlow::Continue((v.as_array_mut().unwrap().get_mut(idx).unwrap(), p))
                } else {
                    ControlFlow::Break((v, p))
                }
            }
            Err(_) => ControlFlow::Break((v, p)),
        },
        Value::Object(_) => {
            if v.as_object_mut().unwrap().contains_key(&*token) {
                p.pop_front();
                ControlFlow::Continue((v.as_object_mut().unwrap().get_mut(&*token).unwrap(), p))
            } else {
                ControlFlow::Break((v, p))
            }
        }
    });
    match res {
        ControlFlow::Continue((v, p)) => Ok((v, p)),
        ControlFlow::Break((v, p)) => match v {
            Value::Null | Value::Object(_) => Ok((v, p)),
            Value::Array(_) => match p.first() {
                Some(i) => {
                    let len = v.as_array().unwrap().len();
                    let idx = i.as_index(len)?;
                    if idx <= len {
                        Ok((v, p))
                    } else {
                        Err(UnresolvableError::new(p).into())
                    }
                }
                None => Ok((v, p)),
            },
            Value::Bool(_) | Value::Number(_) | Value::String(_) => {
                Err(UnresolvableError::new(p).into())
            }
        },
    }
}

#[cfg(test)]
mod test {
    use serde_json::json;

    use crate::{try_resolve_mut, Pointer};

    #[test]
    fn test_try_resolve_mut() {
        let mut data = json!({
            "foo": {
                "bar": {
                    "baz": {
                        "qux": "quux"
                    }
                },
                "strings": ["zero", "one", "two"],
                "nothing": null,
                "boolean": true,
                "objects": [{
                    "field": "zero"
                }, {
                    "field": "one"
                }, {
                    "field": "two"
                }]

            }
        });
        let ptr = Pointer::try_from("/foo/bar/baz/qux").unwrap();
        let (val_res, ptr_res) = try_resolve_mut(&mut data, &ptr).unwrap();
        assert_eq!(&ptr_res, "/");
        assert_eq!(val_res, &mut json!("quux"));

        let ptr = Pointer::try_from("/foo/bar/does_not_exist/derp").unwrap();
        let (val_res, ptr_res) = try_resolve_mut(&mut data, &ptr).unwrap();
        assert_eq!(ptr_res, "/does_not_exist/derp");

        assert_eq!(
            val_res,
            &mut json!({
                "baz": {
                    "qux": "quux"
                }
            })
        );

        let ptr = Pointer::try_from("/foo/strings/0").unwrap();
        let (val_res, ptr_res) = try_resolve_mut(&mut data, &ptr).unwrap();
        assert_eq!(ptr_res, "/");
        assert_eq!(val_res, &mut json!("zero"));

        let ptr = Pointer::try_from("/foo/strings/1").unwrap();
        let (val_res, ptr_res) = try_resolve_mut(&mut data, &ptr).unwrap();
        assert_eq!(ptr_res, "/");
        assert_eq!(val_res, &mut json!("one"));

        let ptr = Pointer::try_from("/foo/strings/2").unwrap();
        let (val_res, ptr_res) = try_resolve_mut(&mut data, &ptr).unwrap();
        assert_eq!(ptr_res, "/");
        assert_eq!(val_res, &mut json!("two"));

        let ptr = Pointer::try_from("/foo/strings/-").unwrap();
        let (val_res, ptr_res) = try_resolve_mut(&mut data, &ptr).unwrap();
        assert_eq!(ptr_res, "/-");
        assert_eq!(val_res, &mut json!(["zero", "one", "two"]));

        let ptr = Pointer::try_from("/foo/strings/0").unwrap();
        let (val_res, ptr_res) = try_resolve_mut(&mut data, &ptr).unwrap();
        assert_eq!(ptr_res, "/");
        assert_eq!(val_res, &mut json!("zero"));

        // let ptr = Pointer::try_from("/foo/strings/7").unwrap();
        // let res = try_resolve_mut(&mut data, &ptr);
        // assert!(res.is_err());

        // assert_eq!(val_res, &mut json!("zero"));
    }
}
