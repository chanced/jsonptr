use super::ResolvedMut;
use crate::{Error, MalformedPointerError, Pointer, Resolve, ResolveMut, UnresolvableError};
use serde_json::{json, Value};
#[test]
fn test_rfc_examples() {
    let data = json!({
        "foo": ["bar", "baz"],
        "": 0,
        "a/b": 1,
        "c%d": 2,
        "e^f": 3,
        "g|h": 4,
        "i\\j": 5,
        "k\"l": 6,
        " ": 7,
        "m~n": 8
    });

    let val = data.get("").unwrap();
    assert_eq!(val, 0);

    // ""           // the whole document
    let ptr = Pointer::default();
    assert_eq!(data.resolve(&ptr).unwrap(), &data);

    // "/foo"       ["bar", "baz"]
    let ptr = Pointer::try_from("/foo").unwrap();

    assert_eq!(data.resolve(&ptr).unwrap(), &json!(["bar", "baz"]));

    // "/foo/0"     "bar"
    let ptr = Pointer::try_from("/foo/0").unwrap();
    assert_eq!(data.resolve(&ptr).unwrap(), &json!("bar"));

    // // "/"          0
    let ptr = Pointer::try_from("/").unwrap();
    assert_eq!(data.resolve(&ptr).unwrap(), &json!(0));

    // "/a~1b"      1
    assert_eq!(data.get("a/b").unwrap(), 1);
    let ptr = Pointer::try_from("/a~1b").unwrap();
    assert_eq!(ptr.as_str(), "/a~1b");
    assert_eq!(data.get("a/b").unwrap(), 1);
    assert_eq!(&ptr.first().unwrap(), "a/b");
    assert_eq!(data.resolve(&ptr).unwrap(), &json!(1));

    // "/c%d"       2
    let ptr = Pointer::try_from("/c%d").unwrap();
    assert_eq!(data.resolve(&ptr).unwrap(), &json!(2));

    // // "/e^f"       3
    let ptr = Pointer::try_from("/e^f").unwrap();
    assert_eq!(data.resolve(&ptr).unwrap(), &json!(3));

    // // "/g|h"       4
    let ptr = Pointer::try_from("/g|h").unwrap();
    assert_eq!(data.resolve(&ptr).unwrap(), &json!(4));

    // "/i\\j"      5
    let ptr = Pointer::try_from("/i\\j").unwrap();
    assert_eq!(data.resolve(&ptr).unwrap(), &json!(5));

    // // "/k\"l"      6
    let ptr = Pointer::try_from("/k\"l").unwrap();
    assert_eq!(data.resolve(&ptr).unwrap(), &json!(6));

    // // "/ "         7
    let ptr = Pointer::try_from("/ ").unwrap();
    assert_eq!(data.resolve(&ptr).unwrap(), &json!(7));
    // // "/m~0n"      8
    let ptr = Pointer::try_from("/m~0n").unwrap();
    assert_eq!(data.resolve(&ptr).unwrap(), &json!(8));
}

#[test]
fn test_try_from_validation() {
    assert!(Pointer::try_from("").is_ok());
    assert!(Pointer::try_from("/").is_ok());
    assert!(Pointer::try_from("/foo").is_ok());

    let res = Pointer::try_from("/foo~");
    assert!(res.is_err());
    let err = res.unwrap_err();
    assert_eq!(
        err,
        MalformedPointerError::InvalidEncoding("/foo~".to_string())
    );

    let res = Pointer::try_from("foo");
    assert!(res.is_err());
    let err = res.unwrap_err();
    assert_eq!(
        err,
        MalformedPointerError::NoLeadingSlash("foo".to_string())
    );

    assert!(Pointer::try_from("/foo/bar/baz/~1/~0").is_ok());

    assert_eq!(
        &Pointer::try_from("/foo/bar/baz/~1/~0").unwrap(),
        "/foo/bar/baz/~1/~0"
    );
}

#[test]
fn test_push_pop_back() {
    let mut ptr = Pointer::default();
    assert_eq!(ptr, "", "default, root pointer should equal \"\"");
    assert_eq!(ptr.count(), 0, "default pointer should have 0 tokens");

    ptr.push_back("foo".into());
    assert_eq!(ptr, "/foo", "pointer should equal \"/foo\" after push_back");

    ptr.push_back("bar".into());
    assert_eq!(
        ptr, "/foo/bar",
        "pointer should equal \"/foo/bar\" after push_back"
    );
    ptr.push_back("/baz".into());
    assert_eq!(
        ptr, "/foo/bar/~1baz",
        "pointer should equal \"/foo/bar/~1baz\" after push_back"
    );
}

#[test]
fn test_replace_token() {
    let mut ptr = Pointer::try_from("/test/token").unwrap();

    let res = ptr.replace_token(0, "new".into());
    assert!(res.is_ok());
    assert_eq!(
        ptr, "/new/token",
        "pointer should equal \"/new/token\" after replace_token"
    );

    let res = ptr.replace_token(3, "invalid".into());

    assert!(res.is_err());
}

#[test]
fn test_push_pop_front() {
    let mut ptr = Pointer::default();
    assert_eq!(ptr, "");
    assert_eq!(ptr.count(), 0);
    ptr.push_front("bar".into());
    assert_eq!(ptr, "/bar");
    assert_eq!(ptr.count(), 1);

    ptr.push_front("foo".into());
    assert_eq!(ptr, "/foo/bar");
    assert_eq!(ptr.count(), 2);

    ptr.push_front("too".into());
    assert_eq!(ptr, "/too/foo/bar");
    assert_eq!(ptr.count(), 3);

    assert_eq!(ptr.pop_front(), Some("too".into()));
    assert_eq!(ptr, "/foo/bar");
    assert_eq!(ptr.count(), 2);

    assert_eq!(ptr.pop_back(), Some("bar".into()));
    assert_eq!(ptr, "/foo");
    assert_eq!(ptr.count(), 1);

    ptr.pop_front();
}

#[test]
fn test_formatting() {
    assert_eq!(Pointer::new(&["foo", "bar"]), "/foo/bar");
    assert_eq!(
        Pointer::new(&["~/foo", "~bar", "/baz"]),
        "/~0~1foo/~0bar/~1baz"
    );
    assert_eq!(Pointer::new(&["field", "", "baz"]), "/field//baz");
    assert_eq!(Pointer::default(), "");
}

#[test]
fn test_last() {
    let ptr = Pointer::try_from("/foo/bar").unwrap();

    assert_eq!(ptr.last(), Some("bar".into()));

    let ptr = Pointer::try_from("/foo/bar/-").unwrap();
    assert_eq!(ptr.last(), Some("-".into()));

    let ptr = Pointer::try_from("/-").unwrap();
    assert_eq!(ptr.last(), Some("-".into()));
}
#[test]
fn test_first() {
    let ptr = Pointer::try_from("/foo/bar").unwrap();
    assert_eq!(ptr.first(), Some("foo".into()));

    let ptr = Pointer::try_from("/foo/bar/-").unwrap();
    assert_eq!(ptr.first(), Some("foo".into()));

    let ptr = Pointer::default();
    assert_eq!(ptr.first(), None);
}

fn test_data() -> serde_json::Value {
    json!({
        "foo": {
            "bar": {
                "baz": {
                    "qux": "quux"
                }
            },
            "strings": ["zero", "one", "two"],
            "nothing": null,
            "bool": true,
            "objects": [{
                "field": "zero"
            }, {
                "field": "one"
            }, {
                "field": "two"
            }]
        }
    })
}

#[test]
fn test_try_resolve_mut() {
    let mut data = test_data();
    let ptr = Pointer::try_from("/foo/bar/baz/qux").unwrap();
    let ResolvedMut {
        value,
        remaining,
        resolved: _resolved,
    } = ptr.try_resolve_mut(&mut data).unwrap();
    assert_eq!(&remaining, "");
    assert_eq!(value, &mut json!("quux"));

    let ptr = Pointer::try_from("/foo/bar/does_not_exist/derp").unwrap();
    let ResolvedMut {
        value,
        remaining,
        resolved: _resolved,
    } = ptr.try_resolve_mut(&mut data).unwrap();
    assert_eq!(remaining, "/does_not_exist/derp");

    assert_eq!(
        value,
        &mut json!({
            "baz": {
                "qux": "quux"
            }
        })
    );

    let ptr = Pointer::try_from("/foo/strings/0").unwrap();
    let res = ptr.try_resolve_mut(&mut data).unwrap();
    assert_eq!(res.remaining, "");
    assert_eq!(res.value, &mut json!("zero"));

    let ptr = Pointer::try_from("/foo/strings/1").unwrap();
    let res = ptr.try_resolve_mut(&mut data).unwrap();
    assert_eq!(res.remaining, "");
    assert_eq!(res.value, &mut json!("one"));

    let ptr = Pointer::try_from("/foo/strings/2").unwrap();
    let res = ptr.try_resolve_mut(&mut data).unwrap();
    assert_eq!(res.remaining, "");
    assert_eq!(res.value, &mut json!("two"));

    let ptr = Pointer::try_from("/foo/strings/-").unwrap();
    let res = ptr.try_resolve_mut(&mut data).unwrap();
    assert_eq!(res.remaining, "/-");
    assert_eq!(res.value, &mut json!(["zero", "one", "two"]));

    let ptr = Pointer::try_from("/foo/strings/0").unwrap();
    let res = ptr.try_resolve_mut(&mut data).unwrap();
    assert_eq!(res.remaining, "");
    assert_eq!(res.value, &mut json!("zero"));
}

#[test]
fn test_try_resolve_mut_overflow_error() {
    let mut data = test_data();
    let ptr = Pointer::try_from("/foo/strings/7").unwrap();
    let res = ptr.try_resolve_mut(&mut data);
    assert!(res.is_err());
}
#[test]
fn test_resolve_unresolvable() {
    let mut data = test_data();
    let ptr = Pointer::try_from("/foo/bool/unresolvable").unwrap();
    let res = ptr.resolve_mut(&mut data);

    assert!(res.is_err());
    let err = res.unwrap_err();
    assert!(err.is_unresolvable());
}
#[test]
fn test_resolve_not_found() {
    let mut data = test_data();
    let ptr = Pointer::new(&["foo", "not_found", "nope"]);
    let res = ptr.resolve_mut(&mut data);
    assert!(res.is_err());
    let err = res.unwrap_err();
    assert!(err.is_not_found());
    match err {
        Error::NotFound(err) => {
            assert_eq!(err.pointer, "/foo/not_found");
        }
        _ => panic!("expected NotFound"),
    }
}

#[test]
fn test_try_resolve_mut_unresolvable() {
    let mut data = test_data();
    let ptr = Pointer::try_from("/foo/bool/unresolvable").unwrap();
    let res = ptr.try_resolve_mut(&mut data).unwrap();

    assert_eq!(res.remaining, "/unresolvable");
    assert_eq!(res.resolved, "/foo/bool");
    assert!(res.value.is_boolean());
}
#[test]
fn test_try_from() {
    let ptr = Pointer::new(&["foo", "bar", "~/"]);

    assert_eq!(Pointer::try_from("/foo/bar/~0~1").unwrap(), ptr);
    let into: Pointer = "/foo/bar/~0~1".try_into().unwrap();
    assert_eq!(ptr, into);
}

#[test]
fn test_try_resolve() {
    let data = test_data();
    let ptr = Pointer::try_from("/foo/bar/baz/qux").unwrap();
    let res = ptr.try_resolve(&data).unwrap();
    assert_eq!(&res.remaining, "");
    assert_eq!(res.value, &mut json!("quux"));

    let ptr = Pointer::try_from("/foo/bar/does_not_exist/derp").unwrap();
    let res = ptr.try_resolve(&data).unwrap();
    assert_eq!(res.remaining, "/does_not_exist/derp");

    assert_eq!(
        res.value,
        &mut json!({
            "baz": {
                "qux": "quux"
            }
        })
    );

    let ptr = Pointer::try_from("/foo/strings/0").unwrap();
    let res = ptr.try_resolve(&data).unwrap();
    assert_eq!(res.remaining, "");
    assert_eq!(res.value, &mut json!("zero"));

    let ptr = Pointer::try_from("/foo/strings/1").unwrap();
    let res = ptr.try_resolve(&data).unwrap();
    assert_eq!(res.remaining, "");
    assert_eq!(res.value, &mut json!("one"));

    let ptr = Pointer::try_from("/foo/strings/2").unwrap();
    let res = ptr.try_resolve(&data).unwrap();
    assert_eq!(res.remaining, "");
    assert_eq!(res.value, &mut json!("two"));

    let ptr = Pointer::try_from("/foo/strings/-").unwrap();
    let res = ptr.try_resolve(&data).unwrap();
    assert_eq!(res.remaining, "/-");
    assert_eq!(res.value, &mut json!(["zero", "one", "two"]));

    let ptr = Pointer::try_from("/foo/strings/0").unwrap();
    let res = ptr.try_resolve(&data).unwrap();
    assert_eq!(res.remaining, "");
    assert_eq!(res.value, &mut json!("zero"));
}

#[test]
fn test_try_resolve_overflow_error() {
    let data = test_data();
    let ptr = Pointer::try_from("/foo/strings/7").unwrap();
    let res = ptr.try_resolve(&data);
    assert!(res.is_err());
}
#[test]
fn test_try_resolve_unresolvable_error() {
    let data = test_data();
    let ptr = Pointer::try_from("/foo/bool/unresolvable/not-in-token").unwrap();
    let res = ptr.try_resolve(&data).unwrap();
    assert_eq!(
        res.remaining,
        Pointer::try_from("/unresolvable/not-in-token").unwrap()
    );
}

#[test]
fn test_resolve_mut_unresolvable_error() {
    let mut data = test_data();
    let ptr = Pointer::try_from("/foo/bool/unresolvable/not-in-token").unwrap();
    let res = ptr.resolve_mut(&mut data);
    assert!(res.is_err());
    let unresolvable = "/foo/bool/unresolvable".try_into().unwrap();
    assert_eq!(
        res.err().unwrap(),
        UnresolvableError::new(unresolvable).into()
    );

    let mut data = json!({"foo": "bar"});
    let ptr = Pointer::try_from("/foo/unresolvable").unwrap();
    let err = data.resolve_mut(&ptr).unwrap_err();
    assert_eq!(err, UnresolvableError::new(ptr.clone()).into());
}

#[test]
fn test_resolve_unresolvable_error() {
    let data = test_data();
    let ptr = Pointer::try_from("/foo/bool/unresolvable/not-in-token").unwrap();
    let res = ptr.resolve(&data);

    assert!(res.is_err());
    let unresolvable = "/foo/bool/unresolvable".try_into().unwrap();
    assert_eq!(
        res.err().unwrap(),
        UnresolvableError::new(unresolvable).into()
    )
}

#[test]
fn test_assign() {
    let mut data = json!({});
    let ptr = Pointer::try_from("/foo").unwrap();
    let val = json!("bar");
    let assignment = ptr.assign(&mut data, val.clone()).unwrap();
    assert_eq!(assignment.replaced, Value::Null);
    assert_eq!(assignment.assigned.clone().into_owned(), val);
    assert_eq!(assignment.assigned_to, "/foo");

    // now testing replacement
    let val2 = json!("baz");
    let assignment = ptr.assign(&mut data, val2.clone()).unwrap();
    assert_eq!(assignment.replaced, Value::String("bar".to_string()));
    assert_eq!(assignment.assigned.clone().into_owned(), val2);
    assert_eq!(assignment.assigned_to, "/foo");
}
#[test]
fn test_assign_with_explicit_array_path() {
    let mut data = json!({});
    let ptr = Pointer::try_from("/foo/0/bar").unwrap();
    let val = json!("baz");

    let assignment = ptr.assign(&mut data, val).unwrap();
    assert_eq!(assignment.replaced, Value::Null);
    assert_eq!(assignment.assigned_to, "/foo/0/bar");
    assert_eq!(assignment.replaced, Value::Null);
    assert_eq!(
        json!({
            "foo": [
                {
                    "bar": "baz"
                }
            ]
        }),
        data.clone()
    );
}
#[test]
fn test_assign_array_with_next_token() {
    let mut data = json!({});
    let ptr = Pointer::try_from("/foo/-/bar").unwrap();
    let val = json!("baz");
    let assignment = ptr.assign(&mut data, val).unwrap();
    assert_eq!(assignment.replaced, Value::Null);
    assert_eq!(
        assignment.assigned_to, "/foo/0/bar",
        "`assigned_to` should equal \"/foo/0/bar\""
    );
    assert_eq!(assignment.replaced, Value::Null);
    assert_eq!(
        json!({
            "foo": [
                {
                    "bar": "baz"
                }
            ]
        }),
        data.clone()
    );
    let val = json!("baz2");
    let assignment = ptr.assign(&mut data, val).unwrap();
    assert_eq!(assignment.replaced, Value::Null);
    assert_eq!(
        assignment.assigned_to, "/foo/1/bar",
        "`assigned_to` should equal \"/foo/1/bar\""
    );
    assert_eq!(assignment.replaced, Value::Null);
    assert_eq!(
        json!({
            "foo": [
                {
                    "bar": "baz"
                },
                {
                    "bar": "baz2"
                }
            ]
        }),
        data.clone()
    );
    let ptr = Pointer::try_from("/foo/0/bar").unwrap();
    let val = json!("qux");
    let assignment = ptr.assign(&mut data, val).unwrap();
    // assert_eq!(assignment.assigned_to, "/foo/0/bar");
    assert_eq!(assignment.replaced, Value::String("baz".to_string()));
    assert_eq!(
        json!({
            "foo": [
                {
                    "bar": "qux"
                },
                {
                    "bar": "baz2"
                }
            ]
        }),
        data.clone()
    );
}
#[test]
fn test_assign_with_obj_path() {
    let mut data = json!({});
    let ptr = Pointer::try_from("/foo/bar").unwrap();
    let val = json!("baz");

    let assignment = ptr.assign(&mut data, val).unwrap();
    assert_eq!(assignment.assigned_to, "/foo/bar");
    assert_eq!(assignment.replaced, Value::Null);
    assert_eq!(
        json!({
            "foo": {
                "bar": "baz"
            }
        }),
        data.clone()
    );
}
#[test]
fn test_assign_with_scalar_replace() {
    let mut data = json!({
        "foo": "bar"
    });

    let ptr = Pointer::try_from("/foo/bar/baz").unwrap();
    let val = json!("qux");

    ptr.assign(&mut data, val).unwrap();
    assert_eq!(
        json!({
            "foo": {
                "bar": {
                    "baz": "qux"
                }
            }
        }),
        data.clone()
    );
}
