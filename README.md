# jsonptr - JSON Pointers for Rust

[![Crate](https://img.shields.io/crates/v/jsonptr.svg?style=flat-square)](https://crates.io/crates/jsonptr)
[![Documentation](https://docs.rs/jsonptr/badge.svg?style=flat-square)](https://docs.rs/jsonptr)
[![Minimum rustc version](https://img.shields.io/badge/rustc-1.36+-lightgray.svg?style=flat-square)](https://github.com/rust-random/rand#rust-version-requirements)

Data structures and logic for resolving, assigning, and deleting by JSON Pointers ([RFC
6901](https://datatracker.ietf.org/doc/html/rfc6901)).

## Usage

### Resolve

JSON Pointers can be created either with a slice of strings or directly from a properly encoded string representing a JSON Pointer.

```rust
use jsonptr::{Pointer, ResolveMut};
use serde_json::json;

fn main() {
    let mut data = json!({
        "foo": {
            "bar": "baz"
        }
    });

    let ptr = Pointer::new(&["foo", "bar"]);
    ptr.resolve(&data);
    let bar = data.resolve(&ptr).unwrap();
    assert_eq!(bar, "baz");

    let ptr = Pointer::try_from("/foo/bar").unwrap();
    let mut bar = data.resolve_mut(&ptr).unwrap(); // alternatively: ptr.resolve_mut(&mut data);
    assert_eq!(bar, "baz");
}

```

### Assign

```rust
use jsonptr::{Pointer, Assign};
use serde_json::json;

fn main() {
    let ptr = Pointer::try_from("/foo/bar").unwrap();
    let mut data = json!({});
    let val = json!("qux");
    let assignment = data.assign(&ptr, val);
    assert_eq!(data, json!({ "foo": { "bar": "qux" }}))
}
```

### Delete

```rust
    use jsonptr::{Pointer, Delete};
    use serde_json::json;
fn main() {
    let mut data = json!({ "foo": { "bar": { "baz": "qux" } } });
    let ptr = Pointer::new(&["foo", "bar", "baz"]);
    assert_eq!(data.delete(&ptr), Ok(Some("qux".into())));
    assert_eq!(data, json!({ "foo": { "bar": {} } }));

    // unresolved pointers return Ok(None)
    let mut data = json!({});
    let ptr = Pointer::new(&["foo", "bar", "baz"]);
    assert_eq!(ptr.delete(&mut data), Ok(None));
    assert_eq!(data, json!({}));

    // replacing a root pointer replaces data with `Value::Null`
    let mut data = json!({ "foo": { "bar": "baz" } });
    let ptr = Pointer::default();
    assert_eq!(data.delete(&ptr), Ok(Some(json!({ "foo": { "bar": "baz" } }))));
    assert!(data.is_null());
}
```

## Contributions / Issues

Contributions and feedback are always welcome and appreciated.

If you find an issue, please open a ticket or a pull request.

## License

MIT or Apache 2.0.
