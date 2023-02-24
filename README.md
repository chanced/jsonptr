# jsonptr - JSON Pointers for Rust

[<img alt="github" src="https://img.shields.io/badge/github-chanced/jsonptr-8da0cb?style=for-the-badge&labelColor=777&logo=github" height="21">](https://github.com/chanced/jsonptr)
[<img alt="crates.io" src="https://img.shields.io/crates/v/jsonptr.svg?style=for-the-badge&color=fc8d62&logo=rust" height="21">](https://crates.io/crates/jsonptr)
[<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-jsonptr-f0f0f0?style=for-the-badge&labelColor=777&logo=docs.rs" height="21">](https://docs.rs/jsonptr)
[<img alt="build status" src="https://img.shields.io/github/actions/workflow/status/chanced/jsonptr/rust.yml?branch=main&style=for-the-badge" height="21">](https://github.com/chanced/jsonptr/actions?query=branch%3Amain)

Data structures and logic for resolving, assigning, and deleting by JSON Pointers ([RFC
6901](https://datatracker.ietf.org/doc/html/rfc6901)).

## Usage

JSON Pointers can be created either with a slice of strings or directly from a properly encoded string representing a JSON Pointer.

### Resolve

```rust
use jsonptr::{Pointer, Resolve, ResolveMut};
use serde_json::json;

fn main() {
    let mut data = json!({
        "foo": {
            "bar": "baz"
        }
    });

    let ptr = Pointer::new(&["foo", "bar"]);
    let bar = ptr.resolve(&data).unwrap();
    assert_eq!(bar, "baz");

    let bar = data.resolve(&ptr).unwrap();
    assert_eq!(bar, "baz");

    let ptr = Pointer::try_from("/foo/bar").unwrap();
    let mut bar = data.resolve_mut(&ptr).unwrap();
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
    let assignment = data.assign(&ptr, "qux");
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
    let expected = json!({ "foo": { "bar": "baz" } });
    assert_eq!(data.delete(&ptr), Ok(Some(expected)));
    assert!(data.is_null());
}
```

## Feature Flags

|     Flag     | Enables                                                                                                    |
| :----------: | ---------------------------------------------------------------------------------------------------------- |
|   `"std"`    | implements `std::error::Error` for errors                                                                  |
|   `"url"`    | implements `TryFrom<url::Url>` for [`Pointer`](`crate::Pointer`)                                           |
| `"uniresid"` | implements `TryFrom<uniresid::Uri>` and `TryFrom<uniresid::AbsoluteUri>` for [`Pointer`](`crate::Pointer`) |

## Contributions / Issues

Contributions and feedback are always welcome and appreciated.

If you find an issue, please open a ticket or a pull request.

## License

MIT or Apache 2.0.
