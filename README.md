# jsonptr - JSON Pointers for Rust

[<img alt="github" src="https://img.shields.io/badge/github-chanced/jsonptr-8da0cb?style=for-the-badge&labelColor=777&logo=github" height="21">](https://github.com/chanced/jsonptr)
[<img alt="crates.io" src="https://img.shields.io/crates/v/jsonptr.svg?style=for-the-badge&color=fc8d62&logo=rust" height="21">](https://crates.io/crates/jsonptr)
[<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-jsonptr-f0f0f0?style=for-the-badge&labelColor=777&logo=docs.rs" height="21">](https://docs.rs/jsonptr)
[<img alt="build status" src="https://img.shields.io/github/actions/workflow/status/chanced/jsonptr/rust.yml?branch=main&style=for-the-badge" height="21">](https://github.com/chanced/jsonptr/actions?query=branch%3Amain)

Data structures and logic for resolving, assigning, and deleting by JSON Pointers ([RFC
6901](https://datatracker.ietf.org/doc/html/rfc6901)).

## Usage

JSON Pointers can be created either with a slice of strings or directly from a properly encoded string representing a JSON Pointer.

### Resolve values

#### `Pointer::resolve`

```rust
use jsonptr::Pointer;
use serde_json::json;

let mut data = json!({"foo": { "bar": "baz" }});
let ptr = Pointer::from_static("/foo/bar");
let bar = ptr.resolve(&data).unwrap();
assert_eq!(bar, "baz");
```

#### `Resolve::resolve`

```rust
use jsonptr::{Pointer, Resolve};
use serde_json::json;

let mut data = json!({ "foo": { "bar": "baz" }});
let ptr = Pointer::from_static("/foo/bar");
let bar = data.resolve(&ptr).unwrap();
assert_eq!(bar, "baz");

```

#### `ResolveMut::resolve_mut`

```rust
use jsonptr::{Pointer, ResolveMut};
use serde_json::json;

let ptr = Pointer::from_static("/foo/bar");
let mut data = json!({ "foo": { "bar": "baz" }});
let mut bar = data.resolve_mut(&ptr).unwrap();
assert_eq!(bar, "baz");
```

### Assign

#### `Pointer::assign`

```rust
use jsonptr::{Pointer, AutoExpand};
use serde_json::json;

let ptr = Pointer::from_static("/foo/bar");
let mut data = json!({});
let _previous = ptr.assign(&mut data, "qux", AutoExpand::Enabled).unwrap();
assert_eq!(data, json!({ "foo": { "bar": "qux" }}))
```

#### `Assign::asign`

```rust
use jsonptr::{Assign, Pointer, AutoExpand};
use serde_json::json;

let ptr = Pointer::from_static("/foo/bar");
let mut data = json!({});
let _previous = data.assign(&ptr, "qux", AutoExpand::Enabled).unwrap();
assert_eq!(data, json!({ "foo": { "bar": "qux" }}))
```

### Delete

#### `Pointer::delete`

```rust
use jsonptr::Pointer;
use serde_json::json;

let mut data = json!({ "foo": { "bar": { "baz": "qux" } } });
let ptr = Pointer::from_static("/foo/bar/baz");
assert_eq!(ptr.delete(&mut data), Some("qux".into()));
assert_eq!(data, json!({ "foo": { "bar": {} } }));

// unresolved pointers return None
let mut data = json!({});
assert_eq!(ptr.delete(&mut data), None);
```

#### `Delete::delete`

```rust
use jsonptr::{Pointer, Delete};
use serde_json::json;

let mut data = json!({ "foo": { "bar": { "baz": "qux" } } });
let ptr = Pointer::from_static("/foo/bar/baz");
assert_eq!(ptr.delete(&mut data), Some("qux".into()));
assert_eq!(data, json!({ "foo": { "bar": {} } }));

// replacing a root pointer replaces data with `Value::Null`
let ptr = Pointer::root();
let deleted = json!({ "foo": { "bar": {} } });
assert_eq!(data.delete(&ptr), Some(deleted));
assert!(data.is_null());
```

## Feature Flags

|      Flag      | Enables                                                                                                                                         |
| :------------: | ----------------------------------------------------------------------------------------------------------------------------------------------- |
|    `"std"`     | implements `std::error::Error` for errors                                                                                                       |
|    `"url"`     | `TryFrom<url::Url>` for [`Pointer`](`crate::Pointer`)                                                                                           |
|  `"uniresid"`  | `TryFrom<uniresid::Uri>` + `TryFrom<uniresid::AbsoluteUri>` for [`Pointer`](`crate::Pointer`)                                                   |
| `"fluent-uri"` | `TryFrom<fluent_uri::Uri<&str>>` + `TryFrom<fluent_uri::Uri<String>>` + `TryFrom<fluent_uri::Uri<&mut [u8]>>` for [`Pointer`](`crate::Pointer`) |

## Contributions / Issues

Contributions and feedback are always welcome and appreciated.

If you find an issue, please open a ticket or a pull request.

## License

MIT or Apache 2.0.

```

```
