# jsonptr - JSON Pointers (RFC 6901)

[<img alt="github" src="https://img.shields.io/badge/github-chanced/jsonptr-62D1FC?style=for-the-badge&labelColor=777&logo=github" height="21">](https://github.com/chanced/jsonptr)
[<img alt="crates.io" src="https://img.shields.io/crates/v/jsonptr.svg?style=for-the-badge&color=fc8d62&logo=rust" height="21">](https://crates.io/crates/jsonptr)
[<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-jsonptr-f0f0f0?style=for-the-badge&labelColor=777&logo=docs.rs" height="21">](https://docs.rs/jsonptr)
[<img alt="build status" src="https://img.shields.io/github/actions/workflow/status/chanced/jsonptr/test.yml?branch=main&style=for-the-badge" height="21">](https://github.com/chanced/jsonptr/actions?query=branch%3Amain)
[<img alt="code coverage" src="https://img.shields.io/codecov/c/github/chanced/jsonptr?style=for-the-badge&color=CBB88D" height="21">](https://codecov.io/gh/chanced/jsonptr)

JSON Pointers ([RFC 6901](https://datatracker.ietf.org/doc/html/rfc6901))
defines a string syntax for identifying a specific location within a JSON
document. This crate provides two types, [`Pointer`] and [`PointerBuf`] (akin to
[`str`] and [`String`]), for working with them abstractly.

A [`Pointer`] is composed of zero or more [`Token`]s, single segments which
represent a field of an object or an [`index`] of an array, and are bounded by
either `'/'` or the end of the string. [`Token`]s are lightly encoded, where
`'~'` is encoded as `"~0"` and `'/'` as `"~1"`. Combined, the [`Pointer`] forms
a path to a specific location within a JSON, or similar, document.

[`Token`]s can be iterated over using either [`Tokens`], returned from the
[`tokens`](`Pointer::tokens`) method of a pointer or [`Components`], returned
from the [`components`](`Pointer::components`) method. The difference being that
[`Tokens`] iterates over each [`Token`] in the [`Pointer`], while a
[`Component`] can represent the [`Root`](Component::Root) document or a single
[`Token`](Component::Token).

Operations [`resolve`], [`assign`] and [`delete`] are provided as traits with
corresponding methods on [`Pointer`]. Implementations of each trait are provided
for [`serde_json::Value`] and [`toml::Value`](https://docs.rs/toml/0.8). All
operations are enabled by default but are gated by [feature flags](#feature-flags).

## Usage

### Basic usage

To parse a pointer from a string, use the [`parse`](Pointer::parse) method or construct
from an iterator of [`Token`]s:

```rust
use jsonptr::Pointer;
use serde_json::json;

let ptr = Pointer::parse("/examples/0/name").unwrap();

let from_tokens = Pointer::from_tokens(["examples", "0", "name"]).unwrap();
assert_eq!(ptr, from_tokens);

let parent = ptr.parent();
assert_eq!(parent, Pointer::parse("/examples/0").unwrap());

let (front, remaining) = ptr.split_front();
assert_eq!(front, "examples");
assert_eq!(remaining, Pointer::parse("/0/name").unwrap());



```

### Assigning a Value

see [`assign`] for more information.

```rust
# use jsonptr::{Pointer};
# use serde_json::json;

let ptr = Pointer::parse("/secret/universe").unwrap();
let mut data = json!({"secret": { "universe": 42 }});
let replaced = ptr.assign(&mut data, json!(34)).unwrap();
assert_eq!(replaced, json!(42));
assert_eq!(data, json!({"secret": { "universe": 34 }}));
```

### Resolving a Value

See [`resolve`] for more information.

```rust
# use jsonptr::{Pointer};
# use serde_json::json;

let ptr = Pointer::parse("/foo/bar").unwrap();
let data = json!({"foo": { "bar": 34 }});
let bar = ptr.resolve().unwrap();
assert_eq!(bar, json!(34));
```

### Assigning a Value

see [`assign`] for more information.

```rust
# use jsonptr::{Pointer};
# use serde_json::json;

let ptr = Pointer::parse("/secret/universe").unwrap();
let mut data = json!({"secret": { "universe": 42 }});
let replaced = ptr.assign(&mut data, json!(34)).unwrap();
assert_eq!(replaced, json!(42));
assert_eq!(data, json!({"secret": { "universe": 34 }}));
```

### Assigning a Value

see [`assign`] for more information.

```rust
# use jsonptr::{Pointer};
# use serde_json::json;

let ptr = Pointer::parse("/secret/universe").unwrap();
let mut data = json!({"secret": { "universe": 42 }});
let replaced = ptr.assign(&mut data, json!(34)).unwrap();
assert_eq!(replaced, json!(42));
assert_eq!(data, json!({"secret": { "universe": 34 }}));
```

## Feature Flags

|    Flag     | Description                                                                                                                               | Enables         | Default |
| :---------: | ----------------------------------------------------------------------------------------------------------------------------------------- | --------------- | :-----: |
|   `"std"`   | Implements `std::error::Error` for error types                                                                                            |                 |    ✓    |
|  `"serde"`  | Enables [`serde`] support for types                                                                                                       |                 |    ✓    |
|  `"json"`   | Implements ops for [`serde_json::Value`]                                                                                                  | `"serde"`       |    ✓    |
|  `"toml"`   | Implements ops for [`toml::Value`](https://docs.rs/toml/0.8)                                                                              | `"std"`, `toml` |         |
| `"assign"`  | Enables the [`assign`] module and related pointer methods, providing a means to assign a value to a specific location within a document   |                 |    ✓    |
| `"resolve"` | Enables the [`resolve`] module and related pointer methods, providing a means to resolve a value at a specific location within a document |                 |    ✓    |
| `"delete"`  | Enables the [`delete`] module and related pointer methods, providing a means to delete a value at a specific location within a document   | `"resolve"`     |    ✓    |

## Contributions / Issues

Contributions and feedback are always welcome and appreciated.

If you find an issue, please open a ticket or a pull request.

## License

MIT or Apache 2.0.
