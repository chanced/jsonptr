<!-- TODO: this will become the doc comments and be replaced with more generic verbiage -->

# jsonptr - JSON Pointers (RFC 6901)

[<img alt="github" src="https://img.shields.io/badge/github-chanced/jsonptr-62D1FC?style=for-the-badge&labelColor=777&logo=github" height="21">](https://github.com/chanced/jsonptr)
[<img alt="crates.io" src="https://img.shields.io/crates/v/jsonptr.svg?style=for-the-badge&color=fc8d62&logo=rust" height="21">](https://crates.io/crates/jsonptr)
[<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-jsonptr-f0f0f0?style=for-the-badge&labelColor=777&logo=docs.rs" height="21">](https://docs.rs/jsonptr)
[<img alt="build status" src="https://img.shields.io/github/actions/workflow/status/chanced/jsonptr/test.yml?branch=main&style=for-the-badge" height="21">](https://github.com/chanced/jsonptr/actions?query=branch%3Amain)
[<img alt="code coverage" src="https://img.shields.io/codecov/c/github/chanced/jsonptr?style=for-the-badge&color=CBB88D" height="21">](https://codecov.io/gh/chanced/jsonptr)

This crate offers two types, [`Pointer`] and [`PointerBuf`] (akin to
[`Path`](std::path::Path) and [`PathBuf`](std::path::PathBuf)), for working with
JSON Pointers ([RFC 6901](https://datatracker.ietf.org/doc/html/rfc6901)),
abstractly.

A [`Pointer`] is composed of zero or more [`Token`]s, single segments which
represent a field of an object or an [`Index`] of an array, and are bounded by
either `'/'` or the end of the string. [`Token`]s are lightly encoded, where
`'~'` is encoded as `"~0"` and `'/'` is encoded as `"~1"`. Combined, the
[`Pointer`] is able to identify a specific location within a JSON, or similar,
document.

[`Token`]s can be iterated over using either [`Tokens`], returned from the
[`tokens`](`Pointer::tokens`) method of a pointer or [`Components`], returned
from the [`components`](`Pointer::components`). The difference being that
[`Tokens`] iterates over each [`Token`] in the pointer, while a [`Component`]
can represent the [`Root`](Component::Root) document or a single
[`Token`](Component::Token).

Operations [`resolve`], [`assign`] and [`delete`] are provided as traits with
corresponding methods on [`Pointer`]. Implementations of each trait are provided
for [`serde_json::Value`] and [`toml::Value`](https://docs.rs/toml/0.8).

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

## Usage

### Resolving a value

Using the `resolve` method, you can resolve a pointer against a value type that
implements [`Resolve`].

```rust
# use jsonptr::{Pointer};
let ptr = Pointer::parse("/foo/bar").unwrap();
let bar = ptr.resolve(&json!({"foo": {"bar": 34}})).unwrap();
assert_eq!(bar, &json!(34));
```

### Resolve

```rust
use jsonptr::Pointer;
use serde_json::json;

let ptr = Pointer::parse("/foo/bar").unwrap();
let bar = ptr.resolve(&json!({"foo": {"bar": 34}})).unwrap();
assert_eq!(bar, &json!(34));
```

### Assign

```rust
use jsonptr::Pointer;
use serde_json::json;

let ptr = Pointer::parse("/foo/bar").unwrap();
let mut data = json!({});
let res = ptr.assign(&mut data, json!({"baz": 34}));
assert_eq!(res, Ok(None));
assert_eq!(data, json!({"foo": {"bar": {"baz": 34}}}));
```

## Contributions / Issues

Contributions and feedback are always welcome and appreciated.

If you find an issue, please open a ticket or a pull request.

## License

MIT or Apache 2.0.

```

```
