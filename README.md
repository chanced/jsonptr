# jsonptr - JSON Pointers for Rust

Data structures and logic for resolving, assigning, and deleting by JSON Pointers ([RFC
6901](https://datatracker.ietf.org/doc/html/rfc6901)).

## Usage

### Resolve

JSON Pointers can be created either with a slice of strings or directly from a properly encoded string representing a JSON Pointer.

```rust
use jsonptr::{Pointer};
use serde_json::{json, Value};

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
    let mut bar = pointer.resolve_mut(&ptr).unwrap();
    assert_eq!(bar, "baz");
}

```

### Assign

```rust
use jsonptr::{Pointer};
use serde_json::{json, Value};

fn main() {
    let ptr = Pointer::try_from("/foo/bar").unwrap();
    let mut data = json!({});
    let val = json!("qux");
    let assignment = ptr.assign(&mut data, val);
    assert_eq!(data, json!({ "foo": { "bar": "qux" }}))
}
```
