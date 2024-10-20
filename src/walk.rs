use crate::{resolve::ResolveError, Pointer, PointerBuf, Resolve, ResolveMut};

/*
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║                                     Walk                                     ║
║                                    ¯¯¯¯¯¯                                    ║
╚══════════════════════════════════════════════════════════════════════════════╝
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
*/

/// A trait implemented by types which can walk a value to or from a given
/// location as represented by a JSON [`Pointer`].
pub trait Walk: Resolve<Error: core::fmt::Debug> {
    /// Iterator type for `walk_to`.
    type WalkTo<'v, 'p>
    where
        Self: 'v + 'p;

    /// Iterator type for `walk_from`
    type WalkFrom<'v>
    where
        Self: 'v;

    /// Walks the path of a JSON Pointer for this value.
    fn walk_to<'v, 'p>(&'v self, to: &'p Pointer) -> Self::WalkTo<'v, 'p>;

    /// Walks this value, starting at the location `from`.
    /// ## Errors
    /// Returns a [`Self::Error`] if the location `from` fails to resolve.
    fn walk_from(&self, from: PointerBuf) -> Result<Self::WalkFrom<'_>, Self::Error>;

    /// Walks the entire value, starting from root.
    fn walk(&self) -> Self::WalkFrom<'_> {
        self.walk_from(PointerBuf::default()).unwrap()
    }
}

/*
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║                                     Walk                                     ║
║                                    ¯¯¯¯¯¯                                    ║
╚══════════════════════════════════════════════════════════════════════════════╝
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
*/

/// A trait implemented by types which can walk a value to or from a given
/// location as represented by a JSON [`Pointer`].
pub trait WalkMut: ResolveMut<Error: core::fmt::Debug> {
    /// Iterator type for `walk_to`.
    type WalkTo<'v, 'p>
    where
        Self: 'v + 'p;

    /// Iterator type for `walk_from`
    type WalkFrom<'v>
    where
        Self: 'v;

    /// Walks the path of a JSON Pointer for this value.
    fn walk_to_mut<'v, 'p>(&'v mut self, to: &'p Pointer) -> Self::WalkTo<'v, 'p>;

    /// Walks this value, starting at the location `from`.
    /// ## Errors
    /// Returns a [`Self::Error`] if the location `from` fails to resolve.
    fn walk_from_mut(&mut self, from: PointerBuf) -> Result<Self::WalkFrom<'_>, Self::Error>;

    /// Walks the entire value, starting from root.
    fn walk_mut(&mut self) -> Self::WalkFrom<'_> {
        self.walk_from_mut(PointerBuf::default()).unwrap()
    }
}

/*
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║                                      to                                      ║
║                                     ¯¯¯¯                                     ║
╚══════════════════════════════════════════════════════════════════════════════╝
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
*/

mod to {
    //! Generic iterators for walking to a location in a value.
    use super::Walk;
    use crate::{resolve::ResolveError, Pointer, Resolve};
    use core::{borrow::Borrow, num::NonZeroUsize};

    /// A generic iterator for walking to a location in a value, intended to be
    /// wrapped by implementations.
    #[derive(Debug)]
    pub(super) struct Iter<'v, 'p, W>
    where
        W: Walk,
        W::Error: core::fmt::Debug,
    {
        cursor: &'v W,
        full_path: &'p Pointer,
        offset: Option<NonZeroUsize>,
    }

    impl<'v, 'p, W> Iter<'v, 'p, W>
    where
        W: Walk<Error = ResolveError>,
        W::Value: Resolve + core::fmt::Debug,
    {
        /// Creates a new `Iter` that walks the path of `to`, as represented by
        /// a JSON Pointer, in `value`
        pub fn new(value: &'v W, to: &'p Pointer) -> Self {
            Self {
                cursor: value,
                full_path: to,
                offset: None,
            }
        }
    }

    impl<'v, 'p, W> Iterator for Iter<'v, 'p, W>
    where
        W: Walk<Error = ResolveError> + Borrow<W::Value>,
        W::Value: Resolve + core::fmt::Debug,
        W::Error: core::fmt::Debug,
        W::Value: Borrow<W>,
    {
        type Item = Result<(&'p Pointer, &'v W::Value), W::Error>;

        fn next(&mut self) -> Option<Self::Item> {
            // we use the offset to record where we are in the pointer
            let offset = if let Some(offset) = self.offset {
                // the offset has previously been set, so we use that
                offset.get()
            } else {
                // An empty offset means we are at the beginning of the walk.

                // this is a special case where the target path is root
                // we need to handle this separately because we later account
                // for tokens, which an empty path has none of.
                if self.full_path.is_root() {
                    // the target path is root, so we set the offset to 1 ensures we
                    // do not send repeats due to the bounds check on offset below.
                    self.offset = NonZeroUsize::new(1);
                    return Some(Ok((Pointer::root(), self.cursor.borrow())));
                }
                // if the offset was not previously set, we start at 0
                0
            };

            // checking to make sure we are not out of bounds
            if offset > self.full_path.len() {
                return None;
            }

            // split the path at the offset, where everything to the left
            // is the full path of the current value to be sent and everything
            // to the right is the remaining path to be resolved.
            let (path, remaining) = self
                .full_path
                .split_at(offset)
                .unwrap_or((self.full_path, Pointer::root()));

            if let Some(next) = remaining.first() {
                // if there is a next token, we set the offset to the next token's length
                // plus 1 to account for the slash.
                self.offset = NonZeroUsize::new(offset + next.encoded().len() + 1);
            } else {
                // otherwise we intentionally push the offset out of bounds
                self.offset = NonZeroUsize::new(offset + 1);
            }

            // we want the last token as a `&Pointer` so that we can use the resolve logic
            // the path is either splittable (contains a token) or is empty (root).
            //
            // If it is splittable, we either use the token's length to determine the token's
            // offset and split the path there or we use the root pointer.
            let token_path = path.last().map_or(Pointer::root(), |t| {
                path.split_at(path.len() - t.encoded().len() - 1).unwrap().1
            });

            // we attempt to resolve the value
            let value = match self.cursor.resolve(token_path) {
                Ok(ok) => ok,
                Err(err) => return Some(Err(err.with_offset(path.len() - token_path.len()))),
            };

            // moving the cursor value to the resolved value
            self.cursor = value.borrow();

            Some(Ok((path, value)))
        }
    }
}

/*
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║                                     from                                     ║
║                                    ¯¯¯¯¯¯                                    ║
╚══════════════════════════════════════════════════════════════════════════════╝
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
*/

pub mod from {
    use core::iter::Enumerate;

    pub struct Iter;
    pub struct IterMut;

    enum Inner<A, O> {
        Array(Enumerate<A>),
        Object(O),
    }
}

/*
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║                                     json                                     ║
║                                    ¯¯¯¯¯¯                                    ║
╚══════════════════════════════════════════════════════════════════════════════╝
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
*/
#[cfg(feature = "json")]
pub mod json {
    use super::Walk;
    use crate::{resolve::ResolveError, Pointer, PointerBuf, Resolve};
    use serde_json::Value;

    impl Walk for Value {
        type WalkTo<'v, 'p> = WalkTo<'v, 'p>;

        type WalkFrom<'v> = WalkFrom<'v>;

        fn walk_to<'v, 'p>(&'v self, to: &'p Pointer) -> Self::WalkTo<'v, 'p> {
            WalkTo::new(self, to)
        }

        fn walk_from(&self, from: PointerBuf) -> Result<Self::WalkFrom<'_>, Self::Error> {
            WalkFrom::new(self, from)
        }
    }

    #[derive(Debug)]
    pub struct WalkTo<'v, 'p> {
        iter: super::to::Iter<'v, 'p, Value>,
    }

    pub struct WalkFrom<'v> {
        v: &'v Value,
    }

    impl<'v> WalkFrom<'v> {
        /// Creates a new `WalkFrom` from a value and a pointer.
        ///
        /// ## Errors
        /// Returns [`ResolveError`] if the `to` pointer fails to resolve.
        pub fn new(v: &'v Value, from: PointerBuf) -> Result<Self, ResolveError> {
            Ok(Self { v })
        }
    }

    impl<'v, 'p> WalkTo<'v, 'p> {
        /// Creates a new `WalkTo` iterator that walks the path of `to`, as
        /// represented by a JSON Pointer, in `value`
        pub fn new(value: &'v Value, to: &'p Pointer) -> Self {
            WalkTo {
                iter: super::to::Iter::new(value, to),
            }
        }
    }

    impl<'v, 'p> Iterator for WalkTo<'v, 'p> {
        type Item = Result<(&'p Pointer, &'v Value), ResolveError>;

        fn next(&mut self) -> Option<Self::Item> {
            self.iter.next()
        }
    }
}

#[cfg(test)]
mod test {
    #[cfg(feature = "json")]
    mod json {

        use crate::{
            index::Index,
            walk::{json::WalkTo, Walk},
            Pointer,
        };
        use alloc::vec::Vec;
        use serde_json::json;

        #[test]
        fn valid() {
            let value = json!({
                "foo": {
                    "bar": [
                        {
                            "baz": {
                                "qux": 34
                            }
                        }
                    ]
                }
            });
            let full_path = Pointer::from_static("/foo/bar/0/baz/qux");
            let walk_to = WalkTo::new(&value, full_path);
            let foo = value.get("foo").unwrap();
            let foo_bar = foo.get("bar").unwrap();
            let foo_bar_0 = foo_bar.get(0).unwrap();
            let foo_bar_0_baz = foo_bar_0.get("baz").unwrap();
            let foo_bar_0_baz_qux = foo_bar_0_baz.get("qux").unwrap();
            assert_eq!(
                walk_to.collect::<Vec<_>>(),
                vec![
                    Ok((Pointer::from_static(""), &value)),
                    Ok((Pointer::from_static("/foo"), foo)),
                    Ok((Pointer::from_static("/foo/bar"), foo_bar)),
                    Ok((Pointer::from_static("/foo/bar/0"), foo_bar_0)),
                    Ok((Pointer::from_static("/foo/bar/0/baz"), foo_bar_0_baz)),
                    Ok((
                        Pointer::from_static("/foo/bar/0/baz/qux"),
                        foo_bar_0_baz_qux
                    )),
                ]
            );

            assert_eq!(
                value.walk_to(full_path).collect::<Vec<_>>(),
                vec![
                    Ok((Pointer::from_static(""), &value)),
                    Ok((Pointer::from_static("/foo"), foo)),
                    Ok((Pointer::from_static("/foo/bar"), foo_bar)),
                    Ok((Pointer::from_static("/foo/bar/0"), foo_bar_0)),
                    Ok((Pointer::from_static("/foo/bar/0/baz"), foo_bar_0_baz)),
                    Ok((
                        Pointer::from_static("/foo/bar/0/baz/qux"),
                        foo_bar_0_baz_qux
                    )),
                ]
            );
        }

        #[test]
        fn root() {
            let value = json!({
                "foo": {
                    "bar": [
                        {
                            "baz": {
                                "qux": 34
                            }
                        }
                    ]
                }
            });

            let walk_to = WalkTo::new(&value, Pointer::from_static(""));
            assert_eq!(
                walk_to.collect::<Vec<_>>(),
                vec![Ok((Pointer::from_static(""), &value))]
            );
        }

        #[test]
        fn invalid() {
            use crate::resolve::ResolveError;
            let value = json!({
                "foo": {
                    "bar": [
                        {
                            "baz": {
                                "qux": 34
                            }
                        }
                    ]
                }
            });

            let walk_to = WalkTo::new(&value, Pointer::from_static("/invalid"));
            let mut results = walk_to.collect::<Vec<_>>();
            assert!(results.len() == 2);
            assert!(results[0].is_ok()); // root is always valid
            assert!(results[1].is_err());
            assert_eq!(
                results.pop().unwrap().unwrap_err(),
                ResolveError::NotFound { offset: 0 }
            );

            let walk_to = WalkTo::new(&value, Pointer::from_static("/foo/invalid"));
            let mut results = walk_to.collect::<Vec<_>>();
            assert!(results.len() == 3);
            assert!(results[0].is_ok()); // root is always valid
            assert!(results[1].is_ok());
            assert!(results[2].is_err());
            assert_eq!(
                results.pop().unwrap().unwrap_err(),
                ResolveError::NotFound { offset: 4 }
            );

            let walk_to = WalkTo::new(&value, Pointer::from_static("/foo/bar/invalid"));
            let mut results = walk_to.collect::<Vec<_>>();
            assert!(results.len() == 4);
            assert!(results[0].is_ok()); // root is always valid
            assert!(results[1].is_ok());
            assert!(results[2].is_ok());
            assert!(results[3].is_err());
            assert_eq!(
                results.pop().unwrap().unwrap_err(),
                ResolveError::FailedToParseIndex {
                    offset: 8,
                    source: Index::try_from("invalid").unwrap_err()
                }
            );
        }
    }
}
