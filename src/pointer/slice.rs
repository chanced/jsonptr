use super::Pointer;
use crate::Token;
use core::ops::Bound;

pub trait PointerIndex<'p>: private::Sealed {
    type Output: 'p;

    fn get(self, pointer: &'p Pointer) -> Option<Self::Output>;
}

impl<'p> PointerIndex<'p> for usize {
    type Output = Token<'p>;

    fn get(self, pointer: &'p Pointer) -> Option<Self::Output> {
        pointer.tokens().nth(self)
    }
}

impl<'p> PointerIndex<'p> for core::ops::Range<usize> {
    type Output = &'p Pointer;

    fn get(self, pointer: &'p Pointer) -> Option<Self::Output> {
        if self.end < self.start {
            // never valid
            return None;
        }

        let mut idx = 0;
        let mut offset = 0;
        let mut start_offset = None;
        let mut end_offset = None;

        for token in pointer.tokens() {
            if idx == self.start {
                start_offset = Some(offset);
            }
            if idx == self.end {
                end_offset = Some(offset);
                break;
            }
            idx += 1;
            // also include the `/` separator
            offset += token.encoded().len() + 1;
        }

        // edge case where end is last token index + 1
        // this is valid because range is exclusive
        if idx == self.end {
            end_offset = Some(offset);
        }

        let slice = &pointer.0.as_bytes()[start_offset?..end_offset?];
        // SAFETY: start and end offsets are token boundaries, so the slice is
        // valid utf-8 (and also a valid json pointer!)
        Some(unsafe { Pointer::new_unchecked(core::str::from_utf8_unchecked(slice)) })
    }
}

impl<'p> PointerIndex<'p> for core::ops::RangeFrom<usize> {
    type Output = &'p Pointer;

    fn get(self, pointer: &'p Pointer) -> Option<Self::Output> {
        {
            let mut offset = 0;
            let mut start_offset = None;

            for (idx, token) in pointer.tokens().enumerate() {
                if idx == self.start {
                    start_offset = Some(offset);
                    break;
                }
                // also include the `/` separator
                offset += token.encoded().len() + 1;
            }

            let slice = &pointer.0.as_bytes()[start_offset?..];
            // SAFETY: start offset is token boundary, so the slice is valid
            // utf-8 (and also a valid json pointer!)
            Some(unsafe { Pointer::new_unchecked(core::str::from_utf8_unchecked(slice)) })
        }
    }
}

impl<'p> PointerIndex<'p> for core::ops::RangeTo<usize> {
    type Output = &'p Pointer;

    fn get(self, pointer: &'p Pointer) -> Option<Self::Output> {
        {
            let mut idx = 0;
            let mut offset = 0;
            let mut end_offset = None;

            for token in pointer.tokens() {
                if idx == self.end {
                    end_offset = Some(offset);
                    break;
                }
                idx += 1;
                // also include the `/` separator
                offset += token.encoded().len() + 1;
            }

            // edge case where end is last token index + 1
            // this is valid because range is exclusive
            if idx == self.end {
                end_offset = Some(offset);
            }

            let slice = &pointer.0.as_bytes()[..end_offset?];
            // SAFETY: start and end offsets are token boundaries, so the slice is
            // valid utf-8 (and also a valid json pointer!)
            Some(unsafe { Pointer::new_unchecked(core::str::from_utf8_unchecked(slice)) })
        }
    }
}

impl<'p> PointerIndex<'p> for core::ops::RangeFull {
    type Output = &'p Pointer;

    fn get(self, pointer: &'p Pointer) -> Option<Self::Output> {
        Some(pointer)
    }
}

impl<'p> PointerIndex<'p> for core::ops::RangeInclusive<usize> {
    type Output = &'p Pointer;

    fn get(self, pointer: &'p Pointer) -> Option<Self::Output> {
        let (start, end) = self.into_inner();
        if end < start {
            // never valid
            return None;
        }

        let mut offset = 0;
        let mut start_offset = None;
        let mut end_offset = None;

        for (idx, token) in pointer.tokens().enumerate() {
            if idx == start {
                start_offset = Some(offset);
            }
            // also include the `/` separator
            offset += token.encoded().len() + 1;
            // since the range is inclusive, we wish to slice up until the end
            // of the token whose index is `end`, so we increment offset first
            // before checking for a match
            if idx == end {
                end_offset = Some(offset);
                break;
            }
        }

        // notice that we don't use an inclusive range here, because we already
        // acounted for the included end token when computing `end_offset` above
        let slice = &pointer.0.as_bytes()[start_offset?..end_offset?];
        // SAFETY: start and end offsets are token boundaries, so the slice is
        // valid utf-8 (and also a valid json pointer!)
        Some(unsafe { Pointer::new_unchecked(core::str::from_utf8_unchecked(slice)) })
    }
}

impl<'p> PointerIndex<'p> for core::ops::RangeToInclusive<usize> {
    type Output = &'p Pointer;

    fn get(self, pointer: &'p Pointer) -> Option<Self::Output> {
        {
            let mut offset = 0;
            let mut end_offset = None;

            for (idx, token) in pointer.tokens().enumerate() {
                // also include the `/` separator
                offset += token.encoded().len() + 1;
                // since the range is inclusive, we wish to slice up until the end
                // of the token whose index is `end`, so we increment offset first
                // before checking for a match
                if idx == self.end {
                    end_offset = Some(offset);
                    break;
                }
            }

            // notice that we don't use an inclusive range here, because we already
            // acounted for the included end token when computing `end_offset` above
            let slice = &pointer.0.as_bytes()[..end_offset?];
            // SAFETY: start and end offsets are token boundaries, so the slice is
            // valid utf-8 (and also a valid json pointer!)
            Some(unsafe { Pointer::new_unchecked(core::str::from_utf8_unchecked(slice)) })
        }
    }
}

impl<'p> PointerIndex<'p> for (Bound<usize>, Bound<usize>) {
    type Output = &'p Pointer;

    fn get(self, pointer: &'p Pointer) -> Option<Self::Output> {
        match self {
            (Bound::Included(start), Bound::Included(end)) => pointer.get(start..=end),
            (Bound::Included(start), Bound::Excluded(end)) => pointer.get(start..end),
            (Bound::Included(start), Bound::Unbounded) => pointer.get(start..),
            (Bound::Excluded(start), Bound::Included(end)) => pointer.get(start + 1..=end),
            (Bound::Excluded(start), Bound::Excluded(end)) => pointer.get(start + 1..end),
            (Bound::Excluded(start), Bound::Unbounded) => pointer.get(start + 1..),
            (Bound::Unbounded, Bound::Included(end)) => pointer.get(..=end),
            (Bound::Unbounded, Bound::Excluded(end)) => pointer.get(..end),
            (Bound::Unbounded, Bound::Unbounded) => pointer.get(..),
        }
    }
}

mod private {
    use core::ops;

    pub trait Sealed {}
    impl Sealed for usize {}
    impl Sealed for ops::Range<usize> {}
    impl Sealed for ops::RangeTo<usize> {}
    impl Sealed for ops::RangeFrom<usize> {}
    impl Sealed for ops::RangeFull {}
    impl Sealed for ops::RangeInclusive<usize> {}
    impl Sealed for ops::RangeToInclusive<usize> {}
    impl Sealed for (ops::Bound<usize>, ops::Bound<usize>) {}
}

#[cfg(test)]
mod tests {
    use core::ops::Bound;

    use crate::{Pointer, Token};

    #[test]
    fn get_single() {
        let ptr = Pointer::from_static("/foo/bar/qux");
        let s = ptr.get(0);
        assert_eq!(s, Some(Token::new("foo")));
        let s = ptr.get(1);
        assert_eq!(s, Some(Token::new("bar")));
        let s = ptr.get(2);
        assert_eq!(s, Some(Token::new("qux")));
        let s = ptr.get(3);
        assert_eq!(s, None);

        let ptr = Pointer::from_static("/");
        let s = ptr.get(0);
        assert_eq!(s, Some(Token::new("")));
        let s = ptr.get(1);
        assert_eq!(s, None);

        let ptr = Pointer::from_static("");
        let s = ptr.get(0);
        assert_eq!(s, None);
        let s = ptr.get(1);
        assert_eq!(s, None);
    }

    #[allow(clippy::reversed_empty_ranges)]
    #[test]
    fn get_range() {
        let ptr = Pointer::from_static("/foo/bar/qux");
        let s = ptr.get(0..3);
        assert_eq!(s, Some(ptr));
        let s = ptr.get(0..2);
        assert_eq!(s, Some(Pointer::from_static("/foo/bar")));
        let s = ptr.get(0..1);
        assert_eq!(s, Some(Pointer::from_static("/foo")));
        let s = ptr.get(0..0);
        assert_eq!(s, Some(Pointer::from_static("")));
        let s = ptr.get(1..3);
        assert_eq!(s, Some(Pointer::from_static("/bar/qux")));
        let s = ptr.get(1..2);
        assert_eq!(s, Some(Pointer::from_static("/bar")));
        let s = ptr.get(1..1);
        assert_eq!(s, Some(Pointer::from_static("")));
        let s = ptr.get(1..0);
        assert_eq!(s, None);
        let s = ptr.get(0..4);
        assert_eq!(s, None);
        let s = ptr.get(2..4);
        assert_eq!(s, None);

        let ptr = Pointer::from_static("/");
        let s = ptr.get(0..1);
        assert_eq!(s, Some(ptr));
        let s = ptr.get(0..0);
        assert_eq!(s, Some(Pointer::root()));
        let s = ptr.get(1..0);
        assert_eq!(s, None);
        let s = ptr.get(0..2);
        assert_eq!(s, None);
        let s = ptr.get(1..2);
        assert_eq!(s, None);
        let s = ptr.get(1..1);
        assert_eq!(s, None);

        let ptr = Pointer::root();
        let s = ptr.get(0..1);
        assert_eq!(s, None);
        let s = ptr.get(0..0);
        assert_eq!(s, None);
        let s = ptr.get(1..0);
        assert_eq!(s, None);
        let s = ptr.get(1..1);
        assert_eq!(s, None);
    }

    #[test]
    fn get_from_range() {
        let ptr = Pointer::from_static("/foo/bar/qux");
        let s = ptr.get(0..);
        assert_eq!(s, Some(ptr));
        let s = ptr.get(1..);
        assert_eq!(s, Some(Pointer::from_static("/bar/qux")));
        let s = ptr.get(2..);
        assert_eq!(s, Some(Pointer::from_static("/qux")));
        let s = ptr.get(3..);
        assert_eq!(s, None);

        let ptr = Pointer::from_static("/");
        let s = ptr.get(0..);
        assert_eq!(s, Some(ptr));
        let s = ptr.get(1..);
        assert_eq!(s, None);

        let ptr = Pointer::from_static("");
        let s = ptr.get(0..);
        assert_eq!(s, None);
    }

    #[test]
    fn get_to_range() {
        let ptr = Pointer::from_static("/foo/bar/qux");
        let s = ptr.get(..4);
        assert_eq!(s, None);
        let s = ptr.get(..3);
        assert_eq!(s, Some(ptr));
        let s = ptr.get(..2);
        assert_eq!(s, Some(Pointer::from_static("/foo/bar")));
        let s = ptr.get(..1);
        assert_eq!(s, Some(Pointer::from_static("/foo")));
        let s = ptr.get(..0);
        assert_eq!(s, Some(Pointer::from_static("")));

        let ptr = Pointer::from_static("/");
        let s = ptr.get(..0);
        assert_eq!(s, Some(Pointer::from_static("")));
        let s = ptr.get(..1);
        assert_eq!(s, Some(ptr));
        let s = ptr.get(..2);
        assert_eq!(s, None);

        let ptr = Pointer::from_static("");
        let s = ptr.get(..0);
        assert_eq!(s, Some(ptr));
        let s = ptr.get(..1);
        assert_eq!(s, None);
    }

    #[test]
    fn get_full_range() {
        let ptr = Pointer::from_static("/foo/bar");
        let s = ptr.get(..);
        assert_eq!(s, Some(ptr));

        let ptr = Pointer::from_static("/");
        let s = ptr.get(..);
        assert_eq!(s, Some(ptr));

        let ptr = Pointer::from_static("");
        let s = ptr.get(..);
        assert_eq!(s, Some(ptr));
    }

    #[allow(clippy::reversed_empty_ranges)]
    #[test]
    fn get_range_inclusive() {
        let ptr = Pointer::from_static("/foo/bar/qux");
        let s = ptr.get(0..=3);
        assert_eq!(s, None);
        let s = ptr.get(0..=2);
        assert_eq!(s, Some(ptr));
        let s = ptr.get(0..=1);
        assert_eq!(s, Some(Pointer::from_static("/foo/bar")));
        let s = ptr.get(0..=0);
        assert_eq!(s, Some(Pointer::from_static("/foo")));
        let s = ptr.get(1..=3);
        assert_eq!(s, None);
        let s = ptr.get(1..=2);
        assert_eq!(s, Some(Pointer::from_static("/bar/qux")));
        let s = ptr.get(1..=1);
        assert_eq!(s, Some(Pointer::from_static("/bar")));
        let s = ptr.get(1..=0);
        assert_eq!(s, None);

        let ptr = Pointer::from_static("/");
        let s = ptr.get(0..=0);
        assert_eq!(s, Some(ptr));
        let s = ptr.get(1..=0);
        assert_eq!(s, None);
        let s = ptr.get(0..=1);
        assert_eq!(s, None);
        let s = ptr.get(1..=1);
        assert_eq!(s, None);

        let ptr = Pointer::root();
        let s = ptr.get(0..=1);
        assert_eq!(s, None);
        let s = ptr.get(0..=0);
        assert_eq!(s, None);
        let s = ptr.get(1..=0);
        assert_eq!(s, None);
        let s = ptr.get(1..=1);
        assert_eq!(s, None);
    }

    #[test]
    fn get_to_range_inclusive() {
        let ptr = Pointer::from_static("/foo/bar/qux");
        let s = ptr.get(..=3);
        assert_eq!(s, None);
        let s = ptr.get(..=2);
        assert_eq!(s, Some(ptr));
        let s = ptr.get(..=1);
        assert_eq!(s, Some(Pointer::from_static("/foo/bar")));
        let s = ptr.get(..=0);
        assert_eq!(s, Some(Pointer::from_static("/foo")));

        let ptr = Pointer::from_static("/");
        let s = ptr.get(..=0);
        assert_eq!(s, Some(ptr));
        let s = ptr.get(..=1);
        assert_eq!(s, None);

        let ptr = Pointer::from_static("");
        let s = ptr.get(..=0);
        assert_eq!(s, None);
        let s = ptr.get(..=1);
        assert_eq!(s, None);
    }

    #[test]
    fn get_by_explicit_bounds() {
        let ptr = Pointer::from_static("/foo/bar/qux");
        let s = ptr.get((Bound::Excluded(0), Bound::Included(2)));
        assert_eq!(s, Some(Pointer::from_static("/bar/qux")));
        let s = ptr.get((Bound::Excluded(0), Bound::Excluded(2)));
        assert_eq!(s, Some(Pointer::from_static("/bar")));
        let s = ptr.get((Bound::Excluded(0), Bound::Unbounded));
        assert_eq!(s, Some(Pointer::from_static("/bar/qux")));
        let s = ptr.get((Bound::Included(0), Bound::Included(2)));
        assert_eq!(s, Some(Pointer::from_static("/foo/bar/qux")));
        let s = ptr.get((Bound::Included(0), Bound::Excluded(2)));
        assert_eq!(s, Some(Pointer::from_static("/foo/bar")));
        let s = ptr.get((Bound::Included(0), Bound::Unbounded));
        assert_eq!(s, Some(Pointer::from_static("/foo/bar/qux")));
        let s = ptr.get((Bound::Unbounded, Bound::Included(2)));
        assert_eq!(s, Some(Pointer::from_static("/foo/bar/qux")));
        let s = ptr.get((Bound::Unbounded, Bound::Excluded(2)));
        assert_eq!(s, Some(Pointer::from_static("/foo/bar")));
        let s = ptr.get((Bound::Unbounded, Bound::Unbounded));
        assert_eq!(s, Some(Pointer::from_static("/foo/bar/qux")));

        let ptr = Pointer::from_static("/foo/bar");
        let s = ptr.get((Bound::Excluded(0), Bound::Included(2)));
        assert_eq!(s, None);
        let s = ptr.get((Bound::Excluded(0), Bound::Excluded(2)));
        assert_eq!(s, Some(Pointer::from_static("/bar")));
        let s = ptr.get((Bound::Excluded(0), Bound::Unbounded));
        assert_eq!(s, Some(Pointer::from_static("/bar")));
        let s = ptr.get((Bound::Included(0), Bound::Included(2)));
        assert_eq!(s, None);
        let s = ptr.get((Bound::Included(0), Bound::Excluded(2)));
        assert_eq!(s, Some(ptr));
        let s = ptr.get((Bound::Included(0), Bound::Unbounded));
        assert_eq!(s, Some(ptr));
        let s = ptr.get((Bound::Unbounded, Bound::Included(2)));
        assert_eq!(s, None);
        let s = ptr.get((Bound::Unbounded, Bound::Excluded(2)));
        assert_eq!(s, Some(ptr));
        let s = ptr.get((Bound::Unbounded, Bound::Unbounded));
        assert_eq!(s, Some(ptr));

        // testing only the start excluded case a bit more exhaustively since
        // other cases just delegate directly (so are covered by other tests)
        let ptr = Pointer::from_static("/");
        let s = ptr.get((Bound::Excluded(0), Bound::Included(0)));
        assert_eq!(s, None);
        let s = ptr.get((Bound::Excluded(0), Bound::Excluded(0)));
        assert_eq!(s, None);
        let s = ptr.get((Bound::Excluded(0), Bound::Unbounded));
        assert_eq!(s, None);

        let ptr = Pointer::from_static("");
        let s = ptr.get((Bound::Excluded(0), Bound::Included(0)));
        assert_eq!(s, None);
        let s = ptr.get((Bound::Excluded(0), Bound::Excluded(0)));
        assert_eq!(s, None);
        let s = ptr.get((Bound::Excluded(0), Bound::Unbounded));
        assert_eq!(s, None);
    }
}
