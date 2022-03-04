use std::{
    mem::{replace, swap},
    ops::Range,
};

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct WrapForwardRange {
    start: usize,
    end: usize,
    reset: usize,
    overflow: usize,
}

impl WrapForwardRange {
    pub(crate) fn new(range: Range<usize>, full: Range<usize>) -> Self {
        if range.start > range.end {
            Self {
                start: range.start,
                end: full.end,
                reset: full.start,
                overflow: range.end,
            }
        } else {
            Self {
                start: range.start,
                end: range.end,
                reset: full.start,
                overflow: full.start,
            }
        }
    }
}

impl Iterator for WrapForwardRange {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.start;
        self.start += 1;
        if self.start > self.end {
            if self.overflow != self.reset {
                self.start = self.reset + 1;
                self.end = replace(&mut self.overflow, self.reset);
                Some(self.overflow)
            } else {
                None
            }
        } else {
            Some(next)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.end + self.overflow - self.start - self.reset;
        (len, Some(len))
    }
}

impl ExactSizeIterator for WrapForwardRange {}

#[test]
#[allow(clippy::reversed_empty_ranges)]
fn wrap_forward_iter_test() {
    // contained
    assert!(WrapForwardRange::new(0..0, 0..5).eq([]));
    assert!(WrapForwardRange::new(0..1, 0..5).eq([0]));
    assert!(WrapForwardRange::new(0..2, 0..5).eq([0, 1]));
    assert!(WrapForwardRange::new(0..3, 0..5).eq([0, 1, 2]));
    assert!(WrapForwardRange::new(0..4, 0..5).eq([0, 1, 2, 3]));
    assert!(WrapForwardRange::new(0..5, 0..5).eq([0, 1, 2, 3, 4]));
    assert!(WrapForwardRange::new(1..1, 0..5).eq([]));
    assert!(WrapForwardRange::new(1..2, 0..5).eq([1]));
    assert!(WrapForwardRange::new(1..3, 0..5).eq([1, 2]));
    assert!(WrapForwardRange::new(1..4, 0..5).eq([1, 2, 3]));
    assert!(WrapForwardRange::new(1..5, 0..5).eq([1, 2, 3, 4]));
    assert!(WrapForwardRange::new(1..2, 0..2).eq([1]));
    assert!(WrapForwardRange::new(1..3, 0..3).eq([1, 2]));
    assert!(WrapForwardRange::new(1..4, 0..4).eq([1, 2, 3]));
    assert!(WrapForwardRange::new(1..5, 0..5).eq([1, 2, 3, 4]));
    assert!(WrapForwardRange::new(1..2, 1..5).eq([1]));
    assert!(WrapForwardRange::new(2..3, 2..5).eq([2]));
    assert!(WrapForwardRange::new(3..4, 3..5).eq([3]));
    assert!(WrapForwardRange::new(4..5, 4..5).eq([4]));
    assert!(WrapForwardRange::new(1..2, 1..2).eq([1]));
    assert!(WrapForwardRange::new(2..3, 2..3).eq([2]));
    assert!(WrapForwardRange::new(3..4, 3..4).eq([3]));

    // wrapped
    assert!(WrapForwardRange::new(1..0, 0..5).eq([1, 2, 3, 4]));
    assert!(WrapForwardRange::new(3..2, 0..5).eq([3, 4, 0, 1]));
    assert!(WrapForwardRange::new(4..1, 0..5).eq([4, 0]));
    assert!(WrapForwardRange::new(4..2, 0..5).eq([4, 0, 1]));
    assert!(WrapForwardRange::new(4..3, 0..5).eq([4, 0, 1, 2]));
    assert!(WrapForwardRange::new(2..1, 0..3).eq([2, 0]));
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct WrapBackwardRange {
    start: usize,
    end: usize,
    reset: usize,
    overflow: usize,
}

impl WrapBackwardRange {
    pub(crate) fn new(range: Range<usize>, full: Range<usize>) -> Self {
        if range.start < range.end {
            Self {
                start: range.start,
                end: full.start,
                reset: full.end,
                overflow: range.end,
            }
        } else {
            Self {
                start: range.start,
                end: range.end,
                reset: full.end,
                overflow: full.end,
            }
        }
    }
}

impl Iterator for WrapBackwardRange {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start > self.end {
            let next = self.start;
            self.start -= 1;
            Some(next)
        } else if self.reset == self.overflow {
            None
        } else {
            let next = replace(&mut self.start, self.reset - 1);
            self.end = replace(&mut self.overflow, self.reset);
            Some(next)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.start + self.reset - self.end - self.overflow;
        (len, Some(len))
    }
}

impl ExactSizeIterator for WrapBackwardRange {}

#[test]
#[allow(clippy::reversed_empty_ranges)]
fn wrap_backward_iter_test() {
    // contained
    assert!(WrapBackwardRange::new(0..0, 0..5).eq([]));
    assert!(WrapBackwardRange::new(1..0, 0..5).eq([1]));
    assert!(WrapBackwardRange::new(2..0, 0..5).eq([2, 1]));
    assert!(WrapBackwardRange::new(3..0, 0..5).eq([3, 2, 1]));
    assert!(WrapBackwardRange::new(4..0, 0..5).eq([4, 3, 2, 1]));
    assert!(WrapBackwardRange::new(0..0, 0..0).eq([]));
    assert!(WrapBackwardRange::new(0..0, 1..1).eq([]));
    assert!(WrapBackwardRange::new(1..1, 0..0).eq([]));
    assert!(WrapBackwardRange::new(1..1, 1..1).eq([]));
    assert!(WrapBackwardRange::new(1..0, 1..2).eq([1]));
    assert!(WrapBackwardRange::new(1..0, 1..3).eq([1]));
    assert!(WrapBackwardRange::new(1..0, 1..4).eq([1]));
    assert!(WrapBackwardRange::new(2..1, 1..3).eq([2]));
    assert!(WrapBackwardRange::new(3..1, 1..4).eq([3, 2]));

    // wrapped
    assert!(WrapBackwardRange::new(0..2, 0..5).eq([0, 4, 3]));
    assert!(WrapBackwardRange::new(1..2, 0..5).eq([1, 0, 4, 3]));
    assert!(WrapBackwardRange::new(2..4, 0..5).eq([2, 1, 0]));
    assert!(WrapBackwardRange::new(0..1, 0..2).eq([0]));
    assert!(WrapBackwardRange::new(0..0, 0..2).eq([]));
    assert!(WrapBackwardRange::new(0..7, 0..9).eq([0, 8]));
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum WrapEitherRange {
    Forward(WrapForwardRange),
    Backward(WrapBackwardRange),
}

impl From<WrapForwardRange> for WrapEitherRange {
    fn from(forward: WrapForwardRange) -> Self {
        Self::Forward(forward)
    }
}

impl From<WrapBackwardRange> for WrapEitherRange {
    fn from(backward: WrapBackwardRange) -> Self {
        Self::Backward(backward)
    }
}

impl Iterator for WrapEitherRange {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Forward(range) => range.next(),
            Self::Backward(range) => range.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            Self::Forward(range) => range.size_hint(),
            Self::Backward(range) => range.size_hint(),
        }
    }
}

impl ExactSizeIterator for WrapEitherRange {}

#[allow(clippy::eval_order_dependence)]
pub fn extrema<T>(
    Range { mut start, end }: Range<usize>,
    mut value: impl FnMut(usize) -> T,
    mut less: impl FnMut(&T, &T) -> bool,
) -> [usize; 2] {
    macro_rules! next {
        () => {{
            let index = start;
            start += 1;
            (index, value(index))
        }};
    }
    if start + 1 >= end {
        return [start, end];
    }
    let [mut l, mut r] = [next!(), next!()];
    if less(&r.1, &l.1) {
        swap(&mut l, &mut r);
    }
    while start != end {
        let first = next!();
        if start != end {
            let second = next!();
            if less(&first.1, &second.1) {
                if less(&first.1, &l.1) {
                    l = first
                }
                if less(&r.1, &second.1) {
                    r = second
                }
            } else {
                if less(&second.1, &l.1) {
                    l = second
                }
                if less(&r.1, &first.1) {
                    r = first
                }
            }
        } else {
            if less(&first.1, &l.1) {
                l = first
            } else if less(&r.1, &first.1) {
                r = first
            }
            break;
        }
    }
    [l.0, r.0]
}

#[test]
fn extrema_test() {
    assert_eq!(extrema(0..4, |i| [0, 1, 2, 3][i], |a, b| a < b), [0, 3]);
    assert_eq!(extrema(0..4, |i| [0, 3, 2, 1][i], |a, b| a < b), [0, 1]);
    assert_eq!(extrema(0..4, |i| [3, 0, 2, 1][i], |a, b| a < b), [1, 0]);
    assert_eq!(extrema(0..4, |i| [2, 1, 3, 0][i], |a, b| a < b), [3, 2]);
}
