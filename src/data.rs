use {
    num_traits::{AsPrimitive, Float, FloatConst},
    std::{
        marker::PhantomData,
        ops::{Mul, Range, Sub},
    },
};

pub use {
    crate::utils::{WrapBackwardRange, WrapEitherRange, WrapForwardRange},
    mint::Point2 as Point,
};

pub trait Num: Copy + PartialOrd + Mul<Output = Self> + Sub<Output = Self> {}

impl<T: Float> Num for T {}

pub trait Idx: Copy {
    fn from_usize(n: usize) -> Self;

    fn into_usize(self) -> usize;
}

impl<T> Idx for T
where
    T: AsPrimitive<usize>,
    usize: AsPrimitive<T>,
{
    fn from_usize(n: usize) -> Self {
        n.as_()
    }
    fn into_usize(self) -> usize {
        self.as_()
    }
}

pub trait Polygon {
    type Scalar: Num;

    fn index_range(&self) -> Range<usize>;

    fn get_point(&self, index: usize) -> Point<Self::Scalar>;
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct SliceMapPolygon<'a, T, P = Point<T>, F = fn(P) -> Point<T>>
where
    T: Num,
    P: Copy,
    F: Fn(P) -> Point<T>,
{
    pub slice: &'a [P],
    pub map: F,
    phantom: PhantomData<T>,
}

impl<'a, T, P, F> SliceMapPolygon<'a, T, P, F>
where
    T: Num,
    P: Copy,
    F: Fn(P) -> Point<T>,
{
    pub fn new(slice: &'a [P], map: F) -> Self {
        Self {
            slice,
            map,
            phantom: Default::default(),
        }
    }
}

impl<'a, T, P, F> Polygon for SliceMapPolygon<'a, T, P, F>
where
    T: Num,
    P: Copy,
    F: Fn(P) -> Point<T>,
{
    type Scalar = T;

    fn index_range(&self) -> Range<usize> {
        0..self.slice.len()
    }

    #[inline]
    fn get_point(&self, index: usize) -> Point<T> {
        (self.map)(self.slice[index])
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct LenMapPolygon<T: Num, F: Fn(usize) -> Point<T> = fn(usize) -> Point<T>> {
    pub len: usize,
    pub map: F,
    phantom: PhantomData<T>,
}

impl<T: Num, F: Fn(usize) -> Point<T>> LenMapPolygon<T, F> {
    pub fn new(len: usize, map: F) -> Self {
        Self {
            len,
            map,
            phantom: Default::default(),
        }
    }
}

impl<T: Num, F: Fn(usize) -> Point<T>> Polygon for LenMapPolygon<T, F> {
    type Scalar = T;

    fn index_range(&self) -> Range<usize> {
        0..self.len
    }

    #[inline]
    fn get_point(&self, index: usize) -> Point<T> {
        (self.map)(index)
    }
}

pub trait Look {
    type Scalar: Num;
    type WrapRange: Iterator<Item = usize>;

    fn are_left_and_right(&self, first: Point<Self::Scalar>, second: Point<Self::Scalar>) -> bool;

    fn are_clockwise(
        &self,
        a: Point<Self::Scalar>,
        b: Point<Self::Scalar>,
        c: Point<Self::Scalar>,
    ) -> bool;

    fn are_prev_and_next(&self, first: usize, second: usize) -> bool;

    fn wrap_next(&self, index: usize, full: Range<usize>) -> usize;

    fn wrap_prev(&self, index: usize, full: Range<usize>) -> usize;

    fn wrap_range(&self, range: Range<usize>, full: Range<usize>) -> Self::WrapRange;
}

fn are_left_and_right<T: Num>(cot: T, first: Point<T>, second: Point<T>) -> bool {
    let lhs = second.x - first.x;
    let rhs = cot * (second.y - first.y);
    lhs > rhs
}

macro_rules! are_clockwise {
    ($lt_pi:expr => $a:expr, $b:expr, $c:expr) => {{
        let lhs = ($b.x - $a.x) * ($c.y - $b.y);
        let rhs = ($c.x - $b.x) * ($b.y - $a.y);
        if $lt_pi {
            lhs < rhs
        } else {
            lhs > rhs
        }
    }};
}

fn wrap_forward(index: usize, full: Range<usize>) -> usize {
    let increment = index + 1;
    if increment < full.end {
        increment
    } else {
        full.start
    }
}

fn wrap_backward(index: usize, full: Range<usize>) -> usize {
    if index > full.start {
        index - 1
    } else {
        full.end - 1
    }
}

macro_rules! are_prev_and_next {
    ($rev:expr => $first:expr, $second:expr) => {
        if $rev {
            $second < $first
        } else {
            $first < $second
        }
    };
}

macro_rules! wrap_next {
    ($rev:expr => $index:expr, $full:expr) => {
        if $rev {
            wrap_backward($index, $full)
        } else {
            wrap_forward($index, $full)
        }
    };
}

macro_rules! wrap_prev {
    ($rev:expr => $index:expr, $full:expr) => {
        if $rev {
            wrap_forward($index, $full)
        } else {
            wrap_backward($index, $full)
        }
    };
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct ConstLook<T: Num, const IS_CLOCKWISE: bool, const IS_EXTERIOR: bool, const LT_PI: bool> {
    pub cot: T,
}

impl<T: Num, const IS_CLOCKWISE: bool, const IS_EXTERIOR: bool, const LT_PI: bool>
    ConstLook<T, IS_CLOCKWISE, IS_EXTERIOR, LT_PI>
{
    pub fn from_cot(cot: T) -> Self {
        Self { cot }
    }

    pub fn from_angle(angle: T) -> Self
    where
        T: Float,
    {
        Self::from_cot(angle.tan().recip())
    }
}

macro_rules! impl_const_look {
    ($iter:ident: $is_clockwise:expr, $is_exterior:expr, $lt_pi:expr) => {
        impl<T: Num> Look for ConstLook<T, $is_clockwise, $is_exterior, $lt_pi> {
            type Scalar = T;
            type WrapRange = $iter;

            #[inline]
            fn are_left_and_right(&self, first: Point<T>, second: Point<T>) -> bool {
                are_left_and_right(self.cot, first, second)
            }

            #[inline]
            fn are_clockwise(&self, a: Point<T>, b: Point<T>, c: Point<T>) -> bool {
                are_clockwise!($lt_pi => a, b, c)
            }

            fn are_prev_and_next(&self, first: usize, second: usize) -> bool {
                are_prev_and_next!($is_clockwise ^ $is_exterior ^ $lt_pi => first, second)
            }

            fn wrap_next(&self, index: usize, full: Range<usize>) -> usize {
                wrap_next!($is_clockwise ^ $is_exterior ^ $lt_pi => index, full)
            }

            fn wrap_prev(&self, index: usize, full: Range<usize>) -> usize {
                wrap_prev!($is_clockwise ^ $is_exterior ^ $lt_pi => index, full)
            }

            fn wrap_range(&self, range: Range<usize>, full: Range<usize>) -> Self::WrapRange {
                $iter::new(range,full)
            }
        }
    };
}

impl_const_look!(WrapForwardRange:  false, false, false);
impl_const_look!(WrapForwardRange:  false, false, true);
impl_const_look!(WrapBackwardRange: false, true,  false);
impl_const_look!(WrapBackwardRange: false, true,  true);
impl_const_look!(WrapBackwardRange: true,  false, false);
impl_const_look!(WrapBackwardRange: true,  false, true);
impl_const_look!(WrapForwardRange:  true,  true,  false);
impl_const_look!(WrapForwardRange:  true,  true,  true);

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct EitherLook<T: Num> {
    pub cot: T,
    pub lt_pi: bool,
    pub rev: bool,
}

impl<T: Num> EitherLook<T> {
    pub fn from_cot(cot: T, is_clockwise: bool, is_exterior: bool, lt_pi: bool) -> Self {
        Self {
            cot,
            lt_pi,
            rev: is_clockwise ^ is_exterior ^ lt_pi,
        }
    }

    pub fn from_angle(mut angle: T, is_clockwise: bool, is_exterior: bool) -> Self
    where
        T: Float + FloatConst,
    {
        let tau = T::TAU();
        angle = angle % tau;
        if angle.is_sign_negative() {
            angle = angle + tau
        }
        let cot = angle.tan().recip();
        Self::from_cot(cot, is_clockwise, is_exterior, angle < T::PI())
    }
}

impl<T: Num> Look for EitherLook<T> {
    type Scalar = T;
    type WrapRange = WrapEitherRange;

    #[inline]
    fn are_left_and_right(&self, first: Point<T>, second: Point<T>) -> bool {
        are_left_and_right(self.cot, first, second)
    }

    #[inline]
    fn are_clockwise(&self, a: Point<T>, b: Point<T>, c: Point<T>) -> bool {
        are_clockwise!(self.lt_pi => a, b, c)
    }

    fn are_prev_and_next(&self, first: usize, second: usize) -> bool {
        are_prev_and_next!(self.rev => first, second)
    }

    fn wrap_next(&self, index: usize, full: Range<usize>) -> usize {
        wrap_next!(self.rev => index, full)
    }

    fn wrap_prev(&self, index: usize, full: Range<usize>) -> usize {
        wrap_prev!(self.rev => index, full)
    }

    fn wrap_range(&self, range: Range<usize>, full: Range<usize>) -> Self::WrapRange {
        if self.rev {
            WrapEitherRange::from(WrapBackwardRange::new(range, full))
        } else {
            WrapEitherRange::from(WrapForwardRange::new(range, full))
        }
    }
}

#[test]
fn either_look_test() {
    let points = [[1f32, 1.0], [1.0, -1.0], [-1.0, -2.0], [-1.0, 2.0]];
    let polygon = SliceMapPolygon::new(&points, Into::into);
    for angle in [179, 180, 181] {
        let look = EitherLook::from_angle((angle as f32).to_radians(), true, true);
        assert!(look.are_left_and_right(polygon.get_point(2), polygon.get_point(3)));
        let mut iter = look.wrap_range(2..3, polygon.index_range());
        assert_eq!(iter.next(), Some(2));
        assert_eq!(iter.next(), Some(1));
        assert_eq!(iter.next(), Some(0));
        assert_eq!(iter.next(), None);
    }
}
