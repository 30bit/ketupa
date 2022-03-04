use {
    crate::{
        data::{Look, Point, Polygon},
        utils::extrema,
    },
    std::{
        mem::{replace, swap},
        ops::RangeInclusive,
    },
};

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct Chord<I> {
    pub leftmost: I,
    pub rightmost: I,
}

impl<I> Chord<I> {
    pub fn new(leftmost: I, rightmost: I) -> Self {
        Self {
            leftmost,
            rightmost,
        }
    }
}

impl<I> From<RangeInclusive<I>> for Chord<I> {
    fn from(range: RangeInclusive<I>) -> Self {
        let (leftmost, rightmost) = range.into_inner();
        Chord::new(leftmost, rightmost)
    }
}

impl<I> From<Chord<I>> for RangeInclusive<I> {
    fn from(chord: Chord<I>) -> Self {
        chord.leftmost..=chord.rightmost
    }
}

impl Chord<usize> {
    pub fn search_diameter<P: Polygon, L: Look<Scalar = P::Scalar>>(polygon: &P, look: &L) -> Self {
        let [leftmost, rightmost] = extrema(
            polygon.index_range(),
            |i| polygon.get_point(i),
            |a, b| look.are_left_and_right(*a, *b),
        );
        Chord::new(leftmost, rightmost)
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct Event {
    pub partially_visible_chord: Chord<usize>,
    pub is_concavity_left: bool,
}

impl Event {
    pub fn new(partially_visible_chord: Chord<usize>, is_concavity_left: bool) -> Self {
        Self {
            partially_visible_chord,
            is_concavity_left,
        }
    }
}

struct Node<P: Polygon> {
    index: usize,
    point: Point<P::Scalar>,
}

impl<P: Polygon> Clone for Node<P> {
    fn clone(&self) -> Self {
        Self::new(self.index, self.point)
    }
}

impl<P: Polygon> Copy for Node<P> {}

impl<P: Polygon> Node<P> {
    fn new(index: usize, point: Point<P::Scalar>) -> Self {
        Self { index, point }
    }

    fn get(polygon: &P, indices: &mut impl Iterator<Item = usize>) -> Option<Self> {
        let index = indices.next()?;
        Some(Self::new(index, polygon.get_point(index)))
    }
}

impl<P: Polygon> From<Node<P>> for (usize, Point<P::Scalar>) {
    fn from(node: Node<P>) -> Self {
        (node.index, node.point)
    }
}

#[derive(Copy, Clone)]
pub struct EventIter<'a, P: Polygon, L: Look<Scalar = P::Scalar>> {
    polygon: &'a P,
    look: &'a L,
    wrap_range: L::WrapRange,
    left: Node<P>,
    right: Node<P>,
    rightmost: Option<usize>,
    exhausted: bool,
}

impl<'a, P: Polygon, L: Look<Scalar = P::Scalar>> EventIter<'a, P, L> {
    pub fn new(polygon: &'a P, look: &'a L, diameter: Chord<usize>) -> Self
    where
        L::WrapRange: std::fmt::Debug,
    {
        let full = polygon.index_range();
        let mut wrap_range = look.wrap_range(diameter.leftmost..diameter.rightmost, full);
        let _leftmost = wrap_range.next();
        let right_index = wrap_range.next();
        let left = Node::new(diameter.leftmost, polygon.get_point(diameter.leftmost));
        let right = if let Some(right_index) = right_index {
            Node::new(right_index, polygon.get_point(right_index))
        } else {
            left
        };
        Self {
            polygon,
            look,
            wrap_range,
            left,
            right,
            rightmost: Some(diameter.rightmost),
            exhausted: false,
        }
    }
}

fn surpass<P: Polygon>(
    polygon: &P,
    wrap_range: &mut impl Iterator<Item = usize>,
    prev: &mut Node<P>,
    edge: Point<P::Scalar>,
    f: &impl Fn(Point<P::Scalar>, Point<P::Scalar>) -> bool,
) -> Option<Node<P>> {
    loop {
        let next = Node::get(polygon, wrap_range)?;
        if f(edge, next.point) {
            break Some(next);
        }
        *prev = next;
    }
}

fn turn<P: Polygon>(
    polygon: &P,
    wrap_range: &mut impl Iterator<Item = usize>,
    a: &mut Node<P>,
    b: &mut Node<P>,
    f: &impl Fn(Point<P::Scalar>, Point<P::Scalar>) -> bool,
) -> Option<Node<P>> {
    loop {
        let c = Node::get(polygon, wrap_range)?;
        if f(b.point, c.point) {
            *a = replace(b, c);
            continue;
        }
        break Some(c);
    }
}

enum TurnAndSurpass<P: Polygon> {
    Finish,
    JustTurn,
    AndSurpass { last: Node<P> },
}

fn turn_and_surpass<P: Polygon>(
    polygon: &P,
    wrap_range: &mut impl Iterator<Item = usize>,
    a: &mut Node<P>,
    b: &mut Node<P>,
    just_turn: impl FnOnce(Point<P::Scalar>, Point<P::Scalar>, Point<P::Scalar>) -> bool,
    f: &impl Fn(Point<P::Scalar>, Point<P::Scalar>) -> bool,
) -> TurnAndSurpass<P> {
    let turning = if let Some(node) = turn(polygon, wrap_range, a, b, f) {
        node
    } else {
        return TurnAndSurpass::Finish;
    };
    if just_turn(replace(a, turning).point, b.point, turning.point) {
        TurnAndSurpass::JustTurn
    } else if let Some(mut surpassing) = surpass(polygon, wrap_range, a, b.point, f) {
        swap(b, &mut surpassing);
        TurnAndSurpass::AndSurpass { last: surpassing }
    } else {
        TurnAndSurpass::Finish
    }
}

impl<'a, P: Polygon, L: Look<Scalar = P::Scalar>> Iterator for EventIter<'a, P, L> {
    type Item = Event;

    fn next(&mut self) -> Option<Self::Item> {
        let leftmost = self.left.index;
        match turn_and_surpass(
            self.polygon,
            &mut self.wrap_range,
            &mut self.left,
            &mut self.right,
            |a, b, c| self.look.are_clockwise(a, b, c),
            &|a, b| self.look.are_left_and_right(a, b),
        ) {
            TurnAndSurpass::Finish if self.exhausted => return None,
            TurnAndSurpass::Finish => {
                let right = if let Some(rightmost) = self.rightmost {
                    self.rightmost = None;
                    replace(&mut self.right.index, rightmost)
                } else {
                    self.exhausted = true;
                    self.right.index
                };
                return Some(Event::new(Chord::new(leftmost, right), true));
            }
            TurnAndSurpass::AndSurpass { last } => {
                return Some(Event::new(Chord::new(leftmost, last.index), true))
            }
            TurnAndSurpass::JustTurn => (),
        };
        let event_chord = Chord::new(leftmost, self.right.index);
        loop {
            match turn_and_surpass(
                self.polygon,
                &mut self.wrap_range,
                &mut self.right,
                &mut self.left,
                |a, b, c| self.look.are_clockwise(c, b, a),
                &|a, b| self.look.are_left_and_right(b, a),
            ) {
                TurnAndSurpass::AndSurpass { .. } => continue,
                TurnAndSurpass::Finish => {
                    if let Some(rightmost) = self.rightmost {
                        self.rightmost = None;
                        self.right.index = rightmost;
                    }
                    break;
                }
                TurnAndSurpass::JustTurn => break,
            }
        }
        Some(Event::new(event_chord, false))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let wrap_range_hint = self.wrap_range.size_hint().0;
        if wrap_range_hint == 0 {
            (0, Some(0))
        } else {
            (1, Some(wrap_range_hint / 2))
        }
    }
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct Buffer<I, J = I> {
    pub partially_visible_chords: Vec<Chord<I>>,
    pub concavity_direction_extrema: Vec<J>,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct Slice<'a, I, J = I> {
    pub partially_visible_chords: &'a [Chord<I>],
    pub concavity_direction_extrema: &'a [J],
    pub diameter: Chord<I>,
}
