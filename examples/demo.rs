use {
    clipboard::{ClipboardContext, ClipboardProvider},
    ketupa::{
        algorithm::{Chord, Event, EventIter},
        data::{EitherLook, Look, Polygon as _, SliceMapPolygon},
    },
    ketupa_demo_engine::{
        color, instance, layer_bounds, setup, tessellation_chain, transform, vec2, Color, Keys,
        LayerBounds, Mat2, Mouse, State, Vec2, Vec2Swizzles,
    },
    serde_json::{from_str, to_string},
    std::mem::take,
};

const LAYER_BOUNDS: &[LayerBounds] = &[layer_bounds(360, 720, 1); 9];

fn main() {
    let mut cursor = Cursor::new(0, Vec2::ONE * 40.0, 25.0);
    let mut bodies = [
        Body {
            left_concavities_layer_index: 1,
            right_concavities_layer_index: 2,
            shape_layer_index: 3,
            shadow_layer_index: 7,
            color: color(235, 137, 52, 238),
            // translation: vec2(-180.0, 65.0),
            points: vec![
                vec2(-120.0, 25.0),
                vec2(-45.0, 210.0),
                vec2(80.0, 135.0),
                vec2(105.0, -90.0),
                vec2(-20.0, -265.0),
            ],
            ..Default::default()
        },
        Body {
            left_concavities_layer_index: 4,
            right_concavities_layer_index: 5,
            shape_layer_index: 6,
            shadow_layer_index: 8,
            color: color(29, 180, 194, 238),
            translation: vec2(175.0, 12.5),
            points: vec![
                vec2(-100.0, 262.5),
                vec2(100.0, 187.5),
                vec2(0.0, -112.5),
                vec2(125.0, -87.5),
                vec2(-100.0, -212.5),
                vec2(-25.0, -37.5),
            ],
            ..Default::default()
        },
    ];
    let mut scroll = 0.0;
    setup("Demo", 0, 0, LAYER_BOUNDS).run(move |mut st: State| {
        scroll += st.mouse.scroll.y / 600.0;
        st.screen.set_clear_color(color(40, 31, 43, 255));
        st.screen.set_zoom(scroll.exp());

        cursor.draw(&mut st);
        if !cursor.input(&st) && !bodies[0].input(&mut st) && bodies[1].input(&mut st) {
            bodies.swap(0, 1);
        }
        let look_cos_sin = -cursor.cos_sin;
        let cursor_angle = look_cos_sin.y.atan2(look_cos_sin.x);
        for (i, mut body) in bodies.iter_mut().enumerate() {
            if i == 1 {
                break;
            }
            body.shadow_layer_index = i + 7;
            body.left_concavities_layer_index = i * 3 + 1;
            body.right_concavities_layer_index = body.left_concavities_layer_index + 1;
            body.shape_layer_index = body.right_concavities_layer_index + 1;
            body.draw(&mut st, cursor.is_stroked);
            body.release(&st);
            let look = EitherLook::from_angle(cursor_angle, true, !cursor.is_stroked);
            let mat = Mat2::from_angle(body.current_rotation_angle());
            let polygon = SliceMapPolygon::new(&body.points, |p| (mat * p).into());
            let diameter = Chord::search(&polygon, &look);
            body.draw_shadow(
                &mut st,
                look.wrap_range(diameter.leftmost..diameter.rightmost, polygon.index_range()),
                diameter,
                Vec2::from((cursor_angle - body.current_rotation_angle()).sin_cos()).yx(),
            );
            let event_iter = EventIter::new(&polygon, &look, diameter);
            body.draw_concavities(&mut st, look, event_iter);
        }
    })
}

#[derive(Default)]
pub struct AreaDrag {
    size: Vec2,
    start: Vec2,
    is_rotating: bool,
}

#[derive(Default)]
pub struct Body {
    left_concavities_layer_index: usize,
    right_concavities_layer_index: usize,
    shape_layer_index: usize,
    shadow_layer_index: usize,
    color: Color,
    points: Vec<Vec2>,
    translation: Vec2,
    rotation_angle: f32,
    point_drag_index: Option<usize>,
    area_drag: Option<AreaDrag>,
}

impl Body {
    const LEFT_CONCAVITIES_COLOR: Color = color(22, 71, 15, 255);
    const RIGHT_CONCAVITIES_COLOR: Color = color(145, 15, 6, 255);
    const CONCAVITIES_STROKE_WIDTH: f32 = 5.0;

    fn draw_concavities(&self, st: &mut State, look: impl Look, iter: impl Iterator<Item = Event>) {
        let instance = st.layers.get(self.shape_layer_index).unwrap().instances()[0];
        let mut left_tess = tessellation_chain(self.points.len() * 3);
        let mut right_tess = tessellation_chain(self.points.len() * 3);
        for event in iter {
            let tess = if event.is_concavity_left {
                &mut left_tess
            } else {
                &mut right_tess
            };
            let leftmost = event.partially_visible_chord.leftmost;
            let rightmost = event.partially_visible_chord.rightmost;
            tess.chain(
                look.wrap_range(leftmost..rightmost, 0..self.points.len())
                    .map(|i| self.points[i])
                    .chain([self.points[rightmost]]),
            );
        }
        let zoom = st.screen.zoom();
        let mut left = st
            .layers
            .get_mut(self.left_concavities_layer_index)
            .unwrap();
        st.tessellator.stroke_clear(
            left_tess.finish().iter(),
            Self::CONCAVITIES_STROKE_WIDTH * zoom,
        );
        left.set_indices(st.tessellator.indices().iter().cloned());
        left.set_vertices(st.tessellator.vertices().iter().cloned());
        left.set_instances([instance.with_color(Self::LEFT_CONCAVITIES_COLOR)]);
        let mut right = st
            .layers
            .get_mut(self.right_concavities_layer_index)
            .unwrap();
        st.tessellator.stroke_clear(
            right_tess.finish().iter(),
            Self::CONCAVITIES_STROKE_WIDTH * zoom,
        );
        right.set_indices(st.tessellator.indices().iter().cloned());
        right.set_vertices(st.tessellator.vertices().iter().cloned());
        right.set_instances([instance.with_color(Self::RIGHT_CONCAVITIES_COLOR)]);
    }

    const SHADOW_COLOR: Color = color(60, 60, 60, 238);

    fn draw_shadow(
        &self,
        st: &mut State,
        diameter_iter: impl Iterator<Item = usize>,
        diameter: Chord<usize>,
        direction: Vec2,
    ) {
        let iter = diameter_iter.map(|i| self.points[i]).chain(
            [self.points[diameter.rightmost]].into_iter().chain(
                [diameter.rightmost, diameter.leftmost]
                    .into_iter()
                    .map(|i| self.points[i] + direction * 10000.0),
            ),
        );
        let tesselation = tessellation_chain(self.points.len()).chain(iter).finish();
        st.tessellator.fill_clear(tesselation.iter());
        let instance = st.layers.get(self.shape_layer_index).unwrap().instances()[0];
        let mut layer = st.layers.get_mut(self.shadow_layer_index).unwrap();
        layer.set_indices(st.tessellator.indices().iter().cloned());
        layer.set_vertices(st.tessellator.vertices().iter().cloned());
        layer.set_instances([instance.with_color(Self::SHADOW_COLOR)]);
    }

    fn draw(&self, st: &mut State, is_stroked: bool) {
        let chain = tessellation_chain(self.points.len())
            .chain(self.points.iter().cloned())
            .close()
            .finish();
        if is_stroked {
            let width = st.screen.zoom() * 5.0;
            st.tessellator.stroke_clear(chain.iter(), width);
        } else {
            st.tessellator.fill_clear(chain.iter());
        }
        let mut layer = st.layers.get_mut(self.shape_layer_index).unwrap();
        layer.set_indices(st.tessellator.indices().iter().cloned());
        layer.set_vertices(st.tessellator.vertices().iter().cloned());
        let mut tr = self.translation;
        let mut rot = self.rotation_angle;
        if let Some(drag) = &self.area_drag {
            if drag.is_rotating {
                rot += drag.size.y * 0.3;
            } else {
                tr += drag.size;
            }
        }
        layer.set_instances([instance(transform(Vec2::ONE, rot, tr), self.color)])
    }

    fn input(&mut self, st: &mut State) -> bool {
        let world_mouse = st.screen.world_of(st.mouse.position);
        let mouse = Mat2::from_angle(-self.rotation_angle) * (world_mouse - self.translation);
        if let Some(index) = self.point_drag_index {
            self.points[index] = mouse;
        } else if let Some(drag) = &mut self.area_drag {
            drag.size = world_mouse - drag.start;
        } else if st.mouse.is_just_pressed(Mouse::RIGHT) {
            if let Some(index) = self.vertex_near(mouse) {
                if self.points.len() > 3 {
                    self.points.remove(index);
                }
            } else if self.is_inside(st, mouse) {
                self.area_drag = Some(AreaDrag {
                    start: world_mouse,
                    is_rotating: true,
                    ..Default::default()
                });
            } else {
                return false;
            }
        } else if st.mouse.is_pressed(Mouse::LEFT) {
            if let Some(index) = self.vertex_near(mouse) {
                self.point_drag_index = Some(index);
            } else if let Some(index) = self.segment_near(mouse) {
                self.points.insert(index + 1, mouse);
            } else if self.is_inside(st, mouse) {
                self.area_drag = Some(AreaDrag {
                    start: world_mouse,
                    is_rotating: false,
                    ..Default::default()
                });
            } else {
                return false;
            }
        } else if st.keys.is_logo || st.keys.is_ctrl {
            if st.keys.is_just_pressed(Keys::V) && self.is_inside(st, mouse) {
                if let Ok(mut context) = ClipboardContext::new() {
                    if let Ok(contents) = context.get_contents() {
                        if let Ok(points) = from_str::<Vec<Vec2>>(&contents) {
                            if points.len() > 3 {
                                self.points = points;
                            }
                        }
                    }
                }
            } else if st.keys.is_just_pressed(Keys::C) && self.is_inside(st, mouse) {
                if let Ok(mut context) = ClipboardContext::new() {
                    if let Ok(points) = to_string(&self.points) {
                        let _ = context.set_contents(points);
                    }
                }
            } else {
                return false;
            }
        } else {
            return false;
        }
        true
    }

    fn release(&mut self, st: &State) {
        if !st.mouse.is_pressed(Mouse::RIGHT) {
            if let Some(drag) = &mut self.area_drag {
                if drag.is_rotating {
                    self.rotation_angle += drag.size.y * 0.3;
                    self.area_drag = None;
                }
            }
        }
        if !st.mouse.is_pressed(Mouse::LEFT) {
            self.point_drag_index = None;
            if let Some(drag) = &mut self.area_drag {
                if !drag.is_rotating {
                    self.translation += drag.size;
                    self.area_drag = None;
                }
            }
        }
    }

    fn current_rotation_angle(&self) -> f32 {
        let mut angle = self.rotation_angle;
        if let Some(drag) = &self.area_drag {
            if drag.is_rotating {
                angle += drag.size.y * 0.3
            }
        }
        angle
    }

    fn segment_near(&self, target: Vec2) -> Option<usize> {
        if self.points.is_empty() {
            return None;
        }
        self.points
            .iter()
            .zip(self.points.iter().skip(1))
            .enumerate()
            .chain({
                let last = self.points.len() - 1;
                [(last, (&self.points[last], &self.points[0]))]
            })
            .filter_map(|(index, (&from, &to))| {
                let from_to = to - from;
                let length_recip = from_to.length_recip();
                if length_recip < 16.0 {
                    Some((index, from, to, from_to * length_recip))
                } else {
                    None
                }
            })
            .filter_map(|(index, from, to, from_to)| {
                let l = target - from;
                let d = l.dot(from_to);
                if d.is_sign_positive() != (target - to).dot(from_to).is_sign_positive() {
                    let h = l - from_to * d;
                    Some((index, h.length()))
                } else {
                    None
                }
            })
            .min_by(|(_, a), (_, b)| a.partial_cmp(b).unwrap())
            .and_then(
                |(index, distance)| {
                    if distance <= 10.0 {
                        Some(index)
                    } else {
                        None
                    }
                },
            )
    }

    fn vertex_near(&self, target: Vec2) -> Option<usize> {
        self.points.iter().position(|&o| target.distance(o) <= 20.0)
    }

    fn is_inside(&self, st: &State, target: Vec2) -> bool {
        let chunk = st.layers.get(self.shape_layer_index).unwrap();
        let is_clockwise = |k0, k1| {
            let [v1, v2] = [chunk.vertices()[k0 as usize], chunk.vertices()[k1 as usize]];
            (v2 - v1).perp_dot(target - v2) <= 0.0
        };
        for i in (0..chunk.indices_len()).step_by(3) {
            let j0 = chunk.get_index(i).unwrap();
            let j1 = chunk.get_index(i + 1).unwrap();
            let j2 = chunk.get_index(i + 2).unwrap();
            if is_clockwise(j0, j1) && is_clockwise(j1, j2) && is_clockwise(j2, j0) {
                return true;
            }
        }
        false
    }
}

#[derive(Default)]
pub struct Cursor {
    layer_index: usize,
    screen_padding: Vec2,
    radius: f32,
    cos_sin: Vec2,
    is_dragged: bool,
    is_stroked: bool,
    points: [Vec2; 3],
}

impl Cursor {
    const COLOR: Color = color(25, 23, 26, 255);

    fn new(layer_index: usize, screen_padding: Vec2, radius: f32) -> Self {
        Self {
            layer_index,
            screen_padding,
            radius,
            cos_sin: vec2(0.0, -1.0),
            is_dragged: false,
            is_stroked: false,
            points: [Vec2::ZERO; 3],
        }
    }

    fn draw(&mut self, st: &mut State) {
        self.points = {
            let position = self.position(st);
            let normal = st.screen.world_of(self.cos_sin);
            let first = position - normal * self.radius;
            let side = vec2(0.86603, 0.5) * self.radius;
            let base = position + normal * side.y;
            let second = base + normal.perp() * side.x;
            let third = base - normal.perp() * side.x;
            [first, second, third]
        };
        let mut layer = st.layers.get_mut(self.layer_index).unwrap();
        if self.is_stroked {
            let tesselation_chain = tessellation_chain(3)
                .chain(self.points.iter().cloned())
                .close()
                .finish();
            let width = st.screen.zoom() * 5.0;
            st.tessellator.stroke_clear(tesselation_chain.iter(), width);
            layer.set_indices(st.tessellator.indices().iter().cloned());
            layer.set_vertices(st.tessellator.vertices().iter().cloned());
        } else {
            layer.set_vertices(self.points);
            layer.set_indices([0, 1, 2]);
        }
        layer.set_instances([instance(Default::default(), Self::COLOR)]);
    }

    fn input(&mut self, st: &State) -> bool {
        let mouse = st.screen.world_of(st.mouse.position);
        self.cos_sin = if mouse == Vec2::ZERO {
            vec2(0.0, -1.0)
        } else {
            mouse.normalize()
        };
        if st.mouse.is_released(Mouse::LEFT) {
            return take(&mut self.is_dragged);
        }
        let is_clockwise = |i1, i2| {
            let [v1, v2]: [Vec2; 2] = [self.points[i1], self.points[i2]];
            (v2 - v1).perp_dot(mouse - v2) <= 0.0
        };
        if is_clockwise(0, 1) && is_clockwise(1, 2) && is_clockwise(2, 0) {
            if st.mouse.is_just_pressed(Mouse::LEFT) {
                self.is_stroked = !self.is_stroked;
                return true;
            } else if st.mouse.is_pressed(Mouse::LEFT) {
                self.is_dragged = true;
                return true;
            }
        }
        false
    }

    fn position(&self, st: &State) -> Vec2 {
        let half = st.screen.world_of(st.screen.half() - self.screen_padding);
        self.cos_sin * (self.cos_sin / half).length_recip()
    }
}
