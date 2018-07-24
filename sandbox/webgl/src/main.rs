#![feature(iterator_flatten)]

#[macro_use]
extern crate stdweb;
extern crate rand;

mod vector;
mod render;
mod figures;
mod shapes;

use vector::*;
use render::*;
use figures::Triangle;
use shapes::Tetrahedron;

use std::iter::Extend;
use stdweb::web::TypedArray;

fn scene(time: f64) -> TypedArray<f32> {
    let time = time as f32;

    let shapes= vec![
        Triangle {
            a: ORIGIN,
            b: ORIGIN,
            c: Vector { x: time.cos(), y: time.sin(), z: 0.0 },
            color: RED
        }
//        Tetrahedron {
//            base: Triangle {
//                a: UNIT_X,
//                b: UNIT_Y,
//                c: UNIT_Z,
//
//                color: RED
//            },
//            peak: Point {
//                position: ORIGIN,
//                color: GRAY
//            }
//        }.scale_eq(0.3).shift_x(-0.5),
//
//        Tetrahedron {
//            base: Triangle {
//                a: UNIT_X,
//                b: UNIT_Y,
//                c: UNIT_Z,
//
//                color: GREEN
//            },
//            peak: Point {
//                position: ORIGIN,
//                color: GRAY
//            }
//        }.rotate_yz(std::f32::consts::PI / 3.0).scale_eq(0.3),
//
//        Tetrahedron {
//            base: Triangle {
//                a: UNIT_X,
//                b: UNIT_Y,
//                c: UNIT_Z,
//
//                color: BLUE
//            },
//            peak: Point {
//                position: ORIGIN,
//                color: GRAY
//            }
//        }.rotate_yz(2.0 * std::f32::consts::PI / 3.0).scale_eq(0.3).shift_x(0.5),
    ];

    let mut simplexes = vec![];
    for shape in shapes {
        simplexes.extend(Renderable::render(shape));
    }

    let raw = Simplex2D::encode_all(simplexes);
    (&raw[..]).into()
}

fn main() {
    stdweb::initialize();

    js! {
        window.wasm = {};
        window.wasm.scene = @{scene};
    }

    stdweb::event_loop();
}