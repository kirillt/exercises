#![feature(iterator_flatten)]

#[macro_use]
extern crate stdweb;

use stdweb::web::TypedArray;

fn triangulate_2d(contour: TypedArray<f32>, z: f64, r: f64, g: f64, b: f64) -> TypedArray<f32> {
    let contour = contour.to_vec();

    let n = contour.len();
    if n < 6 {
        js! {
            alert("Can't triangulate " + n / 2 + " vertices");
        }
        panic!();
    }

    let z = z as f32;
    let r = r as f32;
    let g = g as f32;
    let b = b as f32;

    let mut center = (0.0, 0.0);
    for i in (0..n).step_by(2) {
        center.0 = center.0 + contour[i];
        center.1 = center.1 + contour[i+1];
    }
    center.0 = 2.0 * center.0 / (n as f32);
    center.1 = 2.0 * center.1 / (n as f32);

    let center = vec![center.0, center.1, z, r, g, b];

    let mut result: Vec<f32> = vec![];
    for i in (0..n-2).step_by(2) {
        result.extend_from_slice(&[contour[i],   contour[i+1], z, r, g, b]);
        result.extend_from_slice(&[contour[i+2], contour[i+3], z, r, g, b]);
        result.extend_from_slice(&center[..]);
    }
    result.extend_from_slice(&[contour[n-2],   contour[n-1], z, r, g, b]);
    result.extend_from_slice(&[contour[0], contour[1], z, r, g, b]);
    result.extend_from_slice(&center[..]);


    (&result[..]).into()
}

fn main() {
    stdweb::initialize();

    js! {
        window.wasm = {};
        window.wasm.triangulate_2d = @{triangulate_2d};
    }

    stdweb::event_loop();
}