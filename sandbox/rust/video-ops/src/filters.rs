use stdweb::web::TypedArray;

use std::cmp::min;

pub fn grayscale(data: TypedArray<u8>) -> TypedArray<u8> {
    let mut data: Vec<u8> = data.to_vec();
    let n = data.len();

    for i in (0..n).step_by(4) {
        data[i+1] = data[i];
        data[i+2] = data[i];
    }

    (&data[..]).into()
}

pub fn negative(data: TypedArray<u8>) -> TypedArray<u8> {
    let mut data: Vec<u8> = data.to_vec();
    let n = data.len();

    for i in (0..n).step_by(4) {
        data[i] = 255 - data[i];
        data[i+1] = 255 - data[i+1];
        data[i+2] = 255 - data[i+2];
    }

    (&data[..]).into()
}

fn multi_filter(mut data: Vec<u8>, width: usize,
                step: usize, mag: u8, mult: u8,
                adj: usize) -> TypedArray<u8> {
    let n = data.len();
    let n = min(n - 4 * width, n - adj);

    for i in (0..n).step_by(step) {
        if i % 4 != 3 {
            data[i] = mag + mult * data[i] - data[i + adj] - data[i + 4 * width];
        }
    }

    (&data[..]).into()
}

pub fn sunset(data: TypedArray<u8>, width: i32) -> TypedArray<u8> {
    multi_filter(data.to_vec(), width as usize, 4, 127, 2, 4)
}

pub fn forest(data: TypedArray<u8>, width: i32) -> TypedArray<u8> {
    multi_filter(data.to_vec(), width as usize, 5, 127, 3, 1)
}

pub fn longhorn(data: TypedArray<u8>, width: i32) -> TypedArray<u8> {
    multi_filter(data.to_vec(), width as usize, 2, 27, 3, 2)
}

fn conv_filter(mut data: Vec<u8>, width: usize, height: usize,
               kernel: Vec<Vec<u8>>, divisor: u8, bias: u8,
               count: usize) -> TypedArray<u8> {
    let kernel_width = kernel[0].len();

    let kernel_height = kernel.len();
    let kernel_height_half = kernel_height / 2;

    for _ in 0..count {
        for y in 1..(height - 1) {
            for x in 1..(width - 1) {
                let px = (x + y * width) * 4;
                let mut r: u8 = 0;
                let mut g: u8 = 0;
                let mut b: u8 = 0;

                for ky in 0..kernel_height {
                    for kx in 0..kernel_width {
                        let kpx = 4 * (width * (y + (ky - kernel_height_half)) + (x + (kx - kernel_height_half)));

                        r += data[kpx + 0] * kernel[ky][kx];
                        g += data[kpx + 1] * kernel[ky][kx];
                        b += data[kpx + 2] * kernel[ky][kx];
                    }
                }

                data[px + 0] = r / divisor + bias;
                data[px + 1] = g / divisor + bias;
                data[px + 2] = b / divisor + bias;
            }
        }
    }

    (&data[..]).into()
}

pub fn blur(data: TypedArray<u8>, width: i32, height: i32) -> TypedArray<u8> {
    conv_filter(data.to_vec(), width as usize, height as usize,
                vec![vec![1,1,1], vec![1,1,1], vec![1,1,1]],
                9, 0, 3)
}

pub fn good_morning(data: TypedArray<u8>, width: i32, height: i32) -> TypedArray<u8> {
    conv_filter(data.to_vec(), width as usize, height as usize,
                vec![vec![255,255,1], vec![255,14,255], vec![1,255,255]],
                3, 0, 1)
}