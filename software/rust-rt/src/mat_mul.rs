use alloc::format;
use core::convert::TryInto;
use print;
use println;

pub fn mat_mul_sequential(
    A: &[i8],
    B: &[i8],
    C: &mut [isize],
    M: usize,
    N: usize,
    P: usize,
    hartid: usize,
    numThreads: usize,
) {
    for i in 0..M {
        for j in 0..P {
            let mut c: isize = 0;
            for k in 0..N {
                c += A[i * N + k] as isize * B[k * P + j] as isize;
            }
            C[i * P + j] = c;
        }
    }
}

pub fn mat_mul_parallel_i8(
    A: &[i8],
    B: &[i8],
    C: &mut [isize],
    M: usize,
    N: usize,
    P: usize,
    hartid: usize,
    numThreads: usize,
) {
    for i in (hartid..M).step_by(numThreads.try_into().unwrap()) {
        for j in 0..P {
            let mut c: isize = 0;

            for k in 0..N {
                c += A[i * N + k] as isize * B[k * P + j] as isize;
            }
            C[i * P + j] = c;
        }
    }
}

pub fn mat_mul_unrolled_parallel_i8(
    A: &[i8],
    B: &[i8],
    C: &mut [isize],
    M: usize,
    N: usize,
    P: usize,
    hartid: usize,
    numThreads: usize,
) {
    for i in (hartid..M).step_by(numThreads.try_into().unwrap()) {
        for j in (0..P).step_by(4) {
            let mut c0: isize = 0;
            let mut c1: isize = 0;
            let mut c2: isize = 0;
            let mut c3: isize = 0;

            for k in 0..N {
                let val_a = A[i * N + k];
                let val_b0 = B[k * P + j + 0];
                let val_b1 = B[k * P + j + 1];
                let val_b2 = B[k * P + j + 2];
                let val_b3 = B[k * P + j + 3];

                c0 += val_a as isize * val_b0 as isize;
                c1 += val_a as isize * val_b1 as isize;
                c2 += val_a as isize * val_b2 as isize;
                c3 += val_a as isize * val_b3 as isize;
            }

            C[i * P + j + 0] = c0;
            C[i * P + j + 1] = c1;
            C[i * P + j + 2] = c2;
            C[i * P + j + 3] = c3;
        }
    }
}

pub fn mat_mul_unrolled_2x2_parallel_i8(
    A: &[i8],
    B: &[i8],
    C: &mut [isize],
    M: usize,
    N: usize,
    P: usize,
    hartid: usize,
    numThreads: usize,
) {
    let c: usize = 8;
    let c_start = (P / c) * (hartid % c);
    let c_end = (P / c) * ((hartid % c) + 1);
    for i in ((2 * (hartid / c))..M).step_by(2*(numThreads /c)) {
        for j in (c_start..c_end).step_by(2) {
            let mut  c00: isize = 0;
            let mut c01: isize = 0;
            let mut c10: isize = 0;
            let mut c11: isize = 0;

            for k in (0..N).step_by(2) {
                let val_a00: i8 = A[(i + 0) * N + k + 0];
                let val_a01: i8 = A[(i + 0) * N + k + 1];
                let val_a10: i8 = A[(i + 1) * N + k + 0];
                let val_a11: i8 = A[(i + 1) * N + k + 1];
                let val_b00: i8 = B[(k + 0) * P + j + 0];
                let val_b01: i8 = B[(k + 0) * P + j + 1];
                let val_b10: i8 = B[(k + 1) * P + j + 0];
                let val_b11: i8 = B[(k + 1) * P + j + 1];

                c00 += (val_a00 * val_b00) as isize;
                c00 += (val_a01 * val_b10) as isize;
                c01 += (val_a00 * val_b01) as isize;
                c01 += (val_a01 * val_b11) as isize;
                c10 += (val_a10 * val_b00) as isize;
                c10 += (val_a11 * val_b10) as isize;
                c11 += (val_a10 * val_b01) as isize;
                c11 += (val_a11 * val_b11) as isize;
            }
            C[(i + 0) * P + j + 0] = c00;
            C[(i + 0) * P + j + 1] = c01;
            C[(i + 1) * P + j + 0] = c10;
            C[(i + 1) * P + j + 1] = c11;
        }
    }
}

pub fn mat_mul_parallel_i32(
    A: &[isize],
    B: &[isize],
    C: &mut [isize],
    M: usize,
    N: usize,
    P: usize,
    hartid: usize,
    numThreads: usize,
) {
    for i in (hartid..M).step_by(numThreads) {
        for j in 0..P {
            let mut c: isize = 0;

            for k in 0..N {
                c += A[i * N + k] * B[k * P + j];
            }
            C[i * P + j] = c;
        }
    }
}

pub fn mat_mul_unrolled_parallel_i32(
    A: &[isize],
    B: &[isize],
    C: &mut [isize],
    M: usize,
    N: usize,
    P: usize,
    hartid: usize,
    numThreads: usize,
) {
    for i in (hartid..M).step_by(numThreads) {
        for j in (0..P).step_by(4) {
            let mut c0: isize = 0;
            let mut c1: isize = 0;
            let mut c2: isize = 0;
            let mut c3: isize = 0;

            for k in 0..N {
                let val_a = A[i * N + k];
                let val_b0 = B[k * P + j + 0];
                let val_b1 = B[k * P + j + 1];
                let val_b2 = B[k * P + j + 2];
                let val_b3 = B[k * P + j + 3];

                c0 += val_a * val_b0;
                c1 += val_a * val_b1;
                c2 += val_a * val_b2;
                c3 += val_a * val_b3;
            }

            C[i * P + j + 0] = c0;
            C[i * P + j + 1] = c1;
            C[i * P + j + 2] = c2;
            C[i * P + j + 3] = c3;
        }
    }
}

pub fn mat_mul_unrolled_2x2_parallel_i32(
    A: &[isize],
    B: &[isize],
    C: &mut [isize],
    M: usize,
    N: usize,
    P: usize,
    hartid: usize,
    numThreads: usize,
) {
    let c: usize = 8;
    let c_start = (P / c) * (hartid % c);
    let c_end = (P / c) * ((hartid % c) + 1);
    for i in ((2 * (hartid / c))..M).step_by(2*(numThreads / c)) {
        for j in (c_start..c_end).step_by(2) {
            let mut c00: isize = 0;
            let mut c01: isize = 0;
            let mut c10: isize = 0;
            let mut c11: isize = 0;

            for k in (0..N).step_by(2) {
                let val_a00: isize = A[(i + 0) * N + k + 0];
                let val_a01: isize = A[(i + 0) * N + k + 1];
                let val_a10: isize = A[(i + 1) * N + k + 0];
                let val_a11: isize = A[(i + 1) * N + k + 1];
                let val_b00: isize = B[(k + 0) * P + j + 0];
                let val_b01: isize = B[(k + 0) * P + j + 1];
                let val_b10: isize = B[(k + 1) * P + j + 0];
                let val_b11: isize = B[(k + 1) * P + j + 1];

                c00 += val_a00 * val_b00;
                c00 += val_a01 * val_b10;
                c01 += val_a00 * val_b01;
                c01 += val_a01 * val_b11;
                c10 += val_a10 * val_b00;
                c10 += val_a11 * val_b10;
                c11 += val_a10 * val_b01;
                c11 += val_a11 * val_b11;
            }
            C[(i + 0) * P + j + 0] = c00;
            C[(i + 0) * P + j + 1] = c01;
            C[(i + 1) * P + j + 0] = c10;
            C[(i + 1) * P + j + 1] = c11;
        }
    }
}

pub unsafe fn matrix_init_i8(
    matrix: &mut [i8],
    num_rows: usize,
    num_cols: usize,
    a: i8,
    b: i8,
    c: i8,
    hartid: usize,
    num_cores: usize,
) {
    for i in (hartid..num_rows).step_by(num_cores) {
        for j in 0..num_cols {
            matrix[i * num_cols + j] = a * (i as i8) + b * (j as i8) + c;
        }
    }
}

pub fn verify_matrix_i8(
    matrix: &mut [isize],
    num_rows: usize,
    num_cols: usize,
    inner_dim: usize,
    aa: i8,
    ab: i8,
    ac: i8,
    ba: i8,
    bb: i8,
    bc: i8,
    hartid: usize,
    num_cores: usize,
) -> isize {
    let n: isize = inner_dim as isize;

    for i in (hartid..num_rows).step_by(num_cores.try_into().unwrap()) {
        for j in 0..num_cols {
            let ii: isize = i as isize;
            let jj: isize = j as isize;
            let lin: isize = (aa as isize * bb as isize * ii * jj
                + aa as isize * bc as isize * ii
                + ac as isize * bb as isize * jj
                + ac as isize * bc as isize)
                * n;

            let qua: isize = ((aa as isize * ba as isize * ii
                + ab as isize * bb as isize * jj
                + ab as isize * bc as isize
                + ba as isize * ac as isize)
                * (n * (n - 1)))
                / 2;

            let cub: isize = ((ab as isize * ba as isize) * (n * (n - 1) * (2 * n - 1))) / 6;

            let golden: isize = lin + qua + cub;

            if matrix[i * num_cols + j] as isize != golden {
                if i + j == 0 {
                    return -1;
                } else {
                    return (i * num_cols + j).try_into().unwrap();
                }
            }
            matrix[i * num_cols + j] = 0;
        }
    }
    0
}

pub unsafe fn matrix_init_i32(
    matrix: &mut [isize],
    num_rows: usize,
    num_cols: usize,
    a: isize,
    b: isize,
    c: isize,
    hartid: usize,
    num_cores: usize,
) {
    for i in (hartid..num_rows).step_by(num_cores) {
        for j in 0..num_cols {
            matrix[i * num_cols + j] = a * i as isize + b * j as isize + c;
        }
    }
}

pub fn verify_matrix_i32(
    matrix: &mut [isize],
    num_rows: usize,
    num_cols: usize,
    inner_dim: usize,
    aa: isize,
    ab: isize,
    ac: isize,
    ba: isize,
    bb: isize,
    bc: isize,
    hartid: usize,
    num_cores: usize,
) -> isize {
    let n: isize = inner_dim as isize;

    for i in (hartid..num_rows).step_by(num_cores) {
        for j in 0..num_cols {
            let ii: isize = i as isize;
            let jj: isize = j as isize;
            let lin: isize = (aa * bb * ii * jj
                + aa * bc * ii
                + ac  * bb * jj
                + ac  * bc)
                * n;

            let qua: isize = ((aa * ba * ii
                + ab * bb * jj
                + ab * bc
                + ba * ac)
                * (n * (n - 1)))
                / 2;

            let cub: isize = ((ab * ba) * (n * (n - 1) * (2 * n - 1))) / 6;

            let golden: isize = lin + qua + cub;

            if matrix[i * num_cols + j] != golden {
                if i + j == 0 {
                    return -1;
                } else {
                    return (i * num_cols + j).try_into().unwrap();
                }
            }
            matrix[i * num_cols + j] = 0;
        }
    }
    0
}

pub fn print_matrix_8(matrix: &[i8], num_rows: usize, num_cols: usize) {
    for i in 0..num_rows {
        for j in 0..num_cols {
            let element = matrix[i * num_cols + j];
            print!("{} ", element);
        }
        println!(" ");
    }
}

pub fn print_matrix_32(matrix: &[isize], num_rows: usize, num_cols: usize) {
    for i in 0..num_rows {
        for j in 0..num_cols {
            let element = matrix[i * num_cols + j];
            print!("{} ", element);
        }
        println!(" ");
    }
}
