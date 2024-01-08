#!/usr/bin/env python3

# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# This script generates data for the fp16 matmul.
# Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

import numpy as np
import argparse
import pathlib
from mako.template import Template


def generate_cmatmul_f16(matrix_M, matrix_N, matrix_P):

    # Create matrix
    A = np.random.rand(matrix_M, matrix_N) + 1j * \
        np.random.rand(matrix_M, matrix_N)
    B = np.random.rand(matrix_N, matrix_P) + 1j * \
        np.random.rand(matrix_N, matrix_P)
    C = np.matmul(A, B)

    A = np.reshape(A, (matrix_M * matrix_N), order='C')
    B = np.reshape(B, (matrix_N * matrix_P), order='C')
    C = np.reshape(C, (matrix_M * matrix_P), order='C')

    A = np.column_stack((A.imag, A.real)).astype(np.float16).flatten()
    B = np.column_stack((B.imag, B.real)).astype(np.float16).flatten()
    C = np.column_stack((C.imag, C.real)).astype(np.float16).flatten()

    return A, B, C


def generate_cmatmul_q16(matrix_M, matrix_N, matrix_P):
    MAX = 2**15
    FIXED_POINT = 15

    # Create matrix
    A = np.random.randint(-MAX, MAX - 1, size=(matrix_M, matrix_N)) + 1j * \
        np.random.randint(-MAX, MAX - 1, size=(matrix_M, matrix_N))
    B = np.random.randint(-MAX, MAX - 1, size=(matrix_N, matrix_P)) + 1j * \
        np.random.randint(-MAX, MAX - 1, size=(matrix_N, matrix_P))

    C = np.zeros((matrix_M, matrix_P), dtype=complex)
    for k in range(matrix_P):
        for i in range(matrix_M):
            for j in range(matrix_N):
                a = A[i][j].real
                b = A[i][j].imag
                c = B[j][k].real
                d = B[j][k].imag
                C[i][k] += (a * c - b * d) // (1 << FIXED_POINT)
                C[i][k] += (b * c + a * d) // (1 << FIXED_POINT) * 1j

    A = np.reshape(A, (matrix_M * matrix_N), order='C')
    B = np.reshape(B, (matrix_N * matrix_P), order='C')
    C = np.reshape(C, (matrix_M * matrix_P), order='C')

    A = np.column_stack((A.imag, A.real)).astype(np.int16).flatten()
    B = np.column_stack((B.imag, B.real)).astype(np.int16).flatten()
    C = np.column_stack((C.imag, C.real)).astype(np.int16).flatten()

    return A, B, C


def generate_matmul_f16(matrix_M, matrix_N, matrix_P):

    # Create matrix
    A = (np.random.rand(matrix_M, matrix_N) - 0.5).astype(np.float16)
    B = (np.random.rand(matrix_N, matrix_P) - 0.5).astype(np.float16)
    C = np.matmul(A, B)

    A = np.reshape(A, (matrix_M * matrix_N), order='C').astype(np.float16)
    B = np.reshape(B, (matrix_N * matrix_P), order='C').astype(np.float16)
    C = np.reshape(C, (matrix_M * matrix_P), order='C').astype(np.float16)

    return A, B, C


def generate_matmul_f32(matrix_M, matrix_N, matrix_P):

    # Create matrix
    A = np.random.rand(matrix_M, matrix_N)
    B = np.random.rand(matrix_N, matrix_P)
    C = np.matmul(A, B)

    A = np.reshape(A, (matrix_M * matrix_N), order='C').astype(np.float32)
    B = np.reshape(B, (matrix_N * matrix_P), order='C').astype(np.float32)
    C = np.reshape(C, (matrix_M * matrix_P), order='C').astype(np.float32)

    return A, B, C

##################
# compute_result #
##################


def gen_data_header_file(outdir: pathlib.Path.cwd(),
                         tpl: pathlib.Path.cwd(), **kwargs):

    file = outdir / f"{kwargs['name']}.h"

    print(tpl, outdir, kwargs['name'])

    template = Template(filename=str(tpl))
    with file.open('w') as f:
        f.write(template.render(**kwargs))


def main():

    parser = argparse.ArgumentParser(description='Generate data for kernels')
    parser.add_argument(
        "-o",
        "--outdir",
        type=pathlib.Path,
        default=pathlib.Path(__file__).parent.absolute(),
        required=False,
        help='Select out directory of generated data files'
    )
    parser.add_argument(
        "-m",
        "--dim_m",
        type=int,
        required=False,
        default=16,
        help='First dimension.'
    )
    parser.add_argument(
        "-n",
        "--dim_n",
        type=int,
        required=False,
        default=16,
        help='Second dimension.'
    )
    parser.add_argument(
        "-p",
        "--dim_p",
        type=int,
        required=False,
        default=16,
        help='Third dimension.'
    )

    args = parser.parse_args()

    matrix_M = args.dim_m
    matrix_N = args.dim_n
    matrix_P = args.dim_p

    A, B, C = generate_cmatmul_f16(matrix_M, matrix_N, matrix_P)
    tpl = pathlib.Path(__file__).parent.absolute() / "data_cmatmul_f16.h.tpl"
    kwargs = {
        'name': 'data_cmatmul_f16',
        'A': A,
        'B': B,
        'C': C,
        'matrix_M': matrix_M,
        'matrix_N': matrix_N,
        'matrix_P': matrix_P}
    gen_data_header_file(args.outdir, tpl, **kwargs)

    A, B, C = generate_cmatmul_q16(matrix_M, matrix_N, matrix_P)
    tpl = pathlib.Path(__file__).parent.absolute() / "data_cmatmul_q16.h.tpl"
    kwargs = {
        'name': 'data_cmatmul_q16',
        'A': A,
        'B': B,
        'C': C,
        'matrix_M': matrix_M,
        'matrix_N': matrix_N,
        'matrix_P': matrix_P}
    gen_data_header_file(args.outdir, tpl, **kwargs)

    A, B, C = generate_matmul_f16(matrix_M, matrix_N, matrix_P)
    tpl = pathlib.Path(__file__).parent.absolute() / "data_matmul_f16.h.tpl"
    kwargs = {
        'name': 'data_matmul_f16',
        'A': A,
        'B': B,
        'C': C,
        'matrix_M': matrix_M,
        'matrix_N': matrix_N,
        'matrix_P': matrix_P}
    gen_data_header_file(args.outdir, tpl, **kwargs)

    A, B, C = generate_matmul_f32(matrix_M, matrix_N, matrix_P)
    tpl = pathlib.Path(__file__).parent.absolute() / "data_matmul_f32.h.tpl"
    kwargs = {
        'name': 'data_matmul_f32',
        'A': A,
        'B': B,
        'C': C,
        'matrix_M': matrix_M,
        'matrix_N': matrix_N,
        'matrix_P': matrix_P}
    gen_data_header_file(args.outdir, tpl, **kwargs)


if __name__ == "__main__":
    main()
