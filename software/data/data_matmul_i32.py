#!/usr/bin/env python3

# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# This script generates data for the fp32 matmul.
# Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

import numpy as np
import argparse
import pathlib
from mako.template import Template


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
        "-t",
        "--tpl",
        type=pathlib.Path,
        required=False,
        default=pathlib.Path(__file__).parent.absolute() /
        "data_matmul_i32.h.tpl",
        help='Path to mako template'
    )
    parser.add_argument(
        "-v",
        "--verbose",
        action='store_true',
        help='Set verbose'
    )

    parser.add_argument(
        "-m",
        "--dim_m",
        type=int,
        required=False,
        default=128,
        help='First dimension.'
    )
    parser.add_argument(
        "-n",
        "--dim_n",
        type=int,
        required=False,
        default=128,
        help='Second dimension.'
    )
    parser.add_argument(
        "-p",
        "--dim_p",
        type=int,
        required=False,
        default=128,
        help='Third dimension.'
    )

    args = parser.parse_args()

    matrix_M = args.dim_m
    matrix_N = args.dim_n
    matrix_P = args.dim_p

    # Create matrix
    rng = np.random.default_rng()
    A = rng.integers(0, 2**15, (matrix_M, matrix_N), dtype=np.int32)
    B = rng.integers(0, 2**15, (matrix_N, matrix_P), dtype=np.int32)
    C = np.matmul(A, B)

    A = np.reshape(A, (matrix_M * matrix_N), order='C').astype(np.int32)
    B = np.reshape(B, (matrix_N * matrix_P), order='C').astype(np.int32)
    C = np.reshape(C, (matrix_M * matrix_P), order='C').astype(np.int32)

    kwargs = {
        'name': 'data_matmul_i32',
        'A': A,
        'B': B,
        'C': C,
        'matrix_M': matrix_M,
        'matrix_N': matrix_N,
        'matrix_P': matrix_P}

    gen_data_header_file(args.outdir, args.tpl, **kwargs)


if __name__ == "__main__":
    main()
