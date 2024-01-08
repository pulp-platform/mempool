#!/usr/bin/env python3

# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# This script generates data for the fp16 cholesky.
# Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

import numpy as np
import argparse
import pathlib
from scipy.linalg import solve_triangular
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
        "data_cholesky_q32.h.tpl",
        help='Path to mako template'
    )
    parser.add_argument(
        "-v",
        "--verbose",
        action='store_true',
        help='Set verbose'
    )
    parser.add_argument(
        "-n",
        "--dimension",
        type=int,
        required=False,
        default=4,
        help='Matrix dimension'
    )

    args = parser.parse_args()
    n_matrix = args.dimension

    # Create hermitian matrix
    L = np.random.randint(-2**(15), 2**(15) - 1,
                          size=(n_matrix, n_matrix), dtype=np.int32)
    L = np.tril(L).astype(np.int32)
    G = np.dot(np.asmatrix(L), np.asmatrix(L).transpose())

    y = np.random.randint(-2**(15), 2**(15) - 1, n_matrix, dtype=np.int32)

    # Linear system solution
    y = solve_triangular(L, y, lower=True)
    # x = solve_triangular(np.asmatrix(L).T, y)

    # Reshape
    G = np.reshape(
        np.asarray(G),
        (n_matrix * n_matrix),
        order='C').astype(
        np.int32)
    L = np.reshape(
        np.asarray(L),
        (n_matrix * n_matrix),
        order='C').astype(
        np.int32)
    y = np.reshape(np.asarray(y), (n_matrix), order='C').astype(np.int32)

    kwargs = {'name': 'data_cholesky_q32',
              'G': G,
              'L': L,
              'y': y,
              'n_matrix': n_matrix}

    gen_data_header_file(args.outdir, args.tpl, **kwargs)


if __name__ == "__main__":
    main()
