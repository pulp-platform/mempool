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


def gen_data_header_file(outdir: pathlib.Path.cwd(), tpl: pathlib.Path.cwd(), **kwargs):

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
        "data_cholesky_q16.h.tpl",
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
    parser.add_argument(
        "-s",
        "--num_samples",
        type=int,
        required=False,
        default=256,
        help='Number samples'
    )

    args = parser.parse_args()
    n_matrix = args.dimension
    n_samples = args.num_samples

    vector_G = []
    vector_L = []
    for k in range(n_samples):
        # Create hermitian matrix
        H = (np.random.randint(-2**(15), 2**(15) - 1, n_matrix * n_matrix, dtype=np.int16) + 1.j * \
            np.random.randint(-2**(15), 2**(15) - 1, n_matrix * n_matrix, dtype=np.int16)).reshape(n_matrix, n_matrix)
        # Matrix to be inverted
        H_h = (np.asmatrix(H).H)
        # H_H = np.asmatrix(H).H
        G = H_h * H
        # Cholesky decomposition
        L = np.linalg.cholesky(G)
        # Reshape
        G = np.reshape(np.asarray(G), (n_matrix * n_matrix), order='C')
        L = np.reshape(np.asarray(L), (n_matrix * n_matrix), order='C')
        G = np.column_stack((G.real, G.imag)).astype(np.int16).flatten()
        L = np.column_stack((L.real, L.imag)).astype(np.int16).flatten()
        # Output vectors
        vector_G.append(G)
        vector_L.append(L)

    vector_G = np.concatenate(vector_G, axis=0)
    vector_L = np.concatenate(vector_L, axis=0)

    kwargs = {'name': 'data_cholesky_q16',
              'G': vector_G,
              'L': vector_L,
              'n_matrix': n_matrix,
              'n_samples': n_samples}

    gen_data_header_file(args.outdir, args.tpl, **kwargs)


if __name__ == "__main__":
    main()
