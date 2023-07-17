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
        default=pathlib.Path( __file__ ).parent.absolute(),
        required=False,
        help='Select out directory of generated data files'
    )
    parser.add_argument(
        "-t",
        "--tpl",
        type=pathlib.Path,
        required=False,
        default=pathlib.Path( __file__ ).parent.absolute() / "data_cholesky_f16.h.tpl",
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
    N=args.dimension

    # Create hermitian matrix
    H = np.random.rand(N, N) + 1.j * np.random.rand(N, N)
    # Matrix to be inverted
    G = H*(np.asmatrix(H).H)
    # Cholesky decomposition
    L = np.linalg.cholesky(G)

    G = np.reshape(G, (N*N, -1), order='C')
    L = np.reshape(L, (N*N, -1), order='C')
    G_RI = np.zeros(2*N*N)
    L_RI = np.zeros(2*N*N)

    for i in range(N*N):
        G_RI[2*i]   = G[i].real
        G_RI[2*i+1] = G[i].imag
        L_RI[2*i]   = L[i].real
        L_RI[2*i+1] = L[i].imag

    G_RI = G_RI.astype(np.float16)
    L_RI = L_RI.astype(np.float16)
    print("Input matrix in (Re, Im) format:\n",  G_RI)
    print("Output matrix in (Re, Im) format:\n", L_RI)


    kwargs = {'name': 'data_cholesky_f16', 'G': G_RI, 'L' : L_RI, 'N' : N}
    gen_data_header_file(args.outdir, args.tpl, **kwargs)

if __name__ == "__main__":
    main()
