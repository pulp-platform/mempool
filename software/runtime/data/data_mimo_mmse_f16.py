#!/usr/bin/env python3

# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# This script generates data for the fp16 mmse.
# Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

import numpy as np
import argparse
import pathlib
from mako.template import Template
from scipy.linalg import solve_triangular


##################
# compute_result #
##################

def gen_data_header_file(outdir: pathlib.Path.cwd(), tpl: pathlib.Path.cwd(), **kwargs):

    file = outdir / f"{kwargs['name']}.h"

    print(tpl, outdir, kwargs['name'])

    template = Template(filename=str(tpl))
    with file.open('w') as f:
        f.write(template.render(**kwargs))


def gen_input_data(N_rx, N_tx):
    # Create channel matrix
    H = np.random.rand(N_rx, N_tx).astype(np.float16) + 1.j * \
        np.random.rand(N_rx, N_tx).astype(np.float16)
    # Create input vector
    b = np.random.rand(N_rx).astype(np.float16) + 1.j * \
        np.random.rand(N_rx).astype(np.float16)
    # Generate noise variance
    sigma = np.diag(np.random.rand(N_tx, N_tx).astype(np.float16))

    # Matrix to be inverted in MMSE estimator
    H_h = (np.asmatrix(H).H)

    G = H_h * H
    G = G + np.diag(sigma)
    # Cholesky decomposition
    L = np.linalg.cholesky(G)
    # Linear system solution
    s = np.transpose(np.dot(H_h, b))
    y = solve_triangular(L, s, lower=True)
    x = solve_triangular(np.asmatrix(L).H, y)

    H = np.reshape(np.asarray(H), (N_tx*N_rx), order='C')
    G = np.reshape(np.asarray(G), (N_tx*N_tx), order='C')
    L = np.reshape(np.asarray(L), (N_tx*N_tx), order='C')
    H = np.column_stack((H.real, H.imag)).astype(np.float16).flatten()
    G = np.column_stack((G.real, G.imag)).astype(np.float16).flatten()
    L = np.column_stack((L.real, L.imag)).astype(np.float16).flatten()

    b = np.column_stack((b.real, b.imag)).astype(np.float16).flatten()
    s = np.column_stack((s.real, s.imag)).astype(np.float16).flatten()
    x = np.column_stack((x.real, x.imag)).astype(np.float16).flatten()
    y = np.column_stack((y.real, y.imag)).astype(np.float16).flatten()

    return sigma, H, G, b, x


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
        "data_mimo_mmse_f16.h.tpl",
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
        "--transmitters",
        type=int,
        required=False,
        default=4,
        help='First dimension.'
    )
    parser.add_argument(
        "-m",
        "--receivers",
        type=int,
        required=False,
        default=32,
        help='First dimension.'
    )
    parser.add_argument(
        "-k",
        "--iterations",
        type=int,
        required=False,
        default=256,
        help='Iterations.'
    )

    args = parser.parse_args()
    N_tx = args.transmitters
    N_rx = args.receivers
    itr = args.iterations

    sigma = np.zeros([itr, N_tx])
    H_RI = np.zeros([itr, 2*N_tx*N_rx])
    G_RI = np.zeros([itr, 2*N_tx*N_tx])
    b_RI = np.zeros([itr, 2*N_rx])
    x_RI = np.zeros([itr, 2*N_tx])
    for k in range(itr):
        sigma[k, :], H_RI[k, :], G_RI[k, :], b_RI[k,
                                                  :], x_RI[k, :] = gen_input_data(N_rx, N_tx)

    sigma = np.reshape(sigma, (N_tx*itr)).astype(np.float16)
    H_RI = np.reshape(H_RI, (2*N_rx*N_tx*itr)).astype(np.float16)
    G_RI = np.reshape(G_RI, (2*N_tx*N_tx*itr)).astype(np.float16)
    b_RI = np.reshape(b_RI, (2*N_rx*itr)).astype(np.float16)
    x_RI = np.reshape(x_RI, (2*N_tx*itr)).astype(np.float16)

    kwargs = {'name': 'data_mimo_mmse_f16',
              'H': H_RI,
              'G': G_RI,
              'sigma': sigma,
              'b': b_RI,
              'x': x_RI,
              'N_tx': N_tx,
              'N_rx': N_rx,
              'N_itr': itr}

    gen_data_header_file(args.outdir, args.tpl, **kwargs)


if __name__ == "__main__":
    main()
