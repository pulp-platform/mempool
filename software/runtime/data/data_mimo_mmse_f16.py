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

def gen_data_header_file(outdir: pathlib.Path.cwd(),
                         tpl: pathlib.Path.cwd(), **kwargs):

    file = outdir / f"{kwargs['name']}.h"

    print(tpl, outdir, kwargs['name'])

    template = Template(filename=str(tpl))
    with file.open('w') as f:
        f.write(template.render(**kwargs))


def gen_input_data(N_rx, N_tx, y):
    # Create channel matrix
    H = np.random.rand(N_rx, N_tx).astype(np.float16) + 1.j * \
        np.random.rand(N_rx, N_tx).astype(np.float16)
    # Generate noise variance
    sigma = np.diag(np.random.rand(N_tx, N_tx).astype(np.float16))

    # Matrix to be inverted in MMSE estimator
    H_h = (np.asmatrix(H).H)

    G = H_h * H
    G = G + np.diag(sigma)
    # Cholesky decomposition
    L = np.linalg.cholesky(G)
    # Linear system solution
    y1 = np.transpose(np.dot(H_h, y))
    y2 = solve_triangular(L, y1, lower=True)
    x = solve_triangular(np.asmatrix(L).H, y2)

    sigma = sigma + 0j
    H = np.reshape(np.asarray(H), (N_tx * N_rx), order='C')
    G = np.reshape(np.asarray(G), (N_tx * N_tx), order='C')
    L = np.reshape(np.asarray(L), (N_tx * N_tx), order='C')
    sigma = np.column_stack((sigma.real, sigma.imag)
                            ).astype(np.float16).flatten()
    H = np.column_stack((H.real, H.imag)).astype(np.float16).flatten()
    G = np.column_stack((G.real, G.imag)).astype(np.float16).flatten()
    L = np.column_stack((L.real, L.imag)).astype(np.float16).flatten()

    y = np.column_stack((y.real, y.imag)).astype(np.float16).flatten()
    x = np.column_stack((x.real, x.imag)).astype(np.float16).flatten()

    return sigma, H, G, y, x


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
    parser.add_argument(
        "-r",
        "--randomize",
        type=int,
        required=False,
        default=0,
        help='Randomizes the number of beamgroups on each subcarrier.'
    )

    args = parser.parse_args()
    N_tx = args.transmitters
    N_rx = args.receivers
    N_itr = args.iterations

    sigma = np.zeros([N_itr, 2 * N_tx])
    H_RI = np.zeros([N_itr, 2 * N_tx * N_rx])
    G_RI = np.zeros([N_itr, 2 * N_tx * N_tx])
    y_RI = np.zeros([N_itr, 2 * N_rx])
    x_RI = np.zeros([N_itr, 2 * N_tx])
    beamgroups = np.zeros(N_itr)

    for k in range(N_itr):

        # Create input vector
        y_bg = np.random.rand(N_rx).astype(np.float16) + 1.j * \
            np.random.rand(N_rx).astype(np.float16)
        if (args.randomize == 1):
            N_beamgroups = 2 ** np.random.randint(0, np.log2(2 * N_tx))
        else:
            N_beamgroups = 1
        N_tx_itr = N_tx // N_beamgroups
        beamgroups[k] = N_beamgroups

        for i in range(N_beamgroups):

            sigma_itr, H_itr, G_itr, y_itr, x_itr = gen_input_data(
                N_rx, N_tx_itr, y_bg)
            sigma[k, (i * 2 * N_tx_itr):((i + 1) * 2 * N_tx_itr)] = sigma_itr
            H_RI[k, (i * 2 * N_tx_itr * N_rx)
                     :((i + 1) * 2 * N_tx_itr * N_rx)] = H_itr
            G_RI[k, (i * 2 * N_tx_itr * N_tx_itr)
                     :((i + 1) * 2 * N_tx_itr * N_tx_itr)] = G_itr
            y_RI[k, :] = y_itr
            x_RI[k, (i * 2 * N_tx_itr):((i + 1) * 2 * N_tx_itr)] = x_itr

    sigma = np.reshape(sigma, (2 * N_tx * N_itr)).astype(np.float16)
    H_RI = np.reshape(H_RI, (2 * N_rx * N_tx * N_itr)).astype(np.float16)
    G_RI = np.reshape(G_RI, (2 * N_tx * N_tx * N_itr)).astype(np.float16)
    y_RI = np.reshape(y_RI, (2 * N_rx * N_itr)).astype(np.float16)
    x_RI = np.reshape(x_RI, (2 * N_tx * N_itr)).astype(np.float16)
    beamgroups = beamgroups.astype(np.int32)

    kwargs = {'name': 'data_mimo_mmse_f16',
              'H': H_RI,
              'G': G_RI,
              'sigma': sigma,
              'y': y_RI,
              'x': x_RI,
              'beamgroups': beamgroups,
              'N_tx': N_tx,
              'N_rx': N_rx,
              'N_itr': N_itr}

    gen_data_header_file(args.outdir, args.tpl, **kwargs)


if __name__ == "__main__":
    main()
