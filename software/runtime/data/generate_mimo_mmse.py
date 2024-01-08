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


def generate_mimo_mmse_f32(N_tx, N_rx, N_itr):

    vSigma = np.zeros([N_itr, N_tx], dtype=np.float32)
    vH = np.zeros([N_itr, 2 * N_tx * N_rx], dtype=np.float32)
    vG = np.zeros([N_itr, 2 * N_tx * N_tx], dtype=np.float32)
    vy = np.zeros([N_itr, 2 * N_rx], dtype=np.float32)
    vx = np.zeros([N_itr, 2 * N_tx], dtype=np.float32)

    for k in range(N_itr):
        # Create channel matrix
        H = np.random.rand(N_rx, N_tx).astype(np.float32) + 1.j * \
            np.random.rand(N_rx, N_tx).astype(np.float32)
        # Create input vector
        y = np.random.rand(N_rx).astype(np.float32) + 1.j * \
            np.random.rand(N_rx).astype(np.float32)
        # Generate noise variance
        sigma = np.diag(np.random.rand(N_tx).astype(np.float32))

        # Matrix to be inverted in MMSE estimator
        H_h = np.asmatrix(H).H
        G = np.matmul(H_h, H) + sigma

        # Cholesky decomposition
        L = np.linalg.cholesky(G)
        # Linear system solution
        y1 = np.transpose(np.dot(H_h, y))
        y2 = solve_triangular(L, y1, lower=True)
        x = solve_triangular(np.asmatrix(L).H, y2)

        sigma = np.diag(sigma)
        H = np.reshape(np.asarray(H), (N_tx * N_rx), order='C')
        G = np.reshape(np.asarray(G), (N_tx * N_tx), order='C')

        vSigma[k, :] = sigma.astype(np.float32).flatten()
        vH[k, :] = np.column_stack(
            (H.real, H.imag)).astype(np.float32).flatten()
        vG[k, :] = np.column_stack(
            (G.real, G.imag)).astype(np.float32).flatten()
        vy[k, :] = np.column_stack(
            (y.real, y.imag)).astype(np.float32).flatten()
        vx[k, :] = np.column_stack(
            (x.real, x.imag)).astype(np.float32).flatten()

    vSigma = np.reshape(vSigma, (N_tx * N_itr)).astype(np.float32)
    vH = np.reshape(vH, (2 * N_rx * N_tx * N_itr)).astype(np.float32)
    vG = np.reshape(vG, (2 * N_tx * N_tx * N_itr)).astype(np.float32)
    vy = np.reshape(vy, (2 * N_rx * N_itr)).astype(np.float32)
    vx = np.reshape(vx, (2 * N_tx * N_itr)).astype(np.float32)

    return vSigma, vH, vG, vy, vx


def generate_mimo_mmse_f16(N_tx, N_rx, N_itr, randomize):

    vSigma = np.zeros([N_itr, 2 * N_tx], dtype=np.float16)
    vH = np.zeros([N_itr, 2 * N_tx * N_rx], dtype=np.float16)
    vG = np.zeros([N_itr, 2 * N_tx * N_tx], dtype=np.float16)
    vy = np.zeros([N_itr, 2 * N_rx], dtype=np.float16)
    vx = np.zeros([N_itr, 2 * N_tx], dtype=np.float16)
    beamgroups = np.zeros(N_itr)

    for k in range(N_itr):

        # Create input vector
        y_bg = np.random.rand(N_rx).astype(np.float16) + 1.j * \
            np.random.rand(N_rx).astype(np.float16)
        if (randomize == 1):
            N_beamgroups = 2 ** np.random.randint(0, np.log2(2 * (N_tx - 1)))
        else:
            N_beamgroups = 1
        N_tx_itr = N_tx // N_beamgroups
        beamgroups[k] = N_beamgroups

        for i in range(N_beamgroups):

            # Create channel matrix
            H = np.random.rand(N_rx, N_tx_itr).astype(np.float16) + 1.j * \
                np.random.rand(N_rx, N_tx_itr).astype(np.float16)
            # Generate noise variance
            sigma = np.diag(np.random.rand(N_tx_itr).astype(np.float16))

            # Matrix to be inverted in MMSE estimator
            H_h = np.asmatrix(H).H
            G = np.matmul(H_h, H) + sigma

            # Cholesky decomposition
            L = np.linalg.cholesky(G)
            # Linear system solution
            y1 = np.transpose(np.dot(H_h, y_bg))
            y2 = solve_triangular(L, y1, lower=True)
            x = solve_triangular(np.asmatrix(L).H, y2)

            sigma = np.diag(sigma) + 0j
            H = np.reshape(np.asarray(H), (N_tx_itr * N_rx), order='C')
            G = np.reshape(np.asarray(G), (N_tx_itr * N_tx_itr), order='C')

            sigma = np.column_stack(
                (sigma.real, sigma.imag)).astype(
                np.float16).flatten()
            H = np.column_stack((H.real, H.imag)).astype(np.float16).flatten()
            G = np.column_stack((G.real, G.imag)).astype(np.float16).flatten()
            y = np.column_stack(
                (y_bg.real, y_bg.imag)).astype(
                np.float16).flatten()
            x = np.column_stack((x.real, x.imag)).astype(np.float16).flatten()

            vSigma[k, (i * 2 * N_tx_itr):((i + 1) * 2 * N_tx_itr)] = sigma
            vH[k, (i * 2 * N_tx_itr * N_rx):((i + 1) * 2 * N_tx_itr * N_rx)] = H
            vG[k, (i * 2 * N_tx_itr * N_tx_itr)
                   :((i + 1) * 2 * N_tx_itr * N_tx_itr)] = G
            vy[k, :] = y
            vx[k, (i * 2 * N_tx_itr):((i + 1) * 2 * N_tx_itr)] = x

    vSigma = np.reshape(vSigma, (2 * N_tx * N_itr)).astype(np.float16)
    vH = np.reshape(vH, (2 * N_rx * N_tx * N_itr)).astype(np.float16)
    vG = np.reshape(vG, (2 * N_tx * N_tx * N_itr)).astype(np.float16)
    vy = np.reshape(vy, (2 * N_rx * N_itr)).astype(np.float16)
    vx = np.reshape(vx, (2 * N_tx * N_itr)).astype(np.float16)
    beamgroups = beamgroups.astype(np.int32)

    return vSigma, vH, vG, vy, vx, beamgroups


def generate_mimo_mmse_q16(N_tx, N_rx, N_itr):

    vSigma = np.zeros([N_itr, 2 * N_tx], dtype=np.int16)
    vH = np.zeros([N_itr, 2 * N_tx * N_rx], dtype=np.int16)
    vG = np.zeros([N_itr, 2 * N_tx * N_tx], dtype=np.int16)
    vy = np.zeros([N_itr, 2 * N_rx], dtype=np.int16)
    vx = np.zeros([N_itr, 2 * N_tx], dtype=np.int16)
    for k in range(N_itr):
        # Create channel matrix
        H = np.random.randint(-2**(15), 2**(15) - 1, N_rx * N_tx, dtype=np.int16) \
            + 1.j * np.random.randint(-2**(15), 2 **
                                      (15) - 1, N_rx * N_tx, dtype=np.int16)
        # Create input vector
        y = np.random.randint(-2**(15), 2**(15) - 1, N_rx, dtype=np.int16) \
            + 1.j * np.random.randint(-2**(15), 2 **
                                      (15) - 1, N_rx, dtype=np.int16)
        # Generate noise variance
        sigma = np.random.randint(-2**(15), 2**(15) - 1, N_tx, dtype=np.int16)

        H = H.reshape(N_rx, N_tx)
        # Matrix to be inverted in MMSE estimator
        H_h = (np.asmatrix(H).H)
        # Hermitian
        G = np.matmul(H_h, H) + sigma

        # Matrix vector product
        y1 = np.transpose(np.dot(H_h, y))
        # Cholesky decomposition
        # L = np.linalg.cholesky(G)
        L = G
        # Linear system solution
        y2 = solve_triangular(L, y1, lower=True)
        x = solve_triangular(np.asmatrix(L).H, y2)

        sigma = sigma + 0j
        H = np.reshape(np.asarray(H), (N_rx * N_tx), order='C')
        G = np.reshape(np.asarray(G), (N_tx * N_tx), order='C')
        vSigma[k, :] = np.column_stack(
            (sigma.real, sigma.imag)).astype(np.int16).flatten()
        vH[k, :] = np.column_stack((H.real, H.imag)).astype(np.int16).flatten()
        vG[k, :] = np.column_stack((G.real, G.imag)).astype(np.int16).flatten()
        vy[k, :] = np.column_stack((y.real, y.imag)).astype(np.int16).flatten()
        vx[k, :] = np.column_stack((x.real, x.imag)).astype(np.int16).flatten()

    vSigma = np.reshape(vSigma, (2 * N_tx * N_itr)).astype(np.int16)
    vH = np.reshape(vH, (2 * N_rx * N_tx * N_itr)).astype(np.int16)
    vG = np.reshape(vG, (2 * N_tx * N_tx * N_itr)).astype(np.int16)
    vy = np.reshape(vy, (2 * N_rx * N_itr)).astype(np.int16)
    vx = np.reshape(vx, (2 * N_tx * N_itr)).astype(np.int16)

    return vSigma, vH, vG, vy, vx


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
        default=1,
        help='Iterations.'
    )

    args = parser.parse_args()
    N_tx = args.transmitters
    N_rx = args.receivers
    N_itr = args.iterations

    vSigma, vH, vG, vy, vx = generate_mimo_mmse_f32(N_tx, N_rx, N_itr)
    tpl = pathlib.Path(__file__).parent.absolute() / "data_mimo_mmse_f32.h.tpl"
    kwargs = {'name': 'data_mimo_mmse_f32',
              'H': vH,
              'G': vG,
              'sigma': vSigma,
              'y': vy,
              'x': vx,
              'N_tx': N_tx,
              'N_rx': N_rx,
              'N_itr': N_itr}
    gen_data_header_file(args.outdir, tpl, **kwargs)

    vSigma, vH, vG, vy, vx, beamgroups = generate_mimo_mmse_f16(
        N_tx, N_rx, N_itr, 1)
    tpl = pathlib.Path(__file__).parent.absolute() / "data_mimo_mmse_f16.h.tpl"
    kwargs = {'name': 'data_mimo_mmse_f16',
              'H': vH,
              'G': vG,
              'sigma': vSigma,
              'y': vy,
              'x': vx,
              'beamgroups': beamgroups,
              'N_tx': N_tx,
              'N_rx': N_rx,
              'N_itr': N_itr}
    gen_data_header_file(args.outdir, tpl, **kwargs)

    vSigma, vH, vG, vy, vx = generate_mimo_mmse_q16(N_tx, N_rx, N_itr)
    tpl = pathlib.Path(__file__).parent.absolute() / "data_mimo_mmse_q16.h.tpl"
    kwargs = {'name': 'data_mimo_mmse_q16',
              'H': vH,
              'G': vG,
              'sigma': vSigma,
              'y': vy,
              'x': vx,
              'N_tx': N_tx,
              'N_rx': N_rx,
              'N_itr': N_itr}
    gen_data_header_file(args.outdir, tpl, **kwargs)


if __name__ == "__main__":
    main()
