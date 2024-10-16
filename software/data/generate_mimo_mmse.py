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
import pyflexfloat as ff
from scipy.linalg import solve_triangular


def gen_data_header_file(outdir: pathlib.Path.cwd(),
                         tpl: pathlib.Path.cwd(), **kwargs):

    file = outdir / f"{kwargs['name']}.h"

    print(tpl, outdir, kwargs['name'])

    template = Template(filename=str(tpl))
    with file.open('w') as f:
        f.write(template.render(**kwargs))


def generate_fmmse(N_tx, N_rx, N_itr, my_type):

    vH = np.zeros([N_itr, N_tx * 2 * N_rx], dtype=my_type)
    vG = np.zeros([N_itr, N_tx * 2 * N_tx], dtype=my_type)
    vy = np.zeros([N_itr, 2 * N_rx], dtype=my_type)
    vN = np.zeros([N_itr, 2 * N_tx], dtype=my_type)
    vx = np.zeros([N_itr, 2 * N_tx], dtype=my_type)

    for k in range(N_itr):

        # Create input vector
        y = np.random.rand(N_rx).astype(my_type) + 1.j * \
            np.random.rand(N_rx).astype(my_type)

        # Create channel matrix
        H = np.random.rand(N_rx, N_tx).astype(my_type) + 1.j * \
            np.random.rand(N_rx, N_tx).astype(my_type)
        # Generate noise variance
        N = np.random.rand(1).astype(my_type)

        # Matrix to be inverted in MMSE estimator
        H_h = np.asmatrix(H).H
        G = np.matmul(H_h, H) + N * np.eye(H.shape[1])
        N = N * np.ones(N_tx)

        # Cholesky decomposition
        L = np.linalg.cholesky(G)
        # Linear system solution
        y1 = np.transpose(np.dot(H_h, y))
        y2 = solve_triangular(L, y1, lower=True)
        x = solve_triangular(np.asmatrix(L).H, y2)

        H = np.reshape(np.asarray(H), (N_tx * N_rx), order='C')
        G = np.reshape(np.asarray(G), (N_tx * N_tx), order='C')
        N = np.column_stack((N.real, N.imag)).astype(my_type).flatten()
        H = np.column_stack((H.real, H.imag)).astype(my_type).flatten()
        G = np.column_stack((G.real, G.imag)).astype(my_type).flatten()
        x = np.column_stack((x.real, x.imag)).astype(my_type).flatten()
        y = np.column_stack((y.real, y.imag)).astype(my_type).flatten()

        vH[k, :] = H
        vG[k, :] = G
        vy[k, :] = y
        vN[k, :] = N
        vx[k, :] = x

    vN = np.reshape(vN, (2 * N_tx * N_itr)).astype(my_type)
    vH = np.reshape(vH, (2 * N_rx * N_tx * N_itr)).astype(my_type)
    vG = np.reshape(vG, (2 * N_tx * N_tx * N_itr)).astype(my_type)
    vy = np.reshape(vy, (2 * N_rx * N_itr)).astype(my_type)
    vx = np.reshape(vx, (2 * N_tx * N_itr)).astype(my_type)

    return vN, vH, vG, vy, vx


def generate_mimo_mmse_q16(N_tx, N_rx, N_itr):

    vN = np.zeros([N_itr, 2 * N_tx], dtype=np.int16)
    vH = np.zeros([N_itr, 2 * N_tx * N_rx], dtype=np.int16)
    vG = np.zeros([N_itr, 2 * N_tx * N_tx], dtype=np.int16)
    vy = np.zeros([N_itr, 2 * N_rx], dtype=np.int16)
    vx = np.zeros([N_itr, 2 * N_tx], dtype=np.int16)
    MAX = 2**15
    for k in range(N_itr):
        # Create channel matrix
        rH = np.random.randint(-MAX, MAX - 1, N_rx * N_tx, dtype=np.int16)
        iH = np.random.randint(-MAX, MAX - 1, N_rx * N_tx, dtype=np.int16)
        H = rH + 1.j * iH
        # Create input vector
        y = np.random.randint(-MAX, MAX - 1, N_rx, dtype=np.int16) + 1.j * \
            np.random.randint(-MAX, MAX - 1, N_rx, dtype=np.int16)
        # Generate noise variance
        N = np.random.randint(-MAX, MAX - 1, N_tx, dtype=np.int16)

        H = H.reshape(N_rx, N_tx)
        # Matrix to be inverted in MMSE estimator
        H_h = (np.asmatrix(H).H)
        # Hermitian
        G = np.matmul(H_h, H) + N

        # Matrix vector product
        y1 = np.transpose(np.dot(H_h, y))
        # Cholesky decomposition
        # L = np.linalg.cholesky(G)
        L = G
        # Linear system solution
        y2 = solve_triangular(L, y1, lower=True)
        x = solve_triangular(np.asmatrix(L).H, y2)

        vN[k, :] = np.column_stack((N.real, N.imag)).astype(np.int16).flatten()
        vH[k, :] = np.column_stack((H.real, H.imag)).astype(np.int16).flatten()
        vG[k, :] = np.column_stack((G.real, G.imag)).astype(np.int16).flatten()
        vy[k, :] = np.column_stack((y.real, y.imag)).astype(np.int16).flatten()
        vx[k, :] = np.column_stack((x.real, x.imag)).astype(np.int16).flatten()

    vN = np.reshape(vN, (2 * N_tx * N_itr)).astype(np.int16)
    vH = np.reshape(vH, (2 * N_rx * N_tx * N_itr)).astype(np.int16)
    vG = np.reshape(vG, (2 * N_tx * N_tx * N_itr)).astype(np.int16)
    vy = np.reshape(vy, (2 * N_rx * N_itr)).astype(np.int16)
    vx = np.reshape(vx, (2 * N_tx * N_itr)).astype(np.int16)

    return vN, vH, vG, vy, vx


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

    vN, vH, vG, vy, vx = generate_fmmse(
        N_tx, N_rx, N_itr, np.float32)
    tpl = pathlib.Path(__file__).parent.absolute() / "data_mimo_mmse_f32.h.tpl"
    kwargs = {'name': 'data_mimo_mmse_f32',
              'H': vH,
              'G': vG,
              'N': vN,
              'y': vy,
              'x': vx,
              'N_tx': N_tx,
              'N_rx': N_rx,
              'N_itr': N_itr}
    gen_data_header_file(args.outdir, tpl, **kwargs)

    vN, vH, vG, vy, vx = generate_fmmse(
        N_tx, N_rx, N_itr, np.float16)
    tpl = pathlib.Path(__file__).parent.absolute() / "data_mimo_mmse_f16.h.tpl"
    kwargs = {'name': 'data_mimo_mmse_f16',
              'H': vH,
              'G': vG,
              'N': vN,
              'y': vy,
              'x': vx,
              'N_tx': N_tx,
              'N_rx': N_rx,
              'N_itr': N_itr}
    gen_data_header_file(args.outdir, tpl, **kwargs)

    vN, vH, vG, vy, vx = generate_fmmse(
        N_tx, N_rx, N_itr, np.float16)
    tpl = pathlib.Path(__file__).parent.absolute() / "data_mimo_mmse_f8.h.tpl"
    kwargs = {'name': 'data_mimo_mmse_f8',
              'H': ff.array(vH, "e5m2"),
              'G': vG,
              'N': ff.array(vN, "e5m2"),
              'y': ff.array(vy, "e5m2"),
              'x': vx,
              'N_tx': N_tx,
              'N_rx': N_rx,
              'N_itr': N_itr}
    gen_data_header_file(args.outdir, tpl, **kwargs)

    vN, vH, vG, vy, vx = generate_mimo_mmse_q16(N_tx, N_rx, N_itr)
    tpl = pathlib.Path(__file__).parent.absolute() / "data_mimo_mmse_q16.h.tpl"
    kwargs = {'name': 'data_mimo_mmse_q16',
              'H': vH,
              'G': vG,
              'N': vN,
              'y': vy,
              'x': vx,
              'N_tx': N_tx,
              'N_rx': N_rx,
              'N_itr': N_itr}
    gen_data_header_file(args.outdir, tpl, **kwargs)


if __name__ == "__main__":
    main()
