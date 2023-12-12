# Copyright 2022 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Marco Bertuletti, ETH Zurich

#!/usr/bin/env python3

import numpy as np
import math as M
import argparse
import pathlib
from mako.template import Template
from scipy.linalg import solve_triangular
from sympy.combinatorics import Permutation

##################
# compute_result #
##################

def compute_bitreversal(N, R):
    # Decompose
    logR2 = []
    idx = N
    while (idx >= R):
        logR2.append(int(M.log2(R)))
        idx = idx // R
    if (idx > 1):
        logR2.append(int(M.log2(idx)))
    # Bitreversal
    indexes = []
    for x in range(N):
        result = 0
        for bits in logR2:
            mask = (0xffffffff >> (32 - bits))
            result = (result << bits) | (x & mask)
            x = x >> bits
        indexes.append(result)

    # Create transpositions table
    tps = []
    for c in Permutation.from_sequence(indexes).cyclic_form:
        for i in range(len(c) - 1):
            tps.append([c[i] * 8, c[-1] * 8])
    return tps

def gen_data_header_file(outdir: pathlib.Path.cwd(), tpl: pathlib.Path.cwd(), **kwargs):

    file = outdir / f"data_{kwargs['name']}.h"

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
        default=pathlib.Path(__file__).parent.absolute() / "data_ofdm.h.tpl",
        help='Path to mako template'
    )
    parser.add_argument(
        "-v",
        "--verbose",
        action='store_true',
        help='Set verbose'
    )
    parser.add_argument(
        "-rx",
        "--receivers",
        type=int,
        required=False,
        default=64,
        help='First dimension.'
    )
    parser.add_argument(
        "-bs",
        "--beams",
        type=int,
        required=False,
        default=32,
        help='Second dimension.'
    )
    parser.add_argument(
        "-sc",
        "--subcarriers",
        type=int,
        required=False,
        default=4096,
        help='Iterations.'
    )

    args = parser.parse_args()
    N_rx=args.receivers
    N_bs=args.beams
    N_sc=args.subcarriers

    pFFT_src = ( np.random.rand(2 * N_rx * N_sc)  ).astype(np.float16)
    pTw_coef = ( np.random.rand(int(3 * N_sc / 4))     ).astype(np.float16)
    pBF_coef = ( np.random.rand(2 * N_rx * N_bs)  ).astype(np.float16)
    pBF_dst = ( np.random.rand(2 * N_bs * N_sc)  ).astype(np.float16)

    Bitreversal = np.ndarray.flatten(np.array(compute_bitreversal(N_sc, 2)))

    kwargs = {'name': 'ofdm',
    'pFFT_src': pFFT_src,
    'pTw_coef': pTw_coef,
    'pBF_coef': pBF_coef,
    'pBF_dst': pBF_dst,
    'bitrev': Bitreversal,
    'N_rx' : N_rx,
    'N_bs' : N_bs,
    'N_sc' : N_sc,
    'Log2Len': int(np.log2(N_sc)),
    'BitrevLen': len(Bitreversal)}
    gen_data_header_file(args.outdir, args.tpl, **kwargs)

if __name__ == "__main__":
    main()
