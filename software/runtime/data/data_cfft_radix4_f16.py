#!/usr/bin/env python3

# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# This script generates data for the fp16 FFT.
# Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

import numpy as np
import math as M
import argparse
import pathlib
from mako.template import Template
from sympy.combinatorics import Permutation


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


def gen_data_header_file(
        outdir: pathlib.Path.cwd(),
        tpl: pathlib.Path.cwd(),
        **kwargs):

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
        "data_cfft_radix4_f16.h.tpl",
        help='Path to mako template')
    parser.add_argument(
        "-v",
        "--verbose",
        action='store_true',
        help='Set verbose'
    )
    parser.add_argument(
        "-d",
        "--dimension",
        type=int,
        required=False,
        default=4096,
        help='FFT dimension'
    )

    args = parser.parse_args()
    Len = args.dimension

    src = np.random.rand(Len) + 1.j * np.random.rand(Len)
    dst = np.fft.fft(src)

    twi_RI = np.zeros(2 * int(3 * Len / 4))
    for i in range(int(3 * Len / 4)):
        twi_RI[2 * i] = np.cos(i * 2 * np.pi / Len).astype(np.float16)
        twi_RI[2 * i + 1] = np.sin(i * 2 * np.pi / Len).astype(np.float16)

    Bitreversal = np.ndarray.flatten(np.array(compute_bitreversal(Len, 2)))

    src_RI = np.zeros(2 * Len)
    dst_RI = np.zeros(2 * Len)
    for i in range(Len):
        src_RI[2 * i] = (src[i].real).astype(np.float16)
        src_RI[2 * i + 1] = (src[i].imag).astype(np.float16)
        dst_RI[2 * i] = (dst[i].real).astype(np.float16)
        dst_RI[2 * i + 1] = (dst[i].imag).astype(np.float16)

    kwargs = {'name': 'data_cfft_radix4_f16',
              'src': src_RI,
              'dst': dst_RI,
              'twi': twi_RI,
              'bitrev': Bitreversal,
              'Len': Len,
              'Log2Len': int(np.log2(Len)),
              'BitrevLen': len(Bitreversal)}

    gen_data_header_file(args.outdir, args.tpl, **kwargs)


if __name__ == "__main__":
    main()
