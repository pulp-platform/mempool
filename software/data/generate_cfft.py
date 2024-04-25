#!/usr/bin/env python3

# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# This script generates data for the cfft kernel.
# Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

import numpy as np
import math as M
import argparse
import pathlib
from mako.template import Template
from sympy.combinatorics import Permutation

# Function to generate the expected result of the testcase.


def generate_cfft_q16(N):
    # Q16:
    # len=16:    Q1.15 -> Q5.11
    # len=32:    Q1.15 -> Q6.10
    # len=64:    Q1.15 -> Q7.9
    # len=128:   Q1.15 -> Q8.8
    # len=256:   Q1.15 -> Q9.7
    # len=512:   Q1.15 -> Q10.6
    # len=1024:  Q1.15 -> Q11.5
    # len=2048:  Q1.15 -> Q12.4
    # len=4096:  Q1.15 -> Q13.3
    src = (np.random.randint(-2**(15), 2**(15) - 1,
           2 * N, dtype=np.int16)).astype(np.int16)

    bit_shift_dict_q16 = {
        16: 11,
        32: 10,
        64: 9,
        128: 8,
        256: 7,
        512: 6,
        1024: 5,
        2048: 4,
        4096: 3}
    my_fixpoint = 15
    dst = np.zeros(2 * N, dtype=np.int16)
    complex_src = np.zeros(N, dtype=np.csingle)
    complex_dst = np.zeros(N, dtype=np.csingle)
    for i in range(N):
        shift = 2**(my_fixpoint)
        complex_src[i] = (src[2 * i].astype(np.csingle) / shift) + \
            1j * (src[2 * i + 1].astype(np.csingle) / shift)
    complex_dst = np.fft.fft(complex_src)
    for i in range(N):
        shift = 2**(bit_shift_dict_q16[N])
        dst[2 * i] = (np.real(complex_dst[i]) * shift).astype(np.int16)
        dst[2 * i + 1] = (np.imag(complex_dst[i]) * shift).astype(np.int16)
    return src, dst


def generate_cfft_f16(N):
    src = np.random.rand(N).astype(np.float16)
    src = src + 1.j * np.random.rand(N).astype(np.float16)
    dst = np.fft.fft(src)
    src = np.column_stack((src.imag, src.real)).astype(np.float16).flatten()
    dst = np.column_stack((dst.imag, dst.real)).astype(np.float16).flatten()
    return src, dst


def generate_twiddleCoefq15(N):
    PI = 3.14159265358979
    twiddleCoefq15 = np.zeros((int)(2 * 3 * N / 4), np.int16)
    for i in range(0, (int)(3 * N / 4)):
        twiddleCoefq15_cos = M.cos(i * 2 * PI / N)
        twiddleCoefq15_sin = M.sin(i * 2 * PI / N)
        twiddleCoefq15[2 * i] = int(round(twiddleCoefq15_cos * (2**15 - 1)))
        twiddleCoefq15[2 * i +
                       1] = int(round(twiddleCoefq15_sin * (2**15 - 1)))
    return twiddleCoefq15


def generate_twiddleCoeff16(N):
    PI = np.pi
    twiddleCoeff16 = np.zeros((int)(2 * 3 * N / 4), np.float16)
    for i in range(0, int(3 * N / 4)):
        twiddleCoeff16_sin = np.sin(i * 2 * PI / N).astype(np.float16)
        twiddleCoeff16_cos = np.cos(i * 2 * PI / N).astype(np.float16)
        twiddleCoeff16[2 * i] = twiddleCoeff16_sin
        twiddleCoeff16[2 * i + 1] = twiddleCoeff16_cos
    return twiddleCoeff16


def generate_bitreversal(N, R):
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
    return np.ndarray.flatten(np.array(tps))


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
        "-d",
        "--dimension",
        type=int,
        required=False,
        default=64,
        help='Input dimension'
    )

    args = parser.parse_args()

    # Create inputs cfft_q16
    Len = args.dimension
    src_cfft_q16, dst_cfft_q16 = generate_cfft_q16(Len)
    twi_cfft_q16 = generate_twiddleCoefq15(Len)
    brv_cfft_q16 = generate_bitreversal(Len, 2)
    tolerance = {
        16: 16,
        32: 20,
        64: 24,
        128: 28,
        256: 32,
        512: 48,
        1024: 64,
        2048: 96,
        4096: 128}

    kwargs = {'name': 'data_cfft_radix4_q16',
              'vector_inp': src_cfft_q16,
              'vector_res': dst_cfft_q16,
              'vector_twi': twi_cfft_q16,
              'vector_bitrev': brv_cfft_q16,
              'Len': Len,
              'Log2Len': int(np.log2(Len)),
              'BitrevLen': len(brv_cfft_q16),
              'tolerance': tolerance[int(Len)]}
    gen_data_header_file(
        args.outdir,
        pathlib.Path(__file__).parent.absolute() /
        "data_cfft_q16.h.tpl",
        **kwargs)

    kwargs = {'name': 'data_cfft_radix2_q16',
              'vector_inp': src_cfft_q16,
              'vector_res': dst_cfft_q16,
              'vector_twi': twi_cfft_q16,
              'vector_bitrev': brv_cfft_q16,
              'Len': Len,
              'Log2Len': int(np.log2(Len)),
              'BitrevLen': int(2 * len(brv_cfft_q16)),
              'tolerance': tolerance[int(Len)]}
    gen_data_header_file(
        args.outdir,
        pathlib.Path(__file__).parent.absolute() /
        "data_cfft_q16.h.tpl",
        **kwargs)

    # Create inputs cfft_f16
    Len = args.dimension
    src_cfft_f16, dst_cfft_f16 = generate_cfft_f16(Len)
    twi_cfft_f16 = generate_twiddleCoeff16(Len)

    kwargs = {'name': 'data_cfft_radix4_f16',
              'vector_inp': src_cfft_f16,
              'vector_res': dst_cfft_f16,
              'vector_twi': twi_cfft_f16,
              'vector_bitrev': brv_cfft_q16,
              'Len': Len,
              'Log2Len': int(np.log2(Len)),
              'BitrevLen': len(brv_cfft_q16)}
    gen_data_header_file(
        args.outdir,
        pathlib.Path(__file__).parent.absolute() /
        "data_cfft_f16.h.tpl",
        **kwargs)


if __name__ == "__main__":
    main()
