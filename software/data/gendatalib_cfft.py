#!/usr/bin/env python3

# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# This script generates data for the cfft kernel.
# Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

import numpy as np
import math as M
from sympy.combinatorics import Permutation


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


def generate_cfft_q16(N_CSAMPLES):
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
    MAX = 2**(15)
    src = (np.random.randint(-MAX, MAX - 1, 2 *
           N_CSAMPLES, dtype=np.int16)).astype(np.int16)
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
    dst = np.zeros(2 * N_CSAMPLES, dtype=np.int16)
    complex_src = np.zeros(N_CSAMPLES, dtype=np.csingle)
    complex_dst = np.zeros(N_CSAMPLES, dtype=np.csingle)
    for i in range(N_CSAMPLES):
        shift = 2**(my_fixpoint)
        complex_src[i] = (src[2 * i].astype(np.csingle) / shift) + \
            1j * (src[2 * i + 1].astype(np.csingle) / shift)
    complex_dst = np.fft.fft(complex_src)
    for i in range(N_CSAMPLES):
        shift = 2**(bit_shift_dict_q16[N_CSAMPLES])
        dst[2 * i] = (np.real(complex_dst[i]) * shift).astype(np.int16)
        dst[2 * i + 1] = (np.imag(complex_dst[i]) * shift).astype(np.int16)

    twiddles = generate_twiddleCoefq15(N_CSAMPLES)
    bitrever = generate_bitreversal(N_CSAMPLES, 2)

    return src, dst, twiddles, bitrever, tolerance[N_CSAMPLES]
