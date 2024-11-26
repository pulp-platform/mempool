#!/usr/bin/env python3

# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# This script generates data for the fp16 matmul.
# Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

# The script generates random inputs for the C functions. The inputs are
# propagated though a python golden model. Golden models are from the
# numpy library or the qmath bit-true library.

import numpy as np
import math
import qmath
from scipy import signal


def select_maxval(my_type=np.int32):
    size = 8 * np.dtype(my_type).itemsize
    MAX = 2**(size - 2) - 1
    return MAX


def irandom(size, MAX, my_type=np.int16):
    """Generate random numbers.
    size (int or tuple): Size of the array to generate.
    mytype (np.dtype): Data type for the fixed-point representation.
    Defaults to np.int16.

    Returns:
        np.ndarray: Array of random fixed-point numbers.
    """
    return np.random.randint(-MAX, MAX - 1, size=size, dtype=my_type)


def icrandom(size, MAX, my_type=np.int16):
    """Generate random complex numbers.
    size (int or tuple): Size of the array to generate.
    mytype (np.dtype): Data type for the fixed-point representation.
    Defaults to np.int16.

    Returns:
        np.ndarray: Array of random complex fixed-point numbers.
    """
    real_part = np.random.randint(-MAX, MAX - 1, size=size, dtype=my_type)
    imag_part = np.random.randint(-MAX, MAX - 1, size=size, dtype=my_type)
    return real_part + 1j * imag_part


def generate_iarray(my_type=np.float32, defines={}):

    # Create random array of integers
    array_N = defines['array_N']
    MAX = select_maxval(my_type)
    A = irandom(MAX=MAX, size=(array_N), my_type=my_type)
    return A, defines


def generate_fmatmul(my_type=np.float32, defines={}):

    # Create matrix
    matrix_M = defines['matrix_M']
    matrix_N = defines['matrix_N']
    matrix_P = defines['matrix_P']
    A = (np.random.rand(matrix_M, matrix_N) - 0.5).astype(my_type)
    B = (np.random.rand(matrix_N, matrix_P) - 0.5).astype(my_type)
    C = np.matmul(A, B)

    A = np.reshape(A, (matrix_M * matrix_N), order='C').astype(my_type)
    B = np.reshape(B, (matrix_N * matrix_P), order='C').astype(my_type)
    C = np.reshape(C, (matrix_M * matrix_P), order='C').astype(my_type)

    return [A, B, C], defines


def generate_imatmul(my_type=np.int32, defines={}):

    # Create matrix
    matrix_M = defines['matrix_M']
    matrix_N = defines['matrix_N']
    matrix_P = defines['matrix_P']
    MAX = select_maxval(my_type)
    A = irandom(MAX=MAX, size=(matrix_M, matrix_N), my_type=my_type)
    B = irandom(MAX=MAX, size=(matrix_M, matrix_N), my_type=my_type)
    C = np.matmul(A, B)

    A = np.reshape(A, (matrix_M * matrix_N), order='C').astype(my_type)
    B = np.reshape(B, (matrix_N * matrix_P), order='C').astype(my_type)
    C = np.reshape(C, (matrix_M * matrix_P), order='C').astype(np.int32)

    return [A, B, C], defines


def generate_iaxpy(my_type=np.int32, defines={}):

    # Create matrix
    ALPHA = defines['ALPHA']
    array_N = defines['array_N']
    MAX = select_maxval(my_type)
    X = irandom(MAX=MAX, size=(array_N), my_type=my_type)
    Y = irandom(MAX=MAX, size=(array_N), my_type=my_type)
    Z = (Y + X * ALPHA).astype(my_type)

    return [X, Y, Z], defines


def generate_idotp(my_type=np.int32, defines={}):

    # Create matrix
    array_N = defines['array_N']
    MAX = select_maxval(my_type)
    X = irandom(MAX=MAX, size=(array_N), my_type=my_type)
    Y = irandom(MAX=MAX, size=(array_N), my_type=my_type)
    Z = np.array((np.dot(X, Y))).astype(my_type)

    return [X, Y, Z], defines


def generate_iconv(my_type=np.int32, defines={}):

    # Create matrix
    matrix_M = defines['matrix_M']
    matrix_N = defines['matrix_N']
    kernel_N = defines['kernel_N']
    MAX = select_maxval(my_type)
    X = irandom(MAX=MAX, size=(matrix_M, matrix_N), my_type=my_type)
    K = irandom(MAX=MAX, size=(kernel_N, kernel_N), my_type=my_type)
    Y = signal.convolve2d(X, K, mode="same", boundary='fill')

    X = X.flatten().astype(my_type)
    K = K.flatten().astype(my_type)
    Y = Y.flatten().astype(my_type)

    return [X, K, Y], defines


def generate_qchest(defines={}, fixed_point=15, my_type=np.int16):

    N_TX = defines['N_TX']
    N_RX = defines['N_RX']
    N_SAMPLES = defines['N_SAMPLES']

    qvector_pilot_tx = []
    qvector_pilot_rx = []
    qvector_Hest = []
    for k in range(N_SAMPLES):
        # Create pilots
        pilot_rx = icrandom(size=N_RX, MAX=2**7, my_type=np.int32)
        pilot_tx = icrandom(size=N_TX, MAX=2**7, my_type=np.int32)
        # Compute Hest
        Hest = qmath.qchest(pilot_rx, pilot_tx, fixed_point=8)

        pilot_tx = np.column_stack((pilot_tx.imag, pilot_tx.real))
        pilot_rx = np.column_stack((pilot_rx.imag, pilot_rx.real))
        qvector_pilot_tx.append(pilot_tx.astype(np.int16).flatten())
        qvector_pilot_rx.append(pilot_rx.astype(np.int16).flatten())
        qvector_Hest.append(Hest)

    qvector_pilot_tx = np.reshape(qvector_pilot_tx, [2 * N_TX * N_SAMPLES])
    qvector_pilot_rx = np.reshape(qvector_pilot_rx, [2 * N_RX * N_SAMPLES])
    qvector_Hest = np.reshape(qvector_Hest, [2 * N_TX * N_RX * N_SAMPLES])
    return [qvector_pilot_tx, qvector_pilot_rx, qvector_Hest], defines


def generate_qcholesky(defines={}, fixed_point=15, my_type=np.int32):

    matrix_N = defines['matrix_N']
    FIXED_POINT = defines['FIXED_POINT']

    A = irandom(size=(matrix_N, matrix_N), MAX=2**14, my_type=my_type)
    y = irandom(size=matrix_N, MAX=2**14, my_type=my_type)
    A = qmath.qmatmul(A.T, A, FIXED_POINT, my_type)
    L = qmath.qcholesky(A, fixed_point=FIXED_POINT, mytype=my_type)

    A = np.reshape(A, (matrix_N * matrix_N), order='C').astype(my_type)
    L = np.reshape(L, (matrix_N * matrix_N), order='C').astype(my_type)
    return [A, L, y], defines


def generate_cfft_q16(defines={}, fixed_point=15, my_type=np.int16):

    N_CSAMPLES = defines['N_CSAMPLES']
    src = icrandom(size=N_CSAMPLES, MAX=2**fixed_point, my_type=my_type)
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

    dst = np.fft.fft(src.astype(np.csingle) / (2**fixed_point))
    dst = dst * 2**(bit_shift_dict_q16[N_CSAMPLES])

    dst = (np.column_stack((dst.real, dst.imag))).flatten()
    src = (np.column_stack((src.real, src.imag))).flatten()
    dst = dst.astype(np.int16)
    src = src.astype(np.int16)

    twiddles = qmath.qtwiddleCoef(N_CSAMPLES)
    bitrever = qmath.bitreversal(N_CSAMPLES, 2)

    defines['LOG2'] = int(math.log2(N_CSAMPLES))
    defines['N_TWIDDLES'] = 3 * N_CSAMPLES // 4
    defines['BITREVINDEXTABLE_LENGTH'] = len(bitrever)
    defines['TOLERANCE'] = tolerance[N_CSAMPLES]

    return [src, dst, twiddles, bitrever], defines
