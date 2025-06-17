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
from scipy.linalg import solve_triangular


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


##############################################################################


def generate_faxpy(my_type=np.float32, defines={}):

    # Create matrix
    array_N = defines['array_N']
    A = np.random.rand(1) - 0.5
    X = (np.random.rand(array_N) - 0.5).astype(my_type)
    Y = (np.random.rand(array_N) - 0.5).astype(my_type)
    Z = (Y + X * A).astype(my_type)

    return [A, X, Y, Z], defines


def generate_fdotp(my_type=np.float32, defines={}):

    # Create matrix
    array_N = defines['array_N']
    X = (np.random.rand(array_N) - 0.5).astype(my_type)
    Y = (np.random.rand(array_N) - 0.5).astype(my_type)
    Z = np.dot(X, Y).astype(my_type)
    Z = np.array(Z).astype(my_type)
    Z = np.resize(Z, 1)

    return [X, Y, Z], defines


def ftwiddleCoef(N, my_type=np.float32):
    PI = np.pi
    twiddleCoeff16 = np.zeros((int)(2 * 3 * N / 4), my_type)
    for i in range(0, int(3 * N / 4)):
        twiddleCoeff16_sin = np.sin(i * 2 * PI / N).astype(my_type)
        twiddleCoeff16_cos = np.cos(i * 2 * PI / N).astype(my_type)
        twiddleCoeff16[2 * i] = twiddleCoeff16_sin
        twiddleCoeff16[2 * i + 1] = twiddleCoeff16_cos
    return twiddleCoeff16


def generate_fcfft(my_type=np.float32, defines={}):

    N_CSAMPLES = defines['N_CSAMPLES']
    src_r = np.random.normal(0, 5, N_CSAMPLES).astype(np.float16)
    src_i = np.random.normal(0, 5, N_CSAMPLES).astype(np.float16)
    src = src_r + 1.j * src_i
    src = np.fft.ifft(src)
    dst = np.fft.fft(src)
    src = np.column_stack((src.imag, src.real)).astype(my_type).flatten()
    dst = np.column_stack((dst.imag, dst.real)).astype(my_type).flatten()

    twiddles = ftwiddleCoef(N_CSAMPLES, my_type)
    bitrever = qmath.bitreversal(N_CSAMPLES, 2)

    defines['LOG2'] = int(math.log2(N_CSAMPLES))
    defines['N_TWIDDLES'] = 3 * N_CSAMPLES // 4
    defines['BITREVINDEXTABLE_LENGTH'] = len(bitrever)
    defines['TOLERANCE'] = 0.1 * np.max(dst)

    return [src, dst, twiddles, bitrever], defines


def generate_fchest(my_type=np.float32, defines={}, division=False):

    nb_tx = defines['N_TX']
    nb_rx = defines['N_RX']
    nb_samples = defines['N_SAMPLES']

    H = np.random.randn(nb_rx, nb_tx)
    H = H + 1j * np.random.randn(nb_rx, nb_tx)

    vpilot_tx = []
    vpilot_rx = []
    vHest = []
    for k in range(nb_samples):
        if (division):
            # Compute data division
            pilot_tx = 1 * np.exp(1j * np.random.randn(nb_tx))
            pilot_rx = np.dot(H, pilot_tx)
            Hest = pilot_rx[:, np.newaxis] / pilot_tx[np.newaxis, :]
        else:
            # Compute data multiplication
            pilot_tx = np.exp(1j * np.random.randn(nb_tx))
            pilot_rx = np.dot(H, pilot_tx)
            pilot_tx = np.reciprocal(pilot_tx)
            Hest = pilot_rx[:, np.newaxis] * pilot_tx[np.newaxis, :]
            Hest = Hest.flatten()

        # Interleaved real and imaginary parts
        pilot_tx = np.column_stack((pilot_tx.imag, pilot_tx.real))
        pilot_rx = np.column_stack((pilot_rx.imag, pilot_rx.real))
        Hest = np.column_stack((Hest.imag, Hest.real))
        # Flatten arrays
        pilot_tx = pilot_tx.astype(my_type).flatten()
        pilot_rx = pilot_rx.astype(my_type).flatten()
        Hest = Hest.astype(my_type).flatten()
        # Output vectors
        vpilot_tx.append(pilot_tx)
        vpilot_rx.append(pilot_rx)
        vHest.append(Hest)

    vpilot_rx = np.concatenate(vpilot_rx, axis=0)
    vpilot_tx = np.concatenate(vpilot_tx, axis=0)
    vHest = np.concatenate(vHest, axis=0)

    return [vpilot_tx, vpilot_rx, vHest], defines


def generate_fccholesky(my_type=np.float32, defines={}):

    n_matrix = defines['matrix_N']
    n_samples = defines['N_SAMPLES']

    vector_G = []
    vector_L = []
    for k in range(n_samples):
        # Create hermitian matrix
        H = np.random.rand(n_matrix, n_matrix) + 1.j * \
            np.random.rand(n_matrix, n_matrix)
        # Matrix to be inverted
        # H_H = np.asmatrix(H).H
        G = np.matmul(H, np.asmatrix(H).H)
        # Cholesky decomposition
        L = np.linalg.cholesky(G)
        # Reshape
        G = np.reshape(np.asarray(G), (n_matrix * n_matrix), order='C')
        L = np.reshape(np.asarray(L), (n_matrix * n_matrix), order='C')
        G = np.column_stack((G.real, G.imag)).astype(my_type).flatten()
        L = np.column_stack((L.real, L.imag)).astype(my_type).flatten()
        # Output vectors
        vector_G.append(G)
        vector_L.append(L)

    vector_G = np.concatenate(vector_G, axis=0)
    vector_L = np.concatenate(vector_L, axis=0)
    return [vector_G, vector_L], defines


def generate_fcmatmul(my_type=np.float32, defines={}):

    # Create matrix
    matrix_M = defines['matrix_M']
    matrix_N = defines['matrix_N']
    matrix_P = defines['matrix_P']
    A = np.random.rand(matrix_M, matrix_N) + 1j * \
        np.random.rand(matrix_M, matrix_N)
    B = np.random.rand(matrix_N, matrix_P) + 1j * \
        np.random.rand(matrix_N, matrix_P)
    C = np.matmul(A, B)

    A = np.reshape(A, (matrix_M * matrix_N), order='C')
    B = np.reshape(B, (matrix_N * matrix_P), order='C')
    C = np.reshape(C, (matrix_M * matrix_P), order='C')

    A = np.column_stack((A.imag, A.real)).astype(my_type).flatten()
    B = np.column_stack((B.imag, B.real)).astype(my_type).flatten()
    C = np.column_stack((C.imag, C.real)).astype(my_type).flatten()

    return [A, B, C], defines


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

def generate_fgemv(my_type=np.float32, defines={}):
    # Create matrix
    matrix_N = defines['matrix_N']
    matrix_P = defines['matrix_P']
    A = (np.random.rand(matrix_P, matrix_N) - 0.5).astype(my_type)
    X = (np.random.rand(matrix_N) - 0.5).astype(my_type)
    Y = np.matmul(A, X)
    
    A = np.reshape(A, (matrix_P * matrix_N), order='C').astype(my_type)
    X = np.reshape(X, (matrix_N), order='C').astype(my_type)
    Y = np.reshape(Y, (matrix_P), order='C').astype(my_type)
    
    return [A, X, Y], defines


def generate_fmmse(my_type=np.float16, defines={}):

    N_tx = defines['N_TX']
    N_rx = defines['N_RX']
    N_itr = defines['N_ITR']
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

    return [vH, vG, vy, vN, vx], defines


def generate_fofdm(my_type=np.float32, defines={}):

    N_sc = defines['N_SC']
    N_rx = defines['N_RX']
    N_bs = defines['N_BEAMS']

    pFFT_src = (np.random.rand(2 * N_rx * N_sc)).astype(np.float16)
    pBF_coef = (np.random.rand(2 * N_rx * N_bs)).astype(np.float16)
    pBF_dst = (np.random.rand(2 * N_bs * N_sc)).astype(np.float16)
    twiddles = ftwiddleCoef(N_sc, my_type)
    bitrever = qmath.bitreversal(N_sc, 2)

    defines['LOG2'] = int(math.log2(N_sc))
    defines['N_TWIDDLES'] = 3 * N_sc // 4
    defines['BITREVINDEXTABLE_LENGTH'] = len(bitrever)

    return [pFFT_src, pBF_coef, pBF_dst, twiddles, bitrever], defines


##############################################################################


def generate_iaxpy(my_type=np.int32, defines={}):

    # Create matrix
    array_N = defines['array_N']
    MAX = select_maxval(my_type)
    A = np.random.randint(-MAX, MAX - 1, size=1, dtype=my_type)
    X = irandom(MAX=MAX, size=(array_N), my_type=my_type)
    Y = irandom(MAX=MAX, size=(array_N), my_type=my_type)
    Z = (Y + X * A).astype(my_type)

    return [A, X, Y, Z], defines


def generate_idotp(my_type=np.int32, defines={}):

    # Create matrix
    array_N = defines['array_N']
    MAX = select_maxval(my_type)
    X = irandom(MAX=MAX, size=(array_N), my_type=my_type)
    Y = irandom(MAX=MAX, size=(array_N), my_type=my_type)
    Z = np.dot(X, Y)
    Z = np.array(Z).astype(my_type)
    Z = np.resize(Z, 1)

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


def generate_imatmul(my_type=np.int32, defines={}):

    # Create matrix
    matrix_M = defines['matrix_M']
    matrix_N = defines['matrix_N']
    matrix_P = defines['matrix_P']
    MAX = select_maxval(my_type)
    A = irandom(MAX=MAX, size=(matrix_M, matrix_N), my_type=my_type)
    B = irandom(MAX=MAX, size=(matrix_N, matrix_P), my_type=my_type)
    C = np.matmul(A, B)

    A = np.reshape(A, (matrix_M * matrix_N), order='C').astype(my_type)
    B = np.reshape(B, (matrix_N * matrix_P), order='C').astype(my_type)
    C = np.reshape(C, (matrix_M * matrix_P), order='C').astype(np.int32)

    return [A, B, C], defines


##############################################################################


def generate_qcmatmul(defines={}, fixed_point=15, my_type=np.int32):
    MAX = 2**(fixed_point - 1)
    # Create matrix
    matrix_M = defines['matrix_M']
    matrix_N = defines['matrix_N']
    matrix_P = defines['matrix_P']
    A = np.random.randint(-MAX, MAX - 1, size=(matrix_M, matrix_N)) + 1j * \
        np.random.randint(-MAX, MAX - 1, size=(matrix_M, matrix_N))
    B = np.random.randint(-MAX, MAX - 1, size=(matrix_N, matrix_P)) + 1j * \
        np.random.randint(-MAX, MAX - 1, size=(matrix_N, matrix_P))
    [Cr, Ci] = qmath.qcmatmul(A.real, A.imag, B.real,
                              B.imag, fixed_point, my_type)

    A = np.reshape(A, (matrix_M * matrix_N), order='C')
    B = np.reshape(B, (matrix_N * matrix_P), order='C')
    A = np.column_stack((A.imag, A.real)).astype(my_type).flatten()
    B = np.column_stack((B.imag, B.real)).astype(my_type).flatten()
    C = np.column_stack((Ci, Cr)).astype(my_type).flatten()

    return [A, B, C], defines


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


def generate_qccholesky(defines={}, fixed_point=15, my_type=np.int32):

    matrix_N = defines['matrix_N']
    FIXED_POINT = defines['FIXED_POINT']
    N_SAMPLES = defines['N_SAMPLES']

    vA = np.zeros([N_SAMPLES, 2 * matrix_N * matrix_N], dtype=my_type)
    vL = np.zeros([N_SAMPLES, 2 * matrix_N * matrix_N], dtype=my_type)
    for k in range(N_SAMPLES):

        Ar = np.random.normal(0, 1, [matrix_N, matrix_N]).astype(np.float32)
        Ai = np.random.normal(0, 1, [matrix_N, matrix_N]).astype(np.float32)
        A = Ar + 1.j * Ai
        G = np.matmul(A.conj().T, A)
        MAX_A = max(np.abs(A.real).max(), np.abs(A.imag).max())
        MAX_G = max(np.abs(G.real).max(), np.abs(G.imag).max())
        MAX = max(MAX_A, MAX_G)

        Ar = np.round((Ar / MAX) * 2**FIXED_POINT).astype(int)
        Ai = np.round((Ai / MAX) * 2**FIXED_POINT).astype(int)
        Ar = Ar + np.eye(matrix_N, dtype=int) * 256
        Ai = Ai + np.eye(matrix_N, dtype=int) * 256

        Ar, Ai = qmath.qcmatmul(Ar.T, -Ai.T, Ar, Ai, FIXED_POINT, my_type)
        Lr, Li = qmath.qccholesky(
            Ar, Ai, fixed_point=FIXED_POINT, mytype=my_type)

        A = np.column_stack((Ar, Ai)).astype(my_type).flatten()
        L = np.column_stack((Lr, Li)).astype(my_type).flatten()
        vA[k, :] = np.reshape(A, (2 * matrix_N * matrix_N),
                              order='C').astype(my_type)
        vL[k, :] = np.reshape(L, (2 * matrix_N * matrix_N),
                              order='C').astype(my_type)

    vA = np.reshape(vA, (2 * matrix_N * matrix_N * N_SAMPLES)).astype(my_type)
    vL = np.reshape(vL, (2 * matrix_N * matrix_N * N_SAMPLES)).astype(my_type)
    return [vA, vL], defines


def generate_qcholesky(defines={}, fixed_point=15, my_type=np.int32):

    matrix_N = defines['matrix_N']
    FIXED_POINT = defines['FIXED_POINT']
    N_SAMPLES = defines['N_SAMPLES']

    vA = np.zeros([N_SAMPLES, matrix_N * matrix_N], dtype=my_type)
    vL = np.zeros([N_SAMPLES, matrix_N * matrix_N], dtype=my_type)
    vy = np.zeros([N_SAMPLES, matrix_N], dtype=my_type)
    for k in range(N_SAMPLES):
        A = irandom(size=(matrix_N, matrix_N), MAX=2**14, my_type=my_type)
        y = irandom(size=matrix_N, MAX=2**14, my_type=my_type)
        A = qmath.qmatmul(A.T, A, FIXED_POINT, my_type)
        L = qmath.qcholesky(A, FIXED_POINT, my_type)

        vA[k, :] = np.reshape(A, (matrix_N * matrix_N),
                              order='C').astype(my_type)
        vL[k, :] = np.reshape(L, (matrix_N * matrix_N),
                              order='C').astype(my_type)
        vy[k, :] = np.reshape(y, matrix_N, order='C').astype(my_type)

    vA = np.reshape(vA, (matrix_N * matrix_N * N_SAMPLES)).astype(my_type)
    vL = np.reshape(vL, (matrix_N * matrix_N * N_SAMPLES)).astype(my_type)
    vy = np.reshape(vy, (matrix_N * N_SAMPLES)).astype(my_type)

    return [vA, vL, vy], defines


def generate_qmmse(defines={}, fixed_point=15, my_type=np.int32):

    FIXED_POINT = defines['FIXED_POINT']
    N_tx = defines['N_TX']
    N_rx = defines['N_RX']
    N_itr = defines['N_ITR']

    vN = np.zeros([N_itr, 2 * N_tx], dtype=np.int16)
    vH = np.zeros([N_itr, 2 * N_tx * N_rx], dtype=np.int16)
    vG = np.zeros([N_itr, 2 * N_tx * N_tx], dtype=np.int16)
    vy = np.zeros([N_itr, 2 * N_rx], dtype=np.int16)
    vx = np.zeros([N_itr, 2 * N_tx], dtype=np.int16)

    for k in range(N_itr):

        # Floating point inputs
        rH = np.random.normal(0, 1, [N_rx, N_tx]).astype(np.float32)
        iH = np.random.normal(0, 1, [N_rx, N_tx]).astype(np.float32)
        rN = np.random.normal(0, 1, [N_rx]).astype(np.float32)
        ry = np.random.normal(0, 1, [N_rx]).astype(np.float32)
        iy = np.random.normal(0, 1, [N_rx]).astype(np.float32)
        H = rH + 1j * iH
        y = ry + 1j * iy
        G = np.matmul(H.conj().T, H) + rN * np.eye(H.shape[1])
        y1 = np.dot(H.conj().T, y)

        # Rescale inputs
        H_max = max(np.abs(H.real).max(), np.abs(H.imag).max())
        G_max = max(np.abs(G.real).max(), np.abs(G.imag).max())
        y_max = max(np.abs(y.real).max(), np.abs(y.imag).max())
        y1_max = max(np.abs(y1.real).max(), np.abs(y1.imag).max())
        N_max = np.abs(rN).max()
        MAX = max(H_max, G_max, N_max, y_max, y1_max)
        SCALE_FACTOR = 2**FIXED_POINT
        rH = np.round((H.real / MAX) * SCALE_FACTOR).astype(int)
        iH = np.round((H.imag / MAX) * SCALE_FACTOR).astype(int)
        ry = np.round((y.real / MAX) * SCALE_FACTOR).astype(int)
        iy = np.round((y.imag / MAX) * SCALE_FACTOR).astype(int)
        rN = np.round((rN / MAX) * SCALE_FACTOR).astype(int) + 1024

        # Hermitian
        rG, iG = qmath.qcmatmul(rH.T, -iH.T, rH, iH, FIXED_POINT, my_type)
        ry1, iy1 = qmath.qcmvmul(rH.T, -iH.T, ry, iy, FIXED_POINT, my_type)
        np.fill_diagonal(rG, rG.diagonal() + rN)

        # Solve linear system
        rL, iL = qmath.qccholesky(rG, iG, FIXED_POINT, my_type)
        ry2, iy2 = qmath.qinvertLt(rL, iL, ry1, iy1, FIXED_POINT, my_type)
        rx, ix = qmath.qinvertUt(rL.T, -iL.T, ry2, iy2, FIXED_POINT, my_type)

        vN[k, :] = np.column_stack(
            (rN, np.zeros(np.size(rN)))).astype(my_type).flatten()
        vH[k, :] = np.column_stack((rH, iH)).astype(my_type).flatten()
        vG[k, :] = np.column_stack((rG, iG)).astype(my_type).flatten()
        vy[k, :] = np.column_stack((ry, iy)).astype(my_type).flatten()
        vx[k, :] = np.column_stack((rx, ix)).astype(my_type).flatten()

    vN = np.reshape(vN, (2 * N_tx * N_itr)).astype(my_type)
    vH = np.reshape(vH, (2 * N_rx * N_tx * N_itr)).astype(my_type)
    vG = np.reshape(vG, (2 * N_tx * N_tx * N_itr)).astype(my_type)
    vy = np.reshape(vy, (2 * N_rx * N_itr)).astype(my_type)
    vx = np.reshape(vx, (2 * N_tx * N_itr)).astype(my_type)
    return [vN, vH, vG, vy, vx], defines


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
