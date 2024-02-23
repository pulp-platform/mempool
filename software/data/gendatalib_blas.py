#!/usr/bin/env python3

# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# This script generates data for the fp16 matmul.
# Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

import numpy as np
from scipy import signal


def select_maxval(my_type=np.int32):
    size = 8 * np.dtype(my_type).itemsize
    MAX = 2**(size - 2) - 1
    return MAX


def generate_iarray(array_N=16, my_type=np.float32):

    # Create random array of integers
    MAX = select_maxval(my_type)
    A = np.random.randint(-MAX, MAX - 1, size=(array_N)).astype(my_type)
    return A


def generate_fmatmul(matrix_M=16, matrix_N=16,
                     matrix_P=16, my_type=np.float32):

    # Create matrix
    A = (np.random.rand(matrix_M, matrix_N) - 0.5).astype(my_type)
    B = (np.random.rand(matrix_N, matrix_P) - 0.5).astype(my_type)
    C = np.matmul(A, B)

    A = np.reshape(A, (matrix_M * matrix_N), order='C').astype(my_type)
    B = np.reshape(B, (matrix_N * matrix_P), order='C').astype(my_type)
    C = np.reshape(C, (matrix_M * matrix_P), order='C').astype(my_type)

    return A, B, C


def generate_imatmul(matrix_M=16, matrix_N=16, matrix_P=16, my_type=np.int32):

    # Create matrix
    MAX = select_maxval(my_type)
    A = np.random.randint(-MAX, MAX - 1, size=(matrix_M, matrix_N))
    B = np.random.randint(-MAX, MAX - 1, size=(matrix_M, matrix_N))
    C = np.matmul(A, B)

    A = np.reshape(A, (matrix_M * matrix_N), order='C').astype(my_type)
    B = np.reshape(B, (matrix_N * matrix_P), order='C').astype(my_type)
    C = np.reshape(C, (matrix_M * matrix_P), order='C').astype(np.int32)

    return A, B, C


def qmatmul(A, B, matrix_M=16, matrix_N=16, matrix_P=16,
            FIXED_POINT=10, my_type=np.int32):

    # fixed-point mul is rounded up
    half = 2**FIXED_POINT - 1
    C = np.zeros((matrix_M, matrix_P), dtype=my_type)
    for i in range(matrix_M):
        for j in range(matrix_N):
            for k in range(matrix_P):
                C[i][k] += (A[i][j] * B[j][k] + half) / 2**FIXED_POINT
    return C


def generate_qmatmul(matrix_M=16, matrix_N=16, matrix_P=16,
                     FIXED_POINT=10, my_type=np.int32):

    # Create matrix
    MAX = select_maxval(my_type)
    A = np.random.randint(-MAX, MAX - 1, size=(matrix_M, matrix_N))
    B = np.random.randint(-MAX, MAX - 1, size=(matrix_M, matrix_N))
    C = qmatmul(A, B, matrix_M, matrix_N, matrix_P, FIXED_POINT, my_type)
    # Cast outputs
    A = np.reshape(A, (matrix_M * matrix_N), order='C').astype(my_type)
    B = np.reshape(B, (matrix_N * matrix_P), order='C').astype(my_type)
    C = np.reshape(C, (matrix_M * matrix_P), order='C').astype(my_type)

    return A, B, C


def generate_qcholesky(matrix_N=16, FIXED_POINT=10, my_type=np.int32):

    # Create matrix
    MAX = select_maxval(my_type)
    A = np.random.randint(-MAX, MAX - 1, size=(matrix_N, matrix_N))
    y = np.random.randint(-MAX, MAX - 1, size=matrix_N)
    A = qmatmul(A.T, A, matrix_N, matrix_N, matrix_N, FIXED_POINT, my_type)
    L = np.zeros((matrix_N, matrix_N), dtype=my_type)

    # TO_DO: Compute Cholesky Golden model
    # TO_DO: Compute Triangular system solver Golden model

    A = np.reshape(A, (matrix_N * matrix_N), order='C').astype(my_type)
    L = np.reshape(L, (matrix_N * matrix_N), order='C').astype(my_type)
    return A, L, y


def generate_iaxpy(ALPHA=6, array_N=1024, my_type=np.int32):

    # Create matrix
    MAX = select_maxval(my_type)
    X = np.random.randint(-MAX, MAX, size=(array_N)).astype(my_type)
    Y = np.random.randint(-MAX, MAX, size=(array_N)).astype(my_type)
    Z = (Y + X * ALPHA).astype(my_type)

    return X, Y, Z


def generate_iconv(matrix_M=32, matrix_N=32, kernel_N=3, my_type=np.int32):

    # Create matrix
    MAX = select_maxval(my_type)
    X = np.random.randint(-MAX, MAX, size=(matrix_M, matrix_N)).astype(my_type)
    K = np.random.randint(-MAX, MAX, size=(kernel_N, kernel_N)).astype(my_type)
    Y = signal.convolve2d(X, K, mode="same", boundary='fill')

    X = X.flatten().astype(my_type)
    K = K.flatten().astype(my_type)
    Y = Y.flatten().astype(my_type)

    return X, K, Y
