#!/usr/bin/env python3

# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# This script generates data for the fp16 mmse.
# Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

import numpy as np
import math
from sympy.combinatorics import Permutation


def to_fixed_point(matrix, fixed_point=15, mytype=np.int16):
    """Convert a complex matrix to a fixed-point matrix.
    matrix (np.ndarray): Input complex matrix.
    fixed_point (int): Number of bits for the fractional part.
    mytype (np.dtype): Data type for the fixed-point representation.

    Returns:
        tuple: Real and imaginary parts of the fixed-point matrix.
    """
    SCALE_FACTOR = 2**fixed_point
    real_part = np.round(matrix.real * SCALE_FACTOR).astype(mytype)
    imag_part = np.round(matrix.imag * SCALE_FACTOR).astype(mytype)
    if (np.abs(real_part.any()) > 2**(fixed_point - 1)):
        raise ValueError("Overflow")
    if (np.abs(imag_part.any()) > 2**(fixed_point - 1)):
        raise ValueError("Overflow")
    return real_part, imag_part


def from_fixed_point(real_part, imag_part, fixed_point=15, mytype=np.int16):
    """Convert a fixed-point matrix back to a floating-point complex matrix.
    real_part (np.ndarray): Real part of the fixed-point matrix.
    imag_part (np.ndarray): Imaginary part of the fixed-point matrix.
    fixed_point (int): Number of bits for the fractional part.
    mytype (np.dtype): Data type for the fixed-point representation.

    Returns:
        np.ndarray: Reconstructed complex matrix.
    """
    SCALE_FACTOR = 2**fixed_point
    return (real_part / SCALE_FACTOR) + 1j * (imag_part / SCALE_FACTOR)


def qmatmul(A, B, fixed_point=15, mytype=np.int16):
    """Perform fixed-point matrix multiplication.
    A (np.ndarray): First matrix.
    B (np.ndarray): Second matrix.
    fixed_point (int): Number of bits for the fractional part.
    mytype (np.dtype): Data type for the fixed-point representation.

    Returns:
        np.ndarray: Fixed-point result of the matrix multiplication.
    """
    SCALE_FACTOR = 2**fixed_point
    rows_A, cols_A = A.shape
    cols_B = B.shape[1]
    C = np.zeros((rows_A, cols_B), dtype=np.int32)

    for i in range(rows_A):
        for j in range(cols_B):
            for k in range(cols_A):
                C[i, j] += A[i, k] * B[k, j] // SCALE_FACTOR
    return C.astype(mytype)


def qcmatmul(A_real, A_imag, B_real, B_imag, fixed_point=15, mytype=np.int16):
    """Perform fixed-point complex matrix multiplication.
    A_real (np.ndarray): Real part of the first matrix.
    A_imag (np.ndarray): Imaginary part of the first matrix.
    B_real (np.ndarray): Real part of the second matrix.
    B_imag (np.ndarray): Imaginary part of the second matrix.
    fixed_point (int): Number of bits for the fractional part.
    mytype (np.dtype): Data type for the fixed-point representation.

    Returns:
        tuple: Real and imaginary parts of the result matrix.
    """
    SCALE_FACTOR = 2**fixed_point
    rows_A, cols_A = A_real.shape
    cols_B = B_real.shape[1]

    C_real = np.zeros((rows_A, cols_B), dtype=np.int32)
    C_imag = np.zeros((rows_A, cols_B), dtype=np.int32)

    for i in range(rows_A):
        for j in range(cols_B):
            for k in range(cols_A):
                real_product = A_real[i, k] * \
                    B_real[k, j] - A_imag[i, k] * B_imag[k, j]
                imag_product = A_real[i, k] * \
                    B_imag[k, j] + A_imag[i, k] * B_real[k, j]

                C_real[i, j] += real_product // SCALE_FACTOR
                C_imag[i, j] += imag_product // SCALE_FACTOR

    return C_real.astype(mytype), C_imag.astype(mytype)


def qcmvmul(A_real, A_imag, B_real, B_imag, fixed_point=15, mytype=np.int16):
    """Perform fixed-point complex matrix-vector multiplication.
    A_real (np.ndarray): Real part of the matrix.
    A_imag (np.ndarray): Imaginary part of the matrix.
    B_real (np.ndarray): Real part of the vector.
    B_imag (np.ndarray): Imaginary part of the vector.
    fixed_point (int): Number of bits for the fractional part.
    mytype (np.dtype): Data type for the fixed-point representation.

    Returns:
        tuple: Real and imaginary parts of the result vector.
    """
    SCALE_FACTOR = 2**fixed_point
    rows_A, cols_A = A_real.shape

    C_real = np.zeros(rows_A, dtype=np.int32)
    C_imag = np.zeros(rows_A, dtype=np.int32)

    for i in range(rows_A):
        for k in range(cols_A):
            real_product = A_real[i, k] * B_real[k] - A_imag[i, k] * B_imag[k]
            imag_product = A_real[i, k] * B_imag[k] + A_imag[i, k] * B_real[k]

            C_real[i] += real_product // SCALE_FACTOR
            C_imag[i] += imag_product // SCALE_FACTOR

    return C_real.astype(mytype), C_imag.astype(mytype)


def qsqrt(n, fixed_point=15, mytype=np.int16):
    """Compute the square root of a number in fixed-point representation using
    Newton-Raphson method.
    n (np.ndarray): Input value(s) in fixed-point representation.
    fixed_point (int): Number of bits for the fractional part.
    mytype (np.dtype): Data type for the fixed-point representation.

    Returns:
        np.ndarray: Square root of the input in fixed-point representation.
    """
    SCALE_FACTOR = 2**fixed_point
    x = np.ones_like(n, dtype=mytype) * SCALE_FACTOR
    n_one = n * SCALE_FACTOR

    itr = 0
    while True:
        x_old = x
        x = (x + n_one // x) // 2
        if np.array_equal(
                x, x_old) or itr == 10:  # Convergence or max iterations
            break
        itr += 1
    return x


def qcholesky(A, fixed_point=15, mytype=np.int16):
    """Perform fixed-point Cholesky decomposition of a symmetric
    positive-definite matrix.
    A (np.ndarray): Input matrix (must be square and symmetric).
    fixed_point (int): Number of bits for the fractional part.
    mytype (np.dtype): Data type for the fixed-point representation.

    Returns:
        tuple: Flattened input matrix, flattened lower triangular matrix, and
        result vector.
    """
    SCALE_FACTOR = 2**fixed_point
    rows, columns = A.shape
    if rows != columns:
        raise ValueError("Matrix must be square for Cholesky decomposition.")

    L = np.zeros((rows, columns), dtype=mytype)

    for row in range(rows):
        for column in range(columns):
            if row == column:
                pivot = A[row, column]
                for k in range(column):
                    Ljk = L[row, k]
                    pivot -= (Ljk**2) // SCALE_FACTOR
                if pivot < 0:
                    # raise ValueError("Negative value encountered in diagonal
                    # element.")
                    pivot = 0
                L[row, column] = qsqrt(pivot, fixed_point, mytype)
            elif row > column:
                pivot = A[row, column]
                for k in range(column):
                    Lik = L[row, k]
                    Ljk = L[column, k]
                    pivot -= (Lik * Ljk) // SCALE_FACTOR
                diag = L[column, column]
                L[row, column] = (pivot * SCALE_FACTOR) // diag
            else:
                L[row, column] = 0

    return L


def qccholesky(M_real, M_imag, fixed_point=15, mytype=np.int16):
    """Perform fixed-point Cholesky decomposition of a symmetric
    positive-definite matrix.
    A (np.ndarray): Input matrix (must be square and symmetric).
    fixed_point (int): Number of bits for the fractional part.
    mytype (np.dtype): Data type for the fixed-point representation.

    Returns:
        tuple: Flattened input matrix, flattened lower triangular matrix,
        and result vector.
    """

    SCALE_FACTOR = 2**fixed_point
    NEGATIVE = fixed_point**2 + 1

    rows, columns = M_real.shape
    L_real = np.zeros_like(M_real, dtype=mytype)  # Initialize dest with zeros
    L_imag = np.zeros_like(M_imag, dtype=mytype)  # Initialize dest with zeros

    # Check for dimensional errors
    if rows != columns:
        raise ValueError("Matrix must be square for Cholesky decomposition.")

    for row in range(rows):
        for column in range(columns):

            if row == column:
                # Diagonal element
                real_pivot = M_real[row, column]
                for k in range(column):
                    real_Ljk = L_real[row, k]
                    imag_Ljk = L_imag[row, k]
                    product = (real_Ljk**2 + imag_Ljk**2) // SCALE_FACTOR
                    real_pivot = real_pivot - product

                # Handle negative values for square root
                if real_pivot < 0:
                    if real_pivot < NEGATIVE:
                        raise ValueError("Negative value encountered.")
                    real_pivot = 0
                L_real[row, column] = qsqrt(real_pivot, fixed_point, mytype)

            elif row > column:
                # Off-diagonal element (below the diagonal)
                real_pivot = M_real[row, column]
                imag_pivot = M_imag[row, column]

                for k in range(column):
                    real_Lik = L_real[row, k]
                    imag_Lik = L_imag[row, k]
                    real_Ljk = L_real[column, k]
                    imag_Ljk = L_imag[column, k]
                    real_product = (real_Lik * real_Ljk - imag_Lik * imag_Ljk)
                    imag_product = (real_Lik * imag_Ljk + imag_Lik * real_Ljk)
                    real_product = real_product // SCALE_FACTOR
                    imag_product = imag_product // SCALE_FACTOR
                    real_pivot = real_pivot - real_product
                    imag_pivot = imag_pivot - imag_product

                diag = L_real[column, column]
                L_real[row, column] = (real_pivot * SCALE_FACTOR) // diag
                L_imag[row, column] = (imag_pivot * SCALE_FACTOR) // diag

            else:
                # Above diagonal, set to zero
                L_real[row, column] = 0
                L_imag[row, column] = 0

    return L_real, L_imag


def qinvertLt(M_real, M_imag, y_real, y_imag, fixed_point=15, mytype=np.int16):
    """Invert a lower triangular complex matrix using fixed-point arithmetic.
    M_real (np.ndarray): Real part of the lower triangular matrix.
    M_imag (np.ndarray): Imaginary part of the lower triangular matrix.
    y_real (np.ndarray): Real part of the vector.
    y_imag (np.ndarray): Imaginary part of the vector.
    fixed_point (int): Number of bits for the fractional part.
    mytype (np.dtype): Data type for the fixed-point representation.

    Returns:
    tuple: Real and imaginary parts of the result vector.
    """
    SCALE_FACTOR = 2**fixed_point
    n = M_real.shape[0]
    x_real = np.zeros_like(y_real, dtype=mytype)
    x_imag = np.zeros_like(y_imag, dtype=mytype)

    for i in range(n):
        sum_real = y_real[i]
        sum_imag = y_imag[i]
        for j in range(i):
            sum_real -= (M_real[i, j] * x_real[j] -
                         M_imag[i, j] * x_imag[j]) // SCALE_FACTOR
            sum_imag -= (M_real[i, j] * x_imag[j] +
                         M_imag[i, j] * x_real[j]) // SCALE_FACTOR

        x_real[i] = (sum_real * SCALE_FACTOR) // M_real[i, i]
        x_imag[i] = (sum_imag * SCALE_FACTOR) // M_real[i, i]

    return x_real, x_imag


def qinvertUt(M_real, M_imag, y_real, y_imag, fixed_point=15, mytype=np.int16):
    """Invert an upper triangular complex matrix using fixed-point arithmetic.
    M_real (np.ndarray): Real part of the upper triangular matrix.
    M_imag (np.ndarray): Imaginary part of the upper triangular matrix.
    y_real (np.ndarray): Real part of the vector.
    y_imag (np.ndarray): Imaginary part of the vector.
    fixed_point (int): Number of bits for the fractional part.
    mytype (np.dtype): Data type for the fixed-point representation.

    Returns:
    tuple: Real and imaginary parts of the result vector.
    """
    SCALE_FACTOR = 2**fixed_point
    n = M_real.shape[0]
    x_real = np.zeros_like(y_real, dtype=mytype)
    x_imag = np.zeros_like(y_imag, dtype=mytype)

    for i in range(n - 1, -1, -1):
        sum_real = y_real[i]
        sum_imag = y_imag[i]

        for j in range(i + 1, n):
            sum_real -= (M_real[i, j] * x_real[j] -
                         M_imag[i, j] * x_imag[j]) // SCALE_FACTOR
            sum_imag -= (M_real[i, j] * x_imag[j] +
                         M_imag[i, j] * x_real[j]) // SCALE_FACTOR

        x_real[i] = (sum_real * SCALE_FACTOR) // M_real[i, i]
        x_imag[i] = (sum_imag * SCALE_FACTOR) // M_real[i, i]

    return x_real, x_imag


def qtwiddleCoef(N, fixed_point=15, mytype=np.int16):
    """Generate fixed-point twiddle coefficients for FFT.
    N (int): Number of points in FFT.
    fixed_point (int): Number of bits for the fractional part.
    mytype (np.dtype): Data type for the fixed-point representation.

    Returns:
    np.ndarray: Twiddle coefficients in fixed-point representation.
    """
    PI = 3.14159265358979
    twiddleCoefq15 = np.zeros((int(2 * 3 * N / 4)), dtype=mytype)
    for i in range(int(3 * N / 4)):
        twiddleCoefq15_cos = math.cos(i * 2 * PI / N)
        twiddleCoefq15_sin = math.sin(i * 2 * PI / N)
        twiddleCoefq15[2 * i] = \
            int(round(twiddleCoefq15_cos * (2**fixed_point - 1)))
        twiddleCoefq15[2 * i + 1] = \
            int(round(twiddleCoefq15_sin * (2**fixed_point - 1)))
    return twiddleCoefq15


def bitreversal(N, R):
    """Perform bit-reversal for FFT with radix-R decomposition.

    Args:
        N (int): Number of points in FFT.
        R (int): Radix for FFT decomposition.

    Returns:
        np.ndarray: Flattened bit-reversal transposition table.
    """
    # Decompose
    logR2 = []
    idx = N
    while (idx >= R):
        logR2.append(int(math.log2(R)))
        idx = idx // R
    if (idx > 1):
        logR2.append(int(math.log2(idx)))
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


def q_sat(x):
    if x > 2**15 - 1:
        return x - 2**16
    elif x < -2**15:
        return x + 2**16
    else:
        return x


def qchest(in_rx, in_tx, division=False, fixed_point=8, mytype=np.int16):
    """Perform fixed-point complex channel estimation (CHEST).
    in_rx (np.ndarray): Received signal array (complex numbers).
    in_tx (np.ndarray): Transmitted signal array (complex numbers).
    division (bool): Whether to perform division or multiplication.
    Defaults to False.
    fixed_point (int): Number of bits for the fractional part. Defaults to 8.
    mytype (np.dtype): Data type for fixed-point representation.
    Defaults to np.int16.

    Returns:
        np.ndarray: Resulting array in fixed-point representation.
    """
    SCALE_FACTOR = 2**fixed_point
    n_rx = in_rx.size
    n_tx = in_tx.size

    # Resulting array (real and imaginary interleaved)
    result = np.zeros(2 * (n_tx * n_rx), dtype=mytype)

    for i in range(n_rx):
        a_r = in_rx[i].real
        a_i = in_rx[i].imag
        for j in range(n_tx):
            b_r = in_tx[j].real
            b_i = in_tx[j].imag

            if division:
                # Compute data division
                den = (2**16) // (b_r * b_r + b_i * b_i)
                if den == 0:
                    raise ZeroDivisionError(
                        "Division by zero encountered in CHEST.")
                num_r = (a_r * b_r + a_i * b_i)
                num_i = (a_i * b_r - a_r * b_i)
                result[2 * (i * n_tx + j)] = (num_r // den) * SCALE_FACTOR
                result[2 * (i * n_tx + j) + 1] = (num_i // den) * SCALE_FACTOR
            else:
                # Compute data multiplication
                num_r = (a_r * b_r - a_i * b_i)
                num_i = (a_i * b_r + a_r * b_i)
                result[2 * (i * n_tx + j)] = q_sat(num_r // SCALE_FACTOR)
                result[2 * (i * n_tx + j) + 1] = q_sat(num_i // SCALE_FACTOR)

    return result
