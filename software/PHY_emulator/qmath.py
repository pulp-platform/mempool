#!/usr/bin/env python3

# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# This script generates data for the q16 mmse.
# Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

import numpy as np
import math


def to_fixed_point(matrix, fixed_point, mytype):
    """Convert complex matrix to fixed-point integer matrix representation."""
    SCALE_FACTOR = 2**fixed_point
    real_part = np.round(matrix.real * SCALE_FACTOR).astype(mytype)
    imag_part = np.round(matrix.imag * SCALE_FACTOR).astype(mytype)
    if (np.abs(real_part.any()) > 2**(fixed_point-1)):
        raise ValueError("Overflow")
    if (np.abs(imag_part.any()) > 2**(fixed_point-1)):
        raise ValueError("Overflow")
    return real_part, imag_part


def from_fixed_point(real_part, imag_part, fixed_point, mytype):
    """Convert fixed-point integer matrix back to floating-point complex matrix."""
    SCALE_FACTOR = 2**fixed_point
    return (real_part / SCALE_FACTOR) + 1j * (imag_part / SCALE_FACTOR)


def qcmatmul(A_real, A_imag, B_real, B_imag, fixed_point, mytype):
    """Perform fixed-point complex matrix multiplication."""
    SCALE_FACTOR = 2**fixed_point
    # Dimensions
    rows_A, cols_A = A_real.shape
    cols_B = B_real.shape[1]

    # Initialize result matrix
    C_real = np.zeros((rows_A, cols_B), dtype=mytype)
    C_imag = np.zeros((rows_A, cols_B), dtype=mytype)

    # Perform multiplication
    for i in range(rows_A):
        for j in range(cols_B):
            for k in range(cols_A):
                # Real part: (A_real * B_real - A_imag * B_imag)
                real_product = A_real[i, k] * B_real[k, j] - A_imag[i, k] * B_imag[k, j]
                # Imaginary part: (A_real * B_imag + A_imag * B_real)
                imag_product = A_real[i, k] * B_imag[k, j] + A_imag[i, k] * B_real[k, j]

                # Accumulate in fixed-point (with scaling adjustment)
                C_real[i, j] += real_product // SCALE_FACTOR
                C_imag[i, j] += imag_product // SCALE_FACTOR

    return C_real, C_imag


def qcmvmul(A_real, A_imag, B_real, B_imag, fixed_point, mytype):
    """Perform fixed-point complex matrix-vector multiplication."""
    # Dimensions
    SCALE_FACTOR = 2**fixed_point
    rows_A, cols_A = A_real.shape

    # Initialize result vector
    C_real = np.zeros(rows_A, dtype=mytype)
    C_imag = np.zeros(rows_A, dtype=mytype)

    # Perform multiplication
    for i in range(rows_A):
        for k in range(cols_A):
            # Real part: (A_real * B_real - A_imag * B_imag)
            real_product = A_real[i, k] * B_real[k] - A_imag[i, k] * B_imag[k]
            # Imaginary part: (A_real * B_imag + A_imag * B_real)
            imag_product = A_real[i, k] * B_imag[k] + A_imag[i, k] * B_real[k]

            # Accumulate in fixed-point (with scaling adjustment)
            C_real[i] += real_product // SCALE_FACTOR
            C_imag[i] += imag_product // SCALE_FACTOR

    return C_real, C_imag


def qsqrt(n, fixed_point, mytype):
    """
    Return the square root of n as a fixed-point number. It uses a
    second-order Newton-Raphson convergence, doubling the number
    of significant figures on each iteration.

    fixed_point is the number of bits in the fractional part of the fixed
    point number.
    """
    SCALE_FACTOR = 2**fixed_point
    # Initial guess
    x = np.ones_like(n, dtype=mytype) * SCALE_FACTOR  # Initial guess for each element
    n_one = n * SCALE_FACTOR                            # Scaling input to fixed point

    itr = 0
    while True:
        x_old = x
        x = (x + n_one // x) // 2
        # Check for convergence
        if (np.array_equal(x, x_old) or itr == 10):
            break
        itr += 1
    return x


def qcholesky(M_real, M_imag, fixed_point, mytype):
    """
    Cholesky decomposition.
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
                    real_product = (real_Lik * real_Ljk - imag_Lik * imag_Ljk) // SCALE_FACTOR
                    imag_product = (real_Lik * imag_Ljk + imag_Lik * real_Ljk) // SCALE_FACTOR
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


def qinvertLt(M_real, M_imag, y_real, y_imag, fixed_point, mytype):
    """
    Invert a lower triangular system.
    """
    SCALE_FACTOR = 2**fixed_point
    n = M_real.shape[0]  # Get the number of rows/columns (square matrix)
    x_real = np.zeros_like(y_real, dtype=mytype)  # Initialize dest with zeros
    x_imag = np.zeros_like(y_imag, dtype=mytype)  # Initialize dest with zeros

    # Invert the lower triangular system and save the result
    for i in range(0, n, 1):

        sum_real = y_real[i]
        sum_imag = y_imag[i]
        for j in range(0, i, 1):
            real_Lij = M_real[i, j]
            imag_Lij = M_imag[i, j]
            real_xj = x_real[j]
            imag_xj = x_imag[j]
            sum_real -= (real_Lij * real_xj - imag_Lij * imag_xj) // SCALE_FACTOR
            sum_imag -= (real_Lij * imag_xj + imag_Lij * real_xj) // SCALE_FACTOR

        x_real[i] = (sum_real * SCALE_FACTOR) // M_real[i, i]
        x_imag[i] = (sum_imag * SCALE_FACTOR) // M_real[i, i]

    return x_real, x_imag


def qinvertUt(M_real, M_imag, y_real, y_imag, fixed_point, mytype):
    """
    Invert upper triangular system.
    """
    SCALE_FACTOR = 2**fixed_point
    n = M_real.shape[0]
    x_real = np.zeros_like(y_real, dtype=mytype)
    x_imag = np.zeros_like(y_imag, dtype=mytype)

    # Solve the upper triangular system Ux = y
    for i in range(n - 1, -1, -1):
        sum_real = y_real[i]
        sum_imag = y_imag[i]

        for j in range(i + 1, n):
            real_Uij = M_real[i, j]
            imag_Uij = M_imag[i, j]
            real_xj = x_real[j]
            imag_xj = x_imag[j]
            sum_real -= (real_Uij * real_xj - imag_Uij * imag_xj) // SCALE_FACTOR
            sum_imag -= (real_Uij * imag_xj + imag_Uij * real_xj) // SCALE_FACTOR

        # The diagonal element of U
        diag = M_real[i, i]
        x_real[i] = (sum_real * SCALE_FACTOR) // M_real[i, i]
        x_imag[i] = (sum_imag * SCALE_FACTOR) // M_real[i, i]

    return x_real, x_imag
