#!/usr/bin/env python3

# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# This script generates data for the fp16 matmul.
# Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

# The script generates random inputs for the C functions.

import numpy as np
import math

try:
    import pyflexfloat as ff
except ModuleNotFoundError:
    ff = None


def fconv2d_depthwise(A, W, B):
    """Two-dimensional depthwise convolution.

    Uses SAME padding with 0s, a stride of 1 and no dilation. A single output
    channel is used per input channel (channel_multiplier=1).

    input: input array with shape (height, width, in_depth)
    w: filter array with shape (fd, fd, in_depth)

    Returns a result with shape (height, width, in_depth).
    """

    [matrix_M, matrix_N, matrix_D] = np.shape(A)
    kernel_K = np.shape(W)[0]

    padw = kernel_K // 2
    padded_input = np.pad(A,
                          pad_width=((padw, padw), (padw, padw), (0, 0)),
                          mode='constant',
                          constant_values=0)

    for c in range(matrix_D):
        # For each input channel separately, apply its corresponsing filter
        # to the input.
        for i in range(matrix_M):
            for j in range(matrix_N):

                for fi in range(kernel_K):
                    for fj in range(kernel_K):
                        w_element = W[fi, fj, c]
                        B[i, j, c] += (
                            padded_input[i + fi, j + fj, c] * w_element)
    return B


def fconv2d_pointwise(A, W, B):
    """Depthwise separable convolution.

    Performs a pointwise 1x1 convolution with w_pointwise.

    Uses SAME padding with 0s, a stride of 1 and no dilation. A single output
    channel is used per input channel (channel_multiplier=1) in w_depth.

    input: input array with shape (height, width, in_depth)
    w_pointwise: pointwise filter array with shape (in_depth, out_depth)

    Returns a result with shape (height, width, out_depth).
    """
    # First run the depthwise convolution. Its result has the same shape as
    # input.

    [matrix_M, matrix_N, matrix_D] = np.shape(A)
    kernel_D = np.shape(W)[1]

    for out_c in range(kernel_D):

        for i in range(matrix_M):
            for j in range(matrix_N):
                for c in range(matrix_D):
                    w_element = W[c, out_c]
                    B[i, j, out_c] += A[i, j, c] * w_element
    return B


def generate_fconv2d_depthwise_pointwise(my_type=np.float32, defines={}):

    matrix_M = defines['matrix_M']  # width of input
    matrix_N = defines['matrix_N']  # height of input
    matrix_D = defines['matrix_D']  # depth of input

    kernel_K = defines['kernel_K']  # Width of kernel
    kernel_D = defines['kernel_D']  # Channels of kernel

    A = np.random.rand(matrix_M, matrix_N, matrix_D).astype(my_type)
    Wd = np.random.rand(kernel_K, kernel_K, matrix_D).astype(my_type)
    Wp = (5 * np.random.rand(matrix_D, kernel_D) - 2.5)

    B = np.zeros((matrix_M, matrix_N, matrix_D), dtype=my_type)
    B = fconv2d_depthwise(A, Wd, B)
    Bd = np.reshape(B, (matrix_M * matrix_N * matrix_D)).astype(my_type)

    Bp = np.zeros((matrix_M, matrix_N, kernel_D), dtype=my_type)
    Bp = fconv2d_pointwise(B, Wp, Bp)
    A = np.reshape(A, (matrix_M * matrix_N * matrix_D)).astype(my_type)
    Bp = np.reshape(Bp, (matrix_M * matrix_N * kernel_D)).astype(my_type)
    Wd = np.reshape(Wd, (kernel_K * kernel_K * matrix_D)).astype(my_type)
    Wp = np.reshape(Wp, (matrix_D * kernel_D), order='F').astype(my_type)

    return [A, Wd, Wp, Bd, Bp], defines


def generate_fconv2d_depthwise(my_type=np.float32, defines={}):

    matrix_M = defines['matrix_M']  # width of input
    matrix_N = defines['matrix_N']  # height of input
    matrix_D = defines['matrix_D']  # depth of input

    kernel_K = defines['kernel_K']  # Channels of kernel

    A = np.random.rand(matrix_M, matrix_N, matrix_D).astype(my_type)
    W = np.random.rand(kernel_K, kernel_K, matrix_D).astype(my_type)
    B = np.zeros((matrix_M, matrix_N, matrix_D), dtype=my_type)

    B = fconv2d_depthwise(A, W, B)

    A = np.reshape(A, (matrix_M * matrix_N * matrix_D)).astype(my_type)
    B = np.reshape(B, (matrix_M * matrix_N * matrix_D)).astype(my_type)
    W = np.reshape(W, (kernel_K * kernel_K * matrix_D)).astype(my_type)

    return [A, W, B], defines


def generate_fconv2d_pointwise(my_type=np.float32, defines={}):

    matrix_M = defines['matrix_M']  # width of input
    matrix_N = defines['matrix_N']  # height of input
    matrix_D = defines['matrix_D']  # depth of input

    kernel_D = defines['kernel_D']  # Channels of kernel

    A = (5 * np.random.rand(matrix_M, matrix_N, matrix_D) - 2.5)
    W = (5 * np.random.rand(matrix_D, kernel_D) - 2.5)
    A = A.astype(my_type)
    W = W.astype(my_type)
    B = np.zeros((matrix_M, matrix_N, kernel_D), dtype=my_type)

    B = fconv2d_pointwise(A, W, B)

    A = np.reshape(A, (matrix_M * matrix_N * matrix_D)).astype(my_type)
    B = np.reshape(B, (matrix_M * matrix_N * kernel_D)).astype(my_type)
    W = np.reshape(W, (matrix_D * kernel_D), order='F').astype(my_type)

    return [A, W, B], defines


def generate_ffullyconn(my_type=np.float32, defines={}):

    matrix_M = defines['matrix_M']  # width of input
    matrix_N = defines['matrix_N']  # height of input

    W = (5 * np.random.rand(matrix_M, matrix_N) - 2.5).astype(my_type)
    A = (5 * np.random.rand(matrix_N) - 2.5).astype(my_type)
    if defines['BIAS'] == 1:
        B = (5 * np.random.rand(matrix_M) - 2.5).astype(my_type)
    else:
        B = np.zeros((matrix_M), dtype=my_type)
    B += np.matmul(W, A).astype(my_type)
    if defines['RELU'] == 1:
        Y = np.maximum(B, 0)
    else:
        Y = B

    W = np.reshape(W, (matrix_M * matrix_N)).astype(my_type)

    return [A, Y, W, B], defines


def flayernorm(A, my_type=None, eps=0.0, gamma=None, beta=None):
    """
    LayerNorm over the last axis: (x - mean) / sqrt(var + eps).

    This helper is shared by generate_flayernorm() and generate_fcnn().
    """
    if my_type is None:
        my_type = A.dtype

    A32 = A.astype(np.float32, copy=False)
    mean = np.mean(A32, axis=-1, keepdims=True)
    var = np.var(A32, axis=-1, keepdims=True)
    out = (A32 - mean) / np.sqrt(var + eps)
    if gamma is not None:
        out = out * gamma
    if beta is not None:
        out = out + beta
    return out.astype(my_type)


def generate_fbatchnorm(my_type=np.float32, defines={}):

    # f8: Cast correct type
    if ff is not None and f"{my_type}" == f"{ff.FlexFloat('e5m2')}":

        # Define dimension
        matrix_M = defines['matrix_M']
        matrix_N = defines['matrix_N']

        # Create input matrix
        A = (np.random.rand(matrix_M, matrix_N) - 0.5).astype(np.float16)
        Sum = np.zeros(matrix_N, ).astype(np.float16)
        Squared_diff = np.zeros(matrix_N, ).astype(np.float16)
        # Cast the correct type
        A = ff.array(A, 'e5m2')
        Sum = ff.array(Sum, 'e5m2')
        Squared_diff = ff.array(Squared_diff, 'e5m2')

        # Normalize matrix A (using BatchNorm)
        for i in range(matrix_M):
            Sum += A[i]
        mean = Sum / matrix_M

        for i in range(matrix_M):
            diff = A[i] - mean
            Squared_diff += diff * diff
        var = Squared_diff / matrix_M

        B = (A - mean) / np.sqrt(var)

        # Flatten the matrices into 1D arrays
        A = np.reshape(A, (matrix_M * matrix_N), order='C')
        B = np.reshape(B, (matrix_M * matrix_N), order='C')

    # f16,f32: Use normal operation (FP type automatically retained)
    else:
        # Define dimension
        matrix_M = defines['matrix_M']
        matrix_N = defines['matrix_N']

        # Create input matrix
        A = (np.random.rand(matrix_M, matrix_N) - 0.5).astype(my_type)
        Sum = np.zeros(matrix_N, ).astype(my_type)
        Squared_diff = np.zeros(matrix_N, ).astype(my_type)

        # Normalize matrix A (using BatchNorm)
        for i in range(matrix_M):
            Sum += A[i]
        mean = Sum / matrix_M

        for i in range(matrix_M):
            diff = A[i] - mean
            Squared_diff += diff * diff
        var = Squared_diff / matrix_M

        B = (A - mean) / np.sqrt(var)

        # Flatten the matrices into 1D arrays
        A = np.reshape(A, (matrix_M * matrix_N), order='C')
        B = np.reshape(B, (matrix_M * matrix_N), order='C')

    return [A, B], defines


def generate_flayernorm(my_type=np.float32, defines={}):

    # f8: Cast correct type
    if ff is not None and f"{my_type}" == f"{ff.FlexFloat('e5m2')}":

        # Define dimension
        matrix_M = defines['matrix_M']
        matrix_N = defines['matrix_N']

        # Create input matrix
        A = (np.random.rand(matrix_M, matrix_N) - 0.25).astype(np.float16)
        B = np.zeros((matrix_M, matrix_N)).astype(np.float16)
        # Cast the correct type
        A = ff.array(A, 'e5m2')
        B = ff.array(B, 'e5m2')

        # Normalize matrix A (using LayerNorm)
        for i in range(matrix_M):  # Loop over each sample (row)
            row = A[i]
            # Compute: mean = sum / N
            row_sum = ff.FlexFloat("e5m2", 0)
            for el in row:
                row_sum += el
            mean = row_sum / matrix_N
            # Compute E[x^2]
            row_sq = row * row
            row_sum = ff.FlexFloat("e5m2", 0)
            for el in row_sq:
                row_sum += el
            expected = row_sum / matrix_N
            # Compute mean^2
            mean_sq = mean * mean
            # Compute: var = E[x^2] - mean^2
            var = expected - mean_sq
            # Compute: std = sqrt(var)
            std = np.sqrt(var)

            diff = row - mean
            B[i] = (diff) / std

        # Flatten the matrices into 1D arrays
        A = np.reshape(A, (matrix_M * matrix_N), order='C')
        B = np.reshape(B, (matrix_M * matrix_N), order='C')

    # f16,f32: Use normal operation (FP type automatically retained)
    else:
        # Define dimension
        matrix_M = defines['matrix_M']
        matrix_N = defines['matrix_N']

        # Create input matrix
        A = (np.random.rand(matrix_M, matrix_N) - 0.5).astype(my_type)
        B = flayernorm(A, my_type=my_type, eps=0.0)

        # Flatten the matrices into 1D arrays
        A = np.reshape(A, (matrix_M * matrix_N), order='C')
        B = np.reshape(B, (matrix_M * matrix_N), order='C')

    return [A, B], defines


def fsoftmax_taylor(A, normalized=True, my_type=None):
    """
    Row-wise softmax-like function using the same Taylor exp approximation used
    by the MemPool softmax generators.
    """
    # e5m2 path (float8)
    if my_type is not None and ff is not None and f"{my_type}" == f"{ff.FlexFloat('e5m2')}":
        if A.ndim != 2:
            raise ValueError("fsoftmax_taylor expects a 2D array.")

        A_q = A.astype(np.float16, copy=False)
        A_q = ff.array(A_q, "e5m2")
        M, N = A_q.shape
        B_q = ff.array(np.zeros((M, N), dtype=np.float16), "e5m2")
        for i in range(M):
            a_max = np.max(A_q[i])
            diff = A_q[i] - a_max
            diff_2 = diff * diff
            diff_3 = diff_2 * diff
            numerator = 1 + diff + 0.5 * diff_2 + 0.167 * diff_3
            if normalized:
                numerator_sum = ff.FlexFloat("e5m2", 0)
                for el in numerator:
                    numerator_sum += el
                B_q[i] = numerator / numerator_sum
            else:
                B_q[i] = numerator
        return B_q

    if my_type is None:
        my_type = A.dtype
    A_t = A.astype(my_type, copy=False)
    if A_t.ndim != 2:
        raise ValueError("fsoftmax_taylor expects a 2D array.")

    a_max = np.max(A_t, axis=1, keepdims=True)
    diff = A_t - a_max
    numerator = 1 + diff + 0.5 * np.square(diff) + 0.167 * np.power(diff, 3)
    if normalized:
        denominator = np.sum(numerator, axis=1, keepdims=True)
        return (numerator / denominator).astype(my_type)
    return numerator.astype(my_type)


def generate_fsoftmax(my_type=np.float32, defines={}):

    # f8: Cast correct type
    if ff is not None and f"{my_type}" == f"{ff.FlexFloat('e5m2')}":

        # Define dimension
        matrix_M = defines['matrix_M']
        matrix_N = defines['matrix_N']

        # Create input matrix
        A = (np.random.rand(matrix_M, matrix_N) - 0.5).astype(np.float16)
        A_q = ff.array(A, 'e5m2')
        B_q = fsoftmax_taylor(A, normalized=True, my_type=my_type)

        # Flatten the matrices into 1D arrays
        A = np.reshape(A_q, (matrix_M * matrix_N), order='C')
        B = np.reshape(B_q, (matrix_M * matrix_N), order='C')

    # f16,f32: Use normal operation (FP type automatically retained)
    else:
        # Define dimension
        matrix_M = defines['matrix_M']
        matrix_N = defines['matrix_N']

        # Create input matrix
        A = (np.random.rand(matrix_M, matrix_N) - 0.5).astype(my_type)
        B = fsoftmax_taylor(A, normalized=True, my_type=my_type)

        # Flatten the matrices into 1D arrays
        A = np.reshape(A, (matrix_M * matrix_N), order='C')
        B = np.reshape(B, (matrix_M * matrix_N), order='C')

    return [A, B], defines


def generate_fmessagep(my_type=np.float32, defines={}):

    P = defines['matrix_P']  # number of graph nodes
    M = defines['matrix_M']  # width of input
    N = defines['matrix_N']  # height of input
    D = defines['matrix_D']  # depth of input
    width_HL = defines['width_HL']  # depth of input

    A = np.random.uniform(-0.5, 0.5, (P, M * N, D)).astype(my_type)
    B = np.zeros((P, M * N, D), dtype=my_type)

    # Outputs and parameters of the hidden-layer
    W_fc1 = np.random.rand(P, D, width_HL).astype(my_type)
    W_fc2 = np.random.rand(P, width_HL, D).astype(my_type)
    HL1 = np.zeros((P, M * N, width_HL), dtype=my_type)
    HL2 = np.zeros((P, M * N, D), dtype=my_type)
    HL1_bias = np.zeros((P, M * N, width_HL), dtype=my_type)
    if defines['BIAS'] == 1:
        HL1_bias = np.random.rand(P, M * N, width_HL).astype(my_type)

    if defines['FC_LAYER'] == 1:
        # Loops over the message passing instances
        for p in range(P):
            HL1[p] = np.matmul(A[p, :, :], W_fc1[p, :, :]) + HL1_bias[p]
            if defines['RELU'] == 1:
                HL1[p] = np.maximum(HL1[p], 0)
            HL2[p] = np.matmul(HL1[p], W_fc2[p, :, :])

    # Loops over the 2D image
    for i in range(M * N):
        # Loop over depth and sum the message passing instances
        for d in range(D):
            sum_val = np.float16(0.0)
            for p in range(P):
                sum_val += HL2[p, i, d]
            for p in range(P):
                B[p, i, d] = (sum_val - HL2[p, i, d]) / np.float16(P)

    A = np.reshape(A, (P * M * N * D))
    B = np.reshape(B, (P * M * N * D))
    HL = np.reshape(HL1, (P * M * N * width_HL))
    HL_bias = np.reshape(HL1_bias, (P * M * N * width_HL))
    W_fc1 = np.reshape(W_fc1, (P * width_HL * D))
    W_fc2 = np.reshape(W_fc2, (P * D * width_HL))

    A = A.astype(my_type)
    B = B.astype(my_type)

    return [A, B, HL, HL_bias, W_fc1, W_fc2], defines


def generate_fslp(my_type=np.float32, defines={}):
    matrix_M = defines["matrix_M"]
    matrix_N = defines["matrix_N"]
    matrix_P = defines["matrix_P"]

    X = (np.random.rand(matrix_M, matrix_N) - 0.5).astype(my_type)
    W = (np.random.rand(matrix_N, matrix_P) - 0.5).astype(my_type)
    Y = (np.random.rand(matrix_M, matrix_P) - 0.5).astype(my_type)
    Z = (np.matmul(X, W) + Y).astype(my_type)

    S = fsoftmax_taylor(Z, normalized=True, my_type=my_type)

    X = np.reshape(X, (matrix_M * matrix_N), order="C").astype(my_type)
    W = np.reshape(W, (matrix_N * matrix_P), order="C").astype(my_type)
    Y = np.reshape(Y, (matrix_M * matrix_P), order="C").astype(my_type)
    Z = np.reshape(Z, (matrix_M * matrix_P), order="C").astype(my_type)
    S = np.reshape(S, (matrix_M * matrix_P), order="C").astype(my_type)

    return [X, W, Y, Z, S], defines


def generate_fcnn(my_type=np.float32, defines={}):
    FM = defines["FM"]
    FN = defines["FN"]
    DW_D = defines["DW_D"]
    PW_D = defines["PW_D"]
    DW_K = defines["DW_K"]

    # Input tensor: (FM, FN, DW_D)
    X_img = (np.random.rand(FM, FN, DW_D) - 0.5).astype(my_type)
    # Bias / initial output buffer for pointwise GEMM: (FM, FN, PW_D)
    Y_img = (np.random.rand(FM, FN, PW_D) - 0.5).astype(my_type)
    # Weights
    Wdw = (np.random.rand(DW_K, DW_K, DW_D) - 0.5).astype(my_type)
    Wpw = (np.random.rand(DW_D, PW_D) - 0.5).astype(my_type)

    # Depthwise
    Xdw = np.zeros((FM, FN, DW_D), dtype=np.float32)
    Xdw = fconv2d_depthwise(X_img, Wdw, Xdw)

    # Pointwise
    Z_pw = fconv2d_pointwise(Xdw, Wpw, Y_img)
    Z_pw = Z_pw.reshape(FM * FN, PW_D)

    # Layernorm and ReLU
    Z_lnrm = flayernorm(Z_pw, my_type=my_type, eps=0.0)
    Z_relu = np.maximum(Z_lnrm, np.array(0.0, dtype=my_type))
    Z_relu = Z_relu.astype(my_type).reshape(FM, FN, PW_D)

    X = np.reshape(X_img, (FM * FN * DW_D), order="C").astype(my_type)
    Y = np.reshape(Y_img, (FM * FN * PW_D), order="C").astype(my_type)
    Z = np.reshape(Z_relu, (FM * FN * PW_D), order="C").astype(my_type)
    Wpw = np.reshape(Wpw, (DW_D * PW_D), order="C").astype(my_type)
    Wdw = np.reshape(Wdw, (DW_K * DW_K * DW_D), order="C").astype(my_type)

    return [X, Wpw, Wdw, Y, Z], defines


def generate_fmultihead(my_type=np.float32, defines={}):
    H = defines["H"]
    M = defines["M"]
    N = defines["N"]

    X = (np.random.rand(H * M, N) - 0.5).astype(my_type)
    Y = np.zeros((H * M, N), dtype=my_type)

    W_q = (np.random.rand(N, N) - 0.5).astype(my_type)
    W_k = (np.random.rand(N, N) - 0.5).astype(my_type)
    W_v = (np.random.rand(N, N) - 0.5).astype(my_type)

    Q = (np.matmul(X, W_q) + Y).astype(my_type)
    K = (np.matmul(X, W_k) + Y).astype(my_type)
    V = (np.matmul(X, W_v) + Y).astype(my_type)

    # Split into heads
    Q = Q.reshape(H, M, N)
    K = K.reshape(H, M, N)
    V = V.reshape(H, M, N)
    Y = Y.reshape(H, M, N)

    # Attention scores
    Kt = np.transpose(K, (0, 2, 1))           # (H, N, M)
    A = np.matmul(Q, Kt).astype(my_type)      # (H, M, M)

    A = fsoftmax_taylor(A.reshape(H * M, M), normalized=True, my_type=my_type)

    # Attention output
    Z = (np.matmul(A.reshape(H, M, M), V) + Y).astype(my_type)  # (H, M, N)

    # Flatten for header emission
    X = np.reshape(X, (H * M * N), order="C").astype(my_type)
    Y = np.reshape(Y, (H * M * N), order="C").astype(my_type)
    W_q = np.reshape(W_q, (N * N), order="C").astype(my_type)
    W_k = np.reshape(W_k, (N * N), order="C").astype(my_type)
    W_v = np.reshape(W_v, (N * N), order="C").astype(my_type)
    Z = np.reshape(Z, (H * M * N), order="C").astype(my_type)

    return [X, Y, W_q, W_k, W_v, Z], defines
