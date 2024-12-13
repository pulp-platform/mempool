#!/usr/bin/env python3

# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# This script generates data for the fp16 matmul.
# Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

# The script generates random inputs for the C functions.

import numpy as np
import math


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


def generate_flayernorm(my_type=np.float32, defines={}):

    # Create matrix
    array_N = defines['array_N']
    X = (np.random.rand(array_N)).astype(my_type)

    eps = np.array([0.01], dtype=np.float32)
    gamma = np.array([np.random.rand() - 0.5], dtype=np.float32)
    beta = np.array([np.random.rand() - 0.5], dtype=np.float32)

    # Compute mean and variance along the last axis
    mean = np.mean(X, axis=-1, keepdims=True).astype(my_type)
    var = np.var(X, axis=-1, keepdims=True).astype(my_type)

    # Normalize
    X_normalized = (X - mean) / np.sqrt(var + eps)
    # Scale and shift
    Y = gamma * X_normalized + beta

    if defines['RELU'] == 1:
        Y = np.maximum(Y, 0)

    return [X, Y, eps, gamma, beta], defines


def generate_fmessagep(my_type=np.float32, defines={}):

    matrix_P = defines['matrix_P']  # number of graph nodes
    matrix_M = defines['matrix_M']  # width of input
    matrix_N = defines['matrix_N']  # height of input
    matrix_D = defines['matrix_D']  # depth of input
    width_HL = defines['width_HL']  # depth of input

    A = np.random.rand(matrix_P, matrix_M, matrix_N, matrix_D).astype(my_type)
    B = np.zeros((matrix_P, matrix_M, matrix_N, matrix_D), dtype=my_type)

    # Outputs and parameters of the hidden-layer
    W_fc1 = np.random.rand(matrix_P, width_HL, matrix_D).astype(my_type)
    W_fc2 = np.random.rand(matrix_P, matrix_D, width_HL).astype(my_type)
    if defines['BIAS'] == 1:
        HL = np.random.rand(matrix_P, matrix_M, matrix_N, width_HL)
        HL = HL.astype(my_type)
    else:
        HL = np.zeros((matrix_P, matrix_M, matrix_N, width_HL))
        HL = HL.astype(my_type)

    # Loops over the 2D image
    for i in range(matrix_M):
        for j in range(matrix_N):
            # Loops over the message passing instances
            for p in range(matrix_P):

                if defines['FC_LAYER'] == 1:
                    # Apply hidden-layer
                    HL[p, i, j, :] += np.matmul(W_fc1[p, :], A[p, i, j, :])
                    if defines['RELU'] == 1:
                        HL = np.maximum(HL, 0)
                    A[p, i, j, :] = np.matmul(W_fc2[p, :], HL[p, i, j, :])

                # Loop over depth and sum the message passing instances
                for d in range(matrix_D):
                    sum_val = np.float16(0.0)
                    for np_idx in range(matrix_P):
                        if np_idx != p:
                            sum_val += A[np_idx, i, j, d]

                    # Divide sum
                    sum_val = sum_val / np.float16(matrix_P)
                    B[p, i, j, d] = sum_val

    A = np.reshape(A, (matrix_P * matrix_M * matrix_N * matrix_D))
    B = np.reshape(B, (matrix_P * matrix_M * matrix_N * matrix_D))
    HL = np.reshape(HL, (matrix_P * matrix_M * matrix_N * width_HL))
    W_fc1 = np.reshape(W_fc1, (matrix_P * width_HL * matrix_D))
    W_fc2 = np.reshape(W_fc2, (matrix_P * matrix_D * width_HL))

    A = A.astype(my_type)
    B = B.astype(my_type)

    return [A, B, HL, W_fc1, W_fc2], defines
