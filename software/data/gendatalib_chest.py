#!/usr/bin/env python3

# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# This script generates data for the Channel estimation.
# Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

import numpy as np


def q_sat(x):
    if x > 2**15 - 1:
        return x - 2**16
    elif x < -2**15:
        return x + 2**16
    else:
        return x


def compute_chest_q16(in_rx, in_tx, p):
    n_rx = in_rx.size
    n_tx = in_tx.size
    result = np.zeros(2 * (n_tx * n_rx), dtype=np.int16)
    for i in range(n_rx):
        a_r = in_rx[i].real
        a_i = in_rx[i].imag
        for j in range(n_tx):
            b_r = in_tx[j].real
            b_i = in_tx[j].imag

#            # Compute data division
#            den = (2**16) // (b_r * b_r + b_i * b_i)
#            num_r = (a_r * b_r) + (a_i * b_i)
#            num_i = (a_i * b_r) - (a_r * b_i)
#            result[2 * (i * n_tx + j)] = q_sat((num_r * den) // 2**p)
#            result[2 * (i * n_tx + j) + 1] = q_sat((num_i * den) // 2**p)

            # Compute data multiplication
            num_r = (a_r * b_r) - (a_i * b_i)
            num_i = (a_i * b_r) + (a_r * b_i)
            result[2 * (i * n_tx + j)] = q_sat(num_r // 2**p)
            result[2 * (i * n_tx + j) + 1] = q_sat(num_i // 2**p)
    return result


def generate_chest_q16(N_TX, N_RX, N_SAMPLES):
    FIXED_POINT = 8
    MAX = 2**7

    qvector_pilot_tx = []
    qvector_pilot_rx = []
    qvector_Hest = []
    for k in range(N_SAMPLES):
        # Create pilots
        pilot_rx = np.random.randint(-MAX, MAX - 1, size=N_RX) + 1j * \
            np.random.randint(-MAX, MAX - 1, size=N_RX)
        pilot_tx = np.random.randint(-MAX, MAX - 1, size=N_TX) + 1j * \
            np.random.randint(-MAX, MAX - 1, size=N_TX)
        # Compute Hest
        Hest = compute_chest_q16(pilot_rx, pilot_tx, FIXED_POINT)

        pilot_tx = np.column_stack(
            (pilot_tx.imag, pilot_tx.real)).astype(
            np.int16).flatten()
        pilot_rx = np.column_stack(
            (pilot_rx.imag, pilot_rx.real)).astype(
            np.int16).flatten()
        qvector_pilot_tx.append(pilot_tx)
        qvector_pilot_rx.append(pilot_rx)
        qvector_Hest.append(Hest)

    qvector_pilot_tx = np.reshape(qvector_pilot_tx, [2 * N_TX * N_SAMPLES])
    qvector_pilot_rx = np.reshape(qvector_pilot_rx, [2 * N_RX * N_SAMPLES])
    qvector_Hest = np.reshape(qvector_Hest, [2 * N_TX * N_RX * N_SAMPLES])
    return qvector_pilot_tx, qvector_pilot_rx, qvector_Hest
