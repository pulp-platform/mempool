#!/usr/bin/env python3

# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# This script generates data for the Channel estimation.
# Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

import numpy as np
import argparse
import pathlib

from mako.template import Template

##################
#  write_result  #
##################


def gen_data_header_file(
        outdir: pathlib.Path.cwd(),
        tpl: pathlib.Path.cwd(),
        **kwargs):

    file = outdir / f"data_{kwargs['name']}.h"

    print(tpl, outdir, kwargs['name'])

    template = Template(filename=str(tpl))
    with file.open('w') as f:
        f.write(template.render(**kwargs))

######################
# Fixpoint Functions #
######################


def q_sat(x):
    if x > 2**15 - 1:
        return x - 2**16
    elif x < -2**15:
        return x + 2**16
    else:
        return x


def q_add(a, b):
    return q_sat(a + b)


def q_sub(a, b):
    return q_sat(a - b)


def q_mul(a, b, p):
    return a * b
    # return q_roundnorm(a * b, p)


def q_div(a, b, p):
    return a / b


def q_roundnorm(a, p):
    rounding = 1 << (p - 1)
    return q_sat((a + rounding) >> p)


def main():

    parser = argparse.ArgumentParser(description='Generate data for kernels')
    parser.add_argument(
        "-o",
        "--outdir",
        type=pathlib.Path,
        default=pathlib.Path.cwd(),
        required=False,
        help='Select out directory of generated data files'
    )
    parser.add_argument(
        "-t",
        "--tpl",
        type=pathlib.Path,
        required=False,
        default=pathlib.Path.cwd() / "data_chest_q16.h.tpl",
        help='Path to mako template'
    )
    parser.add_argument(
        "-v",
        "--verbose",
        action='store_true',
        help='Set verbose'
    )
    parser.add_argument(
        "-b",
        "--num_beams",
        type=int,
        required=False,
        default=4,
        help='Number beams'
    )
    parser.add_argument(
        "-l",
        "--num_layers",
        type=int,
        required=False,
        default=4,
        help='Number layers'
    )
    parser.add_argument(
        "-s",
        "--num_samples",
        type=int,
        required=False,
        default=32,
        help='Number samples'
    )

    # Generate the channel mean value
    def random_SDP_matrix(n):
        G = np.random.randn(n, n)
        np.dot(G, G.T, G)
        return G / np.trace(G)

    # Convert to fixed point
    def fixed_point_conversion(v_input, fixed_point, scaling_factor):
        real = (np.multiply(v_input.real,
                            scaling_factor * 2**(np.log2(fixed_point))))
        imag = (np.multiply(v_input.imag,
                            scaling_factor * 2**(np.log2(fixed_point))))
        output = np.zeros(len(real) * 2)
        for i in range(0, len(real)):
            output[2 * i] = real[i]
            output[2 * i + 1] = imag[i]
        return output.astype(np.int16)

    # Compute the channel estimate
    def compute_result(in_rx, in_tx, p):
        my_type = np.int16
        a = in_rx.astype(my_type)
        b = in_tx.astype(my_type)
        n_rx = a.size >> 1
        n_tx = b.size >> 1
        result = np.zeros(2 * (n_tx * n_rx), dtype=my_type)
        for i in range(n_rx):
            a_r = a[2 * i]
            a_i = a[2 * i + 1]
            for j in range(n_tx):
                b_r = b[2 * j]
                b_i = b[2 * j + 1]
                den = q_mul(b_r, b_r, p) + q_mul(b_i, b_i, p)
                num_r = q_add(q_mul(a_r, b_r, p), q_mul(a_i, b_i, p))
                num_i = q_sub(q_mul(a_i, b_r, p), q_mul(a_r, b_i, p))
                result[2 * (i * n_tx + j)] = q_div(num_r, den, p)
                result[2 * (i * n_tx + j) + 1] = q_div(num_i, den, p)
        return result

    args = parser.parse_args()
    nb_tx = args.num_beams
    nb_rx = args.num_layers
    nb_samples = args.num_samples

    H = np.random.randn(nb_rx, nb_tx) + 1j * np.random.randn(nb_rx, nb_tx)

    qvector_pilot_tx = []
    qvector_pilot_rx = []
    qvector_Hest = []
    for k in range(nb_samples):
        pilot_tx = 1 * np.exp(1j * np.random.randn(nb_tx))
        pilot_rx = np.dot(H, pilot_tx)
        fixed_point = 12
        scaling_factor = 1
        q_pilot_tx = fixed_point_conversion(
            np.reshape(pilot_tx, [nb_tx]), fixed_point, 1)
        q_pilot_rx = fixed_point_conversion(
            np.reshape(pilot_rx, [nb_rx]), fixed_point, scaling_factor)
        q_H = fixed_point_conversion(
            np.reshape(H, [nb_tx * nb_rx]), fixed_point, scaling_factor)
        q_Hest = compute_result(q_pilot_rx, q_pilot_tx, fixed_point)
        qvector_pilot_tx.append(q_pilot_tx)
        qvector_pilot_rx.append(q_pilot_rx)
        qvector_Hest.append(q_Hest)
        print(q_H)
        print(q_Hest)

    qvector_pilot_tx = np.reshape(qvector_pilot_tx, [2 * nb_tx * nb_samples])
    qvector_pilot_rx = np.reshape(qvector_pilot_rx, [2 * nb_rx * nb_samples])
    qvector_Hest = np.reshape(qvector_Hest, [2 * nb_tx * nb_rx * nb_samples])

    kwargs = {'name': 'chest_q16', 'pilot_tx': qvector_pilot_tx,
                                   'pilot_rx': qvector_pilot_rx,
                                   'Hest': qvector_Hest,
                                   'nb_tx': nb_tx,
                                   'nb_rx': nb_rx,
                                   'nb_samples': nb_samples}

    gen_data_header_file(args.outdir, args.tpl, **kwargs)


if __name__ == "__main__":
    main()
