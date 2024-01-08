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

    file = outdir / f"{kwargs['name']}.h"

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


def q_div(a, b, p):
    return a / b


def generate_chest_f16(nb_tx, nb_rx, nb_samples):
    H = np.random.randn(nb_rx, nb_tx) + 1j * np.random.randn(nb_rx, nb_tx)
    vector_pilot_tx = []
    vector_pilot_rx = []
    vector_Hest = []
    for k in range(nb_samples):

        # Compute data
        pilot_tx = 1 * np.exp(1j * np.random.randn(nb_tx))
        pilot_rx = np.dot(H, pilot_tx)
        Hest = pilot_rx[:, np.newaxis] / pilot_tx[np.newaxis, :]

        # Interleaved real and imaginary parts
        pilot_tx = np.column_stack(
            (pilot_tx.real, pilot_tx.imag)).astype(np.float16).flatten()
        pilot_rx = np.column_stack(
            (pilot_rx.real, pilot_rx.imag)).astype(np.float16).flatten()
        Hest = Hest.flatten()
        Hest = np.column_stack(
            (Hest.real, Hest.imag)).astype(
            np.float16).flatten()

        # Output vectors
        vector_pilot_tx.append(pilot_tx)
        vector_pilot_rx.append(pilot_rx)
        vector_Hest.append(Hest)

    vector_pilot_rx = np.concatenate(vector_pilot_rx, axis=0)
    vector_pilot_tx = np.concatenate(vector_pilot_tx, axis=0)
    vector_Hest = np.concatenate(vector_Hest, axis=0)
    return vector_pilot_tx, vector_pilot_rx, vector_Hest

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


def compute_chest_q16(in_rx, in_tx, p):
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


def generate_chest_q16(nb_tx, nb_rx, nb_samples):
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
            np.reshape(
                pilot_rx,
                [nb_rx]),
            fixed_point,
            scaling_factor)
        q_Hest = compute_chest_q16(q_pilot_rx, q_pilot_tx, fixed_point)
        qvector_pilot_tx.append(q_pilot_tx)
        qvector_pilot_rx.append(q_pilot_rx)
        qvector_Hest.append(q_Hest)
    qvector_pilot_tx = np.reshape(qvector_pilot_tx, [2 * nb_tx * nb_samples])
    qvector_pilot_rx = np.reshape(qvector_pilot_rx, [2 * nb_rx * nb_samples])
    qvector_Hest = np.reshape(qvector_Hest, [2 * nb_tx * nb_rx * nb_samples])
    return qvector_pilot_tx, qvector_pilot_rx, qvector_Hest


def main():

    parser = argparse.ArgumentParser(description='Generate data for kernels')
    parser.add_argument(
        "-o",
        "--outdir",
        type=pathlib.Path,
        default=pathlib.Path(__file__).parent.absolute(),
        required=False,
        help='Select out directory of generated data files'
    )
    parser.add_argument(
        "-b",
        "--num_rx",
        type=int,
        required=False,
        default=4,
        help='Number beams'
    )
    parser.add_argument(
        "-l",
        "--num_tx",
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

    args = parser.parse_args()
    nb_tx = args.num_tx
    nb_rx = args.num_rx
    nb_samples = args.num_samples

    pilot_tx, pilot_rx, Hest = generate_chest_q16(nb_tx, nb_rx, nb_samples)
    tpl = pathlib.Path(__file__).parent.absolute() / "data_chest_q16.h.tpl"
    kwargs = {'name': 'data_chest_q16',
              'pilot_tx': pilot_tx,
              'pilot_rx': pilot_rx,
              'Hest': Hest,
              'nb_tx': nb_tx,
              'nb_rx': nb_rx,
              'nb_samples': nb_samples}
    gen_data_header_file(args.outdir, tpl, **kwargs)

    pilot_tx, pilot_rx, Hest = generate_chest_f16(nb_tx, nb_rx, nb_samples)
    tpl = pathlib.Path(__file__).parent.absolute() / "data_chest_f16.h.tpl"
    kwargs = {'name': 'data_chest_f16',
              'pilot_rx': pilot_rx,
              'pilot_tx': pilot_tx,
              'Hest': Hest,
              'nb_tx': nb_tx,
              'nb_rx': nb_rx,
              'nb_samples': nb_samples}
    gen_data_header_file(args.outdir, tpl, **kwargs)


if __name__ == "__main__":
    main()
