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


def generate_chest_q16(nb_tx, nb_rx, nb_samples):
    FIXED_POINT = 8
    MAX = 2**7

    qvector_pilot_tx = []
    qvector_pilot_rx = []
    qvector_Hest = []
    for k in range(nb_samples):
        # Create pilots
        pilot_rx = np.random.randint(-MAX, MAX - 1, size=nb_rx) + 1j * \
            np.random.randint(-MAX, MAX - 1, size=nb_rx)
        pilot_tx = np.random.randint(-MAX, MAX - 1, size=nb_tx) + 1j * \
            np.random.randint(-MAX, MAX - 1, size=nb_tx)
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
        default=32,
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


if __name__ == "__main__":
    main()
