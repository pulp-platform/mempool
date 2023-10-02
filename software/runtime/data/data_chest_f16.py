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
        "-t",
        "--tpl",
        type=pathlib.Path,
        required=False,
        default=pathlib.Path(__file__).parent.absolute() /
        "data_chest_f16.h.tpl",
        help='Path to mako template')
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

    args = parser.parse_args()
    nb_rx = args.num_beams
    nb_tx = args.num_layers
    nb_samples = args.num_samples

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
        Hest = np.column_stack((Hest.real, Hest.imag)
                               ).astype(np.float16).flatten()

        # Output vectors
        vector_pilot_tx.append(pilot_tx)
        vector_pilot_rx.append(pilot_rx)
        vector_Hest.append(Hest)

    vector_pilot_rx = np.concatenate(vector_pilot_rx, axis=0)
    vector_pilot_tx = np.concatenate(vector_pilot_tx, axis=0)
    vector_Hest = np.concatenate(vector_Hest, axis=0)
    print(vector_Hest)

    kwargs = {'name': 'data_chest_f16',
              'pilot_rx': vector_pilot_rx,
              'pilot_tx': vector_pilot_tx,
              'Hest': vector_Hest,
              'nb_tx': nb_tx,
              'nb_rx': nb_rx,
              'nb_samples': nb_samples}

    gen_data_header_file(args.outdir, args.tpl, **kwargs)


if __name__ == "__main__":
    main()
