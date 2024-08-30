#!/usr/bin/env python3

# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# This script generates data for the fp16 matmul.
# Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

import numpy as np
import argparse
import pathlib
from mako.template import Template


def generate_dotp_i32(Len):

    # Create matrix
    MAX = 2**7 - 1
    A = np.random.randint(-MAX, MAX - 1, size=Len)
    B = np.random.randint(-MAX, MAX - 1, size=Len)
    C = np.dot(A, B)
    return A, B, C


def generate_dotp_f32(Len):

    # Create matrix
    A = np.random.rand(Len).astype(np.float32)
    B = np.random.rand(Len).astype(np.float32)
    C = (np.dot(A, B)).astype(np.float32)
    return A, B, C


def generate_dotp_f16(Len):

    # Create matrix
    A = np.random.rand(Len).astype(np.float16)
    B = np.random.rand(Len).astype(np.float16)
    C = (np.dot(A, B)).astype(np.float16)
    return A, B, C

##################
# compute_result #
##################


def gen_data_header_file(outdir: pathlib.Path.cwd(),
                         tpl: pathlib.Path.cwd(), **kwargs):

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
        "-n",
        "--length",
        type=int,
        required=False,
        default=4096,
        help='First dimension.'
    )

    args = parser.parse_args()
    Len = args.length

    A, B, C = generate_dotp_i32(Len)
    tpl = pathlib.Path(__file__).parent.absolute() / "data_dotp_i32.h.tpl"
    kwargs = {
        'name': 'data_dotp_i32',
        'A': A,
        'B': B,
        'C': C,
        'Len': Len}
    gen_data_header_file(args.outdir, tpl, **kwargs)

    A, B, C = generate_dotp_f32(Len)
    tpl = pathlib.Path(__file__).parent.absolute() / "data_dotp_f32.h.tpl"
    kwargs = {
        'name': 'data_dotp_f32',
        'A': A,
        'B': B,
        'C': C,
        'Len': Len}
    gen_data_header_file(args.outdir, tpl, **kwargs)

    A, B, C = generate_dotp_f16(Len)
    tpl = pathlib.Path(__file__).parent.absolute() / "data_dotp_f16.h.tpl"
    kwargs = {
        'name': 'data_dotp_f16',
        'A': A,
        'B': B,
        'C': C,
        'Len': Len}
    gen_data_header_file(args.outdir, tpl, **kwargs)


if __name__ == "__main__":
    main()
