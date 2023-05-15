# Copyright 2022 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Marco Bertuletti, ETH Zurich

#!/usr/bin/env python3

import numpy as np
import argparse
import pathlib
from mako.template import Template
from scipy.linalg import solve_triangular


##################
# compute_result #
##################

def gen_data_header_file(outdir: pathlib.Path.cwd(), tpl: pathlib.Path.cwd(), **kwargs):

    file = outdir / f"data_{kwargs['name']}.h"

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
        default=pathlib.Path.cwd(),
        required=False,
        help='Select out directory of generated data files'
    )
    parser.add_argument(
        "-t",
        "--tpl",
        type=pathlib.Path,
        required=False,
        default=pathlib.Path.cwd() / "data_ofdm.h.tpl",
        help='Path to mako template'
    )
    parser.add_argument(
        "-v",
        "--verbose",
        action='store_true',
        help='Set verbose'
    )
    parser.add_argument(
        "-rx",
        "--receivers",
        type=int,
        required=False,
        default=64,
        help='First dimension.'
    )
    parser.add_argument(
        "-bs",
        "--beams",
        type=int,
        required=False,
        default=32,
        help='Second dimension.'
    )
    parser.add_argument(
        "-sc",
        "--subcarriers",
        type=int,
        required=False,
        default=4096,
        help='Iterations.'
    )
    parser.add_argument(
        "-sb",
        "--symbols",
        type=int,
        required=False,
        default=1,
        help='Iterations.'
    )

    args = parser.parse_args()
    N_rx=args.receivers
    N_bs=args.beams
    N_sc=args.subcarriers
    N_sb=args.symbols

    itr=args.symbols

    pFFT_src = [str(np.random.randint(-2^15, 2^15-1)) for i in range(int(2*N_sb*N_rx*N_sc))]
    pTw_coef = [str(np.random.randint(-2^15, 2^15-1)) for i in range(int(4 * N_sc))]
    pBF_coef = [str(np.random.randint(-2^15, 2^15-1)) for i in range(int(2*N_sb*N_rx*N_bs))]

    kwargs = {'name': 'ofdm', 'pFFT_src': pFFT_src, 'pTw_coef': pTw_coef, 'pBF_coef': pBF_coef, 'N_rx' : N_rx, 'N_bs' : N_bs, 'N_sc' : N_sc, 'N_sb' : N_sb}
    gen_data_header_file(args.outdir, args.tpl, **kwargs)

if __name__ == "__main__":
    main()
