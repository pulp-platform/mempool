#!/usr/bin/env python3

# Copyright 2022 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
# Author: Marco Bertuletti, ETH Zurich

import numpy as np
import argparse
import pathlib
from mako.template import Template

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
        default=pathlib.Path.cwd() / "data_barriers_test.h.tpl",
        help='Path to mako template'
    )
    parser.add_argument(
        "-v",
        "--verbose",
        action='store_true',
        help='Set verbose'
    )
    parser.add_argument(
        "-n",
        "--num_cores",
        type=int,
        required=False,
        default=1024,
        help='Number of cores.'
    )

    parser.add_argument(
        "-a",
        "--a_par",
        type=float,
        required=False,
        default=0.5,
        help='Number of cores.'
    )
    parser.add_argument(
        "-d",
        "--d_par",
        type=int,
        required=False,
        default=1,
        help='Number of cores.'
    )
    parser.add_argument(
        "-m",
        "--max",
        type=int,
        required=False,
        default=1024,
        help='Max delay.'
    )
    args = parser.parse_args()
    num_cores = args.num_cores
    ## Weybull distribution
    # a = args.a_par
    # D = args.d_par
    # delays = D * np.random.weibull(a, size=num_cores)
    # delays = np.asarray(delays, dtype = 'int')
    # Uniform
    max_delay = args.max
    delays = np.random.uniform(low=0.0, high=max_delay, size=num_cores)
    delays = np.asarray(delays, dtype = 'int')

    kwargs = {'name': 'barriers_test', 'delays': delays, 'num_cores' : num_cores}
    gen_data_header_file(args.outdir, args.tpl, **kwargs)

if __name__ == "__main__":
    main()
