#!/usr/bin/env python3
# Copyright 2022 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Diyou Shen         <dishen@student.ethz.ch>

import numpy as np
import torch
import torch.nn as nn
import argparse
import pathlib
import hjson
from functools import reduce

np.random.seed(42)
torch.manual_seed(42)

global verbose

def array_to_cstr(a, fmt=float):
    out = '{'
    if fmt == float:
        if isinstance(a, np.ndarray):
            a = a.flat
        if isinstance(a, torch.Tensor):
            a = a.numpy().flat
        for el in a:
            out += '{}, '.format(el)
    else:
        for sign, exp, mant in zip(a['sign'].numpy().flat, a['exponent'].numpy().flat, a['mantissa'].numpy().flat):
            value = sign * 2**7 + exp * 2**2 + mant
            out += "0x{:02x}, ".format(value)
    out = out[:-2] + '}'
    return out

def emit_header_file(layer_type: str, **kwargs):

    m = kwargs['M']
    cores = kwargs['cores']
    file_path = pathlib.Path(__file__).parent.parent / 'data'
    emit_str = "// Copyright 2022 ETH Zurich and University of Bologna.\n" + \
               "// Licensed under the Apache License, Version 2.0, see LICENSE for details.\n" + \
               "// SPDX-License-Identifier: Apache-2.0\n\n"

    file = file_path / ('data.h')
    emit_str += emit_dotp_layer(**kwargs)
    with file.open('w') as f:
        f.write(emit_str)

def emit_dotp_layer(**kwargs):
    vec_A = kwargs['A']

    m = kwargs['M']
    cores = kwargs['cores']
    offset_size = kwargs['round'] * cores
    offset = kwargs['offset']
    rnd = kwargs['round']

    layer_str = ''
    layer_str += f'const uint32_t M = {m};\n'
    layer_str += f'const uint32_t R = {rnd};\n'

    ctypes = {
        '64': 'int64',
        '32': 'int',
        '16': 'int16',
        '8': 'char'
    }

    dtype = ctypes[str(kwargs['prec'])]

    layer_str += f'const uint32_t active_cores = {cores};\n'
    layer_str += f'{dtype} data_l1[{m}] __attribute__((section(".l1_prio")))' + ';\n'
    layer_str += f'uint32_t offset_l1[{offset_size}] __attribute__((section(".l1_prio")))' + ';\n'
    layer_str += f'static {dtype} data_dram [{m}] __attribute__((section(".data"))) = ' + array_to_cstr(vec_A) + ';\n\n\n'
    layer_str += f'static uint32_t offset_dram [{offset_size}] __attribute__((section(".data"))) = ' + offset + ';\n\n\n'

    return layer_str


def rand_data_generator(shape, prec, alt=False):
    if prec == 64:
        return torch.randint(-100, 100, shape, requires_grad=False, dtype=torch.int64), {}
    elif prec == 32:
        return torch.randint(-100, 100, shape, requires_grad=False, dtype=torch.int32), {}
    elif prec == 16:
        return torch.randint(-100, 100, shape, requires_grad=False, dtype=torch.int16), {}


# generate the random address visited by each cores
def rand_addr_generator(shape=64, min_val=0, max_val=100, step=32):
    # Ensure min_val and max_val are within the uint32 range
    min_val = max(min_val, np.iinfo(np.uint32).min)
    max_val = min(max_val, np.iinfo(np.uint32).max)
    
    # Generate a random array of uint32 values within [min_val, max_val]
    rand_array = np.random.randint(low=min_val, high=max_val + 1, size=shape, dtype=np.uint16)
    rand_array = rand_array * step

    # Convert the array to a formatted string
    formatted_str = "{\n"

    values_per_line = 16  # Adjust as needed for your formatting preference
    max_value_length = len(str(max_val * step))  # Maximum length of the numbers
    for i in range(0, len(rand_array), values_per_line):
        # Format each number to have a fixed width for alignment
        line = ", ".join(f"{num:>{max_value_length}}" for num in rand_array[i:i+values_per_line])
        if i + values_per_line < len(rand_array):
            formatted_str += "  " + line + ",\n"
        else:
            formatted_str += "  " + line  # Last line without a comma at the end

    formatted_str += "\n}"
    
    return formatted_str

def main():

    parser = argparse.ArgumentParser(description='Generate data for kernels')
    parser.add_argument(
        "-c",
        "--cfg",
        type=pathlib.Path,
        required=True,
        help='Select param config file kernel'
    )
    parser.add_argument(
        "-v",
        "--verbose",
        action='store_true',
        help='Set verbose'
    )

    args = parser.parse_args()

    global verbose
    verbose = args.verbose

    with args.cfg.open() as f:
        param = hjson.loads(f.read())

    if param['prec'] == 64:
        dtype = torch.float64
    elif param['prec'] == 16:
        dtype = torch.float16
    elif param['prec'] == 8:
        dtype = None
    else:
        dtype = torch.float32

    vec_A, bits_A = rand_data_generator((param['M'], 1), param['prec'])
    # offset = rand_addr_generator(param['core']*param['round'], 0, param['M']//2, param['step'])
    offset = rand_addr_generator(param['core']*param['round'], 0, param['core']-1, param['step'])

    kwargs = {
      'A': vec_A,
      'M': param['M'],
      'round': param['round'],
      'step': param['step'],
      'prec': param['prec'],
      'expand': param['expand'],
      'bits_A': bits_A,
      'cores': param['core'],
      'offset': offset
    }

    emit_header_file('dotp', **kwargs)

if __name__ == '__main__':
    main()
