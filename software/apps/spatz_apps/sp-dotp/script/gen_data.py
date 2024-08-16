#!/usr/bin/env python3
# Copyright 2022 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Diyou Shen         <dishen@student.ethz.ch>
#         Matheus Cavalcante <matheusd@iis.ee.ethz.ch>

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

    # file = file_path / ('data_' + str(m) + '_' + str(cores) + ".h")
    file = file_path / ("data_dotp.h")
    emit_str += emit_dotp_layer(**kwargs)
    with file.open('w') as f:
        f.write(emit_str)

def emit_dotp_layer(name='dotp', **kwargs):
    vec_A = kwargs['A']
    vec_B = kwargs['B']
    result = kwargs['result']

    m = kwargs['M']
    cores = kwargs['cores']

    layer_str = ''
    layer_str += '#include "layer.h"\n\n'
    layer_str += f'dotp_layer {name}_l = {{\n'
    layer_str += f'\t.M = {m},\n'
    layer_str += f'\t.dtype = FP{kwargs["prec"]},\n'
    layer_str += '};\n\n\n'

    ctypes = {
        '64': 'double',
        '32': 'float',
        '16': '__fp16',
        '8': 'char'
    }

    dtype = ctypes[str(kwargs['prec'])]
    if dtype != 'char':
        layer_str += f'const uint32_t active_cores = {cores};\n'
        layer_str += f'{dtype} a[{m}] __attribute__((section(".l1_prio")))' + ';\n'
        layer_str += f'{dtype} b[{m}] __attribute__((section(".l1_prio")))' + ';\n'
        layer_str += f'{dtype} result[{cores+1}] __attribute__((section(".l1_prio")))' + ';\n\n\n'
        layer_str += f'static {dtype} {name}_A_dram [{m}] __attribute__((section(".data"))) = ' + array_to_cstr(vec_A) + ';\n\n\n'
        layer_str += f'static {dtype} {name}_B_dram [{m}] __attribute__((section(".data"))) = ' + array_to_cstr(vec_B) + ';\n\n\n'
        layer_str += f'static {dtype} {name}_result __attribute__((section(".data"))) = ' + array_to_cstr(result) + ';\n\n\n'
    else:
        layer_str += f'static {dtype} {name}_A_dram [{m}] = ' + \
            array_to_cstr(kwargs['bits_A'], fmt='char') + ';\n\n\n'
        layer_str += f'static {dtype} {name}_B_dram [{m}] = ' + \
            array_to_cstr(kwargs['bits_B'], fmt='char') + ';\n\n\n'
        layer_str += f'static {dtype} {name}_result = ' + \
            array_to_cstr(kwargs['result'], fmt='char') + ';\n\n\n'

    return layer_str


def rand_data_generator(shape, prec, alt=False):
    if prec == 64:
        return torch.randn(shape, requires_grad=False, dtype=torch.float64), {}
    elif prec == 32:
        return torch.randn(shape, requires_grad=False, dtype=torch.float32), {}
    elif prec == 16:
        if alt:
            return torch.randn(shape, requires_grad=False, dtype=torch.bfloat16), {}
        else:
            return torch.randn(shape, requires_grad=False, dtype=torch.float16), {}
    elif prec == 8:
        sign = torch.randint(0, 2, shape, requires_grad=False, dtype=torch.uint8)  # -1 or 1
        exponent = torch.randint(0, 16, shape, requires_grad=False, dtype=torch.uint8)  # < 0b01111
        mantissa = torch.randint(0, 4, shape, requires_grad=False, dtype=torch.uint8)  # can be arbitrary
        bits = {'sign': sign, 'exponent': exponent, 'mantissa': mantissa}
        # TODO: not actually correct
        return ((-1.0)**sign.double())*(2.0**(exponent.double()-15.0))*(1.0 + mantissa.double() / (2**2)), bits

def dotp(a, b):
    return reduce(lambda a, b: a+b, np.multiply(a, b))

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

    CORES = param['core']

    vec_A, bits_A = rand_data_generator((param['M'], 1), param['prec'])
    vec_B, bits_B = rand_data_generator((param['M'], 1), param['prec'])
    result = dotp(vec_A, vec_B)

    kwargs = {
      'A': vec_A,
      'B': vec_B,
      'result': result,
      'M': param['M'],
      'prec': param['prec'],
      'expand': param['expand'],
      'bits_A': bits_A,
      'bits_B': bits_B,
      'cores': CORES
    }

    emit_header_file('dotp', **kwargs)

if __name__ == '__main__':
    main()
