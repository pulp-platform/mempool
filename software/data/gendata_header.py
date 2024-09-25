#!/usr/bin/env python3

# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# This script generates data.h files.
# Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

import argparse
import os
import math
import hjson
import ast
import numpy

import gendatalib_cfft as cfft
import gendatalib_chest as chest
import gendatalib_blas as blas


header = """\
// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// File generated with .data/print_header.py
// Author: Marco Bertuletti\n\n
"""


def print_array(arr, typ, name):

    typ_i32b = ["int32_t", "uint32_t"]
    typ_i16b = ["int16_t", "uint16_t"]
    typ_i8b = ["int8_t", "uint8_t"]

    output_string = typ
    attr = " __attribute__((aligned(sizeof(int32_t)), section(\".l2\"))) "
    output_string += attr
    output_string += name + '[{}] = {{\n'.format(arr.size)
    for (value, count) in zip(arr, range(arr.size)):
        if typ in typ_i32b:
            output_string += '({}) 0X{:08X}, '.format(typ, value & 0xffffffff)
        elif typ in typ_i16b:
            output_string += '({}) 0X{:04X}, '.format(typ, value & 0x0000ffff)
        elif typ in typ_i8b:
            output_string += '({}) 0X{:02X}, '.format(typ, value & 0x000000ff)
        elif typ == 'float':
            output_string += '({}) {:+.8f}, '.format(typ, value)
        elif typ == '__fp16':
            output_string += '({}) {:+.4f}, '.format(typ, value)
        else:
            raise Exception("ERROR: Unsupported data type!!!")
        count += 1
        if count % 4 == 0:
            output_string += '\n'
    output_string = output_string[:-3]
    output_string += "};\n\n"
    return output_string


def print_file(header, defines, arrays, filename):
    """
    Writes defines and arrays to a file.

    :param header: Header of the printed file
    :param defines: A tuple of (define_name, define_value).
    :param arrays: A tuple of (array_name, array_type, array_values).
    :param filename: The output file to write to.
    """

    # Initialize the output string
    output_string = header

    # Write the defines
    for define_name, define_value in defines:
        output_string += "#define {} ({})\n".format(define_name, define_value)
    output_string += "\n"  # Add space between defines and arrays

    # Write the arrays using print_array
    for array_values, array_type, array_name in arrays:
        output_string += print_array(array_values, array_type, array_name)

    # Write everything to the file
    with open(filename, "w") as file:
        file.write(output_string)

    print("Generate {}".format(filename))


def get_type(type_string):
    if type_string == "int8":
        return numpy.int8
    elif type_string == "int16":
        return numpy.int16
    elif type_string == "int32":
        return numpy.int32
    elif type_string == "float32":
        return numpy.float32
    elif type_string == "float16":
        return numpy.float16
    else:
        raise Exception("Input type is not valid")


if __name__ == '__main__':

    parser = argparse.ArgumentParser(
        description='Generate data.h header files.')
    parser.add_argument('--app_name', type=str, help='Name of the app')
    parser.add_argument('--params', type=str, help='Name of the app')

    # Parse the command-line arguments
    args = parser.parse_args()
    app_name = args.app_name
    with open(args.params, 'r') as hjson_file:
        config_data = hjson.load(hjson_file)
    data_args = config_data.get(app_name)

    if data_args is not None:
        my_type = get_type(data_args.get("type"))
        defnes = [ast.literal_eval(defne)
                  for defne in data_args.get("defines")]
        arrays = [ast.literal_eval(array)
                  for array in data_args.get("arrays")]

    # Determine output file name
    filename = os.path.dirname(os.path.abspath(__file__))
    filename = os.path.join(filename, "data_{}.h".format(app_name))

    # Generate data header file
    if app_name == "axpy_i32":

        result = blas.generate_iaxpy(**{name: value for name, value in defnes})
        arrays = [(result[i], *arrays[i]) for i in range(len(arrays))]
        print_file(header, defnes, arrays, filename)

    elif app_name == "cfft_radix4_q16":

        result = cfft.generate_cfft_q16(
            **{name: value for name, value in defnes})
        N = defnes[0][1]
        defnes += [
            ("LOG2", int(math.log2(N))),
            ("N_TWIDDLES", 3 * N // 4),
            ("BITREVINDEXTABLE_LENGTH", len(result[3])),
            ("TOLERANCE", result[4]),
        ]
        result = result[0:4]
        arrays = [(result[i], *arrays[i]) for i in range(len(arrays))]
        print_file(header, defnes, arrays, filename)

    elif app_name == "cfft_radix2_q16":

        result = cfft.generate_cfft_q16(
            **{name: value for name, value in defnes})
        N = defnes[0][1]
        defnes += [
            ("LOG2", int(math.log2(N))),
            ("N_TWIDDLES", 3 * N // 4),
            ("BITREVINDEXTABLE_LENGTH", len(result[3])),
            ("TOLERANCE", result[4]),
        ]
        result = result[0:4]
        arrays = [(result[i], *arrays[i]) for i in range(len(arrays))]
        print_file(header, defnes, arrays, filename)

    elif app_name == "chest_q16":

        result = chest.generate_chest_q16(
            **{name: value for name, value in defnes})
        arrays = [(result[i], *arrays[i]) for i in range(len(arrays))]
        print_file(header, defnes, arrays, filename)

    elif app_name == "cholesky_q32":

        result = blas.generate_qcholesky(
            **{name: value for name, value in defnes})
        arrays = [(result[i], *arrays[i]) for i in range(len(arrays))]
        print_file(header, defnes, arrays, filename)

    elif app_name == "matmul_f16":

        result = blas.generate_fmatmul(
            **{name: value for name, value in defnes}, my_type=my_type)
        arrays = [(result[i], *arrays[i]) for i in range(len(arrays))]
        print_file(header, defnes, arrays, filename)

    elif app_name == "matmul_f32":

        result = blas.generate_fmatmul(
            **{name: value for name, value in defnes}, my_type=my_type)
        arrays = [(result[i], *arrays[i]) for i in range(len(arrays))]
        print_file(header, defnes, arrays, filename)

    elif app_name == "matmul_i32":

        result = blas.generate_imatmul(
            **{name: value for name, value in defnes}, my_type=my_type)
        arrays = [(result[i], *arrays[i]) for i in range(len(arrays))]
        print_file(header, defnes, arrays, filename)

    elif app_name == "matmul_i16":

        result = blas.generate_imatmul(
            **{name: value for name, value in defnes}, my_type=my_type)
        arrays = [(result[i], *arrays[i]) for i in range(len(arrays))]
        print_file(header, defnes, arrays, filename)

    elif app_name == "matmul_i8":

        result = blas.generate_imatmul(
            **{name: value for name, value in defnes}, my_type=my_type)
        arrays = [(result[i], *arrays[i]) for i in range(len(arrays))]
        print_file(header, defnes, arrays, filename)

    elif (app_name == "fence") | (app_name == "memcpy"):

        result = blas.generate_iarray(
            **{name: value for name, value in defnes}, my_type=my_type)
        arrays = [(result, *arrays[0])]
        print_file(header, defnes, arrays, filename)

    else:
        print("No need for data generation.")
