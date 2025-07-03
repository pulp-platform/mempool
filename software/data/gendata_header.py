#!/usr/bin/env python3

# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# This script generates data.h files.
# Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

import argparse
import os
import hjson
import ast
import numpy

import gendatalib as datalib
import pyflexfloat as ff


header = """\
// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// File generated with .data/print_header.py
// Author: Marco Bertuletti\n\n
"""


def format_type(typ, value):
    """
    formats the type for printing in .h file.
    :param typ: Input type
    :param value: Input_value
    """
    typ_i32b = ["int32_t", "uint32_t"]
    typ_i16b = ["int16_t", "uint16_t"]
    typ_i8b = ["int8_t", "uint8_t"]

    if typ in typ_i32b:
        stringyfied_val = '({}) 0X{:08X}'.format(
            typ, value.astype(numpy.uint32) & 0xffffffff)
    elif typ in typ_i16b:
        stringyfied_val = '({}) 0X{:04X}'.format(
            typ, value.astype(numpy.uint32) & 0x0000ffff)
    elif typ in typ_i8b:
        stringyfied_val = '({}) 0X{:02X}'.format(
            typ, value.astype(numpy.uint32) & 0x000000ff)
    elif typ == 'float':
        stringyfied_val = '({}) {:+.8f}'.format(typ, value)
    elif typ == '__fp16':
        stringyfied_val = '({}) {:+.4f}'.format(typ, value)
    elif typ == '__fp8':
        value = ff.FlexFloat("e5m2", value.astype(numpy.double))
        value = value.bits()
        stringyfied_val = '({}) 0X{}'.format(typ, value)
    else:
        raise Exception("ERROR: Unsupported data type!!!")

    return stringyfied_val


def print_array(arr, typ, name):
    """
    Converts arrays to a string.

    :param arr: Input array
    :param typ: Type of the array.
    :param name: Name of the array.
    """

    output_string = typ
    attr = " __attribute__((aligned(sizeof(int32_t)), section(\".l2\"))) "
    if (arr.size > 1):
        output_string += attr
        output_string += name + '[{}] = {{\n'.format(arr.size)
        for (value, count) in zip(arr, range(arr.size)):
            output_string += (format_type(typ, value) + ', ')
            count += 1
            if count % 4 == 0:
                output_string += '\n'
        output_string = output_string[:-3]
        output_string += "};\n\n"
    else:
        output_string += attr
        output_string += (name + ' = ' + format_type(typ, arr[0]))
        output_string += ";\n\n"

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
    for def_key, def_value in defines.items():
        output_string += "#define {} ({})\n".format(def_key, def_value)
    output_string += "\n"  # Add space between defines and arrays

    # Write the arrays using print_array
    for array_values, array_type, array_name in arrays:
        output_string += print_array(array_values, array_type, array_name)

    # Write everything to the file
    with open(filename, "w") as file:
        file.write(output_string)

    print("Generate {}".format(filename))


def get_type(type_string):
    """
    Gets the numpy type from the type specifyied in the json
    :param type_string: type from json file.
    """
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
    elif type_string == "float8":
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
        defnes = dict([ast.literal_eval(defne)
                      for defne in data_args.get("defines")])
        arrays = [ast.literal_eval(array) for array in data_args.get("arrays")]

    # Determine output file name
    filename = os.path.dirname(os.path.abspath(__file__))
    filename = os.path.join(filename, "data_{}.h".format(app_name))

    # Define function mappings for each app_name
    function_map = {
        "axpy_i32": {"func": datalib.generate_iaxpy},
        "axpy_f16": {"func": datalib.generate_faxpy},
        "axpy_f32": {"func": datalib.generate_faxpy},
        "cfft_radix2_q16": {"func": datalib.generate_cfft_q16},
        "cfft_radix4_f16": {"func": datalib.generate_fcfft},
        "cfft_radix4_q16": {"func": datalib.generate_cfft_q16},
        "chest_f16": {"func": datalib.generate_fchest},
        "chest_q16": {"func": datalib.generate_qchest},
        "cholesky_f16": {"func": datalib.generate_fccholesky},
        "cholesky_q16": {"func": datalib.generate_qccholesky},
        "cholesky_q32": {"func": datalib.generate_qcholesky},
        "cmatmul_f16": {"func": datalib.generate_fcmatmul},
        "cmatmul_q16": {"func": datalib.generate_qcmatmul},
        "dotp_f16": {"func": datalib.generate_fdotp},
        "dotp_f32": {"func": datalib.generate_fdotp},
        "dotp_i32": {"func": datalib.generate_idotp},
        "gaussjordan_q32": {"func": datalib.generate_qgaussjordan},
        "matmul_f16": {"func": datalib.generate_fmatmul},
        "matmul_f8": {"func": datalib.generate_fmatmul},
        "matmul_f32": {"func": datalib.generate_fmatmul},
        "matmul_i32": {"func": datalib.generate_imatmul},
        "matmul_i16": {"func": datalib.generate_imatmul},
        "matmul_i8": {"func": datalib.generate_imatmul},
        "mimo_mmse_q16": {"func": datalib.generate_qmmse},
        "mimo_mmse_f16": {"func": datalib.generate_fmmse},
        "mimo_mmse_f32": {"func": datalib.generate_fmmse},
        "mimo_mmse_f8": {"func": datalib.generate_fmmse},
        "ofdm_f16": {"func": datalib.generate_fofdm},
        "fence": {"func": datalib.generate_iarray},
        "memcpy": {"func": datalib.generate_iarray},
        "barriers_test": {"func": datalib.generate_barriers_test},
    }

    # Check if app_name exists in the function map
    if app_name in function_map:
        func_info = function_map[app_name]
        func = func_info["func"]
        # Call the function
        # The defnes dictionary is a function argument in case the generate
        # function adds new definitions.
        result, defnes = func(defines=defnes, my_type=my_type)
        # Print result to data header
        if len(arrays) == 1:
            arrays = [(result, *arrays[0])]
        else:
            arrays = [(result[i], *arrays[i]) for i in range(len(arrays))]
        print_file(header, defnes, arrays, filename)

    else:
        print("Data generation is not defined.")
