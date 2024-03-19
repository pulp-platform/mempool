#!/usr/bin/env python3

# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# This script generates data for the Channel estimation.
# Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

import argparse
import os
import math
import generate_cfft as cfft
import generate_chest as chest


def extract_data_args(filename):
    # Define a dictionary to store numerical values for each flag
    args = {}

    # Open the file for reading
    with open(filename, 'r') as file:
        # Iterate through each line in the file
        for line in file:
            # Split the line into words
            words = line.split()
            # Iterate through each word in the line
            for i in range(len(words)):
                flag = words[i]  # Get the flag name
                # Check if the next word exists and is a numerical value
                if i + 1 < len(words) and words[i + 1].isdigit():
                    # Convert the numerical value to an integer
                    numerical_value = int(words[i + 1])
                    # Store the numerical value in the structure
                    args[flag] = numerical_value

    # Return the structure containing numerical values for each flag
    return args


class dot_dict:
    def __init__(self, data):
        self.data = data

    def __getattr__(self, attr):
        if attr in self.data:
            return self.data[attr]
        else:
            raise AttributeError(f"Object has no attribute '{attr}'")


def print_array(arr, typ, name, str):
    count = 0
    output_string = typ
    output_string += " __attribute__((aligned(sizeof(int32_t)), \
                       section(\".l2\"))) "
    output_string += name + '[{}] = {{\n'.format(arr.size)
    for value in arr:
        output_string += '(int16_t) 0X{:04X}, '.format(value & 0xffff)
        count += 1
        if count % 8 == 0:
            output_string += '\n'
    output_string = output_string[:-3]
    output_string += "};\n"
    return output_string


def print_file(string, filename):
    with open(filename, "w") as file:
        # Write the string to the file
        file.write(string + '\n')
    return file


if __name__ == '__main__':

    parser = argparse.ArgumentParser(
        description='Generate data.h header files.')
    parser.add_argument('--params', type=str, help='Name of the app')
    # Parse the command-line arguments
    args = parser.parse_args()
    params = args.params
    # Read arguments from data.args file
    data_args = extract_data_args(params)
    (app_path, _) = os.path.split(params)
    (_, app_name) = os.path.split(app_path)

    if data_args != {}:
        string = "// Copyright 2022 ETH Zurich and University of \
                 Bologna.\n // Licensed under the Apache License, \
                 Version 2.0, see LICENSE for details.\n \
                 // SPDX-License-Identifier: Apache-2.0\n\n \
                 // File generated with .data/print_header.py\n"

        data_args = dot_dict(data_args)  # Access args with .notation

        if app_name == "cfft_radix4_q16":
            # cfft_radix4_q16
            src_cfft_q16, dst_cfft_q16, tolerance_q16 = cfft.generate_cfft_q16(
                data_args.LEN)
            brv_cfft_q16 = cfft.generate_bitreversal(data_args.LEN, 2)
            twi_cfft_q16 = cfft.generate_twiddleCoefq15(data_args.LEN)
            string += "#define LOG2 ({})\n".format(
                int(math.log2(data_args.LEN)))
            string += "#define N_CSAMPLES ({})\n".format(data_args.LEN)
            string += "#define N_TWIDDLES ({})\n".format(3 *
                                                         data_args.LEN // 4)
            string += "#define BITREVINDEXTABLE_LENGTH ({})\n".format(
                len(brv_cfft_q16))
            string += "#define TOLERANCE ({})\n".format(tolerance_q16)
            string += "#define N_BANKS (NUM_CORES * BANKING_FACTOR)\n"
            string += "#define MAX_COL (N_BANKS / (N_CSAMPLES / 4))\n"
            string += print_array(src_cfft_q16, "int16_t", "l2_pSrc", string)
            string += print_array(dst_cfft_q16, "int16_t", "l2_pRes", string)
            string += print_array(twi_cfft_q16, "int16_t",
                                  "l2_twiddleCoef_q16", string)
            string += print_array(brv_cfft_q16, "int16_t",
                                  "l2_BitRevIndexTable", string)
            filename = app_path + "/data_cfft_radix4_q16.h"

        elif app_name == "cfft_radix2_q16":
            # cfft_radix2_q16
            src_cfft_q16, dst_cfft_q16, tolerance_q16 = cfft.generate_cfft_q16(
                data_args.LEN)
            brv_cfft_q16 = cfft.generate_bitreversal(data_args.LEN, 2)
            twi_cfft_q16 = cfft.generate_twiddleCoefq15(data_args.LEN)
            string += "#define LOG2 ({})\n".format(
                int(math.log2(data_args.LEN)))
            string += "#define N_CSAMPLES ({})\n".format(data_args.LEN)
            string += "#define N_TWIDDLES ({})\n".format(3 *
                                                         data_args.LEN // 4)
            string += "#define BITREVINDEXTABLE_LENGTH ({})\n".format(
                len(brv_cfft_q16))
            string += "#define TOLERANCE ({})\n".format(tolerance_q16)
            string += "#define N_BANKS (NUM_CORES * BANKING_FACTOR)\n"
            string += print_array(src_cfft_q16, "int16_t", "l2_pSrc", string)
            string += print_array(dst_cfft_q16, "int16_t", "l2_pRes", string)
            string += print_array(twi_cfft_q16, "int16_t",
                                  "l2_twiddleCoef_q16", string)
            string += print_array(brv_cfft_q16, "int16_t",
                                  "l2_BitRevIndexTable", string)
            filename = app_path + "/data_cfft_radix2_q16.h"

        elif app_name == "chest_q16":
            src1_chest_q16, src2_chest_q16, dst_chest_q16 = \
                chest.generate_chest_q16(data_args.N_TX, data_args.N_RX,
                                         data_args.N_SAMPLES)
            string += "#define N_TX ({})\n".format(data_args.N_TX)
            string += "#define N_RX ({})\n".format(data_args.N_RX)
            string += "#define N_SAMPLES ({})\n".format(data_args.N_SAMPLES)
            string += print_array(src1_chest_q16,
                                  "int16_t", "l2_PilotTX", string)
            string += print_array(src2_chest_q16,
                                  "int16_t", "l2_PilotRX", string)
            string += print_array(dst_chest_q16, "int16_t", "l2_HEST", string)
            filename = app_path + "/data_chest_q16.h"

        else:
            raise Exception("ERROR: no app with such name!!!")

        print_file(string, filename)
