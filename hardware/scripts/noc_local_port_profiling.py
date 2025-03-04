#!/usr/bin/env python3
# Copyright 2024 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import re


def parse_file(file_path):
    req_read_sum = 0
    req_write_sum = 0
    resp_in_sum = 0

    # Read the file and parse lines
    with open(file_path, "r") as file:
        for line in file:
            # Match patterns for required fields
            match = re.search(r"'req_read_in_num':\s*(\d+)", line)
            if match:
                req_read_sum += int(match.group(1))
            match = re.search(r"'req_write_in_num':\s*(\d+)", line)
            if match:
                req_write_sum += int(match.group(1))
            match = re.search(r"'resp_in_num':\s*(\d+)", line)
            if match:
                resp_in_sum += int(match.group(1))

    return req_read_sum, req_write_sum, resp_in_sum


def main():
    # Argument parser for command-line file input
    parser = argparse.ArgumentParser(
        description="Calculate the sums of fields from a log file."
    )
    parser.add_argument(
        "-f",
        "--file",
        default="spm_profiling/run_logs_remap_f_1024/tests/router_local_input_profile_q_00018000.log",
        help="Path to the input log file.",
    )
    args = parser.parse_args()

    # Summing up the values
    req_read_sum, req_write_sum, resp_in_sum = parse_file(args.file)

    # Calculate the total
    total = req_read_sum + req_write_sum

    # Calculate the ratios
    if total > 0:
        req_read_ratio = req_read_sum / total
        req_write_ratio = req_write_sum / total
    else:
        req_read_ratio = req_write_ratio = 0.0

    # Print the results
    print(
        f"Sum of req_read_in_num: {req_read_sum}. Ratio of req_read_in_num: {req_read_ratio:.2f}%"
    )
    print(
        f"Sum of req_write_in_num: {req_write_sum}. Ratio of req_write_in_num: {req_write_ratio:.2f}%"
    )
    print(f"Sum of resp_in_num: {resp_in_sum}")


if __name__ == "__main__":
    main()
