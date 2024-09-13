#!/usr/bin/env python3

# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# This script generates an xls table with benchmarking results.
# Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

import os
import argparse
import pathlib

import pandas as pd
import numpy as np
import re

            'snitch_loads',
            'snitch_stores',
            'snitch_avg_load_latency',
            'snitch_occupancy',
            'total_ipc',
            'snitch_issues',
            'max_snitch_issues',
            'min_snitch_issues',
            'std_snitch_issues',
            'stall_tot',
            'max_stall_tot',
            'min_stall_tot',
            'std_stall_tot',
            'stall_ins',
            'max_stall_ins',
            'min_stall_ins',
            'std_stall_ins',
            'stall_raw',
            'max_stall_raw',
            'min_stall_raw',
            'std_stall_raw',
            'stall_raw_lsu',
            'stall_raw_acc',
            'stall_lsu',
            'max_stall_lsu',
            'min_stall_lsu',
            'std_stall_lsu',
            'stall_acc',
            'max_stall_acc',
            'min_stall_acc',
            'std_stall_acc',
            'stall_wfi',
            'max_stall_wfi',
            'min_stall_wfi',
            'std_stall_wfi',
            'seq_loads_local',
            'seq_loads_global',
            'itl_loads_local',
            'itl_loads_global',
            'seq_latency_local',
            'seq_latency_global',
            'itl_latency_local',
            'itl_latency_global',
            'seq_stores_local',
            'seq_stores_global',
            'itl_stores_local',
            'itl_stores_global']
    os.chdir(directory)
    path = os.getcwd()
    df = pd.DataFrame(index=keys)
    for subdir in os.listdir(path):
        filename = os.path.join(subdir, 'max.txt')
        filetext = open(filename).read()
        values = []
        for key in keys:
            values.append(re.findall(r'\b%s\b\s*[+-]?([0-9]*[.]?[0-9]+)' %(key), filetext))
        df[subdir] = (np.asarray(values)).flatten()
    return df

def main ():
    script_path = pathlib.Path(__file__).parent.absolute()
    # Parse arguments
    parser = argparse.ArgumentParser(description='Extract performance data from log files')
    parser.add_argument(
        "-i",
        "--input",
        type=pathlib.Path,
        default=script_path / "../results",
        required=False,
        help='Path to log files'
    )
    parser.add_argument(
        "-o",
        "--output",
        type=pathlib.Path,
        default=script_path,
        required=False,
        help='Path to output file'
    )
    parser.add_argument(
        "-v",
        "--verbose",
        action='store_true',
        help='Set verbose'
    )
    args = parser.parse_args()
    df = create_dataframe(args.input)
    df.to_excel(os.path.join(args.output, 'table.xls'))

if __name__ == "__main__":
    main()
