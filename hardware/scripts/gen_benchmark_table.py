#!/usr/bin/env python3

import os
import argparse
import pathlib

import pandas as pd
import numpy as np
import re

def create_dataframe(directory: str):
    keys = [    'cycles',
                'snitch_loads',
                'snitch_stores',
                'snitch_avg_load_latency',
                'snitch_occupancy',
                'total_ipc',
                'snitch_issues   ',
                'stall_tot',
                'stall_ins',
                'stall_raw',
                'stall_raw_lsu',
                'stall_raw_acc',
                'stall_lsu',
                'stall_acc',
                'stall_wfi',
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
                'itl_stores_global' ]
    os.chdir(directory)
    path = os.getcwd()
    df = pd.DataFrame(index=keys)
    for subdir in os.listdir(path):
        filename = os.path.join(subdir, 'avg.txt')
        filetext =  open(filename).read()
        values = []
        for key in keys:
            values.append(re.findall(r'%s\s*[+-]?([0-9]*[.]?[0-9]+)' %(key), filetext))
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
