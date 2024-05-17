#!/usr/bin/env python3

# Copyright 2023 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Samuel Riedel, ETH Zurich

import argparse
import re
import pandas as pd
from collections import deque

def get_time(s):
    time = re.search(r'(\d+)\sns', s)[1]
    return int(time)

def filter_dma(dma_events):
    df = pd.DataFrame(columns=['start', 'end'])
    active = False
    start = 0
    for e in dma_events:
        # Check if we just launched the DMA
        if not active and 'Launch' in e:
            active = True
            start = get_time(e)
        # Check if we finished a DMA transfer
        elif active and 'Complete' in e:
            active = False
            row = pd.DataFrame({'start': [start], 'end': [get_time(e)]})
            df = pd.concat([df, row], ignore_index=True)
    return df.convert_dtypes()

def filter_core(core_events):
    df = pd.DataFrame(columns=['start', 'first_end', 'end'])
    start = deque()
    first_end = deque()
    end = deque()
    valid = [0, 0, 0]
    first_iteration_first_end = True
    first_iteration_end = True
    for e in core_events:
        # Check if we just launched the DMA and skip the first two 'ends'
        if first_iteration_first_end:
            if '0x00000001' in e:
                first_iteration_first_end = False
                continue
        if first_iteration_end:
            if '0x00000002' in e:
                first_iteration_end = False
                continue
        if '0x00000000' in e:
            start.append(get_time(e))
            valid[0] += 1
        elif '0x00000001' in e:
            first_end.append(get_time(e))
            valid[1] += 1
        elif '0x00000002' in e:
            end.append(get_time(e))
            valid[2] += 1
        else:
            pass
            print("Unexpected [DUMP] line {}".format(e))
        if all(valid):
            row = pd.DataFrame({'start': [start.popleft()], 'first_end': [first_end.popleft()], 'end': [end.popleft()]})
            df = pd.concat([df, row], ignore_index=True)
            valid = [x - 1 for x in valid ]
    return df.convert_dtypes()

def parse_file(filename):
    with open(filename, mode="r") as f:
        transcript = f.read()
    dma = re.findall(r'^\[DMA\].*', transcript, re.MULTILINE)
    cores = re.findall(r'^\[DUMP\].*', transcript, re.MULTILINE)
    dma_df = filter_dma(dma)
    core_df = filter_core(cores)
    min_value = min(dma_df.min().min(), core_df.min().min())
    dma_df = dma_df - min_value
    core_df = core_df - min_value
    # Compute Duration
    duration_dma = dma_df['end'] - dma_df['start']
    duration_core = core_df['end'] - core_df['start']
    # Get first start of double buffered region
    start = min(dma_df['start'][2], core_df['start'][1])
    end = max(dma_df['end'][3], core_df['end'][2])
    duration = end - start
    return duration
    # with pd.option_context('display.max_rows', None, 'display.max_columns', None):
    #     print(dma_df['start'])
    #     print(core_df)


def parse_value(s, keyword):
    r = fr'{keyword}=([^-]+)'
    res = re.search(r, s)
    return res[1]

def parse_filename(name):
    res = {}
    res['app'] = parse_value(name, 'app')
    res['axi_data_width'] = parse_value(name, 'axi_data_width')
    res['l2_banks'] = parse_value(name, 'l2_banks')
    return res

if __name__ == '__main__':
    # Argument parsing
    parser = argparse.ArgumentParser(
        description='Parse the data to create a csv which can be plotted', allow_abbrev=True)
    parser.add_argument(
        'input',
        metavar='<transcript>',
        nargs='+',
        help='Results to parse')
    parser.add_argument(
        '-o',
        '--output',
        metavar='<path/to/outputfile.csv>',
        nargs=1,
        default='None',
        help='Output filename')
    args = parser.parse_args()
    # Parse input files
    input = args.input
    print(input)
    output = args.output[0]
    print(output)
    # Parse data
    print('app, axi_data_width, l2_banks, bandwidth, duration')
    for i in input:
        p = parse_filename(i)
        # print(p)
        r = parse_file(i)
        # print(r)
        print(f'{p["app"]}, {p["axi_data_width"]}, {p["l2_banks"]}, {int(p["axi_data_width"]) * int(p["l2_banks"])}, {r}')
