#!/usr/bin/env python3

# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Processes the log created by tracemac_log.py to generate an accumulated CSV
#
# Author: Gua Hao Khov <khovg@student.ethz.ch>

import re
import os
import sys
import argparse
import numpy as np
import csv

# regex matches to groups
# 0 -> core id
# 1 -> start cycle
START_REGEX = r'Trace Start (\d+) (\d+)'

# regex matches to groups
# 0 -> core id
# 1 -> end cycle
END_REGEX = r'Trace End (\d+) (\d+)'

# regex matches to groups
# 0 -> MAC flag
# 1 -> instruction
VALUE_REGEX = r'(\d+) #(\w+)'

re_start = re.compile(START_REGEX)
re_end = re.compile(END_REGEX)
re_value = re.compile(VALUE_REGEX)

starts = []
ends = []
values = []

start_limit = 0
end_limit = 0


def parse_values(line):
    global curr_id, curr_pos
    # print(line)
    match = re_start.match(line)
    # print(match)
    if match:
        curr_id = int(match.group(1))
        curr_pos = int(match.group(2))-start_limit
        return 0
    # print(line)
    match = re_value.match(line)
    # print(match)
    if match:
        if int(match.group(1)):
            values[curr_pos] += 1
        if curr_pos < end_limit:
            curr_pos += 1
            return 0
        else:
            return 1

def parse_limits(line):
    global curr_id
    # print(line)
    match = re_start.match(line)
    # print(match)
    if match:
        starts.append(int(match.group(2)))
        curr_id = int(match.group(1))
        return 0
    # print(line)
    match = re_end.match(line)
    # print(match)
    if match:
        ends.append(int(match.group(2)))
        if curr_id == int(match.group(1)):
            return 0
        else:
            return 1
    return 0


parser = argparse.ArgumentParser('tracemac_csv', allow_abbrev=True)
parser.add_argument(
    'log',
    metavar='<log>',
    nargs='?',
    default='tracemac.txt',
    help='Log from tracemac_log.py')
parser.add_argument(
    '-o',
    '--output',
    metavar='<csv>',
    nargs='?',
    default='tracemac.csv',
    help='Output CSV file')

args = parser.parse_args()

log = args.log
output = args.output

file = open(log)

for lino, line in enumerate(file.readlines()):
    if parse_limits(line):
        print('Missmatched trace end', file=sys.stderr)
file.seek(0)
start_limit = min(starts)
end_limit = max(ends)
values = np.zeros(end_limit - start_limit, dtype=int)
for lino, line in enumerate(file.readlines()):
    if parse_values(line):
        print('Value position exceeds upper axis limit', file=sys.stderr)
cycles = range(start_limit, end_limit)

with open(output, 'w', newline='') as csvfile:
    writer = csv.writer(csvfile, delimiter=' ')
    for row in range(len(values)):
        writer.writerow([cycles[row] , values[row]])
