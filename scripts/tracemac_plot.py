#!/usr/bin/env python3

# Copyright 2021 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Processes the CSV created by tracemac_csv.py to generate a plot
#
# Author: Gua Hao Khov <khovg@student.ethz.ch>

import re
import os
import sys
import argparse
import numpy as np
import csv
import matplotlib.pyplot as plt

# regex matches to groups
# 0 -> core id
# 1 -> end cycle
END_REGEX = r'Trace End (\d+) (\d+)'

re_end = re.compile(END_REGEX)

def moving_average(values, width):
    return np.convolve(values, np.ones(width), 'same') / width

def parse_ends(line):
    global min_end
    match = re_end.match(line)
    if match:
        if (not (int(match.group(1)) % 16 == 0)):
            if (min_end > int(match.group(2))):
                min_end = int(match.group(2))
    return 0

parser = argparse.ArgumentParser('tracemac_plot', allow_abbrev=True)
parser.add_argument(
    'csv',
    metavar='<csv>',
    nargs='?',
    default='tracemac.csv',
    help='CSV from tracemac.py')
parser.add_argument(
    '--log',
    metavar='<log>',
    nargs='?',
    default='tracemac.txt',
    help='Log from tracemac_log.py')
parser.add_argument(
    '-o',
    '--output',
    metavar='<pdf>',
    nargs='?',
    default='tracemac.pdf',
    help='Output PDF file')
parser.add_argument(
    '-s',
    '--settle',
    action='store_true',
    help='Indicate settling via colored regions')
parser.add_argument(
    '-a',
    '--average',
    action='store_true',
    help='Indicate both overall and settled average')

args = parser.parse_args()

csvfile = args.csv
logfile = args.log
output = args.output
show_settling = args.settle
show_average = args.average

cycles = []
values = []

with open(csvfile, newline='') as csvfile:
    reader = csv.reader(csvfile, delimiter=' ')
    for row in reader:
        cycles.append(int(row[0]))
        values.append(float(row[1]))

cycles = np.array(cycles)
values = np.array(values)

if show_settling:
    min_end = cycles[-1]
    log = open(logfile)
    for lino, line in enumerate(log.readlines()):
        parse_ends(line)
    norm_min_end = min_end-cycles[0]

norm_cycles = cycles-cycles[0]

avg_values = moving_average(values, 100)

if show_settling:
    max_val = max(avg_values)
    for idx, val in enumerate(avg_values):
        if (val > 0.95 * max_val):
            settled_idx = idx
            settled_val = val
            break

fig, ax = plt.subplots()
ax.plot(norm_cycles, avg_values)

ax.set_xlim([norm_cycles[0], norm_cycles[-1]])

# ax.set_title('Performance')
ax.set_ylabel('Throughput [MACs/cycle]')
ax.set_xlabel('Cycles [.]')

ax_right = ax.twinx()
y_min, y_max = ax.get_ylim()
ax_right.set_ylim(y_min/256*100, y_max/256*100)
ax_right.set_ylabel('Utilization [%]')

if show_settling:
    ax.axvspan(0, norm_cycles[settled_idx], alpha=0.5, color='tab:red', label='settling')
    ax.axvspan(norm_cycles[settled_idx], norm_min_end, alpha=0.5, color='tab:green', label='settled')
    ax.axvspan(norm_min_end, norm_cycles[-1], alpha=0.5, color='tab:gray', label='trailing')
    ax.legend(framealpha=1, edgecolor='black')

if show_average:
    average = np.mean(values)
    ax.axhline(average, color='black', ls=':', lw=1, label='average')
    print(f'avg: {average}')
    if show_settling:
        peak = np.mean(values[norm_cycles[settled_idx]:norm_min_end])
        ax.axhline(peak, color='black', ls='--', lw=1, label='peak')
        print(f'peak: {peak}')
    ax.legend(framealpha=1, edgecolor='black')

ax.plot(norm_cycles, avg_values, color='tab:blue')

if show_settling:
    print(f'set: {norm_cycles[settled_idx]}')
    print(f'trail: {norm_min_end}')

print(f'end: {norm_cycles[-1]}')

fig.savefig(output)