#!/usr/bin/env python3

# Copyright 2021 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# Author: Sergio Mazzola <smazzola@iis.ee.ethz.ch>

import os
import re
import csv
import matplotlib.pyplot as plt
import numpy as np
import pandas as pd

# settings
RESULTS_DIR   = "./results/conv2d_qlr"
NUM_CORES     = 256

FILTER_RES    = r'^conv_qlr_.*$'
RESULTS_FILE  = "results.csv"
TRACEMAC_PERF = "tracemac_perf.csv"

# list result dirs and filter
dirs = os.listdir(RESULTS_DIR)
dirs = [d for d in dirs if re.match(FILTER_RES, d)]
dirs.sort()

# parse result dir name and report file
entries = []
for dir in dirs:
    entries.append({}) # init dict
    # parse result dir name
    benchmark, unrolling, rows, cols, reps, sys_len = re.match(r'^([a-zA-Z_]+){1}?(?:_(\d+))?_(\d+){1}_(\d+){1}_reps_(\d+)_len_(\d+)__.+$', dir).groups()
    entries[-1]['benchmark'] = benchmark
    entries[-1]['unrolling'] = int(unrolling) if unrolling else 1
    entries[-1]['rows'] = int(rows)
    entries[-1]['cols'] = int(cols)
    entries[-1]['reps'] = int(reps)
    entries[-1]['sys_len'] = int(sys_len)
    # parse performance report
    report_file = os.path.join(RESULTS_DIR, dir, RESULTS_FILE)
    with open(report_file, 'r') as f:
        df = pd.read_csv(f)
        entries[-1]['runtime'] = df['cycles'].mean()
        entries[-1]['avg_load_latency'] = df['snitch_avg_load_latency'].mean()
        entries[-1]['total_ipc'] = df['total_ipc'].mean()
        entries[-1]['num_loads'] = df['snitch_loads'].mean()
        entries[-1]['num_stores'] = df['snitch_stores'].mean()
    # parse tracemac report
    tracemac_file = os.path.join(RESULTS_DIR, dir, TRACEMAC_PERF)
    with open(tracemac_file, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            # num_rows / num_computing_cores (num_computing_cores = num_cores - num_mover_cores)
            #FIXME: row_chunks does not consider unrolling
            entries[-1]['row_chunks'] = int((int(rows) / (NUM_CORES - (NUM_CORES / int(sys_len)))) / entries[-1]['unrolling'])
            entries[-1]['peak_ops'] = float(row['real_peak_moving_avg_ops_cycle'])

filtered_entries = []

filtered_entries.extend([e for e in entries if (
    e['unrolling'] == 1 and
    e['row_chunks'] == 2 and
    e['reps'] == 2
)])

filtered_entries.extend([e for e in entries if (
    e['unrolling'] == 2 and
    e['row_chunks'] == 1 and
    e['reps'] == 2
)])

filtered_entries.extend([e for e in entries if (
    e['unrolling'] == 3 and
    e['row_chunks'] == 1 and
    e['reps'] == 2
)])

# create groups by colors
bars = []
for group in set([e['sys_len'] for e in filtered_entries]):
    bars.append({
        'x': [e['unrolling'] for e in filtered_entries if (e['sys_len'] == group)],
        'y': [e['peak_ops'] for e in filtered_entries if (e['sys_len'] == group)],
        'group': group
    })

# check all arrays are the same length of previous
for i in range(0, len(bars)):
    assert len(bars[i]['x']) == len(bars[i]['y'])
    if i > 0:
        assert len(bars[i]['x']) == len(bars[i-1]['x'])
        assert len(bars[i]['y']) == len(bars[i-1]['y'])
    index = np.arange(len(bars[i]['y']))

# create plot
fig, ax = plt.subplots()
bar_width = 0.35 - len(bars)/20
rects = []
# sort by values of the color variable
bars.sort(key=lambda x: x['group'])
# create bars
for bar in bars:
    rects.append(ax.bar(index, bar['y'], bar_width, label='{}: {}'.format('sys_len', bar['group'])))
    index = index + bar_width

# add labels
ax.set_xlabel('unrolling (output rows per PE)')
ax.set_ylabel('max peak MACs/cycle')
ax.set_title('conv_qlr max peak performance (optimal sizes)')
ax.set_xticks(index - float(bar_width * (len(bars)+1)) / 2)
ax.set_xticklabels(bars[0]['x'])
ax.legend()
# add values
for rect in rects:
    for r in rect:
        height = r.get_height()
        ax.annotate('{}'.format(height),
                    xy=(r.get_x() + r.get_width() / 2, height),
                    xytext=(0, 3),
                    textcoords="offset points",
                    ha='center', va='bottom')
        # annotate utilization higher
        ax.annotate('{}%'.format(int(height/256*100)),
                    xy=(r.get_x() + r.get_width() / 2, height + 4),
                    xytext=(0, 3),
                    textcoords="offset points",
                    ha='center', va='bottom')
fig.tight_layout()
plt.show()

exit()


# plotting
def plot_hist(
        entries: list,
        func_var_x: str,
        func_var_y: str,
        func_var_color: str,
        fix_var_0: dict = {'name': str, 'value': 0},
        fix_var_1: dict = {'name': str, 'value': 0},
        title: str = ''
):
    # filter entries based on fixed variables
    filtered_entries = [e for e in entries          if (e[fix_var_0['name']] == fix_var_0['value'])]
    filtered_entries = [e for e in filtered_entries if (e[fix_var_1['name']] == fix_var_1['value'])]

    # create groups by colors
    bars = []
    for group in set([e[func_var_color] for e in filtered_entries]):
        bars.append({
            'x': [e[func_var_x] for e in filtered_entries if (e[func_var_color] == group)],
            'y': [e[func_var_y] for e in filtered_entries if (e[func_var_color] == group)],
            'group': group
        })

    # check all arrays are the same length of previous
    for i in range(0, len(bars)):
        assert len(bars[i]['x']) == len(bars[i]['y'])
        if i > 0:
            assert len(bars[i]['x']) == len(bars[i-1]['x'])
            assert len(bars[i]['y']) == len(bars[i-1]['y'])
        index = np.arange(len(bars[i]['y']))

    # create plot
    fig, ax = plt.subplots()
    bar_width = 0.35 - len(bars)/20
    rects = []
    # sort by values of the color variable
    bars.sort(key=lambda x: x['group'])
    # create bars
    for bar in bars:
        rects.append(ax.bar(index, bar['y'], bar_width, label='{}: {}'.format(func_var_color, bar['group'])))
        index = index + bar_width

    # add labels
    ax.set_xlabel(func_var_x)
    ax.set_ylabel(func_var_y)
    ax.set_title('[{}] {}: {}, {}: {}'.format(title, fix_var_0['name'], fix_var_0['value'], fix_var_1['name'], fix_var_1['value']))
    ax.set_xticks(index - float(bar_width * (len(bars)+1)) / 2)
    ax.set_xticklabels(bars[0]['x'])
    ax.legend()
    # add values
    for rect in rects:
        for r in rect:
            height = r.get_height()
            ax.annotate('{}'.format(height),
                        xy=(r.get_x() + r.get_width() / 2, height),
                        xytext=(0, 3),
                        textcoords="offset points",
                        ha='center', va='bottom')
    fig.tight_layout()
    plt.show()

plot_hist(
    entries = entries,
    func_var_x = 'sys_len',
    func_var_y = 'peak_ops',
    func_var_color = 'row_chunks',
    fix_var_0 = {'name': 'unrolling', 'value': 1},
    fix_var_1 = {'name': 'reps', 'value': 2},
    title = 'conv_qlr'
)

plot_hist(
    entries = entries,
    func_var_x = 'sys_len',
    func_var_y = 'peak_ops',
    func_var_color = 'row_chunks',
    fix_var_0 = {'name': 'unrolling', 'value': 2},
    fix_var_1 = {'name': 'reps', 'value': 2},
    title = 'conv_qlr'
)

plot_hist(
    entries = entries,
    func_var_x = 'sys_len',
    func_var_y = 'peak_ops',
    func_var_color = 'row_chunks',
    fix_var_0 = {'name': 'unrolling', 'value': 3},
    fix_var_1 = {'name': 'reps', 'value': 2},
    title = 'conv_qlr'
)

plot_hist(
    entries = entries,
    func_var_x = 'unrolling',
    func_var_y = 'runtime',
    func_var_color = 'sys_len',
    fix_var_0 = {'name': 'row_chunks', 'value': 1},
    fix_var_1 = {'name': 'reps', 'value': 2},
    title = 'conv_qlr'
)


