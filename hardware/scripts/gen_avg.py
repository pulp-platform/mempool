

# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# This script takes a set of .csv files in one of the results folders and
# generates the average performances over all the cores used.
# Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>


import csv
import os
import pandas as pd
import numpy as np
from collections import deque, defaultdict
import sys

path = os.getcwd()
ext = ('.csv')
padding = ' ' + '.' * 25
NUM_CORES = int(os.environ.get('num_cores', 256))

keys = [ 'cycles',
         'snitch_loads',
         'snitch_stores',
         'snitch_avg_load_latency',
         'snitch_occupancy',
         'total_ipc',
         'snitch_issues',
         'stall_tot',
         'stall_ins',
         'stall_raw',
         'stall_raw_lsu',
         'stall_raw_acc',
         'stall_lsu',
         'stall_acc',
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

for files in os.listdir(path):
    if files.endswith(ext):
        csvread = pd.read_csv(files)
        n_sections = csvread.shape[0]/NUM_CORES

        print("\n")
        print("*******************************")
        print("**    AVERAGE PERFORMANCE    **")
        print("*******************************")

        print("")
        for section in range(int(n_sections)):
            print("Section %d:\n" % section)
            sectionread = csvread.loc[csvread['section'] == section]
            for key in keys:
                column = sectionread[key].replace(np.nan,0)
                column = column.to_numpy()
                avg = np.average(column)
                #print('{:.40s} {}'.format(key + padding, avg))
                print("%-30s %4.4f" % (key,  avg))
            print('\n')





