import csv
import os
import pandas as pd
import numpy as np
from collections import deque, defaultdict
import sys

path = '/scratch2/mempool/hardware/build/traces'
ext = ('.csv')
padding = ' ' + '.' * 25

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
        print(files)
        csvread = pd.read_csv(files)
        print('\n\n')
        #print(csvread)
        print("******************************")
        print("**    AVERAGE PERFORMANCES  **")
        print("******************************")

        print("")
        for key in keys:
            column = csvread[key].replace(np.nan,0)
            column = column.to_numpy()
            avg = np.average(column)
            #print('{:.40s} {}'.format(key + padding, avg))
            print("%-30s %4.4f" % (key,  avg))
        print('\n\n')





