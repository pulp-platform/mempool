#!/usr/bin/env python3

# Copyright 2021 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# This script takes a csv describing the systolic mapping (cores and
# memory banks) and imports it in Python for further processing such
# as graph analysis and plotting

# Author: Sergio Mazzola <smazzola@iis.ee.ethz.ch>

from math import sqrt
import pandas as pd
import networkx as nx
import numpy
from matplotlib import pyplot as plt
import re
import os

# ----------------- Architecture info -----------------

NUM_CORES = int(os.environ.get('num_cores', 256))
NUM_CORES_PER_TILE = int(os.environ.get('num_cores_per_tile', 4))
BANKING_FACTOR = int(os.environ.get('banking_factor', 4))
NUM_TILES = NUM_CORES / NUM_CORES_PER_TILE
NUM_GROUPS = int(os.environ.get('num_groups', 4))
SEQ_MEM_SIZE_TILE = NUM_CORES_PER_TILE * int(os.environ.get('seq_mem_size', 2048))
BANK_SIZE = 1024
NUM_BANKS_PER_TILE = BANKING_FACTOR * NUM_CORES_PER_TILE
TCDM_SIZE = NUM_BANKS_PER_TILE * BANK_SIZE * NUM_TILES
ADDR_BYTE_OFFSET = 2

# ----------------- Parameters -----------------

INPUT_CSV = '../build/queues.csv'
OUTPUT_FIG = '../build/queues.png'

# -------------------- Main --------------------

# read in csv
df = pd.read_csv(INPUT_CSV)
df.set_index(['xqueue', 'core_id'], inplace=True)

# find cores popping from the same queue
#df.duplicated(['tile_id', 'bank_pop']).sum()
# locate incriminated PE
#df.loc[("queues_x_0", 5)]['address']

# filter
#df_filt = df[0:256]
df_filt = df

# create graph
G = nx.DiGraph()
for i in df_filt.index:
    # extract nodes
    xqueue = i[0]
    core = i[1]
    queue_tile_pop = df_filt.loc[i].queue_tile_pop
    queue_bank_pop = df_filt.loc[i].queue_bank_pop
    queue_tile_push = df_filt.loc[i].queue_tile_push
    queue_bank_push = df_filt.loc[i].queue_bank_push
    # define labels
    core_label = 'c_{}'.format(str(core))
    if not (numpy.isnan(queue_tile_pop) or numpy.isnan(queue_bank_pop)):
        bank_pop_label = 'b_{}_{}'.format(int(queue_tile_pop), int(queue_bank_pop))
        if xqueue == 'queues_x_0':
            G.add_edges_from([(bank_pop_label, core_label)], color='black')
        elif xqueue == 'queues_x_1':
            G.add_edges_from([(bank_pop_label, core_label)], color='gray')
    if not (numpy.isnan(queue_tile_push) or numpy.isnan(queue_bank_push)):
        bank_push_label = 'b_{}_{}'.format(int(queue_tile_push), int(queue_bank_push))
        if xqueue == 'queues_x_0':
            G.add_edges_from([(core_label, bank_push_label)], color='black')
        elif xqueue == 'queues_x_1':
            G.add_edges_from([(core_label, bank_push_label)], color='gray')

# analyze
nx.is_directed_acyclic_graph(G)
nx.is_directed(G)

# set node attributes
node_color = []
node_size = []
node_xy = {}
for node in G:
    if re.match(r'^c_[0-9]*$', node):
        node_color.append('#9c3a34')
        node_size.append(2000)
        if node not in node_xy:
            [core_id] = re.findall(r'^c_([0-9]*)$', node)
            core_id = int(core_id)
            x = core_id % int(sqrt(NUM_CORES))
            y = int(sqrt(NUM_CORES)) - int(core_id/int(sqrt(NUM_CORES)))
            node_xy[node] = (x, y)
    elif re.match(r'^b_[0-9]*_[0-9]*$', node):
        node_color.append('#3767a8')
        node_size.append(1800)
        if node not in node_xy:
            [fields] = re.findall(r'^b_([0-9]*)_([0-9]*)$', node)
            tile_id = int(fields[0])
            bank_id = int(fields[1])
            x = int(bank_id/4) + 4*(tile_id % 4) - 0.5
            y = int(NUM_TILES/4) - int(tile_id/4) - (bank_id % 4)/2 + 0.75
            node_xy[node] = (x, y)

# set edge attributes
edges = G.edges()
colors = [G[u][v]['color'] for u,v in edges]

#node_xy = nx.random_layout(G)
#node_xy = nx.circular_layout(G)
#node_xy = nx.spectral_layout(G)
#node_xy = nx.spring_layout(G)

plt.figure(figsize=(40,40))
nx.draw(
    G,
    pos=node_xy,
    node_color=node_color,
    node_size=node_size,
    node_shape='s',
    linewidths=0.5,
    edge_color=colors,
    width=1,
    arrowsize=25,
    edgecolors='black',
    with_labels=True,
    font_color='white',
    font_size=9,
    arrows=True
)

# plot
#plt.show()

plt.rcParams['figure.dpi'] = 150
plt.savefig(OUTPUT_FIG, format='png')
plt.clf()
