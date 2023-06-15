#!/usr/bin/env python3

# Copyright 2023 ETH Zurich and University of Bologna.
#
# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Author: Sergio Mazzola, ETH Zurich

import argparse
import matplotlib.pyplot as plt
import matplotlib.patches as patches
import re
import random

# arguments
parser = argparse.ArgumentParser(description='Graphical aid for systolic processing elements (PEs) mapping over MemPool\'s manycore hierarchical architecture.')
parser.add_argument('--num_cores', type=int, default=256, help='number of cores in the manycore architecture')
parser.add_argument('--num_cores_tile', type=int, default=4, help='number of cores in a tile')
parser.add_argument('--num_tiles_group', type=int, default=16, help='number of tiles in a group')
parser.add_argument('--grid', type=str, help='dimensions of the 2D systolic grid, e.g., \'16x16\'')
parser.add_argument('--topology', type=str, help='systolic topology')

def int_cond(n) -> int:
    '''
    Conditionally convert to integer if there are no decimal digits
    '''
    if isinstance(n, int):
        return n
    elif n.is_integer():
        return int(n)
    else:
        raise TypeError('\'n\' is not an integer')

def mapping(core_id, num_cores_tile, num_tiles_group, systolic_size_y, systolic_size_x, topology='None'):
    '''
    Customize this function with the same mapping algorithm used in the systolic application.
    '''

    # MATMUL_SQUARE
    if topology == 'MATMUL_SQUARE':
        # architectural details
        if not (num_cores_tile**0.5).is_integer():
            raise ValueError('Only perfect square values supported for \'num_cores_tile\'')
        tile_id = core_id // num_cores_tile

        # systolic col id (x coordinate)
        col_s = tile_id % (systolic_size_x // num_cores_tile**0.5) # how many tiles sections per side
        col_s *= num_cores_tile**0.5 # jump to the correct 'x' based on the tile section width
        col_s += core_id % num_cores_tile**0.5 # inside this tile section, find the correct core 'x'
        # systolic row id (y coordinate)
        row_s = tile_id // (systolic_size_y // num_cores_tile**0.5)
        row_s *= num_cores_tile**0.5
        row_s += (core_id % num_cores_tile) // num_cores_tile**0.5

    # MATMUL_SQUARE_SQUARE
    elif topology == 'MATMUL_SQUARE_SQUARE':
        # architectural details
        if not (num_cores_tile**0.5).is_integer():
            raise ValueError('Only perfect square values supported for \'num_cores_tile\'')
        if not (num_tiles_group**0.5).is_integer():
            raise ValueError('Only perfect square values supported for \'num_tiles_group\'')
        tile_id = core_id // num_cores_tile
        group_id = tile_id // num_tiles_group

        # systolic col id (x coordinate)
        col_s = group_id % (systolic_size_x // (num_tiles_group**0.5 * num_cores_tile**0.5))
        col_s *= num_tiles_group**0.5 * num_cores_tile**0.5
        col_s += (tile_id % num_tiles_group**0.5) * num_cores_tile**0.5
        col_s += core_id % num_cores_tile**0.5
        # systolic row id (y coordinate)
        row_s = group_id // (systolic_size_y // (num_tiles_group**0.5 * num_cores_tile**0.5))
        row_s *= num_tiles_group**0.5 * num_cores_tile**0.5
        row_s += ((tile_id % num_tiles_group) // num_tiles_group**0.5) * num_cores_tile**0.5
        row_s += (core_id % num_cores_tile) // num_cores_tile**0.5

    # MATMUL_ROW_WISE
    elif topology == 'MATMUL_ROW_WISE':

        # systolic col id (x coordinate)
        col_s = core_id % systolic_size_x
        # systolic row id (y coordinate)
        row_s = core_id // systolic_size_x

    # Default
    else:
        raise ValueError(f'Topology \'{topology}\' not supported')
    return (int_cond(row_s), int_cond(col_s))

def colormap(i):
    '''
    Customize this function to change the colormap. The index i must be between 0 and 1 and
    picks a color from the colormap.
    '''
    cmap = plt.cm.get_cmap('Spectral')
    # remap to make random but always dependent on the tile
    i = i*215.2342/0.52 % 1
    return cmap(i)

# main
if __name__ == "__main__":
    args = parser.parse_args()

    # parse systolic grid
    systolic_size_y, systolic_size_x = re.findall(r'^(\d+)x(\d+)$', args.grid)[0]

    # plot the cores grid with systolic mapping
    fig, ax = plt.subplots()
    for core_id in range(args.num_cores):
        # tile id
        tile_id = core_id // args.num_cores_tile
        # find systolic mapping row/col id related to core and tile id
        (row_s, col_s) = mapping(core_id, args.num_cores_tile, args.num_tiles_group, int(systolic_size_y), int(systolic_size_x), args.topology)
        # plot systolic PEs in the correct position and grid
        ax.add_patch(patches.Rectangle((col_s, row_s), 1, 1, fill=True, color=colormap(tile_id/(args.num_cores/args.num_cores_tile)), alpha=0.5, linewidth=0))
        ax.add_patch(patches.Rectangle((col_s, row_s), 1, 1, fill=False, linewidth=0.3, edgecolor='black'))
        # annotate with core id, tile id, systolic row/col
        ax.text(col_s+0.5, row_s+0.31, str(core_id), horizontalalignment='center', verticalalignment='center')
        ax.text(col_s+0.5, row_s+0.56, str(tile_id), horizontalalignment='center', verticalalignment='center', fontsize=7, color='gray')
        ax.text(col_s+0.5, row_s+0.84 , f'({row_s},{col_s})', horizontalalignment='center', verticalalignment='center', fontsize=7, color='blue')
    # set limits, invert y axis, remove axis
    ax.autoscale(tight=True)
    ax.set_ylim(ax.get_ylim()[::-1])
    ax.get_xaxis().set_visible(False)
    ax.get_yaxis().set_visible(False)
    ax.set_aspect('equal')

    plt.show()
