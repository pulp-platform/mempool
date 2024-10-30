#!/usr/bin/env python3
# Copyright 2023 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import re
import pandas as pd
import matplotlib.pyplot as plt
import argparse
import os
import numpy as np
from matplotlib.cm import get_cmap
from matplotlib.colors import Normalize
from matplotlib.ticker import FuncFormatter


def parse_data(file_path, burst_size):
    """
    Parses the data file to extract details for each SPM word including
    initialization and last access cycles, aggregated by burst size.
    Parameters:
    file_path (str): The path to the data file.
    burst_size (int): The size of each burst in bytes for aggregating
    init and last access cycles.
    Returns:
    DataFrame: A pandas DataFrame containing aggregated details for each burst.
    """
    data = []
    pattern = re.compile(
        r"'GROUP':\s*(\d+), 'TILE':\s*(\d+), 'BANK':\s*(\d+), "
        r"'IDX':\s*(0x[0-9a-fA-F]+), 'inited':\s*1,"
        r"\s*'ini_cyc':\s*(\d+),.*'last_rd_cyc':\s*(\d+),"
        r".*'last_wr_cyc':\s*(\d+),.*?'last_acc_cyc':\s*(\d+),"
        r".*?'acc_num':\s*(\d+), "
        r"'rd_cyc':\s*([\d\s]+), 'wr_cyc':\s*([\d\s]+)"
        # r"'rd_cyc':\s*\[(.*?)\], 'wr_cyc':\s*\[(.*?)\]"
    )
    burst_data = {}

    with open(file_path, 'r') as file:
        for line in file:
            match = pattern.search(line)
            if match:
                group = int(match.group(1))
                tile = int(match.group(2))
                bank = int(match.group(3))
                idx = int(match.group(4), 16)
                ini_cyc = int(match.group(5))
                last_rd_cyc = int(match.group(6))
                last_wr_cyc = int(match.group(7))
                last_acc_cyc = int(match.group(8))
                # acc_num = int(match.group(9))
                rd_cycles = list(map(int, match.group(10).strip().split()))
                wr_cycles = list(map(int, match.group(11).strip().split()))

                memory_address = (idx << 10) | \
                                 (group << 8) | \
                                 (tile << 4) | bank

                # memory_address = (idx << 12) | \
                #                  (group << 10) | \
                #                  (tile << 6) | \
                #                  (bank << 2)

                # if (memory_address << 2) >= 0x40000:
                if (memory_address << 2) >= 0x0:
                    # Calculate burst address
                    burst_address = memory_address // burst_size

                    if burst_address not in burst_data:
                        burst_data[burst_address] = {
                            'init': ini_cyc,
                            'last_rd': last_rd_cyc,
                            'last_wr': last_wr_cyc,
                            'last': last_acc_cyc,
                            # each word is 32bit width
                            'mem_addr': (burst_address * burst_size) << 2,
                            'rd_cycles': rd_cycles, 'wr_cycles': wr_cycles
                        }
                    else:
                        burst_entry = burst_data[burst_address]
                        burst_entry['init'] = min(burst_entry['init'], ini_cyc)
                        burst_entry['last_rd'] = max(burst_entry['last_rd'],
                                                     last_rd_cyc)
                        burst_entry['last_wr'] = max(burst_entry['last_wr'],
                                                     last_wr_cyc)
                        burst_entry['last'] = max(burst_entry['last'],
                                                  last_acc_cyc)
                        burst_entry['rd_cycles'].extend(rd_cycles)
                        burst_entry['wr_cycles'].extend(wr_cycles)

    # Convert burst data to DataFrame
    for key, value in burst_data.items():
        data.append((value['mem_addr'],
                     value['init'],
                     value['last'],
                     value['last_rd'],
                     value['last_wr'],
                     value['rd_cycles'],
                     value['wr_cycles']))

    return pd.DataFrame(data, columns=['Memory Address',
                                       'Init Cycle',
                                       'Last Access Cycle',
                                       'Last Read Cycle',
                                       'Last Write Cycle',
                                       'Read Cycles',
                                       'Write Cycles'])


def hex_format(x, pos):
    """
    The two args are the value and tick position.
    Format the number as hex with '0x' prefix.
    """
    return f'0x{int(x):X}'


def round_up_to_msb(num):
    # Convert number to string to easily access digits
    num_str = str(int(num))
    # Get the most significant digit (as integer)
    msd = int(num_str[0])
    # Determine the number of digits
    length = len(num_str)
    # Calculate the rounded up number
    rounded_num = (msd + 1) * (10 ** (length - 1))
    return rounded_num


def calc_completion_percentages(cycles, last_cycles):
    """
    Calculate the percentage of bursts that have completed
    by each cycle in cycles list,
    considering only bursts with 'last_acc_cyc' greater
    than 2000.
    """
    filtered_cycles = last_cycles[last_cycles > 2000]
    percentages = []
    filtered_cycles_sorted = np.sort(filtered_cycles)
    total_bursts = len(filtered_cycles)

    for cycle in cycles:
        completed = np.searchsorted(filtered_cycles_sorted,
                                    cycle, side='right')
        percentages.append(
            (completed / total_bursts) * 100 if total_bursts > 0 else 0)
    return percentages


def custom_xaxis_format(cycles, percentages, tick_spacing):
    """
    Custom formatter to show both cycle number
    and completion percentage on x-axis ticks.
    """
    def format_func(value, tick_number):
        idx = np.clip(int(value // tick_spacing), 0, len(cycles) - 1)
        return f"{int(cycles[idx])}\n({percentages[idx]:.1f}%)"
    return format_func


def plot_lifetime(df, output_file, file_title, burst_size):
    plt.figure(figsize=(20, 12))
    cmap = get_cmap('viridis')
    # cmap = get_cmap('jet')
    norm = Normalize(vmin=df['Init Cycle'].min(),
                     vmax=df['Last Access Cycle'].max())

    legend_added = {'write': False,
                    'next_read': False,
                    'last_read': False}  # To control legend entries

    # Calculate completion percentages for x-axis ticks
    # Defines the spacing between ticks
    tick_spacing_x = round_up_to_msb(df['Last Access Cycle'].max()) / 10
    tick_vals_x = np.arange(
        start=min(0, ((df['Init Cycle'].min() // tick_spacing_x) *
                      tick_spacing_x)),
        stop=(df['Last Access Cycle'].max() // tick_spacing_x + 2) *
        tick_spacing_x,
        step=tick_spacing_x)
    x_ticks = tick_vals_x
    percentages = calc_completion_percentages(
        x_ticks,
        df['Last Access Cycle'].values)

    # print(f"x_ticks: {x_ticks}:{percentages}")

    # Markers for the legend
    markers = {
        # Solid line with round points for read completion
        'next_read': {'line': '-', 'marker': '^',
                      'label': 'Last Access is Read'},
        # Solid line with round points for read completion
        'last_read': {'line': '-', 'marker': 'o',
                      'label': 'Last Access is Read'},
        # Dotted line with 'x' points for write completion
        'write': {'line': '--', 'marker': 'x',
                  'label': 'Last Access is Write'}
    }

    for _, row in df.iterrows():
        wr_cycles = row['Write Cycles']
        rd_cycles = row['Read Cycles']
        wr_cycles.sort()
        rd_cycles.sort()
        for i, wr_cyc in enumerate(wr_cycles):
            # Find the next and last read cycle that is after this write cycle
            # and before the next write cycle (if there is a next write cycle)
            next_wr_cyc = wr_cycles[i+1] if i+1 < len(wr_cycles) \
                                         else float('inf')
            next_rd_cyc = min([rd for rd in rd_cycles
                               if wr_cyc < rd < next_wr_cyc], default=wr_cyc)
            last_rd_cyc = max([rd for rd in rd_cycles
                               if wr_cyc < rd < next_wr_cyc], default=wr_cyc)

            color_line = cmap(norm((wr_cyc + last_rd_cyc * 3) / 4))
            color_init = color_line  # cmap(norm(row['Init Cycle']))
            color_final = cmap(norm(last_rd_cyc))

            if next_rd_cyc < last_rd_cyc:
                plt.plot([wr_cyc, next_rd_cyc],
                         [row['Memory Address'], row['Memory Address']],
                         linestyle=markers['write']['line'],
                         linewidth=1,
                         color=color_line,
                         alpha=0.7)
            plt.plot([next_rd_cyc, last_rd_cyc],
                     [row['Memory Address'], row['Memory Address']],
                     linestyle=markers['last_read']['line'],
                     linewidth=1,
                     color=color_line,
                     alpha=0.7)

            plt.plot(wr_cyc,
                     row['Memory Address'],
                     markers['write']['marker'],
                     markersize=6,
                     color=color_init,
                     markeredgecolor=color_init,
                     markeredgewidth=1,
                     label='Write Point' if not legend_added['write'] else "")
            # Update the legend entry management
            if not legend_added['write']:
                legend_added['write'] = True

            if next_rd_cyc > wr_cyc and next_rd_cyc < last_rd_cyc:
                plt.plot(next_rd_cyc,
                         row['Memory Address'],
                         markers['next_read']['marker'],
                         markersize=6,
                         color=color_final,
                         markeredgecolor='grey',
                         markeredgewidth=0.2,
                         label='Next Read Point'
                         if not legend_added['next_read'] else "")
                # Update the legend entry management
                if not legend_added['next_read']:
                    legend_added['next_read'] = True
            if last_rd_cyc > wr_cyc:
                plt.plot(last_rd_cyc,
                         row['Memory Address'],
                         markers['last_read']['marker'],
                         markersize=6,
                         color=color_final,
                         markeredgecolor='grey',
                         markeredgewidth=0.2,
                         label='Last Read Point'
                         if not legend_added['last_read'] else "")
                # Update the legend entry management
                if not legend_added['last_read']:
                    legend_added['last_read'] = True

    # ax = plt.gca()
    # # ax.set_ylim([df['Memory Address'].min() \
    # # - burst_size, df['Memory Address'].max() + burst_size * 2])

    # # Set custom y-axis tick locations and format them as hexadecimal
    # Defines the spacing between ticks
    # tick_spacing = burst_size * burst_size
    # tick_vals = np.arange(
    #  start=(df['Memory Address'].min() // tick_spacing) * tick_spacing,
    #  stop=(df['Memory Address'].max() // tick_spacing + 2) * tick_spacing,
    #  step=tick_spacing)
    # ax.set_yticks(tick_vals)
    # ax.yaxis.set_major_formatter(FuncFormatter(hex_format))

    ax = plt.gca()
    # ax.set_ylim([df['Memory Address'].min() \
    #              - burst_size, df['Memory Address'].max() + burst_size])
    ax.set_xlim([
        min(0, ((df['Init Cycle'].min() // tick_spacing_x) * tick_spacing_x)),
        (df['Last Access Cycle'].max() // tick_spacing_x + 2)
        ])

    # tick_spacing_x = 5000  # Defines the spacing between ticks
    ax.set_xticks(tick_vals_x)
    # ax.xaxis.set_major_locator(MaxNLocator(integer=True))
    ax.xaxis.set_major_formatter(
        FuncFormatter(
            custom_xaxis_format(x_ticks, percentages, tick_spacing_x)))

    # Set custom y-axis tick locations and format them as hexadecimal
    tick_spacing = 0x10000  # Defines the spacing between ticks
    tick_vals = np.arange(
        start=(df['Memory Address'].min() // tick_spacing) * tick_spacing,
        stop=(df['Memory Address'].max() // tick_spacing + 2) * tick_spacing,
        step=tick_spacing)
    ax.set_yticks(tick_vals)
    ax.yaxis.set_major_formatter(FuncFormatter(hex_format))

    plt.colorbar(plt.cm.ScalarMappable(norm=norm, cmap=cmap),
                 ax=ax,
                 orientation='vertical',
                 label='Cycle Time')

    last_write_cyc = df['Last Write Cycle'].max()
    last_read_cyc = df['Last Read Cycle'].max()
    plt.title(f'Lifetime and Proportion of Each SPM Word in {file_title} \
                (Burst size: {burst_size} Bytes), \
                last write cyc: {last_write_cyc}, \
                last read cyc: {last_read_cyc}')
    plt.xlabel('Cycle Time (Finished access %, excluding the stack access)')
    plt.ylabel('Memory Address (Hex)')
    plt.grid(True)
    # plt.legend(handles=list(legend_handles.values()),
    #            title="Access Types",
    #            title_fontsize='13',
    #            fontsize='11',
    #            loc='upper right')
    plt.legend()
    # plt.show()
    # Save to PNG (High-resolution)
    output_png = f"{output_file}.png"
    plt.savefig(output_png, format='png', dpi=1000, bbox_inches='tight')
    # Save to PDF (Vector)
    output_pdf = f"{output_file}.pdf"
    plt.savefig(output_pdf, format='pdf', bbox_inches='tight')

    plt.close()


def main(args):
    file_path = args.file_path
    app = args.app
    burst_size = args.burst_size
    df = parse_data(file_path, burst_size)
    if not df.empty:
        last_write_cyc = df['Last Write Cycle'].max()
        last_read_cyc = df['Last Read Cycle'].max()
        print(f"last write cyc: {last_write_cyc}, \
              last read cyc: {last_read_cyc}")
        output_dir = 'plots/4'
        if not os.path.exists(output_dir):
            os.makedirs(output_dir)
        # base_name = os.path.basename(file_path)
        # output_file = f"{output_dir}/{base_name.replace('.dasm', '.pdf')}"
        output_file = f"{output_dir}/{app}"
        # file_title = base_name.replace('.dasm', '')
        file_title = f"{app}"
        plot_lifetime(df, output_file, file_title, burst_size)
        print(f"Plot saved as: {output_file}")
    else:
        print("No data found. Check your file or parsing logic.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Analyze SPM Word Lifetime")
    parser.add_argument('file_path', type=str,
                        help='The file path of the data file to analyze')
    parser.add_argument('app', type=str,
                        help='The app name of the data file to analyze')
    parser.add_argument('burst_size', type=int,
                        help='Burst size in bytes for data aggregation')
    args = parser.parse_args()
    main(args)
