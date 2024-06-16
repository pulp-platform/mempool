# Copyright 2024 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import textwrap
import subprocess
import re
import pandas as pd
import matplotlib.pyplot as plt
import numpy as np

HARDWARE_DIR = "../../hardware"
APPS_DIR = "../apps"
OMP_APPS_DIR = APPS_DIR + "/omp"
UART_REGEX = re.compile(r"\[UART\] (.*): (\d+)")
GIT_COMMIT_HASH = subprocess.check_output(
    ["git", "describe", "--always", "--dirty"]).strip().decode("utf-8")
OUTPUT = f'results/{GIT_COMMIT_HASH}/results.csv'


def plot_speedup(df):
    # Separate LLVM and GCC data
    llvm_data = df[df['compiler'] == 'llvm']
    gcc_data = df[df['compiler'] == 'gcc']

    # Merge LLVM and GCC data on 'app' and 'name'
    joined_data = pd.merge(llvm_data, gcc_data, on=[
                           'app', 'name'], suffixes=('_llvm', '_gcc'))

    # Calculate the speedup (GCC cycles / LLVM cycles)
    joined_data['speedup'] = joined_data['cycles_gcc'] / \
        joined_data['cycles_llvm']

    # Get unique applications
    apps = joined_data['app'].unique()

    # Create bar plots for each application showing speedup
    for app in apps:
        # Filter data for the current app
        app_data = joined_data[joined_data['app'] == app]

        # Unique test names
        test_names = app_data['name']
        test_names = ['\n'.join(textwrap.wrap(name, width=10))
                      for name in test_names]

        # Speedup values
        speedup_values = app_data['speedup']

        # Bar positions and bar width
        bar_width = 0.4  # Width of the bars
        x = np.arange(len(test_names))  # Position for bars

        # Create the bar plot
        plt.figure()

        # Plot speedup values
        bars = plt.bar(x, speedup_values, width=bar_width,
                       color='green', label='LLVM Speedup')

        # Add value labels on top of each bar
        for bar, value in zip(bars, speedup_values):
            height = max(1, bar.get_height())
            _, top = plt.ylim()
            plt.ylim(top=max(top, height + 0.3))
            plt.text(bar.get_x() + bar.get_width() / 2, height +
                     0.05, f'{value:.2f}', ha='center', va='bottom')

        # Set x-axis labels, title, etc.
        plt.ylabel('GCC/LLVM Ratio (Speedup)')
        plt.title(f'Speedup of LLVM Against GCC for {app}')
        plt.xticks(x, test_names, rotation=45, ha='right')
        plt.axhline(y=1, color='red', linestyle='--',
                    linewidth=1, label='Baseline (GCC)')
        plt.legend()
        plt.tight_layout()  # Adjust layout for readability
        plt.savefig(f'results/{GIT_COMMIT_HASH}/{app}_speedup.png')
        # plt.show()  # Display plot


def plot_cycles(df):
    # Get unique applications
    apps = df['app'].unique()

    # Create bar plots for each application showing raw cycles for LLVM and GCC
    for app in apps:
        # Filter data for the current app
        app_data = df[df['app'] == app]

        # Unique test names
        test_names = app_data['name'].unique()

        # Initialize arrays for LLVM and GCC cycles
        llvm_cycles = []
        gcc_cycles = []

        # Iterate over test names and align the cycles
        for test in test_names:
            llvm_cycle = app_data[(app_data['name'] == test) & (
                app_data['compiler'] == 'llvm')]['cycles']
            gcc_cycle = app_data[(app_data['name'] == test) & (
                app_data['compiler'] == 'gcc')]['cycles']

            # Add cycles only if both GCC and LLVM data are available for the
            # test
            if not llvm_cycle.empty and not gcc_cycle.empty:
                llvm_cycles.append(llvm_cycle.iloc[0])
                gcc_cycles.append(gcc_cycle.iloc[0])
            elif not llvm_cycle.empty:
                llvm_cycles.append(llvm_cycle.iloc[0])
                gcc_cycles.append(0)  # Add a placeholder 0 for GCC
            elif not gcc_cycle.empty:
                gcc_cycles.append(gcc_cycle.iloc[0])
                llvm_cycles.append(0)  # Add a placeholder 0 for LLVM

        # Bar width and x-positions with closer spacing
        bar_width = 0.4  # Width of the bars
        x = np.arange(len(test_names))  # Position for bars

        # Create the bar plot
        plt.figure(figsize=(10, 6))

        # Plot LLVM cycles if available
        if llvm_cycles:
            plt.bar(x, llvm_cycles, width=bar_width, label='LLVM')

        # Plot GCC cycles if available
        if gcc_cycles:
            plt.bar(x + bar_width, gcc_cycles, width=bar_width, label='GCC')

        # Set x-axis labels, title, etc.
        plt.ylabel('Cycles')
        plt.title(f'Cycles Comparison for {app}')
        plt.xticks(x + bar_width / 2, test_names, rotation=45, ha='right')
        plt.legend()
        plt.tight_layout()  # Adjust layout for readability
        plt.savefig(f'results/{GIT_COMMIT_HASH}/{app}_cycles.png')
        # plt.show()  # Display plot


def main():
    df = pd.read_csv(OUTPUT)

    if ("dirty" in GIT_COMMIT_HASH):
        print("WARNING: The current commit is dirty.")

    plot_speedup(df)
    plot_cycles(df)


if __name__ == '__main__':
    main()
