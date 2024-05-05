import subprocess
import os
import re
import pandas as pd
import matplotlib.pyplot as plt
import numpy as np
from pprint import pp

HARDWARE_DIR="../../hardware"
APPS_DIR="../apps"
KMP_APPS_DIR=APPS_DIR + "/kmp"
OMP_APPS_DIR=APPS_DIR + "/omp"
OUTPUT="results.csv"
UART_REGEX=re.compile(r"\[UART\] (.*): (\d+)")

def main():
    df = pd.read_csv(OUTPUT)

# Separate LLVM and GCC data
    llvm_data = df[df['compiler'] == 'llvm']
    gcc_data = df[df['compiler'] == 'gcc']

    # Merge LLVM and GCC data on 'app' and 'name'
    joined_data = pd.merge(llvm_data, gcc_data, on=['app', 'name'], suffixes=('_llvm', '_gcc'))

    # Calculate the speedup (GCC cycles / LLVM cycles)
    joined_data['speedup'] = joined_data['cycles_gcc'] / joined_data['cycles_llvm']

    # Get unique applications
    apps = joined_data['app'].unique()

    # Create bar plots for each application showing speedup
    for app in apps:
        # Filter data for the current app
        app_data = joined_data[joined_data['app'] == app]

        # Unique test names
        test_names = app_data['name']

        # Speedup values
        speedup_values = app_data['speedup']

        # Bar positions and bar width
        bar_width = 0.4  # Width of the bars
        x = np.arange(len(test_names)) # Position for bars

        # Create the bar plot
        plt.figure()

        # Plot speedup values
        bars = plt.bar(x, speedup_values, width=bar_width, color='green', label='LLVM Speedup')

        # Add value labels on top of each bar
        for bar, value in zip(bars, speedup_values):
            height = bar.get_height()
            plt.text(bar.get_x() + bar.get_width() / 2, height + 0.05, f'{value:.2f}', ha='center', va='bottom')

        # Set x-axis labels, title, etc.
        plt.ylabel('GCC/LLVM Ratio (Speedup)')
        plt.title(f'Speedup of LLVM Against GCC for {app}')
        plt.xticks(x, test_names)
        plt.axhline(y=1, color='red', linestyle='--', linewidth=1, label='Baseline (GCC)')
        plt.legend()
        plt.tight_layout()  # Adjust layout for readability
        plt.savefig(f'results/after/{app}_speedup.png')
        # plt.show()  # Display plot


if __name__ == '__main__':
    main()
