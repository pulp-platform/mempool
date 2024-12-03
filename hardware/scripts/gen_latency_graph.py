#!/usr/bin/env python3

# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# This script takes a set of .csv files in one of the results folders and
# generates the average performances over all the cores used.
# Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

import os
import pandas as pd
import numpy as np
import argparse
import matplotlib.pyplot as plt

ext = ('.csv')

parser = argparse.ArgumentParser()
parser.add_argument(
    '--folder',
    '-f',
    help='Name of the results folder with traces to be averaged.'
)
parser.add_argument(
    '--section',
    '-s',
    help='Index of section for analysis.'
)
args = parser.parse_args()

os.chdir(args.folder)
path = os.getcwd()
section = int(args.section)
snitch_global_load_latency = np.array([])
for files in os.listdir(path):
    if files.endswith(ext):
        csvread = pd.read_csv(files)
        if section not in set(csvread['section']):
            print("Section %d not found in %s" % (section, files))
            exit(1)
        sectionread = csvread.loc[csvread['section'] == section]
        snitch_load_region = sectionread['snitch_load_region'].to_numpy()
        snitch_load_latency = sectionread['snitch_load_latency'].to_numpy()
        for i in range(len(snitch_load_region)):
            region_list = eval(snitch_load_region[i])
            latency_list = eval(snitch_load_latency[i])
            region = np.array(region_list)
            latency = np.array(latency_list)
            
            global_load_indices = np.where(region == 2)[0]
            snitch_global_load_latency = np.append(snitch_global_load_latency, latency[global_load_indices])
            
        bins = list(range(0, 201, 10)) + [np.inf]
        hist, bin_edges = np.histogram(snitch_global_load_latency, bins=bins)
        percentages = (hist / hist.sum()) * 100

        labels = [f"{int(bin_edges[i])}-{int(bin_edges[i+1]-1)}" if i < len(bin_edges) - 2 else "200+"
                for i in range(len(bin_edges) - 1)]

        avg_value = np.mean(snitch_global_load_latency)
        max_value = np.max(snitch_global_load_latency)
        percentile_50 = np.percentile(snitch_global_load_latency, 50)
        percentile_99 = np.percentile(snitch_global_load_latency, 99)
        
        plt.figure(figsize=(10, 6))
        bars = plt.bar(labels, percentages, width=0.8, edgecolor='black')

        for i, bar in enumerate(bars):
            height = bar.get_height()
            plt.text(bar.get_x() + bar.get_width() / 2, height + 0.5, f"{height:.2f}%", ha='center', fontsize=10)

        last_two_levels_dir = os.path.join(*path.split(os.sep)[-2:])
        plt.text(0.95, 0.95, f"Path: {last_two_levels_dir}",
                 ha='right', va='top', transform=plt.gca().transAxes, fontsize=12, bbox=dict(boxstyle="round", alpha=0.5))

        plt.text(0.95, 0.85, f"Avg: {avg_value:.2f}",
                ha='right', va='top', transform=plt.gca().transAxes, fontsize=12, bbox=dict(boxstyle="round", alpha=0.5))
        
        plt.text(0.95, 0.75, f"Max: {max_value}",
                ha='right', va='top', transform=plt.gca().transAxes, fontsize=12, bbox=dict(boxstyle="round", alpha=0.5))
        
        plt.text(0.95, 0.65, f"50th percentile: {percentile_50}",
                ha='right', va='top', transform=plt.gca().transAxes, fontsize=12, bbox=dict(boxstyle="round", alpha=0.5))
        
        plt.text(0.95, 0.55, f"99th percentile: {percentile_99}",
                ha='right', va='top', transform=plt.gca().transAxes, fontsize=12, bbox=dict(boxstyle="round", alpha=0.5))

        plt.title("Distribution of global load latency", fontsize=14)
        plt.xlabel("Latency Range", fontsize=12)
        plt.ylabel("Percentage (%)", fontsize=12)
        plt.xticks(rotation=45)
        plt.tight_layout()
        
        plt.savefig(path + '/global_load_latency.png')
        exit(0)
            
        

