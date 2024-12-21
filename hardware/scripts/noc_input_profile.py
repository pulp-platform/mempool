#!/usr/bin/env python3
# Copyright 2024 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.colors as mcolors
import ast
import sys
import os

network = 'req'
level = 'system'  # system, subnet, group, router
group_sel = 5

result_path = sys.argv[1]
file_path = f"{result_path}/noc_profiling/{network}_floo_input.log"
plot_path = os.path.join(result_path, "noc_profiling", "plot", "input_profile", network + "_network", level + "_level")
os.makedirs(plot_path, exist_ok=True)

# Load and preprocess the data
with open(file_path, "r") as file:
    raw_content = file.readlines()

parsed_data = []
for line in raw_content:
    line = line.strip()
    if line.startswith("{") and not line.endswith("}"):
        line += "}"  # Append a closing brace if missing
    try:
        entry = ast.literal_eval(line)  # Parse JSON-like entries
        parsed_data.append(entry)
    except Exception:
        continue

df = pd.DataFrame(parsed_data)
if df.empty:
    print("Error: No valid data found in the file.")
    exit(1)
    
def plot_input_utilization(df, plt_path):
    if level == 'system':
        max_cyc_num = 409600
    elif level == 'group':
        max_cyc_num = 6400
    elif level == 'subnet':
        max_cyc_num = 12800
    elif level == 'router':
        max_cyc_num = 200
    plt.figure(figsize=(len(df)/20, 4))
    bar_width = 1.0
    index = np.arange(len(df))
    
    vld_cyc_num = np.array(df["in_vld_cyc_num"].values)
    hsk_cyc_num = np.array(df["in_hsk_cyc_num"].values)
    hol_stall_cyc_num = np.array(df["hol_stall_cyc_num"].values)
    man_stall_cyc_num = vld_cyc_num - hsk_cyc_num - hol_stall_cyc_num
    idle_cyc_num = max_cyc_num - vld_cyc_num
    
    man_stall_perc = np.round(man_stall_cyc_num / max_cyc_num * 100, 2)
    hol_stall_perc = np.round(hol_stall_cyc_num / max_cyc_num * 100, 2)
    hsk_perc = np.round(hsk_cyc_num / max_cyc_num * 100, 2)
    idle_perc = np.round(idle_cyc_num / max_cyc_num * 100, 2)
    
    man_stall_sum = np.sum(man_stall_cyc_num)
    hol_stall_sum = np.sum(hol_stall_cyc_num)
    hsk_sum = np.sum(hsk_cyc_num)
    idle_sum = np.sum(idle_cyc_num)
    all_sum = man_stall_sum + hol_stall_sum + hsk_sum + idle_sum
    assert all_sum == max_cyc_num * len(df)
    
    man_stall_tot_perc = np.round(man_stall_sum / all_sum * 100, 2)
    hol_stall_tot_perc = np.round(hol_stall_sum / all_sum * 100, 2)
    hsk_tot_perc = np.round(hsk_sum / all_sum * 100, 2)
    idle_tot_perc = np.round(idle_sum / all_sum * 100, 2)
    
    plt.xlim(-0.5, len(df) - 0.5)
    plt.ylim(0, 100)
    plt.bar(index, idle_perc, bar_width, bottom=hsk_perc+hol_stall_perc+man_stall_perc, label=f"Idle({idle_tot_perc}%)", color='gray')
    plt.bar(index, hsk_perc, bar_width, bottom=hol_stall_perc+man_stall_perc, label=f"In Use({hsk_tot_perc}%)", color='green')
    plt.bar(index, hol_stall_perc, bar_width, bottom=man_stall_perc, label=f"HoL Stall({hol_stall_tot_perc}%)", color='orange')
    plt.bar(index, man_stall_perc, bar_width, label=f"Mandatory Stall({man_stall_tot_perc}%)", color='red')
    plt.xticks([])

    plt.ylabel('Utilization')
    # plt.title(f'Group {group}, Dir {dir}')
    plt.legend(loc='upper right')

    plt.tight_layout()
    plt.savefig(plt_path)
    plt.close()
    
def plot_output_congestion(df, plt_path):
    if level == 'group':
        max_cyc_num = 32000
    elif level == 'router':
        max_cyc_num = 1000
    plt.figure(figsize=(len(df)/20, 4))
    bar_width = 1.0
    index = np.arange(len(df))
    
    dir0_cong_cyc_num = np.array(df["out_dir0_cong_cyc_num"].values)
    dir1_cong_cyc_num = np.array(df["out_dir1_cong_cyc_num"].values)
    dir2_cong_cyc_num = np.array(df["out_dir2_cong_cyc_num"].values)
    dir3_cong_cyc_num = np.array(df["out_dir3_cong_cyc_num"].values)
    dir4_cong_cyc_num = np.array(df["out_dir4_cong_cyc_num"].values)
    clear_cyc_num = max_cyc_num - dir0_cong_cyc_num - dir1_cong_cyc_num - dir2_cong_cyc_num - dir3_cong_cyc_num - dir4_cong_cyc_num
    
    dir0_cong_perc = np.round(dir0_cong_cyc_num / max_cyc_num * 100, 2)
    dir1_cong_perc = np.round(dir1_cong_cyc_num / max_cyc_num * 100, 2)
    dir2_cong_perc = np.round(dir2_cong_cyc_num / max_cyc_num * 100, 2)
    dir3_cong_perc = np.round(dir3_cong_cyc_num / max_cyc_num * 100, 2)
    dir4_cong_perc = np.round(dir4_cong_cyc_num / max_cyc_num * 100, 2)
    clear_perc = np.round(clear_cyc_num / max_cyc_num * 100, 2)
    
    dir0_cong_sum = np.sum(dir0_cong_cyc_num)
    dir1_cong_sum = np.sum(dir1_cong_cyc_num)
    dir2_cong_sum = np.sum(dir2_cong_cyc_num)
    dir3_cong_sum = np.sum(dir3_cong_cyc_num)
    dir4_cong_sum = np.sum(dir4_cong_cyc_num)
    clear_sum = np.sum(clear_cyc_num)
    all_sum = dir0_cong_sum + dir1_cong_sum + dir2_cong_sum + dir3_cong_sum + dir4_cong_sum + clear_sum
    assert all_sum == max_cyc_num * len(df)
    
    dir0_cong_tot_perc = np.round(dir0_cong_sum / all_sum * 100, 2)
    dir1_cong_tot_perc = np.round(dir1_cong_sum / all_sum * 100, 2)
    dir2_cong_tot_perc = np.round(dir2_cong_sum / all_sum * 100, 2)
    dir3_cong_tot_perc = np.round(dir3_cong_sum / all_sum * 100, 2)
    dir4_cong_tot_perc = np.round(dir4_cong_sum / all_sum * 100, 2)
    clear_tot_perc = np.round(clear_sum / all_sum * 100, 2)
    
    plt.xlim(-0.5, len(df) - 0.5)
    plt.ylim(0, 100)
    plt.bar(index, clear_perc, bar_width, bottom=dir0_cong_perc+dir1_cong_perc+dir2_cong_perc+dir3_cong_perc+dir4_cong_perc, label=f"Clear({clear_tot_perc}%)", color='gray')
    plt.bar(index, dir0_cong_perc, bar_width, bottom=dir1_cong_perc+dir2_cong_perc+dir3_cong_perc+dir4_cong_perc, label=f"Eject({dir0_cong_tot_perc}%)", color='brown')
    plt.bar(index, dir1_cong_perc, bar_width, bottom=dir2_cong_perc+dir3_cong_perc+dir4_cong_perc, label=f"North({dir1_cong_tot_perc}%)", color='yellow')
    plt.bar(index, dir2_cong_perc, bar_width, bottom=dir3_cong_perc+dir4_cong_perc, label=f"East({dir2_cong_tot_perc}%)", color='deepskyblue')
    plt.bar(index, dir3_cong_perc, bar_width, bottom=dir4_cong_perc, label=f"South({dir3_cong_tot_perc}%)", color='orange')
    plt.bar(index, dir4_cong_perc, bar_width, label=f"West({dir4_cong_tot_perc}%)", color='blue')
    plt.xticks([])
    
    plt.ylabel('Congestion')
    # plt.title(f'Group {group}')
    plt.legend(loc='upper right')
    
    plt.tight_layout()
    plt.savefig(plt_path)
    plt.close()
    

df = df[~((df["GROUP"] == 0) & (df["DIR"] == 3))]
df = df[~((df["GROUP"] == 4) & (df["DIR"] == 3))]
df = df[~((df["GROUP"] == 8) & (df["DIR"] == 3))]
df = df[~((df["GROUP"] == 12) & (df["DIR"] == 3))]
df = df[~((df["GROUP"] == 0) & (df["DIR"] == 4))]
df = df[~((df["GROUP"] == 1) & (df["DIR"] == 4))]
df = df[~((df["GROUP"] == 2) & (df["DIR"] == 4))]
df = df[~((df["GROUP"] == 3) & (df["DIR"] == 4))]
df = df[~((df["GROUP"] == 3) & (df["DIR"] == 1))]
df = df[~((df["GROUP"] == 7) & (df["DIR"] == 1))]
df = df[~((df["GROUP"] == 11) & (df["DIR"] == 1))]
df = df[~((df["GROUP"] == 15) & (df["DIR"] == 1))]
df = df[~((df["GROUP"] == 12) & (df["DIR"] == 2))]
df = df[~((df["GROUP"] == 13) & (df["DIR"] == 2))]
df = df[~((df["GROUP"] == 14) & (df["DIR"] == 2))]
df = df[~((df["GROUP"] == 15) & (df["DIR"] == 2))]

if(level == 'system'):
    df_pruned = df.drop(columns=["GROUP", "TILE", "PORT", "DIR", "end_cycle", "max_stall_cyc_num", 
                                "out_dir0_cong_cyc_num", "out_dir1_cong_cyc_num", "out_dir2_cong_cyc_num", "out_dir3_cong_cyc_num", "out_dir4_cong_cyc_num"])
    df_grouped = df_pruned.groupby("start_cycle", as_index=False).agg({
        "in_vld_cyc_num": "sum",
        "in_hsk_cyc_num": "sum",
        "hol_stall_cyc_num": "sum"
    })
    plt_path = os.path.join(plot_path, "utilization.png")
    plot_input_utilization(df_grouped, plt_path)

if(level == 'group'):
    for group in range(16):
        df_group = df[df["GROUP"] == group]
        df_congestion = df_group.drop(columns=["GROUP", "TILE", "PORT", "DIR", "end_cycle", "in_vld_cyc_num", "in_hsk_cyc_num", "hol_stall_cyc_num", "max_stall_cyc_num"])
        df_congestion_grouped = df_congestion.groupby("start_cycle", as_index=False).agg({
            "out_dir0_cong_cyc_num": "sum",
            "out_dir1_cong_cyc_num": "sum",
            "out_dir2_cong_cyc_num": "sum",
            "out_dir3_cong_cyc_num": "sum",
            "out_dir4_cong_cyc_num": "sum"
        })
        plt_path = os.path.join(plot_path, f"group_{group}_congestion.png")
        plot_output_congestion(df_congestion_grouped, plt_path)
        for dir in range(5):
            df_dir = df_group[df_group["DIR"] == dir]
            if df_dir.empty:
                continue            
            df_pruned = df_dir.drop(columns=["GROUP", "TILE", "PORT", "DIR", "end_cycle", "max_stall_cyc_num", 
                                "out_dir0_cong_cyc_num", "out_dir1_cong_cyc_num", "out_dir2_cong_cyc_num", "out_dir3_cong_cyc_num", "out_dir4_cong_cyc_num"])
            df_grouped = df_pruned.groupby("start_cycle", as_index=False).agg({
                "in_vld_cyc_num": "sum",
                "in_hsk_cyc_num": "sum",
                "hol_stall_cyc_num": "sum"
            })
            if(dir == 0):
                plt_path = os.path.join(plot_path, f"group_{group}_utilization_inject.png")
            elif(dir == 1):
                plt_path = os.path.join(plot_path, f"group_{group}_utilization_north.png")
            elif(dir == 2):
                plt_path = os.path.join(plot_path, f"group_{group}_utilization_east.png")
            elif(dir == 3):
                plt_path = os.path.join(plot_path, f"group_{group}_utilization_south.png")
            else:
                plt_path = os.path.join(plot_path, f"group_{group}_utilization_west.png")
            plot_input_utilization(df_grouped, plt_path)

elif level == 'subnet':
    for tile in range(16):
        df_tile = df[df["TILE"] == tile]
        for port in range(2):
            df_port = df_tile[df_tile["PORT"] == port]
            df_pruned = df_port.drop(columns=["GROUP", "TILE", "PORT", "DIR", "end_cycle"])
            df_grouped = df_pruned.groupby("start_cycle", as_index=False).agg({
                "in_vld_cyc_num": "sum",
                "in_hsk_cyc_num": "sum",
                "hol_stall_cyc_num": "sum"
            })
            plt_path = os.path.join(plot_path, f"tile_{tile}_port_{port}_utilization.png")
            plot_input_utilization(df_grouped, plt_path)
            
elif level == 'router':
    df_group = df[df["GROUP"] == group_sel]
    for tile in range(16):
        df_tile = df_group[df_group["TILE"] == tile]
        for port in range(2):
            df_port = df_tile[df_tile["PORT"] == port]
            df_congestion = df_port.drop(columns=["GROUP", "TILE", "PORT", "DIR", "end_cycle", "in_vld_cyc_num", "in_hsk_cyc_num", "hol_stall_cyc_num", "max_stall_cyc_num"])
            df_congestion_grouped = df_congestion.groupby("start_cycle", as_index=False).agg({
                "out_dir0_cong_cyc_num": "sum",
                "out_dir1_cong_cyc_num": "sum",
                "out_dir2_cong_cyc_num": "sum",
                "out_dir3_cong_cyc_num": "sum",
                "out_dir4_cong_cyc_num": "sum"
            })
            plt_path = os.path.join(plot_path, f"group_{group_sel}_tile_{tile}_port_{port}_congestion.png")
            plot_output_congestion(df_congestion_grouped, plt_path)
            for dir in range(5):
                df_dir = df_port[df_port["DIR"] == dir]
                if df_dir.empty:
                    continue
                df_pruned = df_dir.drop(columns=["GROUP", "TILE", "PORT", "DIR", "end_cycle"])
                df_grouped = df_pruned.groupby("start_cycle", as_index=False).agg({
                    "in_vld_cyc_num": "sum",
                    "in_hsk_cyc_num": "sum",
                    "hol_stall_cyc_num": "sum"
                })
                if(dir == 0):
                    plt_path = os.path.join(plot_path, f"group_{group_sel}_tile_{tile}_port_{port}_utilization_inject.png")
                elif(dir == 1):
                    plt_path = os.path.join(plot_path, f"group_{group_sel}_tile_{tile}_port_{port}_utilization_north.png")
                elif(dir == 2):
                    plt_path = os.path.join(plot_path, f"group_{group_sel}_tile_{tile}_port_{port}_utilization_east.png")
                elif(dir == 3):
                    plt_path = os.path.join(plot_path, f"group_{group_sel}_tile_{tile}_port_{port}_utilization_south.png")
                else:
                    plt_path = os.path.join(plot_path, f"group_{group_sel}_tile_{tile}_port_{port}_utilization_west.png")
                plot_input_utilization(df_grouped, plt_path)
                