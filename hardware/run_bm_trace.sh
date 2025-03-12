#!/bin/bash

# Copyright 2024 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# Base variables
config="terapool"

# Configuration arrays
noc_rdwr_combinations=("noc_req_rd_channel_num=0 noc_req_rdwr_channel_num=2" "noc_req_rd_channel_num=2 noc_req_rdwr_channel_num=1")
tile_remap_values=(0 1)
spm_remap_values=(0 1)
router_fifo_combinations=("noc_router_input_fifo_dep=2 noc_router_output_fifo_dep=2" "noc_router_input_fifo_dep=4 noc_router_output_fifo_dep=0" "noc_router_input_fifo_dep=8 noc_router_output_fifo_dep=0" "noc_router_input_fifo_dep=16 noc_router_output_fifo_dep=0")

# noc_rdwr_combinations=("noc_req_rd_channel_num=0 noc_req_rdwr_channel_num=2")
# tile_remap_values=(0)
# spm_remap_values=(0)
# router_fifo_combinations=("noc_router_input_fifo_dep=2 noc_router_output_fifo_dep=2")

# Loop through all configurations
for rdwr in "${noc_rdwr_combinations[@]}"; do
    eval $rdwr
    for tile_id_remap in "${tile_remap_values[@]}"; do
        for spm_bank_id_remap in "${spm_remap_values[@]}"; do
            for fifo in "${router_fifo_combinations[@]}"; do
                eval $fifo

                # Construct buildpath and result_dir
                buildpath="/usr/scratch/larain12/zexifu/terapool_noc/mempool/hardware/build_256matmult32i/build_${noc_req_rd_channel_num}r${noc_req_rdwr_channel_num}rw_tremap${tile_id_remap}_bremap${spm_bank_id_remap}_router${noc_router_input_fifo_dep}in${noc_router_output_fifo_dep}out"
                result_dir="results/${noc_req_rd_channel_num}r${noc_req_rdwr_channel_num}rw_tremap${tile_id_remap}_bremap${spm_bank_id_remap}_router${noc_router_input_fifo_dep}in${noc_router_output_fifo_dep}out"

                # Create result directory if not exists
                mkdir -p "$result_dir"

                # Run the trace command in a new xterm window
                echo "Launching trace in xterm for: $buildpath"
                xterm -hold -e bash -c "
                    export config='terapool'
                    export buildpath='$buildpath'
                    export result_dir='$result_dir'
                    make trace
                " &

                sleep 1 # Small delay to prevent overwhelming the system
            done
        done
    done
done

echo "All trace commands have been launched in separate xterm windows."
