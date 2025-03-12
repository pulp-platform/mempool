#!/bin/bash

# Copyright 2024 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# Base variables
# app_path="/usr/scratch2/pisoc8/sem24h30/terapool_noc/mempool/software/bin/apps/baremetal"
# app="matmul_i32"
app_path="/usr/scratch2/pisoc8/sem24h30/terapool_noc/mempool/software/bin/apps/baremetal"
app="matmul_i32_gold"
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


# Loop through all combinations
for rdwr in "${noc_rdwr_combinations[@]}"; do
    eval $rdwr
    for tile_id_remap in "${tile_remap_values[@]}"; do
        for spm_bank_id_remap in "${spm_remap_values[@]}"; do
            for fifo in "${router_fifo_combinations[@]}"; do
                eval $fifo

                # Construct buildpath
                buildpath="/usr/scratch/larain12/zexifu/terapool_noc/mempool/hardware/build_256matmult32i/build_${noc_req_rd_channel_num}r${noc_req_rdwr_channel_num}rw_tremap${tile_id_remap}_bremap${spm_bank_id_remap}_router${noc_router_input_fifo_dep}in${noc_router_output_fifo_dep}out"

                # Display current configuration
                echo "Launching configuration in xterm: $buildpath"

                # Run the command in a new xterm window
                xterm -hold -e bash -c "
                    export app_path='$app_path'
                    export app='$app'
                    export buildpath='$buildpath'
                    export config='$config'
                    export noc_req_rd_channel_num='$noc_req_rd_channel_num'
                    export noc_req_rdwr_channel_num='$noc_req_rdwr_channel_num'
                    export tile_id_remap='$tile_id_remap'
                    export spm_bank_id_remap='$spm_bank_id_remap'
                    export noc_router_input_fifo_dep='$noc_router_input_fifo_dep'
                    export noc_router_output_fifo_dep='$noc_router_output_fifo_dep'
                    make simc
                " &

                sleep 1 # Small delay to prevent overwhelming the system
            done
        done
    done
done

echo "All configurations have been launched in separate xterm windows."
