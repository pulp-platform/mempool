#!/bin/bash

# Copyright 2024 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# Output CSV file
output_file="cycles_analysis_data.csv"
> "$output_file"

# Write the header row
echo "result_dir,noc_req_rd_channel_num,noc_req_rdwr_channel_num,tile_id_remap,spm_bank_id_remap,noc_router_input_fifo_dep,noc_router_output_fifo_dep,cycles_section1,cycles_section2" >> "$output_file"

# Parse avg.txt files
find ./results -name "avg.txt" | while read -r file; do
    # Extract directory name
    result_dir=$(basename "$(dirname "$file")")
    
    # Extract parameters using grep with specific regex
    noc_req_rd_channel_num=$(echo "$result_dir" | awk -F'r' '{print $1}' | awk -F'_' '{print $1}')
    noc_req_rdwr_channel_num=$(echo "$result_dir" | grep -oP '(?<=r)\d+(?=rw)')
    tile_id_remap=$(echo "$result_dir" | grep -oP '(?<=tremap)\d+')
    spm_bank_id_remap=$(echo "$result_dir" | grep -oP '(?<=bremap)\d+')
    noc_router_input_fifo_dep=$(echo "$result_dir" | grep -oP '(?<=router)\d+(?=in)')
    noc_router_output_fifo_dep=$(echo "$result_dir" | grep -oP '(?<=in)\d+(?=out)')
    
    # Extract cycles from Section 1 and Section 2
    cycles_section1=$(awk '/Section 1:/ {flag=1; next} /Section 2:/ {flag=0} flag && /cycles/ {print $2}' "$file")
    cycles_section2=$(awk '/Section 2:/ {flag=1; next} /Section 3:/ {flag=0} flag && /cycles/ {print $2}' "$file")
    
    # Validate extracted data
    if [[ -z "$noc_req_rd_channel_num" || -z "$noc_req_rdwr_channel_num" || -z "$tile_id_remap" || -z "$spm_bank_id_remap" || -z "$noc_router_input_fifo_dep" || -z "$noc_router_output_fifo_dep" || -z "$cycles_section1" || -z "$cycles_section2" ]]; then
        echo "Warning: Incomplete data extracted for $result_dir"
        continue
    fi
    
    # Append data to the CSV
    echo "$result_dir,$noc_req_rd_channel_num,$noc_req_rdwr_channel_num,$tile_id_remap,$spm_bank_id_remap,$noc_router_input_fifo_dep,$noc_router_output_fifo_dep,$cycles_section1,$cycles_section2" >> "$output_file"
done

echo "Data preparation complete. Output saved to $output_file."
