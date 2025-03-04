#!/bin/bash

# Copyright 2024 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# Output file
output_file="avg_all.txt"
> "$output_file" # Clear the file if it already exists

# Write the header
echo -e "Result_Dir\tcycles\ttotal_ipc\tsnitch_issues\tstall_tot\tstall_ins\tstall_raw_lsu\tstall_raw_acc\tstall_lsu\tstall_acc\tstall_wfi\tseq_latency_local\tseq_latency_global\titl_latency_local\titl_latency_global" >> "$output_file"

# Find all avg.txt files and process them
find ./results -name "avg.txt" | while read -r file; do
    # Extract result directory
    result_dir=$(basename "$(dirname "$file")")
    
    # Extract Section 2 values
    cycles=$(awk '/Section 2:/ {flag=1; next} /Section 3:/ {flag=0} flag && /cycles/ {print $2}' "$file")
    total_ipc=$(awk '/Section 2:/ {flag=1; next} /Section 3:/ {flag=0} flag && /total_ipc/ {print $2}' "$file")
    snitch_issues=$(awk '/Section 2:/ {flag=1; next} /Section 3:/ {flag=0} flag && /snitch_issues/ {print $2}' "$file")
    stall_tot=$(awk '/Section 2:/ {flag=1; next} /Section 3:/ {flag=0} flag && /stall_tot/ {print $2}' "$file")
    stall_ins=$(awk '/Section 2:/ {flag=1; next} /Section 3:/ {flag=0} flag && /stall_ins/ {print $2}' "$file")
    stall_raw_lsu=$(awk '/Section 2:/ {flag=1; next} /Section 3:/ {flag=0} flag && /stall_raw_lsu/ {print $2}' "$file")
    stall_raw_acc=$(awk '/Section 2:/ {flag=1; next} /Section 3:/ {flag=0} flag && /stall_raw_acc/ {print $2}' "$file")
    stall_lsu=$(awk '/Section 2:/ {flag=1; next} /Section 3:/ {flag=0} flag && /stall_lsu/ {print $2}' "$file")
    stall_acc=$(awk '/Section 2:/ {flag=1; next} /Section 3:/ {flag=0} flag && /stall_acc/ {print $2}' "$file")
    stall_wfi=$(awk '/Section 2:/ {flag=1; next} /Section 3:/ {flag=0} flag && /stall_wfi/ {print $2}' "$file")
    seq_latency_local=$(awk '/Section 2:/ {flag=1; next} /Section 3:/ {flag=0} flag && /seq_latency_local/ {print $2}' "$file")
    seq_latency_global=$(awk '/Section 2:/ {flag=1; next} /Section 3:/ {flag=0} flag && /seq_latency_global/ {print $2}' "$file")
    itl_latency_local=$(awk '/Section 2:/ {flag=1; next} /Section 3:/ {flag=0} flag && /itl_latency_local/ {print $2}' "$file")
    itl_latency_global=$(awk '/Section 2:/ {flag=1; next} /Section 3:/ {flag=0} flag && /itl_latency_global/ {print $2}' "$file")
    
    # Write data to avg_all.txt
    echo -e "${result_dir}\t${cycles}\t${total_ipc}\t${snitch_issues}\t${stall_tot}\t${stall_ins}\t${stall_raw_lsu}\t${stall_raw_acc}\t${stall_lsu}\t${stall_acc}\t${stall_wfi}\t${seq_latency_local}\t${seq_latency_global}\t${itl_latency_local}\t${itl_latency_global}" >> "$output_file"
done

echo "Data extraction complete. Results are saved in $output_file."
