#!/usr/bin/env python3

# Copyright 2024 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

import sys
import pandas as pd

keys_to_save = [
    "cycles",
    "total_ipc",
    "snitch_issues",
    "stall_tot",
    "stall_ins",
    "stall_raw_lsu",
    "stall_raw_acc",
    "stall_lsu",
    "stall_acc",
    "stall_wfi",
    "seq_latency_local",
    "seq_latency_global",
    "itl_latency_local",
    "itl_latency_global",
]

def extract_section_to_excel(filename, output_file):
    with open(filename, 'r') as file:
        data = file.read()
    
    # Create a DataFrame
    df = pd.DataFrame()
    sections = data.split("Section ")
    for section in sections[1:]:
        section_number, section_content = section.split(":", 1)
        lines = section_content.splitlines()
        lines = [line.strip() for line in lines if line.strip()]
        
        for line in lines:  # Skip the "Section X:" line
            key, value = line.split(None, 1)  # Split on the first space
            if key in keys_to_save:
                df.loc[section_number, key] = value
    
    df.to_excel(output_file, index=True)

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: python script.py <file_path> <output_excel_file>")
        sys.exit(1)
    
    file_path = sys.argv[1]
    output_excel = sys.argv[2]
    
    extract_section_to_excel(file_path, output_excel)
