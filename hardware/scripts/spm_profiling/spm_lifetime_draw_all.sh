#!/bin/bash

# Copyright 2021 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# Bash script to search for 'inited_final.dasm' files, print their last parent directories, and process them
# Uses the current directory as default if no path is provided

# Set the default directory to the current directory if no argument is provided
directory="${1:-.}"

# Initialize an empty array to keep track of directories already printed
declare -A printed_directories

# Find files, print their last parent directories, and process them
find "$directory" -type f -name '*inited_final.dasm' | while read file_path; do
    (
        # Extract directory path
        dir_path=$(dirname "$file_path")
        
        # Get the last name of the folder containing the file
        last_parent_folder=$(basename "$dir_path")
        
        # Check if this folder name has been printed already
        if [[ -z "${printed_directories[$last_parent_folder]}" ]]; then
            echo "Find app: $last_parent_folder"
            printed_directories[$last_parent_folder]=1
        fi
        
        echo "Processing file: $file_path"
        python spm_lifetime.py "$file_path" "$last_parent_folder" 128
    ) &
    sleep 1
done
