#!/bin/bash

# Copyright 2025 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# This script runs spyglass lint for all configuration combinations in parallel.
# There are 38,400 combinations. It limits parallel jobs and checks system resources:
#   - Maximum concurrent tmux sessions (MAX_JOBS)
#   - Memory usage (MEM_THRESHOLD)
#   - Disk usage (DISK_THRESHOLD)
#   - CPU usage (CPU_THRESHOLD)
#
# For each configuration, it also copies the TCL script from spyglass/scripts/run_lint.tcl
# to spyglass/tmp/, renames it to run_lint<SG_SCRIPT_SUF>.tcl (where SG_SCRIPT_SUF is the
# combination of configuration options, compressed with abbreviated keys), and passes
# SG_SCRIPT_PATH and SG_SCRIPT_SUF to the make lint command.
#
# After the lint run finishes, it copies the generated report from the matching
# sg_projects folder to spyglass/reports/ (renaming it accordingly) and removes the
# sg_projects folder.
#
# Each job is run in its own tmux session (named "lint_<suffix>") and that session is
# killed when the job completes.
#
# Usage: ./run_lint.sh
# Author: Zexin Fu <zexifu@iis.ee.ethz.ch>

SPYGLASS_WORK_DIR=spyglass

# Maximum number of concurrent tmux sessions (adjust as needed)
# Declare associative array mapping config names to maximum concurrent jobs.
declare -A config_max_jobs
config_max_jobs[terapool_64core]=60
config_max_jobs[mempool]=40
config_max_jobs[terapool]=10

# Resource usage thresholds (adjust as needed):
MEM_THRESHOLD=70.0      # Memory usage threshold in percent
DISK_THRESHOLD=90       # Disk usage threshold in percent for the root filesystem
CPU_THRESHOLD=70.0      # CPU usage threshold in percent

# Function to check current memory usage (as a percentage).
check_memory() {
  free | awk '/Mem:/ {printf "%.1f", $3/$2 * 100.0}'
}

# Function to check current disk usage for the root filesystem (as a percentage).
check_disk() {
  df / | tail -1 | awk '{gsub(/%/,""); print $5}'
}

# Function to check current CPU usage.
# It uses 'top' to determine the idle percentage and computes 100 - idle.
check_cpu() {
  cpu_idle=$(top -bn1 | grep "Cpu(s)" | sed "s/.*, *\([0-9.]*\)%* id.*/\1/")
  cpu_usage=$(echo "100 - $cpu_idle" | bc -l)
  printf "%.1f" "$cpu_usage"
}

# Function to count active lint tmux sessions.
active_tmux_sessions() {
  tmux ls 2>/dev/null | grep '^lint_' | wc -l
}

# Function to delay launching new jobs until resource usage is below thresholds.
limit_resources() {
  local max_jobs="$1"
  while true; do
    active_sessions=$(active_tmux_sessions)
    mem_usage=$(check_memory)
    disk_usage=$(check_disk)
    cpu_usage=$(check_cpu)

    # Uncomment for debugging resource usage:
    # echo "Active tmux sessions: $active_sessions, Memory usage: ${mem_usage}%, Disk usage: ${disk_usage}%, CPU usage: ${cpu_usage}%"
    printf "\rActive tmux sessions: %s, Memory usage: %s%%, Disk usage: %s%%, CPU usage: %s%%" \
           "$active_sessions" "$mem_usage" "$disk_usage" "$cpu_usage"

    if [ "$active_sessions" -lt "$max_jobs" ] && \
       (( $(echo "$mem_usage < $MEM_THRESHOLD" | bc -l) )) && \
       [ "$disk_usage" -lt "$DISK_THRESHOLD" ] && \
       (( $(echo "$cpu_usage < $CPU_THRESHOLD" | bc -l) )); then
      break
    fi
    sleep 1
  done
}

# Function to run a given command and then post-process the generated report.
run_job() {
  eval "source /usr/local/anaconda3-2022.05/etc/profile.d/conda.sh"
  eval "conda activate floogen"
  local cmd="$1"
  local suf="$2"
  local spy="$3"
  # Run the lint command.
  eval "$cmd"

  # After the command completes, determine the project folder.
  # The folder in ${spy}/sg_projects/ should start with ${suf#_}
  local project_folder
  project_folder=$(find ${spy}/sg_projects/ -maxdepth 1 -type d -name "${suf#_}*" | head -n 1)

  if [ -n "$project_folder" ]; then
    rpt_folder=$(find ${project_folder}/consolidated_reports/ -maxdepth 1 -type d -name "*lint_lint_rtl" | head -n 1)
    local report_src="${rpt_folder}/moresimple.rpt"
    if [ -f "$report_src" ]; then
      mkdir -p ${spy}/reports
      cp "$report_src" "${spy}/reports/${suf#_}_moresimple.rpt"
      echo "Copied report to ${spy}/reports/${suf#_}_moresimple.rpt"
      # Remove the project folder since the report was found.
      rm -rf ${spy}/sg_projects/${suf#_}*
      echo "Removed project ${spy}/sg_projects/${suf#_}*"
    else
      echo "Report file not found in ${project_folder}. Project folder NOT removed."
    fi
  else
    echo "No project folder matching ${suf#_}* found in ${spy}/sg_projects/"
  fi
}

# Export run_job so it can be used inside tmux sessions.
export -f run_job

# configs=("terapool_64core")
# tile_id_remaps=("1")
# spm_bank_id_remaps=("1")
# wr_nums=("0")
# # For noc_req_rd_channel_num and noc_req_rdwr_channel_num:
# pairs_wr0=("0,1")
# pairs_wr1=("0,1")
# # New option: noc_resp_channel_num:
# resp_channels=("2")
# topologies=("2dmesh")
# routing_algorithms=("xy")
# req_remappings=("1")
# resp_remappings=("1")
# virtual_channels=("1")
# # For noc_router FIFO depths (input,output):
# router_fifo_pairs=("4,0")
# noc_router_remap_group_size=("4")

# Define configuration arrays.
configs=("terapool_64core" "mempool" "terapool")
tile_id_remaps=("0" "1")
spm_bank_id_remaps=("0" "1")
wr_nums=("0")
# For noc_req_rd_channel_num and noc_req_rdwr_channel_num:
pairs_wr0=("0,1" "0,2" "1,1" "2,1")
pairs_wr1=("0,1" "0,2" "1,1" "2,1" "1,0" "2,0")
# New option: noc_resp_channel_num:
resp_channels=("1" "2")
topologies=("2dmesh" "torus")
routing_algorithms=("xy" "o1" "odd_even")
req_remappings=("1")
resp_remappings=("1")
virtual_channels=("1")
# For noc_router FIFO depths (input,output):
router_fifo_pairs=("4,0")
noc_router_remap_group_size=("2" "4" "8" "16")

# Create necessary directories.
mkdir -p ${SPYGLASS_WORK_DIR}/tmp/jobs
mkdir -p ${SPYGLASS_WORK_DIR}/tmp/flist
mkdir -p ${SPYGLASS_WORK_DIR}/tmp/tcl
mkdir -p ${SPYGLASS_WORK_DIR}/reports

# Iterate over all configuration combinations.
for config in "${configs[@]}"; do
  # Get the maximum jobs for the current config from the associative array.
  current_max_jobs="${config_max_jobs[$config]}"

  for tile_id_remap in "${tile_id_remaps[@]}"; do
    for spm_bank_id_remap in "${spm_bank_id_remaps[@]}"; do
      for wr in "${wr_nums[@]}"; do
        if [ "$wr" -eq 0 ]; then
          pairs=("${pairs_wr0[@]}")
        else
          pairs=("${pairs_wr1[@]}")
        fi
        for pair in "${pairs[@]}"; do
          IFS=',' read -r rd_channel rdwr_channel <<< "$pair"
          for resp_channel in "${resp_channels[@]}"; do
            for topology in "${topologies[@]}"; do
              # If topology is torus, restrict routing algorithm to xy.
              if [ "$topology" == "torus" ]; then
                current_routing_algs=("xy")
              else
                current_routing_algs=("${routing_algorithms[@]}")
              fi
              for routing_algo in "${current_routing_algs[@]}"; do
                for req_remap in "${req_remappings[@]}"; do
                  for resp_remap in "${resp_remappings[@]}"; do
                    for virt_chan in "${virtual_channels[@]}"; do
                      for router_fifo in "${router_fifo_pairs[@]}"; do
                        IFS=',' read -r input_fifo output_fifo <<< "$router_fifo"
                        for remap_size in "${noc_router_remap_group_size[@]}"; do
                          # Build a compressed SG_SCRIPT_SUF with abbreviated keys.
                          # Abbreviations:
                          #   config                => c
                          #   tile_id_remap         => t
                          #   spm_bank_id_remap     => s
                          #   noc_req_wr_channel_num=> wr
                          #   noc_req_rd_channel_num=> rd
                          #   noc_req_rdwr_channel_num=> rr
                          #   noc_resp_channel_num  => rch
                          #   topology              => top
                          #   routing_algorithm     => ra
                          #   req_remapping         => rm
                          #   resp_remapping        => rsm
                          #   num_virtual_channel   => vc
                          #   noc_router_input_fifo_dep => in
                          #   noc_router_output_fifo_dep=> out
                          #   noc_router_remap_group_size=> rs
                          SG_SCRIPT_SUF="_c${config}_t${tile_id_remap}_s${spm_bank_id_remap}_wr${wr}_rd${rd_channel}_rr${rdwr_channel}_rch${resp_channel}_top${topology}_ra${routing_algo}_rm${req_remap}_rsm${resp_remap}_vc${virt_chan}_in${input_fifo}_out${output_fifo}_rs${remap_size}"

                          # Copy the run_lint.tcl file into the tmp directory with a new name.
                          tcl_src="${SPYGLASS_WORK_DIR}/scripts/run_lint.tcl"
                          tcl_dest="${SPYGLASS_WORK_DIR}/tmp/tcl/run_lint${SG_SCRIPT_SUF}.tcl"
                          cp -p "$tcl_src" "$tcl_dest"

                          # In the newly copied file, replace "set PROJECT_FOLDER_NAME   mempool"
                          # with "set PROJECT_FOLDER_NAME   <SG_SCRIPT_SUF without the leading underscore>"
                          sed -i 's/set PROJECT_FOLDER_NAME\s\+mempool/set PROJECT_FOLDER_NAME   '"${SG_SCRIPT_SUF#_}"'/g' "$tcl_dest"
                          sed -i 's/set PROJECT_FOLDER_NAME\s\+terapool/set PROJECT_FOLDER_NAME   '"${SG_SCRIPT_SUF#_}"'/g' "$tcl_dest"
                          # Also modify the read_file command.
                          sed -i 's/read_file -type sourcelist tmp\/files/read_file -type sourcelist tmp\/flist\/files_'"${SG_SCRIPT_SUF#_}"'/g' "$tcl_dest"

                          # Remove the specific three lines explicitly
                          sed -i '/^# Create a link to the results$/d' "$tcl_dest"
                          sed -i '/^exec rm -rf sg_projects\/\${PROJECT}$/d' "$tcl_dest"
                          sed -i '/^exec ln -sf \${PROJECT_FOLDER_NAME}_\${TIMESTAMP} sg_projects\/\${PROJECT}$/d' "$tcl_dest"

                          # Generate the file list.
                          rm ${SPYGLASS_WORK_DIR}/tmp/files_${SG_SCRIPT_SUF#_}
                          cmd_flist="SG_SCRIPT_PATH=tmp/tcl SG_SCRIPT_SUF=${SG_SCRIPT_SUF} config=${config} tile_id_remap=${tile_id_remap} spm_bank_id_remap=${spm_bank_id_remap} noc_req_wr_channel_num=${wr} noc_req_rd_channel_num=${rd_channel} noc_req_rdwr_channel_num=${rdwr_channel} noc_resp_channel_num=${resp_channel} topology=${topology} routing_algorithm=${routing_algo} req_remapping=${req_remap} resp_remapping=${resp_remap} num_virtual_channel=${virt_chan} noc_router_input_fifo_dep=${input_fifo} noc_router_output_fifo_dep=${output_fifo} noc_router_remap_group_size=${remap_size} make ${SPYGLASS_WORK_DIR}/tmp/files_${SG_SCRIPT_SUF#_} SPYGLASS_WORK_DIR=${SPYGLASS_WORK_DIR}"
                          eval "$cmd_flist"
                          mv ${SPYGLASS_WORK_DIR}/tmp/files_${SG_SCRIPT_SUF#_} ${SPYGLASS_WORK_DIR}/tmp/flist/files_${SG_SCRIPT_SUF#_}

                          # Build the command.
                          cmd="SG_SCRIPT_PATH=tmp/tcl SG_SCRIPT_SUF=${SG_SCRIPT_SUF} config=${config} tile_id_remap=${tile_id_remap} spm_bank_id_remap=${spm_bank_id_remap} noc_req_wr_channel_num=${wr} noc_req_rd_channel_num=${rd_channel} noc_req_rdwr_channel_num=${rdwr_channel} noc_resp_channel_num=${resp_channel} topology=${topology} routing_algorithm=${routing_algo} req_remapping=${req_remap} resp_remapping=${resp_remap} num_virtual_channel=${virt_chan} noc_router_input_fifo_dep=${input_fifo} noc_router_output_fifo_dep=${output_fifo} noc_router_remap_group_size=${remap_size} make lint SPYGLASS_WORK_DIR=${SPYGLASS_WORK_DIR}"

                          echo "Waiting for resources before launching command:"
                          echo "$cmd"
                          # Wait until system resources are below the thresholds.
                          limit_resources "$current_max_jobs"

                          # Create a unique tmux session name based on the suffix (without the leading underscore).
                          session_name="lint_${SG_SCRIPT_SUF#_}"
                          echo "Starting tmux session '$session_name' for command:"
                          echo "$cmd"

                          # Create a temporary script file that the tmux session will execute.
                          tmp_script=$(mktemp ${SPYGLASS_WORK_DIR}/tmp/jobs/lint_job_${session_name}.XXXXXX.sh)
                          cat <<EOF > "$tmp_script"
$(declare -f run_job)
run_job "$cmd" "$SG_SCRIPT_SUF" "${SPYGLASS_WORK_DIR}"
tmux kill-session -t "$session_name"
EOF
                          chmod +x "$tmp_script"

                          sleep 1

                          # Launch the job in a new tmux session.
                          tmux new-session -d -s "$session_name" "$tmp_script"

                          sleep 1
                        done
                      done
                    done
                  done
                done
              done
            done
          done
        done
      done
    done
  done
  sleep 120
done

# Wait until all tmux sessions whose names start with "lint_" have finished.
while tmux ls 2>/dev/null | grep -q '^lint_'; do
  sleep 5
done

echo "All jobs completed."
