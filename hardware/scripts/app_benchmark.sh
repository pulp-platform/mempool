#!/usr/bin/env zsh

# Copyright 2024 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

app_list=("terapool/axpy_i32" "terapool/dotp_i32" "terapool/dct_i32" "terapool/conv2d_i32" "terapool/conv2d_local_i32" "terapool/matmul_i32")
config_list=("config=terapool noc_req_rd_channel_num=0 noc_req_rdwr_channel_num=2 noc_resp_channel_num=2" \
             "config=terapool noc_req_rd_channel_num=1 noc_req_rdwr_channel_num=1 noc_resp_channel_num=2" \
             "config=terapool noc_req_rd_channel_num=1 noc_req_rdwr_channel_num=1 noc_resp_channel_num=3" \
             "config=terapool noc_req_rd_channel_num=0 noc_req_rdwr_channel_num=2 noc_resp_channel_num=2 noc_router_remapping=3 noc_router_remap_group_size=4" \
             "config=terapool noc_req_rd_channel_num=1 noc_req_rdwr_channel_num=1 noc_resp_channel_num=2 noc_router_remapping=3 noc_router_remap_group_size=4" \
             "config=terapool noc_req_rd_channel_num=1 noc_req_rdwr_channel_num=1 noc_resp_channel_num=3 noc_router_remapping=3 noc_router_remap_group_size=4")

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

# Resource usage thresholds (adjust as needed):
MEM_THRESHOLD=70.0      # Memory usage threshold in percent
DISK_THRESHOLD=90       # Disk usage threshold in percent for the root filesystem
CPU_THRESHOLD=70.0      # CPU usage threshold in percent

# Function to delay launching new jobs until resource usage is below thresholds.
limit_resources() {
  local max_jobs=16
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
    else
      sleep 1
    fi
  done
}

for config in "${config_list[@]}"; do
  for app in "${app_list[@]}"; do
    workdir="${config// /_}"
    workdir="${workdir//config=/}"
    workdir="${workdir//noc_req_rd_channel_num=/rd}"
    workdir="${workdir//noc_req_rdwr_channel_num=/rw}"
    workdir="${workdir//noc_resp_channel_num=/rsp}"
    workdir="${workdir//noc_router_remapping=/rrmp}"
    workdir="${workdir//noc_router_remap_group_size=/rgrp}"
    workdir="${workdir//spm_bank_id_remap=/brmp}"
    workdir="${workdir//tile_id_remap=/trmp}"
    workdir=${workdir}/${app}
    # limit_resources
    # ./scripts/exec_benchmark.sh $app \"$config\" $workdir
    tmux new-session -d -s $workdir "./scripts/exec_benchmark.sh $app \"$config\" $workdir"
  done
done

