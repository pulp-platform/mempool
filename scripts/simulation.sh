# Copyright 2026 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

#!/usr/bin/env bash
set -euo pipefail

# --- parameter grids ---
# M_SIZES=(64 128 256)              # matrix_M = matrix_N = matrix_P
# RM_SIZES=(8)                      # redmule_height = redmule_width
# NUM_OUTSTANDING=(4 8 16 32)
# FIFO_DEPTHS=(0 2 4)
# GROUPING=(2 4 8)

# # --- parameter grids ---
M_SIZES=(32)              # matrix_M = matrix_N = matrix_P
RM_SIZES=(8)                      # redmule_height = redmule_width
NUM_OUTSTANDING=(8)
FIFO_DEPTHS=(0)
GROUPING=(2)



# Go to repo root (optional but recommended)
# cd "$(dirname "$0")"

# Activate virtual environment once
source venv/bin/activate

for RM in "${RM_SIZES[@]}"; do
  for M in "${M_SIZES[@]}"; do
    echo "=== Software setup for matrix size $M x $M ==="

    # clean software and golden model
    (
      cd software
      make clean
      cd apps/baremetal
      make clean
    )

    # generate golden model for this matrix size
    python3 ./software/data/gendata_header.py \
      --app_name gemm_f16 \
      --type float16 \
      --defines "matrix_M=${M},matrix_N=${M},matrix_P=${M}" \
      --arrays __fp16:l2_X,__fp16:l2_W,__fp16:l2_Y,__fp16:l2_Z

    

    # now sweep HW parameters
    
    for NOUT in "${NUM_OUTSTANDING[@]}"; do
      for GF in "${GROUPING[@]}"; do
        for FIFO in "${FIFO_DEPTHS[@]}"; do

          # compile software
          (
            cd software/apps/baremetal
            config=tensorpool64 \
            matrix_size="${M}" \
            redmule_height="${RM}" \
            redmule_width="${RM}" \
            num_outstanding_transactions="${NOUT}" \
            fifo_depth="${FIFO}" \
            burst_greq="${GF}" \
            burst_grsp="${GF}" \
            make COMPILER=llvm opope_f16
          )

          echo ">>> Running sim with M=${M}, redmule=${RM}x${RM}, NOUT=${NOUT}, FIFO=${FIFO}"

          (
            cd hardware
            make clean
            config=tensorpool64 \
            matrix_size="${M}" \
            redmule_height="${RM}" \
            redmule_width="${RM}" \
            num_outstanding_transactions="${NOUT}" \
            fifo_depth="${FIFO}" \
            burst_greq="${GF}" \
            burst_grsp="${GF}" \
            app=opope_f16 \
            make sim
            

            # config=tensorpool64 \
            # matrix_size="${M}" \
            # redmule_height="${RM}" \
            # redmule_width="${RM}" \
            # num_outstanding_transactions="${NOUT}" \
            # fifo_depth="${FIFO}" \
            # burst_greq="${GF}" \
            # burst_grsp="${GF}" \
            # app=opope_f16 \
            # make trace

            # Optional: save traces/logs with unique names, e.g.:
            # outdir="../results/M${M}_RM${RM}_NOUT${NOUT}_FIFO${FIFO}"
            # mkdir -p "${outdir}"
            # mv trace.vcd "${outdir}/trace.vcd"
            # mv simc.log "${outdir}/simc.log"
          )
        done
      done
    done
    
  done
done

echo "All simulations completed."