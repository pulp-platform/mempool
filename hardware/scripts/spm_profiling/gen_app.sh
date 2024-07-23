#!/bin/bash

# Copyright 2021 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# APP_PATH="/usr/scratch2/larain1/zexifu/terapool_noc/mempool/software/bin"
APP_PATH="/usr/scratch2/larain1/zexifu/terapool_noc/mempool/software/apps/baremetal/double_buffer_2"
OUTPUT_PATH="/usr/scratch/larain4/zexifu/mempool/hardware"
CONFIGS="terapool"
NUM_CORES_PER_TILE="2 4 8"
NUM_REMOTE_PORTS_PER_TILE="2 3 5"


APPS="axpy \
      conv2d_i8 \
      convolution \
      dct \
      dotp \
      hello_world \
      malloc_test \
      matmul_i16 \
      matmul_i32 \
      matmul_i8 \
      matrix_mul \
      memcpy \
      synth \
      test_group_wu \
      tests \
      test_stackoverflow \
      test_tile_wu"

for config in $CONFIGS;
do
    for num_cores_per_tile in $NUM_CORES_PER_TILE;
    do
        rm -rf ${APP_PATH}/bin
        for app in $APPS;
        do
            config=${config} \
            num_cores_per_tile=${num_cores_per_tile} \
            make -C ${APP_PATH}/apps ${app}
        done
        rm -rf ${APP_PATH}/bin_${config}_c${num_cores_per_tile}
        mv ${APP_PATH}/bin ${APP_PATH}/bin_${config}_c${num_cores_per_tile}
    done
done
