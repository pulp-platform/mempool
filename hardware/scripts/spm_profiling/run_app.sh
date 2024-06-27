#!/bin/bash

# Copyright 2021 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# APP_PATH="/usr/scratch2/larain1/zexifu/terapool_noc/mempool/software/bin"
APP_PATH="/usr/scratch2/larain1/zexifu/terapool_noc/mempool/software/apps/baremetal/double_buffer_2/bin"

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


APP_SUF="_test"

for app in $APPS;
do
    (
        echo -e "[Start running app:${app}${APP_SUF}]"
	    mkdir -p run_logs/${app}${APP_SUF}
        time app_path=${APP_PATH} \
        app=${app} app_suf=${APP_SUF} buildpath=build_${app}${APP_SUF} \
        make -C ../../ simc \
        1> run_logs/${app}${APP_SUF}/run_1.log \
        2> run_logs/${app}${APP_SUF}/run_2.log
        echo -e "[Done running app:${app}${APP_SUF}]"
    ) &
    sleep 1
done
