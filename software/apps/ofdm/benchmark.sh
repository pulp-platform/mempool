# Copyright 2022 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Marco Bertuletti, ETH Zurich

#!/bin/bash
# Benchmark shell script

DIR=$(dirname $(realpath “${BASH_SOURCE:-$0}”))
APP_DIR="$DIR/.."
HW_DIR="$DIR/../../../hardware"
APP="ofdm"

# NONBLOCKING
for len in "4 4" "8 4" "16 4"
do
  set -- $len
  DEFINES+="-DN_FFTs_ROW=${1} -DN_FFTs_COL=${2} -DDMA_NONBLOCKING" make $APP -C $APP_DIR
  app=ofdm make buildpath="build_ofdm" simcvcs -C $HW_DIR
  RES_DIR="$HW_DIR/results_ofdm/beamforming_${1}x${2}_nonblocking_2"
  make buildpath="build_ofdm" result_dir=$RES_DIR trace -C $HW_DIR
done

# BLOCKING
for len in "4 4" "8 4" "16 4"
do
  set -- $len
  DEFINES+="-DN_FFTs_ROW=${1} -DN_FFTs_COL=${2}" make $APP -C $APP_DIR
  app=ofdm make buildpath="build_ofdm" simcvcs -C $HW_DIR
  RES_DIR="$HW_DIR/results_ofdm/beamforming_${1}x${2}_blocking_2"
  make buildpath="build_ofdm" result_dir=$RES_DIR trace -C $HW_DIR
done
