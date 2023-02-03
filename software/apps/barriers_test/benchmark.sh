# Copyright 2022 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Marco Bertuletti, ETH Zurich

#!/bin/bash
# Benchmark shell script

APP="barriers_test"
DIR=$(dirname $(realpath “${BASH_SOURCE:-$0}”))
APP_DIR="$DIR/.."
HW_DIR="$DIR/../../../hardware"

echo $APP_DIR
echo $HW_DIR

N_CORES=256
N_ITR=10


for max_delay in 64 128 256 512
do

  for (( c=1; c<=$N_ITR; c++ ))
  do
      echo "./data_barriers_test.py" -m ${max_delay} -n ${num_cores}
      "./data_barriers_test.py" -m ${max_delay} -n ${num_cores}
      make $APP -C $APP_DIR
      app=$APP make buildpath=build_barriers_test simcvcs -C $HW_DIR
      make buildpath=build_barriers_test resultpath=results_barriers_test trace -C $HW_DIR
  done

done
