# Copyright 2022 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Author: Marco Bertuletti, ETH Zurich

#!/bin/bash
# Benchmark shell script

axis=0

APP="matmul_f32"
DIR=$(dirname $(realpath “${BASH_SOURCE:-$0}”))
APP_DIR="$DIR/.."
HW_DIR="$DIR/../../../hardware"

gcc=$GCC_INSTALL_DIR
my_gcc="/home/mbertuletti/.local/bin/riscv"

echo $APP_DIR
echo $HW_DIR


for dim in "64 32 64" "128 32 128" "128 128 128" "256 128 256"; do

    read -a dims <<< "$dim"
    echo "m = ${dims[0]}"
    echo "n = ${dims[1]}"
    echo "p = ${dims[2]}"

    echo "./data_matmulf32.py" -m ${dims[0]} -n ${dims[1]} -p ${dims[2]}
    "./data_matmulf32.py" -m ${dims[0]} -n ${dims[1]} -p ${dims[2]}
    GCC_INSTALL_DIR=$my_gcc make $APP -C $APP_DIR
    GCC_INSTALL_DIR=$gcc app=$APP make buildpath=build_matmulf32 simcvcs -C $HW_DIR
    make buildpath=build_matmulf32 resultpath=results_matmulf32 trace -C $HW_DIR
done
