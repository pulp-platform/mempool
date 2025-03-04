#!/usr/bin/env zsh

# Copyright 2024 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

app=$1
config=$2

if [[ $config == *terapool* ]]; then
  ulimit -n 4096
fi

source ~/miniconda3/etc/profile.d/conda.sh
conda activate mempool

make clean buildpath=build_${config}/${app}
make compile config=$config buildpath=build_${config}/${app}
make simc app=$app config=$config buildpath=build_${config}/${app}
make trace config=$config result_dir=results/${config}/${app} buildpath=build_${config}/${app}
if [ -e build_${config}/${app}/noc_profiling ]; then
  cp -r build_${config}/${app}/noc_profiling results/${config}/${app}/
fi
make clean buildpath=build_${config}/${app}
python3 scripts/parse_result.py results/${config}/${app}/avg.txt results/${config}/${app}/avg.xlsx
