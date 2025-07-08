#!/usr/bin/env zsh

# Copyright 2024 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

app=$1
config=$2
workdir=$3
buildpath=build_${workdir}
result_dir=results/${workdir}

ulimit -n 4096

source /usr/local/anaconda3/etc/profile.d/conda.sh
conda activate /home/sem24h30/miniconda3/envs/terapool_noc

eval make clean buildpath=${buildpath}
eval make simcvcs app=${app} $config buildpath=${buildpath}
eval make trace $config result_dir=${result_dir} buildpath=${buildpath}
if [ -e ${buildpath}/noc_profiling ]; then
  eval cp -r ${buildpath}/noc_profiling ${result_dir}
fi
eval make clean buildpath=${buildpath}
