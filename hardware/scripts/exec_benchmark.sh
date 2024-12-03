#!/usr/bin/env zsh

app=$1
config=$2
topology=$3

if config=terapool; then
  ulimit -n 2048
fi

source ~/miniconda3/etc/profile.d/conda.sh
conda activate mempool

make clean buildpath=build_${config}_${topology}/${app}
make compile config=$config topology=$topology buildpath=build_${config}_${topology}/${app}
make simc app=$app config=$config topology=$topology buildpath=build_${config}_${topology}/${app}
make trace result_dir=results/${config}_${topology}/${app} buildpath=build_${config}_${topology}/${app}
make clean buildpath=build_${config}_${topology}/${app}
python3 scripts/parse_result.py results/${config}_${topology}/${app}/avg.txt results/${config}_${topology}/${app}/avg.xlsx
