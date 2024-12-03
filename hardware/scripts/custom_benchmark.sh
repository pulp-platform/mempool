#!/usr/bin/env zsh

# app_list=(axpy_i32 matmul_i32)
app_list=(matmul_i32)
# app_list=(axpy_i32)
# app_list=(cfft_radix2_q16 cfft_radix4_q16)
topology_list=(torus 2dmesh)

if [ -z "$1" ]; then
    config=terapool
else
    config=$1
fi

# Single thread version
# if config=terapool; then
#   ulimit -n 2048
# fi

# make clean
# make compile config=$config

# for app in $app_list; do
#   make simc app=$app config=$config
#   make trace result_dir=results/${config}_${app}
# done

# Multi threads version
for topology in $topology_list; do
  for app in $app_list; do
    screen -dmS ${config}_${topology}_${app} ./scripts/exec_benchmark.sh $app $config $topology
  done
done

# Remap test version
# make clean

# for app in $app_list; do
#   make compile config=$config spm_bank_id_remap=0 tile_id_remap=0
#   make simc app=$app config=$config spm_bank_id_remap=0 tile_id_remap=0
#   make trace result_dir=results/${config}_${app}

#   make compile config=$config spm_bank_id_remap=1 tile_id_remap=0
#   make simc app=$app config=$config spm_bank_id_remap=1 tile_id_remap=0
#   make trace result_dir=results/${config}_${app}_bankidremap

#   make compile config=$config spm_bank_id_remap=0 tile_id_remap=1
#   make simc app=$app config=$config spm_bank_id_remap=0 tile_id_remap=1
#   make trace result_dir=results/${config}_${app}_tileidremap

#   make compile config=$config spm_bank_id_remap=1 tile_id_remap=1
#   make simc app=$app config=$config spm_bank_id_remap=1 tile_id_remap=1
#   make trace result_dir=results/${config}_${app}_bankidremap_tileidremap
# done

