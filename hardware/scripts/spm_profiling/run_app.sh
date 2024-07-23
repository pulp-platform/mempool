#!/bin/bash

# Copyright 2021 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# APP_PATH="/usr/scratch2/larain1/zexifu/terapool_noc/mempool/software/bin"
APP_PATH="/usr/scratch2/larain1/zexifu/terapool_noc/mempool/software/apps/baremetal/double_buffer_2"
OUTPUT_PATH="/usr/scratch/larain4/zexifu/mempool/hardware"
CONFIGS="terapool"
# NUM_CORES_PER_TILE="4 8"
# NUM_REMOTE_PORTS_PER_TILE="2 3 5"

NUM_CORES_PER_TILE="4"
NUM_REMOTE_PORTS_PER_TILE="3"


# APPS="axpy \
#       conv2d_i8 \
#       convolution \
#       dct \
#       dotp \
#       hello_world \
#       malloc_test \
#       matmul_i16 \
#       matmul_i32 \
#       matmul_i8 \
#       matrix_mul \
#       memcpy \
#       synth \
#       test_group_wu \
#       tests \
#       test_stackoverflow \
#       test_tile_wu"

# APPS="axpy \
#       conv2d_i8 \
#       convolution \
#       dct \
#       dotp \
#       hello_world \
#       matmul_i16 \
#       matmul_i32 \
#       matmul_i8 \
#       matrix_mul \
#       tests"

# APPS="axpy \
#       conv2d_i8 \
#       convolution \
#       dct \
#       dotp \
#       hello_world"

# APPS="matmul_i16 \
#       matmul_i32 \
#       matmul_i8 \
#       matrix_mul \
#       tests"

APPS="tests"

# APP_SUF="_240701_fixed_port_mapping_c8"
# APP_SUF="_240712_fixed_port_mapping_c8"
# APP_SUF="_240712_fixed_port_mapping_c8_p4"
# APP_SUF="_240712_fixed_port_mapping_c4_p4"
# APP_SUF="_240717_dyn_port_mapping_c4_p2"
# APP_SUF="_240718_dyn_port_remapbank_remaptile_c4_p2"
# APP_SUF="_240718_fix_port_remapbank_remaptile_c4_p2"
# APP_SUF="_240718_fix_port_remapbank_remaptile_c4_p4"
# APP_SUF="_240718_fix_port_remapbank_remaptile_c4_p2"
APP_SUF="_240719_fix_port_remapbank_remaptile_c4_p2_lsu16"

# APP_SUF="_240704_fixed_port_mapping_c8"
# APP_SUF="_240704_fixed_port_mapping_hashbank_sxm_c8"
# APP_SUF="_240703_dynam_port_mapping_hashbank_sx_c8"
# APP_SUF="_240701_dynport_hash"

spm_profiling="1"

# for config in $CONFIGS;
# do
#     for num_cores_per_tile in $NUM_CORES_PER_TILE;
#     do
#         rm -rf ${APP_PATH}/bin
#         for app in $APPS;
#         do
#             config=${config} \
#             num_cores_per_tile=${num_cores_per_tile} \
#             make -C ${APP_PATH}/apps ${app}
#         done
#         rm -rf ${APP_PATH}/bin_${config}_c${num_cores_per_tile}
#         mv ${APP_PATH}/bin ${APP_PATH}/bin_${config}_c${num_cores_per_tile}
#     done
# done

SIM="sim" #sim

for config in $CONFIGS;
do
    for num_cores_per_tile in $NUM_CORES_PER_TILE;
    do
        for num_remote_ports_per_tile in $NUM_REMOTE_PORTS_PER_TILE;
        do
            for app in $APPS;
            do
                case_name="${app}${APP_SUF}_${config}_c${num_cores_per_tile}_rp${num_remote_ports_per_tile}"
                build_name="${APP_SUF}_${config}_c${num_cores_per_tile}_rp${num_remote_ports_per_tile}"
                if [ -e "${APP_PATH}/bin_${config}_c${num_cores_per_tile}/${app}" ]; then
                    (
                        echo -e "[Start running app:${case_name}]"
                        rm -rf ${OUTPUT_PATH}/build_${case_name}
                        mkdir -p run_logs/${case_name}
                        # ../gen_xbar.py -in ${num_cores_per_tile} -on $((num_remote_ports_per_tile - 1)) -o ../../src/selector.sv
                        time app_path=${APP_PATH}/bin_${config}_c${num_cores_per_tile} \
                        app=${app} spm_profiling=${spm_profiling}\
                        app_suf=${APP_SUF}_${config}_c${num_cores_per_tile}_rp${num_remote_ports_per_tile} \
                        buildpath=${OUTPUT_PATH}/build_${case_name} \
                        config=${config} \
                        num_cores_per_tile=${num_cores_per_tile} \
                        num_remote_ports_per_tile=${num_remote_ports_per_tile} \
                        make -C ../../ ${SIM} \
                        1> run_logs/${case_name}/run_1.log \
                        2> run_logs/${case_name}/run_2.log
                        echo -e "[Done running app:${case_name}]"
                    ) 
                    sleep 3
                else
                    echo -e "[Can't find app:${APP_PATH}/bin_${config}_c${num_cores_per_tile}/${app}]"
                fi
            done
        done
    done
done
