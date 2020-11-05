#! /bin/tcsh -x

## Adjust this path to match your local environment
set PULP_BASE_PATH=~/scratch/zc706/big.pulp
set AXI4LITE_VIP_PATH=~/scratch/zc706

## Set variables
set VER=10.6b
set LIB=rtl
set DESIGN=rab
set LOG=${DESIGN}.log

set PULP_SOC_DEFINES_PATH=
set PULP_INTERFACE_PATH=${PULP_BASE_PATH}/fe/rtl/components
set FP_DEFINES_PATH=${PULP_BASE_PATH}/fe/rtl/includes

# Path for all RAB components
set IPS_SOURCE_PATH=${PULP_BASE_PATH}/fe/ips
set PULP_SOC_SOURCE_PATH=${PULP_BASE_PATH}/fe/rtl/pulp_soc
set FPGA_IPS_SOURCE_PATH=${PULP_BASE_PATH}/fpga/ips

set INC_PATHS=${PULP_SOC_DEFINES_PATH}+${PULP_INTERFACE_PATH}+${IPS_SOURCE_PATH}/axi/axi_rab+${FP_DEFINES_PATH}

## Clean up the log before recompiling
if (-e $LOG) then
 rm $LOG
endif

## Clean up the library before recompiling
if (-e $LIB) then
 rm -rf $LIB
endif
 
## make new library
vlib-${VER} $LIB

## Start the log file
echo -n "** Compilation using modelsim version: $VER of ${DESIGN} from: " >> ${LOG}
date                                                                      >> ${LOG}
 
## Compile sources
# Generic FIFO
vlog-${VER}  -work $LIB +incdir+${INC_PATHS} +define+PULP_FPGA_EMUL=1 ${IPS_SOURCE_PATH}/common_cells/generic_fifo.sv >> ${LOG}

# Packages
vlog-${VER}  -work $LIB ${PULP_BASE_PATH}/fe/rtl/packages/CfMath.sv                                >> ${LOG}

# ID remap
vlog-${VER}  -work $LIB  +incdir+${INC_PATHS} ${IPS_SOURCE_PATH}/axi/axi_id_remap/ID_Gen_1.sv      >> ${LOG}
vlog-${VER}  -work $LIB  +incdir+${INC_PATHS} ${IPS_SOURCE_PATH}/axi/axi_id_remap/ID_Gen_4.sv      >> ${LOG}
vlog-${VER}  -work $LIB  +incdir+${INC_PATHS} ${IPS_SOURCE_PATH}/axi/axi_id_remap/ID_Gen_16.sv     >> ${LOG}
vlog-${VER}  -work $LIB  +incdir+${INC_PATHS} ${IPS_SOURCE_PATH}/axi/axi_id_remap/ID_Gen_64.sv     >> ${LOG}
vlog-${VER}  -work $LIB  +incdir+${INC_PATHS} ${IPS_SOURCE_PATH}/axi/axi_id_remap/axi_id_remap.sv  >> ${LOG}
vlog-${VER}  -work $LIB  +incdir+${INC_PATHS} ${PULP_SOC_SOURCE_PATH}/axi_id_remap_wrap.sv         >> ${LOG}

# RAB
vlog-${VER}  -work $LIB  ${IPS_SOURCE_PATH}/axi/axi_rab/rtl/rab_slice.sv                           >> ${LOG}
vlog-${VER}  -work $LIB  ${IPS_SOURCE_PATH}/axi/axi_rab/rtl/slice_top.sv                           >> ${LOG}
vlog-${VER}  -work $LIB  ${IPS_SOURCE_PATH}/axi/axi_rab/rtl/fsm.sv                                 >> ${LOG}
vlog-${VER}  -work $LIB  ${IPS_SOURCE_PATH}/axi/axi_rab/rtl/axi_rab_cfg.sv                         >> ${LOG}

vlog-${VER}  -work $LIB  ${IPS_SOURCE_PATH}/axi/axi_rab/rtl/axi_rab_cfg.sv                         >> ${LOG}
vlog-${VER}  -work $LIB  ${IPS_SOURCE_PATH}/axi/axi_rab/rtl/axi_buffer_rab.sv                      >> ${LOG}
vlog-${VER}  -work $LIB  ${IPS_SOURCE_PATH}/axi/axi_rab/rtl/axi_buffer_rab_bram.sv                 >> ${LOG}
vlog-${VER}  -work $LIB  ${IPS_SOURCE_PATH}/axi/axi_rab/rtl/axi4_ar_buffer.sv                      >> ${LOG}
vlog-${VER}  -work $LIB  ${IPS_SOURCE_PATH}/axi/axi_rab/rtl/axi4_aw_buffer.sv                      >> ${LOG}
vlog-${VER}  -work $LIB  ${IPS_SOURCE_PATH}/axi/axi_rab/rtl/axi4_w_buffer.sv                       >> ${LOG}
vlog-${VER}  -work $LIB  ${IPS_SOURCE_PATH}/axi/axi_rab/rtl/axi4_r_buffer.sv                       >> ${LOG}
vlog-${VER}  -work $LIB  ${IPS_SOURCE_PATH}/axi/axi_rab/rtl/axi4_b_buffer.sv                       >> ${LOG}
vlog-${VER}  -work $LIB  +incdir+${INC_PATHS} ${IPS_SOURCE_PATH}/axi/axi_rab/rtl/axi4_aw_sender.sv >> ${LOG}
vlog-${VER}  -work $LIB  +incdir+${INC_PATHS} ${IPS_SOURCE_PATH}/axi/axi_rab/rtl/axi4_ar_sender.sv >> ${LOG}
vlog-${VER}  -work $LIB  +incdir+${INC_PATHS} ${IPS_SOURCE_PATH}/axi/axi_rab/rtl/axi4_w_sender.sv  >> ${LOG}
vlog-${VER}  -work $LIB  +incdir+${INC_PATHS} ${IPS_SOURCE_PATH}/axi/axi_rab/rtl/axi4_r_sender.sv  >> ${LOG}
vlog-${VER}  -work $LIB  +incdir+${INC_PATHS} ${IPS_SOURCE_PATH}/axi/axi_rab/rtl/axi4_b_sender.sv  >> ${LOG}

vlog-${VER}  -work $LIB  ${IPS_SOURCE_PATH}/axi/axi_rab/rtl/ram_tp_no_change.sv                    >> ${LOG}
vlog-${VER}  -work $LIB  ${IPS_SOURCE_PATH}/axi/axi_rab/rtl/ram_tp_write_first.sv                  >> ${LOG}
vlog-${VER}  -work $LIB  ${IPS_SOURCE_PATH}/axi/axi_rab/rtl/check_ram.sv                           >> ${LOG}
vlog-${VER}  -work $LIB  +incdir+${INC_PATHS} ${IPS_SOURCE_PATH}/axi/axi_rab/rtl/l2_tlb.sv         >> ${LOG}

vlog-${VER}  -work $LIB  +incdir+${INC_PATHS} ${IPS_SOURCE_PATH}/fpga-support/rtl/BramPort.sv      >> ${LOG}
vlog-${VER}  -work $LIB  +incdir+${INC_PATHS} ${IPS_SOURCE_PATH}/fpga-support/rtl/TdpBramArray.sv  >> ${LOG}
vlog-${VER}  -work $LIB  +incdir+${INC_PATHS} ${IPS_SOURCE_PATH}/fpga-support/rtl/BramDwc.sv       >> ${LOG}
vlog-${VER}  -work $LIB  +incdir+${INC_PATHS} ${IPS_SOURCE_PATH}/fpga-support/rtl/BramLogger.sv    >> ${LOG}
vlog-${VER}  -work $LIB  +incdir+${INC_PATHS} ${IPS_SOURCE_PATH}/fpga-support/rtl/AxiBramLogger.sv >> ${LOG}

vlog-${VER}  -work $LIB  +incdir+${INC_PATHS} ${IPS_SOURCE_PATH}/axi/axi_rab/rtl/rab_core.sv       >> ${LOG}
vlog-${VER}  -work $LIB  +incdir+${INC_PATHS} ${IPS_SOURCE_PATH}/axi/axi_rab/rtl/axi_rab_top.sv    >> ${LOG}

vlog-${VER}  -work $LIB  +incdir+${INC_PATHS} ./axi_rab_wrap_tb.sv                                 >> ${LOG}
 
# Traffic Generators
vlog-${VER}  -work $LIB ${AXI4LITE_VIP_PATH}/axi4lite_vip/verification_ip/axi4lite_m_if.sv         >> ${LOG}
vlog-${VER}  -work $LIB ${AXI4LITE_VIP_PATH}/axi4lite_vip/verification_ip/axi4lite_m.sv            >> ${LOG}
vlog-${VER}  -work $LIB ${AXI4LITE_VIP_PATH}/axi4lite_vip/examples/testbench/packet.sv             >> ${LOG}
vlog-${VER}  -work $LIB +incdir+../TGEN_RAB/TGEN/traffic_pattern ../TGEN_RAB/TGEN/TGEN.sv          >> ${LOG}
vlog-${VER}  -work $LIB +incdir+../TGEN_RAB/TGEN/traffic_pattern +incdir+${INC_PATHS}  ../TGEN_RAB/TGEN/TGEN_wrap.sv >> ${LOG}

# AXI memory
vlog-${VER}  -work $LIB ${IPS_SOURCE_PATH}/axi/axi_slice/axi_ar_buffer.sv >> ${LOG}
vlog-${VER}  -work $LIB ${IPS_SOURCE_PATH}/axi/axi_slice/axi_aw_buffer.sv >> ${LOG}
vlog-${VER}  -work $LIB ${IPS_SOURCE_PATH}/axi/axi_slice/axi_b_buffer.sv  >> ${LOG}
vlog-${VER}  -work $LIB ${IPS_SOURCE_PATH}/axi/axi_slice/axi_r_buffer.sv  >> ${LOG}
vlog-${VER}  -work $LIB ${IPS_SOURCE_PATH}/axi/axi_slice/axi_w_buffer.sv  >> ${LOG}

vlog-${VER}  -work $LIB ${PULP_BASE_PATH}/fe/rtl/components/generic_memory.sv
vlog-${VER}  -work $LIB ${IPS_SOURCE_PATH}/axi/axi_mem_if/axi_mem_if.sv
vlog-${VER}  -work $LIB ${PULP_SOC_SOURCE_PATH}/axi_mem_if_wrap.sv
vlog-${VER}  -work $LIB +incdir+${INC_PATHS} ${PULP_SOC_SOURCE_PATH}/l2_generic.sv
vlog-${VER}  -work $LIB +define+PULP_FPGA_SIM=1 ${PULP_SOC_SOURCE_PATH}/l2_mem.sv

# testbench
vlog-${VER}  -work $LIB +incdir+${INC_PATHS}  ./test.sv         >> ${LOG}
vlog-${VER}  -work $LIB +incdir+${INC_PATHS}  ./${DESIGN}_tb.sv >> ${LOG}
