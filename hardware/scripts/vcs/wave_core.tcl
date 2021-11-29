# Copyright 2021 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# Create group for core $3 from group $1 tile $2 (core_id=NUM_CORES_PER_group*$1+NUM_CORES_PER_TILE*$2+$3)

add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/clk_i
delete_group -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/clk_i
add_wave -group core\[$1\]\[$2\]\[$3\]|Params /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/BootAddr
add_wave -group core\[$1\]\[$2\]\[$3\]|Params /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/MTVEC
add_wave -group core\[$1\]\[$2\]\[$3\]|Params /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/RVE
add_wave -group core\[$1\]\[$2\]\[$3\]|Params /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/RVM
add_wave -group core\[$1\]\[$2\]\[$3\]|Params /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/RegisterOffloadReq
add_wave -group core\[$1\]\[$2\]\[$3\]|Params /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/RegisterOffloadResp
add_wave -group core\[$1\]\[$2\]\[$3\]|Params /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/RegisterTCDMReq
add_wave -group core\[$1\]\[$2\]\[$3\]|Params /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/RegisterTCDMResp
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/clk_i
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/rst_i
add_wave -group core\[$1\]\[$2\]\[$3\] -radix unsigned /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/hart_id_i

add_wave -group core\[$1\]\[$2\]\[$3\] -divider Instructions
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/inst_addr_o
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/inst_data_i
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/inst_valid_o
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/inst_ready_i

add_wave -group core\[$1\]\[$2\]\[$3\] -divider Load/Store
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/data_qaddr_o
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/data_qwrite_o
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/data_qamo_o
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/data_qdata_o
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/data_qstrb_o
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/data_qvalid_o
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/data_qready_i
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/data_pdata_i
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/data_perror_i
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/data_pvalid_i
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/data_pready_o

add_wave -group core\[$1\]\[$2\]\[$3\] -divider Accelerator
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/acc_qaddr_o
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/acc_qid_o
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/acc_qdata_op_o
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/acc_qdata_arga_o
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/acc_qdata_argb_o
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/acc_qdata_argc_o
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/acc_qvalid_o
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/acc_qready_i
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/acc_pdata_i
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/acc_pid_i
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/acc_perror_i
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/acc_pvalid_i
add_wave -group core\[$1\]\[$2\]\[$3\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/acc_pready_o

add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/illegal_inst
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/stall
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/lsu_stall
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/acc_stall
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/zero_lsb
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/pc_d
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/pc_q
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/wfi_d
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/wfi_q
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/wake_up_sync_i
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/wake_up_d
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/wake_up_q
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal -divider LSU
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/ls_size
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/ls_amo
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/ld_result
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/lsu_qready
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/lsu_qvalid
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/lsu_pvalid
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/lsu_pready
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/lsu_rd
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/retire_load
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/retire_i
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/retire_acc
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal -divider ALU
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/opa
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/opb
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/iimm
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/uimm
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/jimm
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/bimm
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/simm
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/adder_result
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/alu_result
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/rd
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/rs1
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/rs2
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/gpr_raddr
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/gpr_rdata
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/gpr_waddr
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/gpr_wdata
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/gpr_we
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/consec_pc
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/sb_d
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/sb_q
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/is_load
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/is_store
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/is_signed
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/is_fp_load
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/is_fp_store
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/ls_misaligned
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/ld_addr_misaligned
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/st_addr_misaligned
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/valid_instr
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/exception
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/alu_op
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/opa_select
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/opb_select
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/write_rd
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/uses_rd
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/next_pc
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/rd_select
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/rd_bypass
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/is_branch
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/csr_rvalue
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/csr_en
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/cycle_q
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/instret_q
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/acc_register_rd
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/operands_ready
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/dst_ready
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/opa_ready
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/opb_ready
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/shift_opa
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/shift_opa_reversed
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/shift_right_result
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/shift_left_result
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/shift_opa_ext
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/shift_right_result_ext
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/shift_left
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/shift_arithmetic
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/alu_opa
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/alu_opb
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/alu_writeback
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/csr_trace_q
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/csr_trace_en
add_wave -group core\[$1\]\[$2\]\[$3\]|Internal /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_cores\[$3\]/gen_mempool_cc/riscv_core/i_snitch/core_events_o
