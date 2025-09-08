# Copyright 2021 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

if {$config == {terapool}} {

  add wave -noupdate -group redmule[$1][$2][$3] -divider RedMulE_core
  add wave -noupdate -group redmule[$1][$2][$3] /mempool_tb/dut/i_mempool_cluster/gen_groups[$1]/gen_rtl_group/i_group/gen_sub_groups[$2]/gen_rtl_sg/i_sub_group/gen_tiles[$3]/gen_redmule_tile/i_tile/riscv_core/inst_addr_o
  add wave -noupdate -group redmule[$1][$2][$3] /mempool_tb/dut/i_mempool_cluster/gen_groups[$1]/gen_rtl_group/i_group/gen_sub_groups[$2]/gen_rtl_sg/i_sub_group/gen_tiles[$3]/gen_redmule_tile/i_tile/riscv_core/inst_data_i
  add wave -noupdate -group redmule[$1][$2][$3] /mempool_tb/dut/i_mempool_cluster/gen_groups[$1]/gen_rtl_group/i_group/gen_sub_groups[$2]/gen_rtl_sg/i_sub_group/gen_tiles[$3]/gen_redmule_tile/i_tile/riscv_core/inst_valid_o
  add wave -noupdate -group redmule[$1][$2][$3] /mempool_tb/dut/i_mempool_cluster/gen_groups[$1]/gen_rtl_group/i_group/gen_sub_groups[$2]/gen_rtl_sg/i_sub_group/gen_tiles[$3]/gen_redmule_tile/i_tile/riscv_core/inst_ready_i
  add wave -noupdate -group redmule[$1][$2][$3] -divider RedMulE
  add wave -noupdate -group redmule[$1][$2][$3] /mempool_tb/dut/i_mempool_cluster/gen_groups[$1]/gen_rtl_group/i_group/gen_sub_groups[$2]/gen_rtl_sg/i_sub_group/gen_tiles[$3]/gen_redmule_tile/i_tile/i_redmule_top/*
  add wave -noupdate -group redmule[$1][$2][$3] -divider RedMulE_ports
  add wave -noupdate -group redmule[$1][$2][$3] /mempool_tb/dut/i_mempool_cluster/gen_groups[$1]/gen_rtl_group/i_group/gen_sub_groups[$2]/gen_rtl_sg/i_sub_group/gen_tiles[$3]/gen_redmule_tile/i_tile/redmule_hwpe_req
  add wave -noupdate -group redmule[$1][$2][$3] /mempool_tb/dut/i_mempool_cluster/gen_groups[$1]/gen_rtl_group/i_group/gen_sub_groups[$2]/gen_rtl_sg/i_sub_group/gen_tiles[$3]/gen_redmule_tile/i_tile/redmule_hwpe_gnt
  add wave -noupdate -group redmule[$1][$2][$3] /mempool_tb/dut/i_mempool_cluster/gen_groups[$1]/gen_rtl_group/i_group/gen_sub_groups[$2]/gen_rtl_sg/i_sub_group/gen_tiles[$3]/gen_redmule_tile/i_tile/redmule_hwpe_add
  add wave -noupdate -group redmule[$1][$2][$3] /mempool_tb/dut/i_mempool_cluster/gen_groups[$1]/gen_rtl_group/i_group/gen_sub_groups[$2]/gen_rtl_sg/i_sub_group/gen_tiles[$3]/gen_redmule_tile/i_tile/redmule_hwpe_wen
  add wave -noupdate -group redmule[$1][$2][$3] /mempool_tb/dut/i_mempool_cluster/gen_groups[$1]/gen_rtl_group/i_group/gen_sub_groups[$2]/gen_rtl_sg/i_sub_group/gen_tiles[$3]/gen_redmule_tile/i_tile/redmule_hwpe_be
  add wave -noupdate -group redmule[$1][$2][$3] /mempool_tb/dut/i_mempool_cluster/gen_groups[$1]/gen_rtl_group/i_group/gen_sub_groups[$2]/gen_rtl_sg/i_sub_group/gen_tiles[$3]/gen_redmule_tile/i_tile/redmule_hwpe_data
  add wave -noupdate -group redmule[$1][$2][$3] /mempool_tb/dut/i_mempool_cluster/gen_groups[$1]/gen_rtl_group/i_group/gen_sub_groups[$2]/gen_rtl_sg/i_sub_group/gen_tiles[$3]/gen_redmule_tile/i_tile/redmule_hwpe_r_data
  add wave -noupdate -group redmule[$1][$2][$3] /mempool_tb/dut/i_mempool_cluster/gen_groups[$1]/gen_rtl_group/i_group/gen_sub_groups[$2]/gen_rtl_sg/i_sub_group/gen_tiles[$3]/gen_redmule_tile/i_tile/redmule_hwpe_r_valid

} else {

  add wave -noupdate -group redmule[$1][$2] -divider RedMulE_core
  add wave -noupdate -group redmule[$1][$2] /mempool_tb/dut/i_mempool_cluster/gen_groups[$1]/i_group/gen_tiles[$2]/gen_redmule_tile/i_tile/riscv_core/inst_addr_o
  add wave -noupdate -group redmule[$1][$2] /mempool_tb/dut/i_mempool_cluster/gen_groups[$1]/i_group/gen_tiles[$2]/gen_redmule_tile/i_tile/riscv_core/inst_data_i
  add wave -noupdate -group redmule[$1][$2] /mempool_tb/dut/i_mempool_cluster/gen_groups[$1]/i_group/gen_tiles[$2]/gen_redmule_tile/i_tile/riscv_core/inst_valid_o
  add wave -noupdate -group redmule[$1][$2] /mempool_tb/dut/i_mempool_cluster/gen_groups[$1]/i_group/gen_tiles[$2]/gen_redmule_tile/i_tile/riscv_core/inst_ready_i
  add wave -noupdate -group redmule[$1][$2] -divider RedMulE
  add wave -noupdate -group redmule[$1][$2] /mempool_tb/dut/i_mempool_cluster/gen_groups[$1]/i_group/gen_tiles[$2]/gen_redmule_tile/i_tile/i_redmule_top/*
  add wave -noupdate -group redmule[$1][$2] -divider RedMulE_ports
  add wave -noupdate -group redmule[$1][$2] /mempool_tb/dut/i_mempool_cluster/gen_groups[$1]/i_group/gen_tiles[$2]/gen_redmule_tile/i_tile/redmule_hwpe_req
  add wave -noupdate -group redmule[$1][$2] /mempool_tb/dut/i_mempool_cluster/gen_groups[$1]/i_group/gen_tiles[$2]/gen_redmule_tile/i_tile/redmule_hwpe_gnt
  add wave -noupdate -group redmule[$1][$2] /mempool_tb/dut/i_mempool_cluster/gen_groups[$1]/i_group/gen_tiles[$2]/gen_redmule_tile/i_tile/redmule_hwpe_add
  add wave -noupdate -group redmule[$1][$2] /mempool_tb/dut/i_mempool_cluster/gen_groups[$1]/i_group/gen_tiles[$2]/gen_redmule_tile/i_tile/redmule_hwpe_wen
  add wave -noupdate -group redmule[$1][$2] /mempool_tb/dut/i_mempool_cluster/gen_groups[$1]/i_group/gen_tiles[$2]/gen_redmule_tile/i_tile/redmule_hwpe_be
  add wave -noupdate -group redmule[$1][$2] /mempool_tb/dut/i_mempool_cluster/gen_groups[$1]/i_group/gen_tiles[$2]/gen_redmule_tile/i_tile/redmule_hwpe_data
  add wave -noupdate -group redmule[$1][$2] /mempool_tb/dut/i_mempool_cluster/gen_groups[$1]/i_group/gen_tiles[$2]/gen_redmule_tile/i_tile/redmule_hwpe_r_data
  add wave -noupdate -group redmule[$1][$2] /mempool_tb/dut/i_mempool_cluster/gen_groups[$1]/i_group/gen_tiles[$2]/gen_redmule_tile/i_tile/redmule_hwpe_r_valid

}

