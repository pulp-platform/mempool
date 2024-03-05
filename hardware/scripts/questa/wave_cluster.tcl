# Copyright 2021 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# Create cluster $1

add wave -noupdate -group cluster_[$1] -divider Parameters
add wave -noupdate -group cluster_[$1] mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/TCDMBaseAddr
add wave -noupdate -group cluster_[$1] mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/BootAddr
add wave -noupdate -group cluster_[$1] mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/NumDMAReq
add wave -noupdate -group cluster_[$1] -divider Signals
add wave -noupdate -group cluster_[$1] mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/clk_i
add wave -noupdate -group cluster_[$1] mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/rst_ni
add wave -noupdate -group cluster_[$1] mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/axi_mst_req_o
add wave -noupdate -group cluster_[$1] mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/axi_mst_resp_i
add wave -noupdate -group cluster_[$1] mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/ro_cache_ctrl_i
add wave -noupdate -group cluster_[$1] mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/dma_*
