# Copyright 2021 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# Create group for group $1 tile $2

add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/clk_i
delete_group -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/clk_i
add_wave -group group_\[$1\]|Tile_\[$2\]|Params mempool_pkg::NumBanksPerTile
add_wave -group group_\[$1\]|Tile_\[$2\]|Params mempool_pkg::NumTiles
add_wave -group group_\[$1\]|Tile_\[$2\]|Params mempool_pkg::NumBanks
add_wave -group group_\[$1\]|Tile_\[$2\]|Params /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/TCDMBaseAddr
add_wave -group group_\[$1\]|Tile_\[$2\]|Params /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/BootAddr
add_wave -group group_\[$1\]|Tile_\[$2\]|Params /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_caches\[0\].i_snitch_icache.LINE_WIDTH
add_wave -group group_\[$1\]|Tile_\[$2\]|Params /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_caches\[0\].i_snitch_icache.LINE_COUNT
add_wave -group group_\[$1\]|Tile_\[$2\]|Params /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_caches\[0\].i_snitch_icache.SET_COUNT
add_wave -group group_\[$1\]|Tile_\[$2\]|Params mempool_pkg::ICacheLineWidth
add_wave -group group_\[$1\]|Tile_\[$2\]|Params mempool_pkg::ICacheSizeByte
add_wave -group group_\[$1\]|Tile_\[$2\]|Params mempool_pkg::ICacheSets
add_wave -group group_\[$1\]|Tile_\[$2\]|Params mempool_pkg::NumCores
add_wave -group group_\[$1\]|Tile_\[$2\]|Params /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/TCDMSize
add_wave -group group_\[$1\]|Tile_\[$2\]|Params /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/TCDMMask
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/clk_i
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/rst_ni
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/scan_enable_i
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/scan_data_i
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/scan_data_o
add_wave -group group_\[$1\]|Tile_\[$2\] -radix unsigned /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/tile_id_i

add_wave -group group_\[$1\]|Tile_\[$2\] -divider TCDM
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/tcdm_master_*
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/tcdm_slave_*
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/axi_*
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/refill_*
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/snitch_inst_*
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/snitch_data_*
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/bank_req_*
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/bank_resp_*
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/postreg_tcdm_slave_req_*
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/prereg_tcdm_slave_resp_*
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/prereg_tcdm_master_req_*
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/postreg_tcdm_master_resp_*
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/remote_req_*
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/remote_resp_*
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/local_req_*
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/local_resp_*
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/soc_data_*
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/mask_map
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/soc_req_o
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/soc_resp_i
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/soc_qvalid
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/soc_qready
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/soc_pvalid
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/soc_pready
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/axi_mst_req
add_wave -group group_\[$1\]|Tile_\[$2\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/axi_mst_resp

for {set i 0} {$i < 16} {incr i} {
	add_wave -group group_\[$1\]|Tile_\[$2\]|tcdm_adapter\[$i\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$1\]/i_group/gen_tiles\[$2\]/i_tile/i_tile/gen_banks\[$i\]/i_tcdm_adapter/*
}
