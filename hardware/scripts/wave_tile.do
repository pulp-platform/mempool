# Create group for tile $1

add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/NumBanksPerTile
add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/NumTiles
add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/NumBanks
add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/TCDMBaseAddr
add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/BootAddr
add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/ICacheSizeByte
add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/ICacheSets
add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/ICacheLineWidth
add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/NumCores
add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/TileAddrWidth
add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/TCDMSize
add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/TCDMMask
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/clk_i
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/rst_ni
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/scan_enable_i
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/scan_data_i
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/scan_data_o
add wave -noupdate -group Tile_[$1] -radix unsigned /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/tile_id_i

add wave -noupdate -group Tile_[$1] -divider TCDM
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/tcdm_master_*
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/tcdm_slave_*
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/axi_*
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/refill_*
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/snitch_inst_*
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/snitch_data_*
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/bank_req_*
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/bank_resp_*
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/postreg_tcdm_slave_req_*
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/prereg_tcdm_slave_resp_*
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/prereg_tcdm_master_req_*
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/postreg_tcdm_master_resp_*
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/local_master_xbar_*
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/local_slave_xbar_*
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/soc_data_*
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/mask_map
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/soc_req_o
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/soc_resp_i
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/soc_qvalid
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/soc_qready
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/soc_pvalid
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/soc_pready
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/axi_mst_req
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/axi_mst_resp

for {set i 0} {$i < 16} {incr i} {
	add wave -noupdate -group Tile_[$1] -group tcdm_adapter[$i] /mempool_tb/dut/gen_tiles[$1]/i_tile/i_tile/gen_banks[$i]/i_tcdm_adapter/*
}
