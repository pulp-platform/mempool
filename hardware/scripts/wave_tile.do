# Create group for tile $1

add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/NumCoresPerTile
add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/NumBanksPerTile
add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/NumTiles
add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/NumBanks
add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/TCDMBaseAddr
add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/TCDMSizePerBank
add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/BootAddr
add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/ICacheSizeByte
add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/ICacheSets
add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/ICacheLineWidth
add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/NumCores
add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/TCDMAddrMemWidth
add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/TileAddrWidth
add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/LocalXbarAddrWidth
add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/TCDMSize
add wave -noupdate -group Tile_[$1] -group Params /mempool_tb/dut/gen_tiles[$1]/i_tile/TCDMMask
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/clk_i
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/rst_ni
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/scan_enable_i
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/scan_data_i
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/scan_data_o
add wave -noupdate -group Tile_[$1] -radix unsigned /mempool_tb/dut/gen_tiles[$1]/i_tile/tile_id_i

add wave -noupdate -group Tile_[$1] -divider TCDM
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/tcdm_master_*
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/tcdm_slave_*
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/axi_*
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/refill_qaddr_o
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/refill_qlen_o
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/refill_qvalid_o
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/refill_qready_i
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/refill_pdata_i
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/refill_perror_i
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/refill_pvalid_i
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/refill_plast_i
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/refill_pready_o
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/snitch_inst_addr
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/snitch_inst_data
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/snitch_inst_valid
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/snitch_inst_ready
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/snitch_data_qaddr
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/snitch_data_qwrite
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/snitch_data_qamo
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/snitch_data_qdata
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/snitch_data_qstrb
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/snitch_data_qvalid
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/snitch_data_qready
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/snitch_data_pdata
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/snitch_data_perror
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/snitch_data_pvalid
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/snitch_data_pready
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/bank_req_valid
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/bank_req_ready
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/bank_req_tgt_addr
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/bank_req_ini_addr
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/bank_req_wen
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/bank_req_payload
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/bank_req_be
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/bank_resp_valid
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/bank_resp_ready
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/bank_resp_payload
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/bank_resp_ini_addr
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/postreg_tcdm_slave_req_valid
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/postreg_tcdm_slave_req_ready
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/postreg_tcdm_slave_req_tgt_addr
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/postreg_tcdm_slave_req_wen
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/postreg_tcdm_slave_req_payload
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/postreg_tcdm_slave_req_be
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/prereg_tcdm_slave_resp_valid
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/prereg_tcdm_slave_resp_ready
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/prereg_tcdm_slave_resp_payload
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/local_xbar_*
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/soc_data_q
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/soc_data_qvalid
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/soc_data_qready
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/soc_data_p
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/soc_data_pvalid
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/soc_data_pready
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/mask_map
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/soc_req_o
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/soc_resp_i
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/soc_qvalid
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/soc_qready
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/soc_pvalid
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/soc_pready
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/axi_mst_req
add wave -noupdate -group Tile_[$1] /mempool_tb/dut/gen_tiles[$1]/i_tile/axi_mst_resp
