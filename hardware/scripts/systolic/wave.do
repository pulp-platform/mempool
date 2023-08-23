onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /mempool_tb/wfi
add wave -noupdate -expand -group {core[0][0][0]} -group Params {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/BootAddr}
add wave -noupdate -expand -group {core[0][0][0]} -group Params {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/MTVEC}
add wave -noupdate -expand -group {core[0][0][0]} -group Params {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/RVE}
add wave -noupdate -expand -group {core[0][0][0]} -group Params {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/RVM}
add wave -noupdate -expand -group {core[0][0][0]} -group Params {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/RegisterOffloadReq}
add wave -noupdate -expand -group {core[0][0][0]} -group Params {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/RegisterOffloadResp}
add wave -noupdate -expand -group {core[0][0][0]} -group Params {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/RegisterTCDMReq}
add wave -noupdate -expand -group {core[0][0][0]} -group Params {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/RegisterTCDMResp}
add wave -noupdate -expand -group {core[0][0][0]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/clk_i}
add wave -noupdate -expand -group {core[0][0][0]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/rst_i}
add wave -noupdate -expand -group {core[0][0][0]} -radix unsigned {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/hart_id_i}
add wave -noupdate -expand -group {core[0][0][0]} -divider Stalls
add wave -noupdate -expand -group {core[0][0][0]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/stall}
add wave -noupdate -expand -group {core[0][0][0]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/illegal_inst}
add wave -noupdate -expand -group {core[0][0][0]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/lsu_stall}
add wave -noupdate -expand -group {core[0][0][0]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/acc_stall}
add wave -noupdate -expand -group {core[0][0][0]} -divider QLR
add wave -noupdate -expand -group {core[0][0][0]} -expand -group {IQLR Start} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/gen_qlrs[0]/i_qlr/iqlr_start}
add wave -noupdate -expand -group {core[0][0][0]} -expand -group {IQLR Start} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/gen_qlrs[1]/i_qlr/iqlr_start}
add wave -noupdate -expand -group {core[0][0][0]} -expand -group {IQLR Start} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/gen_qlrs[2]/i_qlr/iqlr_start}
add wave -noupdate -expand -group {core[0][0][0]} -expand -group {IQLR Start} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/gen_qlrs[3]/i_qlr/iqlr_start}
add wave -noupdate -expand -group {core[0][0][0]} -expand -group {OQLR Start} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/gen_qlrs[3]/i_qlr/oqlr_start}
add wave -noupdate -expand -group {core[0][0][0]} -expand -group {OQLR Start} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/gen_qlrs[2]/i_qlr/oqlr_start}
add wave -noupdate -expand -group {core[0][0][0]} -expand -group {OQLR Start} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/gen_qlrs[1]/i_qlr/oqlr_start}
add wave -noupdate -expand -group {core[0][0][0]} -expand -group {OQLR Start} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/gen_qlrs[0]/i_qlr/oqlr_start}
add wave -noupdate -expand -group {core[0][0][0]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/sb}
add wave -noupdate -expand -group {core[0][0][0]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/data_qamo_o}
add wave -noupdate -expand -group {core[0][0][0]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/lsu_out_qlr_o}
add wave -noupdate -expand -group {core[0][0][0]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/lsu_out_valid_o}
add wave -noupdate -expand -group {core[0][0][0]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/lsu_out_ready_i}
add wave -noupdate -expand -group {core[0][0][0]} -expand {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/qlr_sb_enabled}
add wave -noupdate -expand -group {core[0][0][0]} -expand {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/qlr_sb}
add wave -noupdate -expand -group {core[0][0][0]} -color Gold {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/gen_qlrs[3]/i_qlr/fifo_full}
add wave -noupdate -expand -group {core[0][0][0]} -color Gold {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/gen_qlrs[2]/i_qlr/fifo_full}
add wave -noupdate -expand -group {core[0][0][0]} -color Gold {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/gen_qlrs[1]/i_qlr/fifo_full}
add wave -noupdate -expand -group {core[0][0][0]} -color Gold {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/gen_qlrs[0]/i_qlr/fifo_full}
add wave -noupdate -expand -group {core[0][0][0]} -expand {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/qlr_ready}
add wave -noupdate -expand -group {core[0][0][0]} -divider Instructions
add wave -noupdate -expand -group {core[0][0][0]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/inst_addr_o}
add wave -noupdate -expand -group {core[0][0][0]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/inst_data_i}
add wave -noupdate -expand -group {core[0][0][0]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/inst_valid_o}
add wave -noupdate -expand -group {core[0][0][0]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[0]/gen_mempool_cc/riscv_core/i_snitch/inst_ready_i}

onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /mempool_tb/wfi
add wave -noupdate -expand -group {core[0][0][1]} -group Params {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/BootAddr}
add wave -noupdate -expand -group {core[0][0][1]} -group Params {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/MTVEC}
add wave -noupdate -expand -group {core[0][0][1]} -group Params {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/RVE}
add wave -noupdate -expand -group {core[0][0][1]} -group Params {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/RVM}
add wave -noupdate -expand -group {core[0][0][1]} -group Params {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/RegisterOffloadReq}
add wave -noupdate -expand -group {core[0][0][1]} -group Params {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/RegisterOffloadResp}
add wave -noupdate -expand -group {core[0][0][1]} -group Params {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/RegisterTCDMReq}
add wave -noupdate -expand -group {core[0][0][1]} -group Params {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/RegisterTCDMResp}
add wave -noupdate -expand -group {core[0][0][1]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/clk_i}
add wave -noupdate -expand -group {core[0][0][1]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/rst_i}
add wave -noupdate -expand -group {core[0][0][1]} -radix unsigned {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/hart_id_i}
add wave -noupdate -expand -group {core[0][0][1]} -divider Stalls
add wave -noupdate -expand -group {core[0][0][1]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/stall}
add wave -noupdate -expand -group {core[0][0][1]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/illegal_inst}
add wave -noupdate -expand -group {core[0][0][1]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/lsu_stall}
add wave -noupdate -expand -group {core[0][0][1]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/acc_stall}
add wave -noupdate -expand -group {core[0][0][1]} -divider QLR
add wave -noupdate -expand -group {core[0][0][1]} -expand -group {IQLR Start} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/gen_qlrs[0]/i_qlr/iqlr_start}
add wave -noupdate -expand -group {core[0][0][1]} -expand -group {IQLR Start} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/gen_qlrs[1]/i_qlr/iqlr_start}
add wave -noupdate -expand -group {core[0][0][1]} -expand -group {IQLR Start} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/gen_qlrs[2]/i_qlr/iqlr_start}
add wave -noupdate -expand -group {core[0][0][1]} -expand -group {IQLR Start} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/gen_qlrs[3]/i_qlr/iqlr_start}
add wave -noupdate -expand -group {core[0][0][1]} -expand -group {OQLR Start} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/gen_qlrs[3]/i_qlr/oqlr_start}
add wave -noupdate -expand -group {core[0][0][1]} -expand -group {OQLR Start} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/gen_qlrs[2]/i_qlr/oqlr_start}
add wave -noupdate -expand -group {core[0][0][1]} -expand -group {OQLR Start} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/gen_qlrs[1]/i_qlr/oqlr_start}
add wave -noupdate -expand -group {core[0][0][1]} -expand -group {OQLR Start} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/gen_qlrs[0]/i_qlr/oqlr_start}
add wave -noupdate -expand -group {core[0][0][1]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/sb}
add wave -noupdate -expand -group {core[0][0][1]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/data_qamo_o}
add wave -noupdate -expand -group {core[0][0][1]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/lsu_out_qlr_o}
add wave -noupdate -expand -group {core[0][0][1]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/lsu_out_valid_o}
add wave -noupdate -expand -group {core[0][0][1]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/lsu_out_ready_i}
add wave -noupdate -expand -group {core[0][0][1]} -expand {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/qlr_sb_enabled}
add wave -noupdate -expand -group {core[0][0][1]} -expand {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/qlr_sb}
add wave -noupdate -expand -group {core[0][0][1]} -color Gold {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/gen_qlrs[3]/i_qlr/fifo_full}
add wave -noupdate -expand -group {core[0][0][1]} -color Gold {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/gen_qlrs[2]/i_qlr/fifo_full}
add wave -noupdate -expand -group {core[0][0][1]} -color Gold {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/gen_qlrs[1]/i_qlr/fifo_full}
add wave -noupdate -expand -group {core[0][0][1]} -color Gold {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/gen_qlr_group/i_qlr_group/gen_qlrs[0]/i_qlr/fifo_full}
add wave -noupdate -expand -group {core[0][0][1]} -expand {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/qlr_ready}
add wave -noupdate -expand -group {core[0][0][1]} -divider Instructions
add wave -noupdate -expand -group {core[0][0][1]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/inst_addr_o}
add wave -noupdate -expand -group {core[0][0][1]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/inst_data_i}
add wave -noupdate -expand -group {core[0][0][1]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/inst_valid_o}
add wave -noupdate -expand -group {core[0][0][1]} {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_cores[1]/gen_mempool_cc/riscv_core/i_snitch/inst_ready_i}
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {69054018 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 145
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {69048066 ps} {69109570 ps}
