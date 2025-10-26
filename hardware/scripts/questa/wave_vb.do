onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -divider CONTROLLER
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/clk_i}
add wave -noupdate -color Cyan {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/current}
add wave -noupdate -color Cyan {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/streamer_current}
add wave -noupdate -color Cyan {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/acc_state_current}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/out_valid_o}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/out_ready_i}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/mask_y_o}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/mask_z_o}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/y_granted}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/y_counter_q}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/flgs_streamer_i.y_stream_source_flags.done}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/last_iteration_q}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/done_q}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/acc_done_q}
add wave -noupdate -divider {STREAM SOURCE}
add wave -noupdate -color Coral {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/gen_tcdm2stream[2]/i_stream_source/cs}
add wave -noupdate -label flags_o.addressgen_flags.done {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/flags_o.y_stream_source_flags.addressgen_flags.done}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/gen_tcdm2stream[2]/i_stream_source/addr_fifo_flags.empty}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/gen_tcdm2stream[2]/i_stream_source/ctrl_i.addressgen_ctrl.tot_len}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/gen_tcdm2stream[2]/i_stream_source/stream_cnt_q}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/gen_tcdm2stream[2]/i_stream_source/stream_cnt_en}
add wave -noupdate -divider {Y TCDM}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[2]/clk}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[2]/req_valid}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[2]/req_ready}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[2]/resp_valid}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[2]/resp_ready}
add wave -noupdate -divider {Z TCDM}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/z_store/clk}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/z_store/req_valid}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/z_store/req_ready}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/z_store/resp_valid}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/z_store/resp_ready}
add wave -noupdate -divider <NULL>
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {30516000 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 221
configure wave -valuecolwidth 131
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
configure wave -timelineunits ps
update
WaveRestoreZoom {30055459 ps} {30960542 ps}
