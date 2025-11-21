onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -divider CONTROLLER
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/clk_i}
add wave -noupdate -color Cyan {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/current}
add wave -noupdate -color Cyan {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/streamer_current}
add wave -noupdate -color Cyan {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/acc_state_current}
add wave -noupdate -divider <NULL>
add wave -noupdate -group X -divider TCDM
add wave -noupdate -group X {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[0]/clk}
add wave -noupdate -group X {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/x_granted}
add wave -noupdate -group X {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[0]/req_valid}
add wave -noupdate -group X {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[0]/req_ready}
add wave -noupdate -group X {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[0]/resp_valid}
add wave -noupdate -group X {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[0]/resp_ready}
add wave -noupdate -group X {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[0]/resp_data}
add wave -noupdate -group X -divider STREAM
add wave -noupdate -group X {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/x_stream_o/data}
add wave -noupdate -group X {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/gen_tcdm2stream[0]/i_stream_source/stream_cnt_q}
add wave -noupdate -group X {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/out_stream[0]/valid}
add wave -noupdate -group X {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/out_stream[0]/ready}
add wave -noupdate -group W -divider TCDM
add wave -noupdate -group W {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[1]/clk}
add wave -noupdate -group W {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/w_granted}
add wave -noupdate -group W {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[1]/req_valid}
add wave -noupdate -group W {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[1]/req_ready}
add wave -noupdate -group W {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[1]/resp_valid}
add wave -noupdate -group W {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[1]/resp_ready}
add wave -noupdate -group W {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[1]/resp_data}
add wave -noupdate -group W -divider STREAM
add wave -noupdate -group W {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/w_stream_o/data}
add wave -noupdate -group W {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/gen_tcdm2stream[1]/i_stream_source/stream_cnt_q}
add wave -noupdate -group W {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/out_stream[1]/valid}
add wave -noupdate -group W {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/out_stream[1]/ready}
add wave -noupdate -group Y -divider TCDM
add wave -noupdate -group Y {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/out_stream[2]/clk}
add wave -noupdate -group Y {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/y_granted}
add wave -noupdate -group Y {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[2]/req_valid}
add wave -noupdate -group Y {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[2]/req_ready}
add wave -noupdate -group Y {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[2]/resp_valid}
add wave -noupdate -group Y {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[2]/resp_ready}
add wave -noupdate -group Y {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[2]/resp_data}
add wave -noupdate -group Y -divider STREAM
add wave -noupdate -group Y {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/out_stream[2]/clk}
add wave -noupdate -group Y {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/y_stream_o/data}
add wave -noupdate -group Y {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/gen_tcdm2stream[2]/i_stream_source/stream_cnt_q}
add wave -noupdate -group Y {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/out_stream[2]/valid}
add wave -noupdate -group Y {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/out_stream[2]/ready}
add wave -noupdate -group Z -divider {Z TCDM}
add wave -noupdate -group Z {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[3]/clk}
add wave -noupdate -group Z {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[3]/req_valid}
add wave -noupdate -group Z {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[3]/req_ready}
add wave -noupdate -group Z {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[3]/req_data}
add wave -noupdate -group Z {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[3]/resp_valid}
add wave -noupdate -group Z {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/virt_tcdm[3]/resp_ready}
add wave -noupdate -group Z -divider {Z STREAM}
add wave -noupdate -group Z {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/z_stream_i/clk}
add wave -noupdate -group Z {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/z_stream_i/valid}
add wave -noupdate -group Z {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/z_stream_i/ready}
add wave -noupdate -group Z {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_streamer/z_stream_i/data}
add wave -noupdate -label ce_operands_00 -expand {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_engine/ce_operands[0][0]}
add wave -noupdate -label engine_to_reg_00 {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_engine/engine_to_reg_output[0][0]}
add wave -noupdate -label acc_operand_00 {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_engine/acc_operand[0][0]}
add wave -noupdate -label reg_out_data_00 {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_engine/reg_out_data[0][0]}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/y_in_valid_i}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/in_valid_i}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/in_ready_o}
add wave -noupdate -label acc_in_data_00 {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_engine/acc_in_data[0][0]}
add wave -noupdate -label acc_in_valid_00 {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_engine/acc_in_valid[0][0]}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/shift_acc}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/y_write_reg_index_q}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/y_write_row_index_q}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/inner_loop_counter_q}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/inner_loop_counter_d}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/prefetched_q}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/y_bias_selector}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/gen_redmule_tile/i_tile/i_opope_top/i_control/mask_y_o}
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {5838271 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 234
configure wave -valuecolwidth 40
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
WaveRestoreZoom {5825382 ps} {5842616 ps}
