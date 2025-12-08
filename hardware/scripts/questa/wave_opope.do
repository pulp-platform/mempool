onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -divider CONTROLLER
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_control/current}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_control/streamer_current}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_control/acc_state_current}
add wave -noupdate -divider <NULL>
add wave -noupdate -expand -group X -divider {X TCDM}
add wave -noupdate -expand -group X {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[0]/clk}
add wave -noupdate -expand -group X {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[0]/req_valid}
add wave -noupdate -expand -group X {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[0]/req_ready}
add wave -noupdate -expand -group X {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm_rob[0]/req_add}
add wave -noupdate -expand -group X {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[0]/resp_valid}
add wave -noupdate -expand -group X {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[0]/resp_ready}
add wave -noupdate -expand -group X {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[0]/req_data}
add wave -noupdate -expand -group X -divider {X STREAM}
add wave -noupdate -expand -group X {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/out_stream[0]/clk}
add wave -noupdate -expand -group X {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/out_stream[0]/valid}
add wave -noupdate -expand -group X {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/out_stream[0]/ready}
add wave -noupdate -expand -group X {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/out_stream[0]/data}
add wave -noupdate -expand -group W -divider {W TCDM}
add wave -noupdate -expand -group W {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[1]/clk}
add wave -noupdate -expand -group W {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[1]/req_valid}
add wave -noupdate -expand -group W {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[1]/req_ready}
add wave -noupdate -expand -group W {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[1]/req_add}
add wave -noupdate -expand -group W {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[1]/resp_valid}
add wave -noupdate -expand -group W {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[1]/resp_ready}
add wave -noupdate -expand -group W {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[1]/req_data}
add wave -noupdate -expand -group W -divider {W STREAM}
add wave -noupdate -expand -group W {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/out_stream[1]/clk}
add wave -noupdate -expand -group W {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/out_stream[1]/valid}
add wave -noupdate -expand -group W {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/out_stream[1]/ready}
add wave -noupdate -expand -group W {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/out_stream[1]/data}
add wave -noupdate -expand -group Y -divider {Y TCDM}
add wave -noupdate -expand -group Y {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[2]/clk}
add wave -noupdate -expand -group Y {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[2]/req_valid}
add wave -noupdate -expand -group Y {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[2]/req_ready}
add wave -noupdate -expand -group Y {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[2]/req_add}
add wave -noupdate -expand -group Y {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[2]/resp_valid}
add wave -noupdate -expand -group Y {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[2]/resp_ready}
add wave -noupdate -expand -group Y {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[2]/req_data}
add wave -noupdate -expand -group Y -divider {Y STREAM}
add wave -noupdate -expand -group Y {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/out_stream[2]/clk}
add wave -noupdate -expand -group Y {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/out_stream[2]/valid}
add wave -noupdate -expand -group Y {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/out_stream[2]/ready}
add wave -noupdate -expand -group Y {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/out_stream[2]/data}
add wave -noupdate -expand -group Z -divider {Z TCDM}
add wave -noupdate -expand -group Z {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[3]/clk}
add wave -noupdate -expand -group Z {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[3]/req_valid}
add wave -noupdate -expand -group Z {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[3]/req_ready}
add wave -noupdate -expand -group Z {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[3]/req_add}
add wave -noupdate -expand -group Z {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[3]/resp_valid}
add wave -noupdate -expand -group Z {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[3]/resp_ready}
add wave -noupdate -expand -group Z {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[3]/req_data}
add wave -noupdate -expand -group Z -divider {Z STREAM}
add wave -noupdate -expand -group Z {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/z_stream_i/clk}
add wave -noupdate -expand -group Z {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/z_stream_i/valid}
add wave -noupdate -expand -group Z {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/z_stream_i/ready}
add wave -noupdate -expand -group Z {/mempool_tb/dut/i_mempool_cluster/gen_groups[0]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/z_stream_i/data}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[1]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_control/current}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[1]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_control/streamer_current}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[1]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_control/acc_state_current}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[2]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_control/current}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[2]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_control/streamer_current}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[2]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_control/acc_state_current}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_control/current}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_control/streamer_current}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_control/acc_state_current}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_control/flgs_streamer_i.y_stream_source_flags.done}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_control/last_iteration_q}
add wave -noupdate {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_control/in_valid_i}
add wave -noupdate -expand -group {GROUP 3} -divider {X TCDM}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[0]/clk}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[0]/req_valid}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[0]/req_ready}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[0]/resp_valid}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[0]/resp_ready}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[0]/req_add}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[0]/resp_data}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/out_stream[0]/clk}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/out_stream[0]/valid}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/out_stream[0]/ready}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/out_stream[0]/data}
add wave -noupdate -expand -group {GROUP 3} -divider {W TCDM}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[1]/clk}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[1]/req_valid}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[1]/req_ready}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[1]/resp_valid}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[1]/resp_ready}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[1]/req_add}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[1]/req_data}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[1]/resp_data}
add wave -noupdate -expand -group {GROUP 3} -divider {Y TCDM}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[2]/clk}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[2]/req_valid}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[2]/req_ready}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[2]/resp_valid}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[2]/resp_ready}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[2]/req_add}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[2]/req_data}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[2]/resp_data}
add wave -noupdate -expand -group {GROUP 3} -divider {Z TCDM}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[3]/clk}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[3]/req_valid}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[3]/req_ready}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[3]/resp_valid}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[3]/resp_ready}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[3]/req_add}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[3]/req_data}
add wave -noupdate -expand -group {GROUP 3} {/mempool_tb/dut/i_mempool_cluster/gen_groups[3]/i_group/gen_tiles[0]/i_tile/gen_redmule/i_opope_top/i_streamer/virt_tcdm[3]/resp_data}
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {789567 ps} 0} {{Cursor 2} {5212524 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 234
configure wave -valuecolwidth 97
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
WaveRestoreZoom {5316440 ps} {5459045 ps}
