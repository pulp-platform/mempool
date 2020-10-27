onerror {resume}
quietly WaveActivateNextPane {} 0

# Add all cores from group 0 tile 0
for {set core 0}  {$core < [examine -radix dec mempool_pkg::NumCoresPerTile]} {incr core} {
    do ../scripts/wave_core.do 0 0 $core
}

# Add specific cores from different tiles
do ../scripts/wave_core.do 1 0 0

# Add groups
for {set group 0} {$group < [examine -radix dec /mempool_pkg::NumGroups]} {incr group} {
    # Add tiles
    for {set tile 0} {$tile < [expr min(4,[examine -radix dec /mempool_tb/dut/i_mempool/gen_groups[$group]/i_group/NumTilesPerGroup])]} {incr tile} {
        do ../scripts/wave_tile.do $group $tile
    }

    # Interconnects
    add wave -group group_[$group] -group Interconnect_North     /mempool_tb/dut/i_mempool/gen_groups[$group]/i_group/i_north_interco/*
    add wave -group group_[$group] -group Interconnect_East      /mempool_tb/dut/i_mempool/gen_groups[$group]/i_group/i_east_interco/*
    add wave -group group_[$group] -group Interconnect_Northeast /mempool_tb/dut/i_mempool/gen_groups[$group]/i_group/i_northeast_interco/*
    add wave -group group_[$group] -group Interconnect_Local     /mempool_tb/dut/i_mempool/gen_groups[$group]/i_group/i_local_interco/*
}

add wave -group Wake_up_reg /mempool_tb/dut/i_ctrl_registers/clk_i
add wave -group Wake_up_reg /mempool_tb/dut/i_ctrl_registers/wake_up
add wave -group Wake_up_reg /mempool_tb/dut/i_ctrl_registers/wake_up_o
add wave -group Wake_up_reg /mempool_tb/dut/i_ctrl_registers/wr_active_d
add wave -group Wake_up_reg /mempool_tb/dut/i_ctrl_registers/wr_active_q

add wave -group Core_wake_up_sync_i /mempool_tb/dut/i_mempool/gen_groups[0]/i_group/gen_tiles[0]/i_tile/i_tile/gen_cores[0]/riscv_core/i_snitch/wake_up_sync_i
add wave -group Core_wake_up_sync_i /mempool_tb/dut/i_mempool/gen_groups[0]/i_group/gen_tiles[0]/i_tile/i_tile/gen_cores[1]/riscv_core/i_snitch/wake_up_sync_i
add wave -group Core_wake_up_sync_i /mempool_tb/dut/i_mempool/gen_groups[0]/i_group/gen_tiles[0]/i_tile/i_tile/gen_cores[2]/riscv_core/i_snitch/wake_up_sync_i
add wave -group Core_wake_up_sync_i /mempool_tb/dut/i_mempool/gen_groups[0]/i_group/gen_tiles[0]/i_tile/i_tile/gen_cores[3]/riscv_core/i_snitch/wake_up_sync_i

add wave -group Core_wake_up_sync_i /mempool_tb/dut/i_mempool/gen_groups[1]/i_group/gen_tiles[0]/i_tile/i_tile/gen_cores[0]/riscv_core/i_snitch/wake_up_sync_i
add wave -group Core_wake_up_sync_i /mempool_tb/dut/i_mempool/gen_groups[1]/i_group/gen_tiles[0]/i_tile/i_tile/gen_cores[1]/riscv_core/i_snitch/wake_up_sync_i
add wave -group Core_wake_up_sync_i /mempool_tb/dut/i_mempool/gen_groups[1]/i_group/gen_tiles[0]/i_tile/i_tile/gen_cores[2]/riscv_core/i_snitch/wake_up_sync_i
add wave -group Core_wake_up_sync_i /mempool_tb/dut/i_mempool/gen_groups[1]/i_group/gen_tiles[0]/i_tile/i_tile/gen_cores[3]/riscv_core/i_snitch/wake_up_sync_i

add wave -group Core_wake_up_sync_i /mempool_tb/dut/i_mempool/gen_groups[2]/i_group/gen_tiles[0]/i_tile/i_tile/gen_cores[0]/riscv_core/i_snitch/wake_up_sync_i
add wave -group Core_wake_up_sync_i /mempool_tb/dut/i_mempool/gen_groups[2]/i_group/gen_tiles[0]/i_tile/i_tile/gen_cores[1]/riscv_core/i_snitch/wake_up_sync_i
add wave -group Core_wake_up_sync_i /mempool_tb/dut/i_mempool/gen_groups[2]/i_group/gen_tiles[0]/i_tile/i_tile/gen_cores[2]/riscv_core/i_snitch/wake_up_sync_i
add wave -group Core_wake_up_sync_i /mempool_tb/dut/i_mempool/gen_groups[2]/i_group/gen_tiles[0]/i_tile/i_tile/gen_cores[3]/riscv_core/i_snitch/wake_up_sync_i

add wave -group Core_wake_up_sync_i /mempool_tb/dut/i_mempool/gen_groups[3]/i_group/gen_tiles[0]/i_tile/i_tile/gen_cores[0]/riscv_core/i_snitch/wake_up_sync_i
add wave -group Core_wake_up_sync_i /mempool_tb/dut/i_mempool/gen_groups[3]/i_group/gen_tiles[0]/i_tile/i_tile/gen_cores[1]/riscv_core/i_snitch/wake_up_sync_i
add wave -group Core_wake_up_sync_i /mempool_tb/dut/i_mempool/gen_groups[3]/i_group/gen_tiles[0]/i_tile/i_tile/gen_cores[2]/riscv_core/i_snitch/wake_up_sync_i
add wave -group Core_wake_up_sync_i /mempool_tb/dut/i_mempool/gen_groups[3]/i_group/gen_tiles[0]/i_tile/i_tile/gen_cores[3]/riscv_core/i_snitch/wake_up_sync_i

add wave -Group Control_Registers /mempool_tb/dut/i_ctrl_registers/*

# TreeUpdate [SetDefaultTree]
# WaveRestoreCursors {{Core0 0->sp} {445000 ps} 1} {{Cursor 2} {434939 ps} 0}
# quietly wave cursor active 2
# configure wave -namecolwidth 162
# configure wave -valuecolwidth 202
# configure wave -justifyvalue left
# configure wave -signalnamewidth 1
# configure wave -snapdistance 10
# configure wave -datasetprefix 0
# configure wave -rowmargin 4
# configure wave -childrowmargin 2
# configure wave -gridoffset 0
# configure wave -gridperiod 1
# configure wave -griddelta 40
# configure wave -timeline 0
# configure wave -timelineunits ns
# update
# WaveRestoreZoom {433843 ps} {456157 ps}
