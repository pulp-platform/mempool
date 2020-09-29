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
    for {set tile 0} {$tile < [expr min(4,[examine -radix dec /mempool_tb/dut/gen_groups[$group]/i_group/NumTilesPerGroup])]} {incr tile} {
        do ../scripts/wave_tile.do $group $tile
    }

    # Interconnects
    add wave -group group_[$group] -group Interconnect_North     /mempool_tb/dut/gen_groups[$group]/i_group/i_north_interco/*
    add wave -group group_[$group] -group Interconnect_East      /mempool_tb/dut/gen_groups[$group]/i_group/i_east_interco/*
    add wave -group group_[$group] -group Interconnect_Northeast /mempool_tb/dut/gen_groups[$group]/i_group/i_northeast_interco/*
    add wave -group group_[$group] -group Interconnect_Local     /mempool_tb/dut/gen_groups[$group]/i_group/i_local_interco/*
}


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
