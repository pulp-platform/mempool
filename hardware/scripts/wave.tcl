# Copyright 2021 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

onerror {resume}
quietly WaveActivateNextPane {} 0

# Add all cores from group 0 tile 0
for {set core 0}  {$core < [examine -radix dec mempool_pkg::NumCoresPerTile]} {incr core} {
    do ../scripts/wave_core.tcl 0 0 $core
}

# Add specific cores from different tiles
do ../scripts/wave_core.tcl 1 0 0

# Add groups
for {set group 0} {$group < [examine -radix dec /mempool_pkg::NumGroups]} {incr group} {
    # Add tiles
    for {set tile 0} {$tile < [expr min(4,[examine -radix dec /mempool_pkg::NumTilesPerGroup])]} {incr tile} {
        do ../scripts/wave_tile.tcl $group $tile
    }

    # Interconnects
    add wave -group group_[$group] -group Interconnect_North     /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/i_group/i_north_interco/*
    add wave -group group_[$group] -group Interconnect_East      /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/i_group/i_east_interco/*
    add wave -group group_[$group] -group Interconnect_Northeast /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/i_group/i_northeast_interco/*
    add wave -group group_[$group] -group Interconnect_Local     /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/i_group/i_local_interco/*
}

add wave -Group Control_Registers /mempool_tb/dut/i_ctrl_registers/*
