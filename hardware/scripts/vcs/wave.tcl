# Copyright 2021 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# Add a vector of the core's wfi signal to quickly see which cores are active
add_wave -group wfi /mempool_tb/wfi

# Add all cores from group 0 tile 0
for {set core 0}  {$core < [get -radix dec mempool_pkg::NumCoresPerTile]} {incr core} {
    do ../scripts/vcs/wave_core.tcl 0 0 $core
}

# Add specific cores from different tiles
do ../scripts/vcs/wave_core.tcl 1 0 0

# Add min function (DVE does not support TCL8.5)
proc min args {
    set minval [lindex args 0]
    foreach arg $args {
        if { $arg < $minval } {
            set minval $arg
        }
    }
    return $minval
}

# Add groups
for {set group 0} {$group < [get -radix dec mempool_pkg::NumGroups]} {incr group} {
    # Create the group
    add_wave -group group_\[$group\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$group\]/i_group/i_north_interco/*
    delete_group -group group_\[$group\] /mempool_tb/dut/i_mempool_cluster/gen_groups\[$group\]/i_group/i_north_interco/*

    # Add tiles
    for {set tile 0} {$tile < [min 4 [get -radix dec mempool_pkg::NumTilesPerGroup]]} {incr tile} {
        do ../scripts/vcs/wave_tile.tcl $group $tile
    }

    # Interconnects
    add_wave -group group_\[$group\]|Interconnect_North     /mempool_tb/dut/i_mempool_cluster/gen_groups\[$group\]/i_group/i_north_interco/*
    add_wave -group group_\[$group\]|Interconnect_East      /mempool_tb/dut/i_mempool_cluster/gen_groups\[$group\]/i_group/i_east_interco/*
    add_wave -group group_\[$group\]|Interconnect_Northeast /mempool_tb/dut/i_mempool_cluster/gen_groups\[$group\]/i_group/i_northeast_interco/*
    add_wave -group group_\[$group\]|Interconnect_Local     /mempool_tb/dut/i_mempool_cluster/gen_groups\[$group\]/i_group/i_local_interco/*
}

add_wave -group Control_Registers /mempool_tb/dut/i_ctrl_registers/*
