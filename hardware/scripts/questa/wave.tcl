# Copyright 2021 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

onerror {resume}
quietly WaveActivateNextPane {} 0

# Add a vector of the core's wfi signal to quickly see which cores are active
set wfi_names ""
for {set g 0} {$g < [examine -radix dec /mempool_pkg::NumGroups]} {incr g} {
  for {set t 0} {$t < [examine -radix dec /mempool_pkg::NumTilesPerGroup]} {incr t} {
    for {set c 0} {$c < [examine -radix dec mempool_pkg::NumCoresPerTile]} {incr c} {
      set wfi_names "mempool_tb/dut/i_mempool_cluster/gen_groups[$g]/i_group/gen_tiles[$t]/i_tile/i_tile/gen_cores[$c]/gen_mempool_cc/riscv_core/i_snitch/wfi_q $wfi_names"
    }
  }
}
eval "add wave {wfi {$wfi_names}}"

# Add all cores from group 0 tile 0
for {set core 0}  {$core < [examine -radix dec mempool_pkg::NumCoresPerTile]} {incr core} {
    do ../scripts/questa/wave_core.tcl 0 0 $core
}

# Add specific cores from different tiles
do ../scripts/questa/wave_core.tcl 1 0 0

# Add groups
for {set group 0} {$group < [examine -radix dec /mempool_pkg::NumGroups]} {incr group} {
    # Add tiles
    for {set tile 0} {$tile < [expr min(4,[examine -radix dec /mempool_pkg::NumTilesPerGroup])]} {incr tile} {
        do ../scripts/questa/wave_tile.tcl $group $tile
    }

    # Interconnects
    add wave -group group_[$group] -group Interconnect_North     /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/i_group/i_north_interco/*
    add wave -group group_[$group] -group Interconnect_East      /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/i_group/i_east_interco/*
    add wave -group group_[$group] -group Interconnect_Northeast /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/i_group/i_northeast_interco/*
    add wave -group group_[$group] -group Interconnect_Local     /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/i_group/i_local_interco/*
}

add wave -Group Control_Registers /mempool_tb/dut/i_ctrl_registers/*
