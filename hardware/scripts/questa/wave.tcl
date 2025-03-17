# Copyright 2021 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

onerror {resume}
quietly WaveActivateNextPane {} 0

# Add a vector of the core's utilization signals to quickly get an overview of the systems activity
set num_cores [examine -radix dec mempool_pkg::NumCores]

add wave -noupdate -group Utilization -color {Cornflower Blue} -format Analog-Step -height 84 -max $num_cores -radix unsigned /mempool_tb/snitch_utilization
add wave -noupdate -group Utilization /mempool_tb/instruction_handshake
add wave -noupdate -group Utilization -color {Cornflower Blue} -format Analog-Step -height 84 -max $num_cores -radix unsigned /mempool_tb/lsu_utilization
add wave -noupdate -group Utilization /mempool_tb/lsu_handshake
add wave -noupdate -group Utilization -color {Cornflower Blue} -format Analog-Step -height 84 -max $num_cores -radix unsigned /mempool_tb/lsu_pressure
add wave -noupdate -group Utilization /mempool_tb/lsu_request
if {[examine -radix dec /snitch_pkg::XPULPIMG]} {
  add wave -noupdate -group Utilization -color {Cornflower Blue} -format Analog-Step -height 84 -max $num_cores -radix unsigned /mempool_tb/gen_utilization/dspu_utilization
  add wave -noupdate -group Utilization /mempool_tb/gen_utilization/dspu_handshake
  add wave -noupdate -group Utilization -color {Cornflower Blue} -format Analog-Step -height 84 -max $num_cores -radix unsigned /mempool_tb/gen_utilization/mac_utilization
  add wave -noupdate -group Utilization /mempool_tb/gen_utilization/dspu_mac
}
set axi_channels [expr [examine -radix dec mempool_pkg::NumGroups] * [examine -radix dec mempool_pkg::NumAXIMastersPerGroup]]
add wave -noupdate -group Utilization -color {Cornflower Blue} -format Analog-Step -height 84 -max $axi_channels -radix unsigned /mempool_tb/axi_w_utilization
add wave -noupdate -group Utilization -color {Cornflower Blue} -format Analog-Step -height 84 -max $axi_channels -radix unsigned /mempool_tb/axi_r_utilization


# Add a vector of the core's wfi signal to quickly see which cores are active
add wave /mempool_tb/wfi

set num_rmtiles [examine -radix dec mempool_pkg::NumRMTiles]
if {$num_rmtiles > 0} {
  set scoped_tile 1
  if {$config == {terapool}} {
    do ../scripts/questa/wave_redmule.tcl 0 0 0
  } else {
    do ../scripts/questa/wave_redmule.tcl 0 0
  }
} else {
  set scoped_tile 0
}

# Add all cores from group 0 tile 0
for {set core 0}  {$core < [examine -radix dec mempool_pkg::NumCoresPerTile]} {incr core} {
    if {$config == {terapool}} {
        do ../scripts/questa/wave_core.tcl 0 0 $scoped_tile $core
    } else {
        do ../scripts/questa/wave_core.tcl 0 $scoped_tile $core
    }
}

# Add specific cores from different tiles
if {$config == {terapool}} {
    do ../scripts/questa/wave_core.tcl 1 0 $scoped_tile 0
} else {
    do ../scripts/questa/wave_core.tcl 1 $scoped_tile 0
}

# Add groups
for {set group 0} {$group < [examine -radix dec /mempool_pkg::NumGroups]} {incr group} {
    # Add tiles
    if {$config == {terapool}} {
        for {set subgroup 0} {$subgroup < [expr min(4,[examine -radix dec /mempool_pkg::NumSubGroupsPerGroup])]} {incr subgroup} {
            for {set tile $scoped_tile} {$tile < [expr min(4,[examine -radix dec /mempool_pkg::NumTilesPerSubGroup])]} {incr tile} {
                do ../scripts/questa/wave_tile.tcl $group $subgroup $tile
            }
        }
    } else {
        for {set tile $scoped_tile} {$tile < [expr min(4,[examine -radix dec /mempool_pkg::NumTilesPerGroup])]} {incr tile} {
            do ../scripts/questa/wave_tile.tcl $group $tile
        }
    }

    # Interconnects
    for {set tgtgroup 0} {$tgtgroup < [examine -radix dec /mempool_pkg::NumGroups]} {incr tgtgroup} {
        if {$tgtgroup != $group} {
            set interco_idx [expr $group ^ $tgtgroup]
            if {$config == {terapool}} {
                add wave -group group_[$group] -group interconnect_to_group[$tgtgroup] /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/gen_rtl_group/i_group/gen_remote_interco[$interco_idx]/i_remote_interco/*
            } else {
                add wave -group group_[$group] -group interconnect_to_group[$tgtgroup] /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/i_group/gen_remote_interco[$interco_idx]/i_remote_interco/*
            }
        }
    }
    if {$config != {terapool}} {
        add wave -group group_[$group] -group interconnect_local /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/i_group/i_local_interco/*
    }
}

# Add cluster
do ../scripts/questa/wave_cluster.tcl

add wave -Group Control_Registers /mempool_tb/dut/i_ctrl_registers/*

add wave -Group DMA /mempool_tb/dut/i_mempool_dma/*
add wave -Group DMA -Group Reg /mempool_tb/dut/i_mempool_dma/i_mempool_dma_frontend_reg_top/*
for {set group 0} {$group < [examine -radix dec /mempool_pkg::NumGroups]} {incr group} {
  if  {$config == {terapool}} {
    add wave -Group DMA_midend_${group} /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/gen_rtl_group/i_group/i_idma_distributed_midend/NoMstPorts
    add wave -Group DMA_midend_${group} /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/gen_rtl_group/i_group/i_idma_distributed_midend/DmaRegionWidth
    add wave -Group DMA_midend_${group} /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/gen_rtl_group/i_group/i_idma_distributed_midend/DmaRegionStart
    add wave -Group DMA_midend_${group} /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/gen_rtl_group/i_group/i_idma_distributed_midend/DmaRegionEnd
    add wave -Group DMA_midend_${group} /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/gen_rtl_group/i_group/i_idma_distributed_midend/DmaRegionAddressBits
    add wave -Group DMA_midend_${group} /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/gen_rtl_group/i_group/i_idma_distributed_midend/FullRegionAddressBits
    add wave -Group DMA_midend_${group} /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/gen_rtl_group/i_group/i_idma_distributed_midend/*
    for {set subgroup 0} {$subgroup < [examine -radix dec /mempool_pkg::NumSubGroupsPerGroup]} {incr subgroup} {
        for {set dma 0} {$dma < [examine -radix dec /mempool_pkg::NumDmasPerSubGroup]} {incr dma} {
            add wave -Group DMA_${group}_${subgroup}_${dma} /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/gen_rtl_group/i_group/gen_sub_groups[$subgroup]/gen_rtl_sg/i_sub_group/gen_dmas[$dma]/i_axi_dma_backend/*
        }
    }
  } else {
    add wave -Group DMA_midend_${group} /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/i_group/i_idma_distributed_midend/NoMstPorts
    add wave -Group DMA_midend_${group} /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/i_group/i_idma_distributed_midend/DmaRegionWidth
    add wave -Group DMA_midend_${group} /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/i_group/i_idma_distributed_midend/DmaRegionStart
    add wave -Group DMA_midend_${group} /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/i_group/i_idma_distributed_midend/DmaRegionEnd
    add wave -Group DMA_midend_${group} /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/i_group/i_idma_distributed_midend/DmaRegionAddressBits
    add wave -Group DMA_midend_${group} /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/i_group/i_idma_distributed_midend/FullRegionAddressBits
    add wave -Group DMA_midend_${group} /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/i_group/i_idma_distributed_midend/*
    for {set dma 0} {$dma < [examine -radix dec /mempool_pkg::NumDmasPerGroup]} {incr dma} {
      add wave -Group DMA_${group}_${dma} /mempool_tb/dut/i_mempool_cluster/gen_groups[$group]/i_group/gen_dmas[$dma]/i_axi_dma_backend/*
    }
  }
}

add wave -Group DMA_midend_cluster /mempool_tb/dut/i_mempool_cluster/i_idma_distributed_midend/NoMstPorts
add wave -Group DMA_midend_cluster /mempool_tb/dut/i_mempool_cluster/i_idma_distributed_midend/DmaRegionWidth
add wave -Group DMA_midend_cluster /mempool_tb/dut/i_mempool_cluster/i_idma_distributed_midend/DmaRegionStart
add wave -Group DMA_midend_cluster /mempool_tb/dut/i_mempool_cluster/i_idma_distributed_midend/DmaRegionEnd
add wave -Group DMA_midend_cluster /mempool_tb/dut/i_mempool_cluster/i_idma_distributed_midend/DmaRegionAddressBits
add wave -Group DMA_midend_cluster /mempool_tb/dut/i_mempool_cluster/i_idma_distributed_midend/FullRegionAddressBits
add wave -Group DMA_midend_cluster /mempool_tb/dut/i_mempool_cluster/i_idma_distributed_midend/*


add wave -Group DMA_split /mempool_tb/dut/i_mempool_cluster/i_idma_split_midend/*

if {$config == {terapool}} {
  do ../scripts/questa/wave_cache.tcl 0 0 $scoped_tile 0
} else {
  do ../scripts/questa/wave_cache.tcl 0 $scoped_tile 0
}
