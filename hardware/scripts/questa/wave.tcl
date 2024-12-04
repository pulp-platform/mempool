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

# Add the spm bank util of one tile
set NumX [examine -radix dec mempool_pkg::NumX]
set NumY [examine -radix dec mempool_pkg::NumY]
for {set group 0} {$group < [examine -radix dec /mempool_pkg::NumGroups]} {incr group} {
    for {set tile 0} {$tile < [examine -radix dec /mempool_pkg::NumTilesPerGroup]} {incr tile} {
        add wave -Group super_bank_req_valid -position insertpoint sim:/mempool_tb/dut/i_mempool_cluster/gen_groups_x\[[expr ${group}/${NumX}]\]/gen_groups_y\[[expr ${group}%${NumY}]\]/i_group/i_mempool_group/gen_tiles\[${tile}\]/i_tile/superbank_req_valid
    }
}

# Add all cores from group 0 tile 0
for {set core 0}  {$core < [examine -radix dec mempool_pkg::NumCoresPerTile]} {incr core} {
    do ../scripts/questa/wave_core.tcl 0 0 $core $NumY
}

# Add specific cores from different tiles
do ../scripts/questa/wave_core.tcl 1 0 0 $NumY
do ../scripts/questa/wave_core.tcl 1 1 1 $NumY
do ../scripts/questa/wave_core.tcl [expr [examine -radix dec mempool_pkg::NumGroups]-1] [expr [examine -radix dec mempool_pkg::NumTilesPerGroup]-1] [expr [examine -radix dec mempool_pkg::NumCoresPerTile]-1] $NumY

# Add groups
for {set group 0} {$group < [examine -radix dec /mempool_pkg::NumGroups]} {incr group} {
    # Add Interface
    add wave -group group_[$group] -group X[[expr ${group}/${NumX}]]Y[[expr ${group}%${NumY}]]_Intf /mempool_tb/dut/i_mempool_cluster/gen_groups_x\[[expr ${group}/${NumX}]\]/gen_groups_y\[[expr ${group}%${NumY}]\]/i_group/i_mempool_group/*
    # Addr Map
    add wave -group group_[$group] -group addr_map /mempool_tb/dut/i_mempool_cluster/gen_groups_x\[[expr ${group}/${NumX}]\]/gen_groups_y\[[expr ${group}%${NumY}]\]/i_group/i_mempool_group/addr_map
    # Add Tiles
    for {set tile 0} {$tile < [examine -radix dec /mempool_pkg::NumTilesPerGroup]} {incr tile} {
        do ../scripts/questa/wave_tile.tcl $group $tile $NumY
    }
    # Local TCDM
    add wave -group group_[$group] -group interconnect_local /mempool_tb/dut/i_mempool_cluster/gen_groups_x\[[expr ${group}/${NumX}]\]/gen_groups_y\[[expr ${group}%${NumY}]\]/i_group/i_mempool_group/tcdm_master_req*
    add wave -group group_[$group] -group interconnect_local /mempool_tb/dut/i_mempool_cluster/gen_groups_x\[[expr ${group}/${NumX}]\]/gen_groups_y\[[expr ${group}%${NumY}]\]/i_group/i_mempool_group/tcdm_master_resp*
    add wave -group group_[$group] -group interconnect_local /mempool_tb/dut/i_mempool_cluster/gen_groups_x\[[expr ${group}/${NumX}]\]/gen_groups_y\[[expr ${group}%${NumY}]\]/i_group/i_mempool_group/tcdm_slave_req*
    add wave -group group_[$group] -group interconnect_local /mempool_tb/dut/i_mempool_cluster/gen_groups_x\[[expr ${group}/${NumX}]\]/gen_groups_y\[[expr ${group}%${NumY}]\]/i_group/i_mempool_group/tcdm_slave_resp*
    # TCDM Router
    for {set tile 0} {$tile < [examine -radix dec /mempool_pkg::NumTilesPerGroup]} {incr tile} {
        for {set port 1} {$port < [examine -radix dec /mempool_pkg::NumRemotePortsPerTile]} {incr port} {
            add wave -group group_[$group] -group floo_tcdm_router_req /mempool_tb/dut/i_mempool_cluster/gen_groups_x\[[expr ${group}/${NumX}]\]/gen_groups_y\[[expr ${group}%${NumY}]\]/i_group/gen_router_router_i[$tile]/gen_router_router_j[$port]/i_floo_tcdm_req_router/*
            add wave -group group_[$group] -group floo_tcdm_router_resp /mempool_tb/dut/i_mempool_cluster/gen_groups_x\[[expr ${group}/${NumX}]\]/gen_groups_y\[[expr ${group}%${NumY}]\]/i_group/gen_router_router_i[$tile]/gen_router_router_j[$port]/i_floo_tcdm_resp_router/*
        }
    }
    # Splitter & Interleaver
    add wave -group group_[$group] -group axi_splitter /mempool_tb/dut/i_mempool_cluster/gen_groups_x\[[expr ${group}/${NumX}]\]/gen_groups_y\[[expr ${group}%${NumY}]\]/i_group/gen_axi_splitter/i_axi_burst_splitter/*
    add wave -group group_[$group] -group axi_interleaver /mempool_tb/dut/i_mempool_cluster/gen_groups_x\[[expr ${group}/${NumX}]\]/gen_groups_y\[[expr ${group}%${NumY}]\]/i_group/i_axi_L2_interleaver/*
    # AXI Router
    add wave -group group_[$group] -group floo_axi_chimney /mempool_tb/dut/i_mempool_cluster/gen_groups_x\[[expr ${group}/${NumX}]\]/gen_groups_y\[[expr ${group}%${NumY}]\]/i_group/i_floo_narrow_wide_chimney/*
    add wave -group group_[$group] -group floo_axi_router /mempool_tb/dut/i_mempool_cluster/gen_groups_x\[[expr ${group}/${NumX}]\]/gen_groups_y\[[expr ${group}%${NumY}]\]/i_group/i_floo_narrow_wide_router/*
}

# Add cluster
do ../scripts/questa/wave_cluster.tcl

# Add System
add wave -group system -group soc_xbar /mempool_tb/dut/i_soc_xbar/*
add wave -group system -group axi2mem_bootrom /mempool_tb/dut/i_axi2mem_bootrom/*
for {set bank 0} {$bank < [examine -radix dec /mempool_pkg::NumL2Banks]} {incr bank} {
    add wave -group system -group L2_banks -group axi2mem_[$bank] /mempool_tb/dut/gen_l2_adapters[$bank]/i_axi2mem/*
    add wave -group system -group L2_banks -group bank_[$bank] /mempool_tb/dut/gen_l2_banks[$bank]/l2_mem/*
}
add wave -group system -group CSR /mempool_tb/dut/i_ctrl_registers/*

# Add DMA
add wave -group DMA -group dma_top /mempool_tb/dut/i_mempool_dma/*
add wave -group DMA -group frontend_reg /mempool_tb/dut/i_mempool_dma/i_mempool_dma_frontend_reg_top/*
add wave -group DMA -group midend_cluster /mempool_tb/dut/i_mempool_cluster/i_idma_distributed_midend/NoMstPorts
add wave -group DMA -group midend_cluster /mempool_tb/dut/i_mempool_cluster/i_idma_distributed_midend/DmaRegionWidth
add wave -group DMA -group midend_cluster /mempool_tb/dut/i_mempool_cluster/i_idma_distributed_midend/DmaRegionStart
add wave -group DMA -group midend_cluster /mempool_tb/dut/i_mempool_cluster/i_idma_distributed_midend/DmaRegionEnd
add wave -group DMA -group midend_cluster /mempool_tb/dut/i_mempool_cluster/i_idma_distributed_midend/DmaRegionAddressBits
add wave -group DMA -group midend_cluster /mempool_tb/dut/i_mempool_cluster/i_idma_distributed_midend/FullRegionAddressBits
add wave -group DMA -group midend_cluster /mempool_tb/dut/i_mempool_cluster/i_idma_distributed_midend/*
add wave -group DMA -group midend_cluster_split /mempool_tb/dut/i_mempool_cluster/i_idma_split_midend/*

for {set group 0} {$group < [examine -radix dec /mempool_pkg::NumGroups]} {incr group} {
    add wave -group DMA -group midend_group_${group} /mempool_tb/dut/i_mempool_cluster/gen_groups_x\[[expr ${group}/${NumX}]\]/gen_groups_y\[[expr ${group}%${NumY}]\]/i_group/i_mempool_group/i_idma_distributed_midend/NoMstPorts
    add wave -group DMA -group midend_group_${group} /mempool_tb/dut/i_mempool_cluster/gen_groups_x\[[expr ${group}/${NumX}]\]/gen_groups_y\[[expr ${group}%${NumY}]\]/i_group/i_mempool_group/i_idma_distributed_midend/DmaRegionWidth
    add wave -group DMA -group midend_group_${group} /mempool_tb/dut/i_mempool_cluster/gen_groups_x\[[expr ${group}/${NumX}]\]/gen_groups_y\[[expr ${group}%${NumY}]\]/i_group/i_mempool_group/i_idma_distributed_midend/DmaRegionStart
    add wave -group DMA -group midend_group_${group} /mempool_tb/dut/i_mempool_cluster/gen_groups_x\[[expr ${group}/${NumX}]\]/gen_groups_y\[[expr ${group}%${NumY}]\]/i_group/i_mempool_group/i_idma_distributed_midend/DmaRegionEnd
    add wave -group DMA -group midend_group_${group} /mempool_tb/dut/i_mempool_cluster/gen_groups_x\[[expr ${group}/${NumX}]\]/gen_groups_y\[[expr ${group}%${NumY}]\]/i_group/i_mempool_group/i_idma_distributed_midend/DmaRegionAddressBits
    add wave -group DMA -group midend_group_${group} /mempool_tb/dut/i_mempool_cluster/gen_groups_x\[[expr ${group}/${NumX}]\]/gen_groups_y\[[expr ${group}%${NumY}]\]/i_group/i_mempool_group/i_idma_distributed_midend/FullRegionAddressBits
    add wave -group DMA -group midend_group_${group} /mempool_tb/dut/i_mempool_cluster/gen_groups_x\[[expr ${group}/${NumX}]\]/gen_groups_y\[[expr ${group}%${NumY}]\]/i_group/i_mempool_group/i_idma_distributed_midend/*
    for {set dma 0} {$dma < [examine -radix dec /mempool_pkg::NumDmasPerGroup]} {incr dma} {
      add wave -group DMA -Group backend_group${group}_be${dma} /mempool_tb/dut/i_mempool_cluster/gen_groups_x\[[expr ${group}/${NumX}]\]/gen_groups_y\[[expr ${group}%${NumY}]\]/i_group/i_mempool_group/gen_dmas[$dma]/i_axi_dma_backend/*
    }
    add wave -group DMA -group tcdm_dma_group_${group} /mempool_tb/dut/i_mempool_cluster/gen_groups_x\[[expr ${group}/${NumX}]\]/gen_groups_y\[[expr ${group}%${NumY}]\]/i_group/i_mempool_group/tcdm_dma_req*
    add wave -group DMA -group tcdm_dma_group_${group} /mempool_tb/dut/i_mempool_cluster/gen_groups_x\[[expr ${group}/${NumX}]\]/gen_groups_y\[[expr ${group}%${NumY}]\]/i_group/i_mempool_group/tcdm_dma_resp*
}

do ../scripts/questa/wave_cache.tcl 0 0 0 $NumY

