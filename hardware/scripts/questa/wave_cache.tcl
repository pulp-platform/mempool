# Copyright 2021 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# Create cache for core $4 from cluster $1 group $2 tile $3

if {$config == {terapool}} {
  add wave -noupdate -group cache[$1][$2][$3][$4][$5] -divider Parameters
  add wave -noupdate -group cache[$1][$2][$3][$4][$5] /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/gen_rtl_group/i_group/gen_sub_groups[$3]/gen_rtl_sg/i_sub_group/gen_tiles[$4]/i_tile/gen_caches[$5]/i_snitch_icache/NR_FETCH_PORTS
  add wave -noupdate -group cache[$1][$2][$3][$4][$5] /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/gen_rtl_group/i_group/gen_sub_groups[$3]/gen_rtl_sg/i_sub_group/gen_tiles[$4]/i_tile/gen_caches[$5]/i_snitch_icache/L0_LINE_COUNT
  add wave -noupdate -group cache[$1][$2][$3][$4][$5] /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/gen_rtl_group/i_group/gen_sub_groups[$3]/gen_rtl_sg/i_sub_group/gen_tiles[$4]/i_tile/gen_caches[$5]/i_snitch_icache/LINE_WIDTH
  add wave -noupdate -group cache[$1][$2][$3][$4][$5] /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/gen_rtl_group/i_group/gen_sub_groups[$3]/gen_rtl_sg/i_sub_group/gen_tiles[$4]/i_tile/gen_caches[$5]/i_snitch_icache/LINE_COUNT
  add wave -noupdate -group cache[$1][$2][$3][$4][$5] /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/gen_rtl_group/i_group/gen_sub_groups[$3]/gen_rtl_sg/i_sub_group/gen_tiles[$4]/i_tile/gen_caches[$5]/i_snitch_icache/SET_COUNT
  add wave -noupdate -group cache[$1][$2][$3][$4][$5] /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/gen_rtl_group/i_group/gen_sub_groups[$3]/gen_rtl_sg/i_sub_group/gen_tiles[$4]/i_tile/gen_caches[$5]/i_snitch_icache/FETCH_DW
  add wave -noupdate -group cache[$1][$2][$3][$4][$5] /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/gen_rtl_group/i_group/gen_sub_groups[$3]/gen_rtl_sg/i_sub_group/gen_tiles[$4]/i_tile/gen_caches[$5]/i_snitch_icache/FILL_AW
  add wave -noupdate -group cache[$1][$2][$3][$4][$5] /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/gen_rtl_group/i_group/gen_sub_groups[$3]/gen_rtl_sg/i_sub_group/gen_tiles[$4]/i_tile/gen_caches[$5]/i_snitch_icache/FILL_DW
  add wave -noupdate -group cache[$1][$2][$3][$4][$5] /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/gen_rtl_group/i_group/gen_sub_groups[$3]/gen_rtl_sg/i_sub_group/gen_tiles[$4]/i_tile/gen_caches[$5]/i_snitch_icache/EARLY_LATCH
  add wave -noupdate -group cache[$1][$2][$3][$4][$5] /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/gen_rtl_group/i_group/gen_sub_groups[$3]/gen_rtl_sg/i_sub_group/gen_tiles[$4]/i_tile/gen_caches[$5]/i_snitch_icache/L0_EARLY_TAG_WIDTH
  add wave -noupdate -group cache[$1][$2][$3][$4][$5] /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/gen_rtl_group/i_group/gen_sub_groups[$3]/gen_rtl_sg/i_sub_group/gen_tiles[$4]/i_tile/gen_caches[$5]/i_snitch_icache/ISO_CROSSING
  add wave -noupdate -group cache[$1][$2][$3][$4][$5] -divider Signals
  add wave -noupdate -group cache[$1][$2][$3][$4][$5] /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/gen_rtl_group/i_group/gen_sub_groups[$3]/gen_rtl_sg/i_sub_group/gen_tiles[$4]/i_tile/gen_caches[$5]/i_snitch_icache/*

  for {set i 0} {$i < [examine -radix dec /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/gen_rtl_group/i_group/gen_sub_groups[$3]/gen_rtl_sg/i_sub_group/gen_tiles[$4]/i_tile/gen_caches[$5]/i_snitch_icache/NR_FETCH_PORTS]} {incr i} {
    add wave -noupdate -group cache[$1][$2][$3][$4][$5] -group refill[$i] /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/gen_rtl_group/i_group/gen_sub_groups[$3]/gen_rtl_sg/i_sub_group/gen_tiles[$4]/i_tile/gen_caches[$5]/i_snitch_icache/gen_prefetcher[$i]/i_snitch_icache_l0/*
  }

  add wave -noupdate -group cache[$1][$2][$3][$4][$5] -group lookup  /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/gen_rtl_group/i_group/gen_sub_groups[$3]/gen_rtl_sg/i_sub_group/gen_tiles[$4]/i_tile/gen_caches[$5]/i_snitch_icache/i_lookup/*
  add wave -noupdate -group cache[$1][$2][$3][$4][$5] -group handler /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/gen_rtl_group/i_group/gen_sub_groups[$3]/gen_rtl_sg/i_sub_group/gen_tiles[$4]/i_tile/gen_caches[$5]/i_snitch_icache/i_handler/*
  add wave -noupdate -group cache[$1][$2][$3][$4][$5] -group handler /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/gen_rtl_group/i_group/gen_sub_groups[$3]/gen_rtl_sg/i_sub_group/gen_tiles[$4]/i_tile/gen_caches[$5]/i_snitch_icache/i_handler/pending_q
  add wave -noupdate -group cache[$1][$2][$3][$4][$5] -group refill  /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/gen_rtl_group/i_group/gen_sub_groups[$3]/gen_rtl_sg/i_sub_group/gen_tiles[$4]/i_tile/gen_caches[$5]/i_snitch_icache/i_refill/*
} else {
  add wave -noupdate -group cache[$1][$2][$3][$4] -divider Parameters
  add wave -noupdate -group cache[$1][$2][$3][$4] /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/i_group/gen_tiles[$3]/i_tile/gen_caches[$4]/i_snitch_icache/NR_FETCH_PORTS
  add wave -noupdate -group cache[$1][$2][$3][$4] /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/i_group/gen_tiles[$3]/i_tile/gen_caches[$4]/i_snitch_icache/L0_LINE_COUNT
  add wave -noupdate -group cache[$1][$2][$3][$4] /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/i_group/gen_tiles[$3]/i_tile/gen_caches[$4]/i_snitch_icache/LINE_WIDTH
  add wave -noupdate -group cache[$1][$2][$3][$4] /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/i_group/gen_tiles[$3]/i_tile/gen_caches[$4]/i_snitch_icache/LINE_COUNT
  add wave -noupdate -group cache[$1][$2][$3][$4] /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/i_group/gen_tiles[$3]/i_tile/gen_caches[$4]/i_snitch_icache/SET_COUNT
  add wave -noupdate -group cache[$1][$2][$3][$4] /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/i_group/gen_tiles[$3]/i_tile/gen_caches[$4]/i_snitch_icache/FETCH_DW
  add wave -noupdate -group cache[$1][$2][$3][$4] /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/i_group/gen_tiles[$3]/i_tile/gen_caches[$4]/i_snitch_icache/FILL_AW
  add wave -noupdate -group cache[$1][$2][$3][$4] /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/i_group/gen_tiles[$3]/i_tile/gen_caches[$4]/i_snitch_icache/FILL_DW
  add wave -noupdate -group cache[$1][$2][$3][$4] /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/i_group/gen_tiles[$3]/i_tile/gen_caches[$4]/i_snitch_icache/EARLY_LATCH
  add wave -noupdate -group cache[$1][$2][$3][$4] /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/i_group/gen_tiles[$3]/i_tile/gen_caches[$4]/i_snitch_icache/L0_EARLY_TAG_WIDTH
  add wave -noupdate -group cache[$1][$2][$3][$4] /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/i_group/gen_tiles[$3]/i_tile/gen_caches[$4]/i_snitch_icache/ISO_CROSSING
  add wave -noupdate -group cache[$1][$2][$3][$4] -divider Signals
  add wave -noupdate -group cache[$1][$2][$3][$4] /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/i_group/gen_tiles[$3]/i_tile/gen_caches[$4]/i_snitch_icache/*

  for {set i 0} {$i < [examine -radix dec /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/i_group/gen_tiles[$3]/i_tile/gen_caches[$4]/i_snitch_icache/NR_FETCH_PORTS]} {incr i} {
    add wave -noupdate -group cache[$1][$2][$3][$4] -group refill[$i] /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/i_group/gen_tiles[$3]/i_tile/gen_caches[$4]/i_snitch_icache/gen_prefetcher[$i]/i_snitch_icache_l0/*
  }

  add wave -noupdate -group cache[$1][$2][$3][$4] -group lookup  /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/i_group/gen_tiles[$3]/i_tile/gen_caches[$4]/i_snitch_icache/i_lookup/*
  add wave -noupdate -group cache[$1][$2][$3][$4] -group handler /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/i_group/gen_tiles[$3]/i_tile/gen_caches[$4]/i_snitch_icache/i_handler/*
  add wave -noupdate -group cache[$1][$2][$3][$4] -group handler /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/i_group/gen_tiles[$3]/i_tile/gen_caches[$4]/i_snitch_icache/i_handler/pending_q
  add wave -noupdate -group cache[$1][$2][$3][$4] -group refill  /mempool_tb/dut/gen_clusters[$1]/i_mempool_cluster/gen_groups[$2]/i_group/gen_tiles[$3]/i_tile/gen_caches[$4]/i_snitch_icache/i_refill/*
}
