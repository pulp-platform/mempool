# Copyright 2021 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# Useful signal for systolic configuration debugging

# define queue ops radix for readibility
radix define AmoOp {
  4'h0 "AMONone",
  4'h1 "AMOSwap",
  4'h2 "AMOAdd",
  4'h3 "AMOAnd",
  4'h4 "AMOOr",
  4'h5 "AMOXor",
  4'h6 "AMOMax",
  4'h7 "AMOMaxu",
  4'h8 "AMOMin",
  4'h9 "AMOMinu",
  4'hA "AMOLR",
  4'hB "AMOSC",
  4'hC "QPush",
  4'hD "QPop"
}

radix define QueueOpcodes {
  15'b001110100101111 "q_push",
  15'b001100100101111 "q_pop"
}

####################################
# Individual TCDM adapter and core #
####################################

# add tcdm adapter signals
set group_id 3
set tile_id 15
set bank_id 13

set tcdm_adapter "sim:/mempool_tb/dut/i_mempool_cluster/gen_groups[$group_id]/i_group/gen_tiles[$tile_id]/i_tile/gen_banks[$bank_id]/gen_tcdm_adapter_xqueue/i_tcdm_adapter"
add wave -position 0 -group "TCDM adapter" "${tcdm_adapter}/*"
radix signal "${tcdm_adapter}/in_amo_i" AmoOp

# add Snitch signals
set group_id 3
set tile_id 15
set core_id 3

do ../scripts/questa/wave_core.tcl $group_id $tile_id $core_id

# compose opcode fetched by the Snitch core to debug
set opcode_signal "inst_data_i(31 to 29) & inst_data_i(28 to 27) & inst_data_i(14 to 12) & inst_data_i(6 to 2) & inst_data_i(1 to 0)"
set snitch "/mempool_tb/dut/i_mempool_cluster/gen_groups[$group_id]/i_group/gen_tiles[$tile_id]/i_tile/gen_cores[$core_id]/gen_mempool_cc/riscv_core/i_snitch"
set context_cmd "{ ( context $snitch ) ( $opcode_signal ) }"
virtual signal -install $snitch $context_cmd opcode_i
add wave -position 0 -radix QueueOpcodes -label "opcode_i[$group_id][$tile_id][$core_id]" "$snitch/opcode_i"

###############################
# All TCDM adapters and cores #
###############################

# add amo opcode of all tcdm adapters
set num_groups 4
set num_tiles 16
set num_banks 16

for {set g 0} {$g < $num_groups} {incr g} {
  for {set t 0} {$t < $num_tiles} {incr t} {
    for {set b 0} {$b < $num_banks} {incr b} {
      set signal "sim:/mempool_tb/dut/i_mempool_cluster/gen_groups[$g]/i_group/gen_tiles[$t]/i_tile/gen_banks[$b]/gen_tcdm_adapter_xqueue/i_tcdm_adapter/in_amo_i"
      add wave -position 0 -group "TCDM AmoOp (group_tile_bank)" -label "${g}_${t}_${b}" -radix AmoOp $signal
      set signal "sim:/mempool_tb/dut/i_mempool_cluster/gen_groups[$g]/i_group/gen_tiles[$t]/i_tile/gen_banks[$b]/gen_tcdm_adapter_xqueue/i_tcdm_adapter/stalled_queue_op"
      add wave -position 0 -group "Stalled Qop (group_tile_bank)" -label "${g}_${t}_${b}" $signal
    }
  }
}

# add fetched instr opcode from all cores
set num_groups 4
set num_tiles 1
set num_cores 4

set counter 0

set opcode_signal "inst_data_i(31 to 29) & inst_data_i(28 to 27) & inst_data_i(14 to 12) & inst_data_i(6 to 2) & inst_data_i(1 to 0)"

for {set g 0} {$g < $num_groups} {incr g} {
  for {set t 0} {$t < $num_tiles} {incr t} {
    for {set c 0} {$c < $num_cores} {incr c} {
      set snitch "/mempool_tb/dut/i_mempool_cluster/gen_groups[$g]/i_group/gen_tiles[$t]/i_tile/gen_cores[$c]/gen_mempool_cc/riscv_core/i_snitch"
      set context_cmd "{ ( context $snitch ) ( $opcode_signal ) }"
      virtual signal -install $snitch $context_cmd opcode_i
      add wave -position 0 -group "Snitch fetched opcodes" -color Maroon -radix QueueOpcodes -label "opcode_i[$g][$t][$c] - $counter" "$snitch/opcode_i"
      incr counter
    }
  }
}
