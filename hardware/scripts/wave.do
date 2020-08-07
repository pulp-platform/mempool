onerror {resume}
quietly WaveActivateNextPane {} 0

# Add all cores from tile 0
for {set core 0}  {$core < [examine -radix dec mempool_pkg::NumCoresPerTile]} {incr core} {
    do ../scripts/wave_core.do 0 $core
}

# Add specific cores from different tiles
do ../scripts/wave_core.do 1 0
do ../scripts/wave_core.do 2 3

# Add tiles
for {set tile 0}  {$tile < 4} {incr tile} {
    do ../scripts/wave_tile.do $tile
}

# Interconnect
for {set ini 0}  {$ini < [examine -radix dec /mempool_tb/dut/NumHives]} {incr ini} {
  for {set tgt 0}  {$tgt < [examine -radix dec /mempool_tb/dut/NumHives]} {incr tgt} {
      add wave -group Interconnect_ini[$ini] -group Interconnect_tgt[$tgt] /mempool_tb/dut/gen_intercos_ini_hive[$ini]/gen_intercos_tgt_hive[$tgt]/i_interco/*
  }
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
