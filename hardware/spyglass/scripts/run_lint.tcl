# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

set PROJECT   mempool
set TIMESTAMP [exec date +%Y%m%d_%H%M%S]

new_project sg_projects/${PROJECT}_${TIMESTAMP}
current_methodology $env(SPYGLASS_HOME)/GuideWare/latest/block/rtl_handoff

# Read the RTL
read_file -type sourcelist tmp/files

set_option enableSV09 yes
set_option language_mode mixed
set_option allow_module_override yes
set_option designread_disable_flatten no
set_option mthresh 32768
set_option top mempool_group

# Read constraints
current_design mempool_group
set_option sdc2sgdc yes
sdc_data -file sdc/func.sdc

# Link Design
compile_design

# Initial assignment for [] is ignored by synthesis. automatic logic
waive -rule "SYNTH_89"
# Unsigned element [] passed to the $unsigned() function call.
waive -rule "WRN_1024"
# Enable pin EN on Flop [] (master RTL_FDCE) is always disabled (tied low)
waive -rule "FlopEConst"
# Based number [] contains a dont care. riscv_instr.sv
waive -rule "W467"
# Rhs width with shift is less than lhs width.
waive -rule "W486"
# Variable [] set but not read.
waive -rule "W528"
# Signal [] is being assigned multiple times in the same block.
waive -rule "W415a"


# Set lint_rtl goal and run
current_goal lint/lint_rtl
run_goal

# Create a link to the results
exec rm -rf sg_projects/${PROJECT}
exec ln -sf ${PROJECT}_${TIMESTAMP} sg_projects/${PROJECT}

# Ciao!
exit -save
