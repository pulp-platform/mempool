#! /bin/tcsh -x

## Compile RTL and TB
./compile_tb.sh

set TB=rab_tb
set LIB=rtl
set VER=10.6b

## Tests
#vsim-${VER} -voptargs="+acc" -gTEST_NAME="l1_and_l2" -gSRC_ID=9 ${LIB}.${TB}
vsim-${VER} -voptargs="+acc" -gTEST_NAME="multi_hit" -gSRC_ID=10 ${LIB}.${TB}
#vsim-${VER} -voptargs="+acc" -gTEST_NAME="l2" -gSRC_ID=0 ${LIB}.${TB}
#vsim-${VER} -voptargs="+acc" -gTEST_NAME="reg_rd_wr" ${LIB}.${TB}
#vsim-${VER} -voptargs="+acc" -gTEST_NAME="all_l2" ${LIB}.${TB}
#vsim-${VER} -voptargs="+acc" -gTEST_NAME="l2_board" ${LIB}.${TB}
#vsim-${VER} -voptargs="+acc" -gTEST_NAME="print" ${LIB}.${TB}
#vsim-${VER} -voptargs="+acc" -gTEST_NAME="multi_hit" ${LIB}.${TB}

# Use SRC_ID=8 for random AXI traffic

######## Script to run multiple random AXI traffic patterns ###########
# echo "" > status.log
# foreach x (`seq 1 1 200`) ## Change this to change the number of tests to be run. x will be used as the seed for random tests.
# sed -e "s/REPLACE_THIS/$x/g" TRAFFIC_0_13_gen.cmd > TRAFFIC_0_13.cmd
# cp TRAFFIC_0_13.cmd ../TGEN_RAB/TGEN/traffic_pattern/
# echo "Seed is $x" >> status.log
# ./compile_tb.sh
# vsim-${VER}  -c -do batch_mode.do -voptargs="+acc" -gTEST_NAME="l2" ${LIB}.${TB} > test.log
# tail -n 3 test.log >> status.log
# echo "--------------------------------------------------------------------------------------------------------------------" >> status.log
# echo "" >> status.log
# end
###########################
