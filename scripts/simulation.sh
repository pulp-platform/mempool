# clean software and golden model
cd software/
make clean
cd apps/baremetal
make clean
cd ../../../

#activate virtual environment
source venv/bin/activate

# generate golden model
python3 ./software/data/gendata_header.py --app_name gemm_f16 --type float16 --defines matrix_M=32,matrix_N=32,matrix_P=32 --arrays __fp16:l2_X,__fp16:l2_W,__fp16:l2_Y,__fp16:l2_Z

# compile software
cd software/apps/baremetal/
make COMPILER=llvm opope_f16 
deactivate

# compile hardware and run simulation
cd ../../../hardware
make clean
app=baremetal/opope_f16 make sim
