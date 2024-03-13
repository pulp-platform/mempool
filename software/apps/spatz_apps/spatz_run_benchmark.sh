#!/bin/bash

# make -C auto_benchmark clean-all

# Check if no arguments were provided
if [ $# -eq 0 ]; then
    echo "Error: Please give the configuration."
    exit 1
fi

echo ""
echo "-----$1-----"
echo ""

# Check if the first argument starts with "mempool_spatz4"
if [[ $1 == mempool_spatz4* ]]; then
    maxcore=64
elif [[ $1 == terapool_spatz8* ]]; then
    maxcore=128
elif [[ $1 == mempool_spatz2* ]]; then
    core=128
elif [[ $1 == terapool_spatz4* ]]; then
    core=256
else
	echo "Error: Not supported configuration, exit"
	exit 2
fi
make -C ../../../hardware buildspatz config=$1
################
echo ""
echo ""
echo "$0"
make -C auto_benchmark clean
echo ""
echo "dotp"
make -C auto_benchmark dotp config=$1 size=8192 cores=$maxcore
make -C auto_benchmark dotp config=$1 size=16384 cores=$maxcore
make -C auto_benchmark dotp config=$1 size=32768 cores=$maxcore
echo ""
echo "dotp-opt"
make -C auto_benchmark dotp-opt config=$1 size=8192 cores=$maxcore
make -C auto_benchmark dotp-opt config=$1 size=16384 cores=$maxcore
make -C auto_benchmark dotp-opt config=$1 size=32768 cores=$maxcore
echo ""
echo "fft 4 cores"
make -C auto_benchmark fft config=$1 size=512 cores=4
make -C auto_benchmark fft config=$1 size=1024 cores=4
make -C auto_benchmark fft config=$1 size=4096 cores=4
echo "fft 8 cores"
make -C auto_benchmark fft config=$1 size=512 cores=8
make -C auto_benchmark fft config=$1 size=1024 cores=8
make -C auto_benchmark fft config=$1 size=4096 cores=8
echo "fft 16 cores"
make -C auto_benchmark fft config=$1 size=1024 cores=16
make -C auto_benchmark fft config=$1 size=4096 cores=16
echo "fft 32 cores"
make -C auto_benchmark fft config=$1 size=4096 cores=32
echo "fft 64 cores"
make -C auto_benchmark fft config=$1 size=4096 cores=64
echo ""
echo "fmatmul"
make -C auto_benchmark fmatmul config=$1 
