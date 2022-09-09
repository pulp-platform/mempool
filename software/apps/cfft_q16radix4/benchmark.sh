for a in 64 256 1024 4096
do
    cd /scratch2/mbertuletti/mempool/software/apps

    if [[ $a -eq 64 ]]; then
        DEFINES+=-DTEST_64 \
        make cfft_q16radix4
    elif [[ $a -eq 256 ]]; then
        DEFINES+=-DTEST_256 \
        make cfft_q16radix4
    elif [[ $a -eq 1024 ]]; then
        DEFINES+=-DTEST_1024 \
        make cfft_q16radix4
    elif [[ $a -eq 4096 ]]; then
        DEFINES+=-DTEST_4096 \
        make cfft_q16radix4
    fi

    cd /scratch2/mbertuletti/mempool/hardware
    app=cfft_q16radix4 make buildpath=build_cfft simcvcs
    make buildpath=build_cfft resultpath=result_cfft_mempoolsingle_single trace
    cd /scratch2/mbertuletti/mempool/software/apps/cfft_q16radix4
done
