for a in 1 4 8 16 32 64
do
    cd /scratch2/mbertuletti/mempool/software/apps
    DEFINES+=-DN_FFTs=$a \
    make cfft_q16radix4_schedule
    cd /scratch2/mbertuletti/mempool/hardware
    app=cfft_q16radix4_schedule make buildpath=build_cfft simcvcs
    make buildpath=build_cfft resultpath=result_cfft_terapool_single trace
    cd /scratch2/mbertuletti/mempool/software/apps
done

#cd /scratch2/mbertuletti/mempool/hardware/result_cfft
#keys=("cycles")
#keys+=("snitch_loads")
#keys+=("snitch_stores")
#keys+=("snitch_avg_load_latency")
#keys+=("snitch_occupancy")
#keys+=("total_ipc")
#keys+=("snitch_issues")
#keys+=("stall_tot")
#keys+=("stall_ins")
#keys+=("stall_raw")
#keys+=("stall_raw_lsu")
#keys+=("stall_raw_acc")
#keys+=("stall_lsu")
#keys+=("stall_acc")
#keys+=("stall_wfi")
#keys+=("seq_loads_local")
#keys+=("seq_loads_global")
#keys+=("itl_loads_local")
#keys+=("itl_loads_global")
#keys+=("seq_latency_local")
#keys+=("seq_latency_global")
#keys+=("itl_latency_local")
#keys+=("itl_latency_global")
#keys+=("seq_stores_local")
#keys+=("seq_stores_global")
#keys+=("itl_stores_local")
#keys+=("itl_stores_global")
#for str in ${keys[@]}; do
#    # grep -R -h $str */avg.txt >> cfft_results.csv
#    echo $str >> cfft_results.csv
#    grep -R -h $str */avg.txt | grep -Eo "[0-9]+\.[0-9]+" | xargs | sed -e 's/ /, /g' >> cfft_results.csv
#done
