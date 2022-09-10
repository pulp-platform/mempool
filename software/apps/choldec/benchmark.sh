for a in 8 16 32 64
do
    cd /scratch2/mbertuletti/mempool/software/apps
    DEFINES+=-DN=$a \
    make choldec
    cd /scratch2/mbertuletti/mempool/hardware
    app=choldec make buildpath=build_choldec simcvcs
    make buildpath=build_choldec resultpath=results_choldec_parallel trace
    cd /scratch2/mbertuletti/mempool/software/apps
done
