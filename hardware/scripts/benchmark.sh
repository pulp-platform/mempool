#!/usr/bin/env bash

MEMPOOL_DIR=$(git rev-parse --show-toplevel 2>/dev/null || echo $MEMPOOL_DIR)
cd $MEMPOOL_DIR/hardware

# Make sure an app is specified
app="$MEMPOOL_DIR/apps/bin/$1"
if [[ ! -f $app ]]; then
  echo "Please specify an application to execute"
  exit -1
fi

# Run all three scenarios
scenarios=('Original' '1Hive' '2Hives' '4Hives')
for scenario in "${scenarios[@]}"; do
  echo $scenario
  # Do some changes to get the correct HW state
  if [[ "$scenario" == "Original" ]]; then
    cd $MEMPOOL_DIR
    git apply \
      config/patches/0001-Revert-global-interconnect-to-parallel_butterfly.patch
    cd $MEMPOOL_DIR/hardware
    num_hives=0
  elif [[ "$scenario" == "1Hive" ]]; then
    num_hives=1
  elif [[ "$scenario" == "2Hives" ]]; then
    num_hives=2
  else
    num_hives=4
  fi
  # Run the benchmark
  buildpath=build_$scenario
  result_dir=results/$(date +"%Y%m%d_%H%M%S_$1_$scenario")
  rm -rf $buildpath
  buildpath=$buildpath result_dir=$result_dir num_hives=$num_hives app=$1 \
    make benchmark > log_$1_$scenario &
  # Sleep until the compilation is done.
  while [ ! -f $buildpath/trace_hart_0000.dasm ]; do sleep 5; done
  # Revert changes done for each scenario
  if [[ "$scenario" == "Original" ]]; then
    cd $MEMPOOL_DIR
    git apply -R \
      config/patches/0001-Revert-global-interconnect-to-parallel_butterfly.patch
    cd $MEMPOOL_DIR/hardware
  fi
done

wait

# All benchmarks are completed
echo "Benchmark logs:" > log_all
for scenario in "${scenarios[@]}"; do
  cat log_$1_$scenario >> log_all
done

echo "Done" > mail -s "Benchmarking completed" $USER@iis.ee.ethz.ch
