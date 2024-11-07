#!/bin/bash

script="MMSE_BER_1.py"

# Define argument sets
arg_sets=(
    # "-c awgn -s 16QAM -n 4 -m 4 -b 8"						# done
    # "-c awgn -s 64QAM -n 4 -m 4 -b 8"
    # "-c awgn -s 16QAM -n 32 -m 32 -b 1"
    # "-c awgn -s 64QAM -n 32 -m 32 -b 1"
    "-c umi -s 16QAM -n 4 -m 4 -b 1 --fftsize 96"
    "-c umi -s 64QAM -n 4 -m 4 -b 1 --fftsize 96"
    # "-c umi -s 16QAM -n 32 -m 32 -b 1 --fftsize 96"
    # "-c umi -s 64QAM -n 32 -m 32 -b 1 --fftsize 96"
    "-c flatfading -s 16QAM -n 4 -m 4 -b 1"
    "-c flatfading -s 64QAM -n 4 -m 4 -b 1"
    # "-c flatfading -s 16QAM -n 32 -m 32 -b 1"
    # "-c flatfading -s 64QAM -n 32 -m 32 -b 1"
)




# Define the number of times to repeat all simulations
num_repeats=100

# Outer loop to repeat all simulations
for ((i=1; i<=num_repeats; i++)); do
    echo "=== Starting simulation round $i of $num_repeats ==="
    
    # Inner loop to run each argument set
    for args in "${arg_sets[@]}"; do
        echo "Running $script with args: $args (Round $i)"
        python3 "$script" $args
    done
    
    echo "=== Completed simulation round $i of $num_repeats ==="
done



# -------------------------32x32 umi-------------------------------

# Define argument sets
arg_sets=(
    # "-c awgn -s 16QAM -n 4 -m 4 -b 8"						# done
    # "-c awgn -s 64QAM -n 4 -m 4 -b 8"
    # "-c awgn -s 16QAM -n 32 -m 32 -b 1"
    # "-c awgn -s 64QAM -n 32 -m 32 -b 1"
    # "-c umi -s 16QAM -n 4 -m 4 -b 1 --fftsize 96"
    # "-c umi -s 64QAM -n 4 -m 4 -b 1 --fftsize 96"
    "-c umi -s 16QAM -n 32 -m 32 -b 1 --fftsize 96"
    "-c umi -s 64QAM -n 32 -m 32 -b 1 --fftsize 96"
    # "-c flatfading -s 16QAM -n 4 -m 4 -b 1"
    # "-c flatfading -s 64QAM -n 4 -m 4 -b 1"
    # "-c flatfading -s 16QAM -n 32 -m 32 -b 1"
    # "-c flatfading -s 64QAM -n 32 -m 32 -b 1"
)




# Define the number of times to repeat all simulations
num_repeats=10

# Outer loop to repeat all simulations
for ((i=1; i<=num_repeats; i++)); do
    echo "=== Starting simulation round $i of $num_repeats ==="
    
    # Inner loop to run each argument set
    for args in "${arg_sets[@]}"; do
        echo "Running $script with args: $args (Round $i)"
        python3 "$script" $args
    done
    
    echo "=== Completed simulation round $i of $num_repeats ==="
done
# -------------------------32x32-------------------------------

# Define argument sets
arg_sets=(
    # "-c awgn -s 16QAM -n 4 -m 4 -b 8"						# done
    # "-c awgn -s 64QAM -n 4 -m 4 -b 8"
    "-c awgn -s 16QAM -n 32 -m 32 -b 1"
    "-c awgn -s 64QAM -n 32 -m 32 -b 1"
    # "-c umi -s 16QAM -n 4 -m 4 -b 1 --fftsize 96"
    # "-c umi -s 64QAM -n 4 -m 4 -b 1 --fftsize 96"
    # "-c umi -s 16QAM -n 32 -m 32 -b 1 --fftsize 96"
    # "-c umi -s 64QAM -n 32 -m 32 -b 1 --fftsize 96"
    # "-c flatfading -s 16QAM -n 4 -m 4 -b 1"
    # "-c flatfading -s 64QAM -n 4 -m 4 -b 1"
    "-c flatfading -s 16QAM -n 32 -m 32 -b 1"
    "-c flatfading -s 64QAM -n 32 -m 32 -b 1"
)




# Define the number of times to repeat all simulations
num_repeats=5

# Outer loop to repeat all simulations
for ((i=1; i<=num_repeats; i++)); do
    echo "=== Starting simulation round $i of $num_repeats ==="
    
    # Inner loop to run each argument set
    for args in "${arg_sets[@]}"; do
        echo "Running $script with args: $args (Round $i)"
        python3 "$script" $args
    done
    
    echo "=== Completed simulation round $i of $num_repeats ==="
done
# --------------------ALL-----------------------------

# Define argument sets
arg_sets=(
    "-c awgn -s 16QAM -n 4 -m 4 -b 8"						# done
    "-c awgn -s 64QAM -n 4 -m 4 -b 8"
    "-c awgn -s 16QAM -n 32 -m 32 -b 1"
    "-c awgn -s 64QAM -n 32 -m 32 -b 1"
    "-c umi -s 16QAM -n 4 -m 4 -b 1 --fftsize 96"
    "-c umi -s 64QAM -n 4 -m 4 -b 1 --fftsize 96"
    "-c umi -s 16QAM -n 32 -m 32 -b 1 --fftsize 96"
    "-c umi -s 64QAM -n 32 -m 32 -b 1 --fftsize 96"
    "-c flatfading -s 16QAM -n 4 -m 4 -b 1"
    "-c flatfading -s 64QAM -n 4 -m 4 -b 1"
    "-c flatfading -s 16QAM -n 32 -m 32 -b 1"
    "-c flatfading -s 64QAM -n 32 -m 32 -b 1"
)




# Define the number of times to repeat all simulations
num_repeats=100

# Outer loop to repeat all simulations
for ((i=1; i<=num_repeats; i++)); do
    echo "=== Starting simulation round $i of $num_repeats ==="
    
    # Inner loop to run each argument set
    for args in "${arg_sets[@]}"; do
        echo "Running $script with args: $args (Round $i)"
        python3 "$script" $args
    done
    
    echo "=== Completed simulation round $i of $num_repeats ==="
done