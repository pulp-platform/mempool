# PHY Emulator

This repo contains a Python based simulator of a MIMO transmission in the lower PHY of 5G.
- The simulator allows to emulate the MIMO channel on the host machine. It can simulate parts of the receiver as running on MemPool, using emulation through the Banshee binary translator.
- Telecommunication KPIs such as the BER and the MSE can be extracted from the end to end co-simulation of the channel and MemPool kernels.

To support all the arithmetic precisions make sure that your `./configuration` has:

```
zquarterinx = 1
xDivSqrt = 1
```

Compiled binaries are in the `./bin` folder. The simulator compiles binaries for MemPool and runs emulation of the hardware in Banshee from the project root directory, with the following commands:
```
DEFINES="-DFLAG" l1_bank_size=16384 config=terapool make COMPILER=llvm BIN_DIR=./software/PHY_emulator/bin app -C ./software/apps/baremetal
SNITCH_LOG=info cargo run -- --num-cores 1 --num-clusters 1 --configuration config/terapool.yaml ./software/PHY_emulator/bin/app
```


