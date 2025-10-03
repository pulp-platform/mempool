# O-POPE - WIP

To setup the repo from IIS machine:
```bash
make init-iis
```
To setup the repo (general case):
```bash
make init
```

To setup env variables:
```bash
source scripts/setup-hwpe.sh
```

To run a simulation with the GUI:
```bash
make golden OP=gemm M=32 N=32 K=32 fp_fmt=FP16
make sim target=vsim gui=1
```

To run all the performance logs:
```bash
make sim-all
```