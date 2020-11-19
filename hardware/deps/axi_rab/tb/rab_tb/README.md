# RAB RTL Simulation & Testbench

This is the simulation framework and testbench for the AXI RAB IP core.

## Getting started

To start the RTL simulation & testbench of the RAB IP core, perform
the following steps:

1. Download the AMBA4 AXI-Lite Verification IP from SysWip:

        http://syswip.com/axi4-lite-verification-ip

   and extract the archive.

2. Open the compile script `compile_tb.sh` and adjust it to your local
   environment. In particular, you must set up the `PULP_BASE_ADDR`
   variable pointing to where you downloaded the bigPULP repository,
   and the `AXI4LITE_VIP_PATH` variable pointing to where you
   extracted the archive in Step 1.

3. Execute `run_tb.sh` to compile the testbench and the design, and to
   start the simulation.

## How to change the test being executed?

You can change the test name and the AXI traffic using the `TEST_NAME`
and `SRC_ID` parameters in the `run_tb.sh` script.

`TEST_NAME` controls the AXI-Lite config port, i.e., the configuration
written to the RAB.

`SRC_ID` controls the AXI traffic pattern, i.e., the transactions
passing through the RAB and of which the address needs to be
translated.

## How to change the RAB configuration?

Open `test.sv` and alter the section where the RAB is being configured
using the functions `slice_cfg()`, `slice_acp_cfg()`, and `l2_cfg()`.

## How to change the AXI traffic pattern?

The AXI traffic pattern is controlled by the parameter `SRC_ID` in
`rab_tb.sv`. There are a couple of patterns inside
`tb/TGEN_RAB/TGEN/traffic_pattern`.

`TRAFFIC_0_13_gen.cmd` can be used to generate multiple `TRAFFIC_0_13.cmd`
files with different random seeds. You can use this to run different
randomised AXI traffic. A script (commented) is provided in `run_tb.sh`.

## Known issues

- The AXI traffic generator sends AW and W simultaneously.

- It is not clear if read and write transactions following
  back-to-back on the AR and AW channels can be tested properly.

- Prefetch transactions cannot be generated as the tasks inside
  `TGEN_TASK_ADDON.sv` always use the `SRC_ID` as `AXUSER`.

- The verification infrastructure inside `rab_tb.sv` only works on
  Master Port 0 but not on Master Port 1 (the ACP). Consequently,
  when using Port 1, the support for verification is very limited.
  The following is supported for the different tasks inside
  `TGEN_TASK_ADDON.sv` in this case:

  - FILL_LINEAR: checking if there is a response for every issued
    transaction.

  - READ_LINEAR: checking if there is a response for every issued
    transaction.

  - CHECK_LINEAR: checking of responses and read data according
    to a specified pattern. Note: the memory must first be written
    using FILL_LINEAR.

  - FILL_RANDOM: checking if there is a response for every issued
    transaction.
