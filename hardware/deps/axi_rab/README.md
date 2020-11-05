# AXI RAB

This is the AXI Remapping Address Block, a software-managed I/O memory
management unit. Its main purpose is to perform address translation for AXI4
transactions to allow the  interfacing of AXI4 subsystems having different
memory maps. Address translation is performed based on data stored in a
translation lookaside buffer (TLB). The TLB is configured in software through an
AXI-Lite configuration interface.

The RAB was designed to enable shared virtual memory (SVM) between host and
many-core accelerator in the [HERO platform](https://www.pulp-platform.org/hero).

## Features

The RAB is a configurable IP core. It can be configured to have multiple RAB
ports and in parallel interface different AXI4 masters with AXI4 slaves. Every
RAB port features a private TLB while the AXI-Lite configuration interface is
shared among all RAB ports.

Per RAB port, up to two TLBs with a different architecture and of configurable
size can be used. The level-1 (L1) TLB is fully associative and features a
lookup latency of 1 clock cycle. Its entries are of arbitrary size which allows
for maximum flexibility. The L1 TLB is always implemented. The level-1 (L2) TLB
supports page-sized entries (configurable at compile time). It is n-way set
associative where n as well as the set size are configurable parameters. The L2
TLB is implemented using a configurable number of parallel block RAMs that are
searched sequentially. This leads to a configurable, variable multi-cycle lookup
latency. The L2 TLB is only searched after a miss in the L1 TLB. While the L2
TLB is busy, the L1 TLB can continue to perform lookups and translated AXI
transactions can be forwarded downstream (hit under miss). The L2 TLB  can
optionally be enabled on a per-RAB-port basis.

In case the address of an incoming transaction cannot be translated, e.g.
because the TLBs do not contain a valid mapping for the incoming address, the
RAB discards the transaction and signals a slave error in the transaction
response. The issuing master is then responsible for re-issuing the transaction
after the TLBs have been updated.

Every TLB entry features a set of flags which define the allowed transaction
types for the corresponding address region. Besides a read as well as a write
flag, there is also a coherency flag. Depending on the configuration of the RAB,
this flag is used to either modify the AXI cache control signals (AxCACHE) or to
forward the transaction to one of two different AXI master ports. The latter is
suitable for modern SoCs such as the Xilinx Zynq-7000 SoC or the Xilinx
UltraScale+ MPSoC, which feature separate coherent and non-coherent slave ports
on the system interconnect to which accelerators in the programmable logic can
connect (through the RAB).

## Repository structure

This repository has the following structure:
- `doc` contains information on how the RAB sets the AxCACHE flags for different
  types of incoming transactions.
- `rtl` contains the actual RTL code of the RAB.
- `tb` contains the support files, traffic patterns, and compile scripts for the
  RAB testbench. For more information on the testbench see `tb/rab_tb/README.md`.

## Known issues

The RAB does not support multiple incoming transactions on either the AR or AW
channel with the same transaction ID. In particular, reponses might get
reordered if some of the transactions cannot be translated while others can,
which violates the AXI4 protocol specification.
