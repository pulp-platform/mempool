# Multi-Cluster MemPool

The MemPool repository supports a multi-cluster runtime `software/runtime/multi_cluster`
and multi-cluster applications `software/apps/multi_cluster`. There is no RTL
implementation of a multi-cluster MemPool.

A simulator of the multi-cluster MemPool platform is offered by `https://github.com/gvsoc/gvsoc`.
To run the multi-cluster software refer to the `README.md` within `gvsoc/pulp/pulp/chip/mc_pool`.

## Configuration

The Makefile uses the default architecture headers
`software/runtime/multi_cluster/arch/` (10 clusters, 256 PEs/cluster,
16 8x32 RedMulEs/cluster). For any other configuration, generate them with
`gvsoc/pulp/pulp/chip/mc_pool/common/utils/config.py`. The runtime checks that
the headers match `num_cores` and `num_redmule_tiles` used to build the
software.
