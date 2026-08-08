# Configuration file for MemPool

The `config.mk` file is included by all *Makefiles* in the MemPool project to have
a common source for all configurations. Please only edit this file to change some
parameters such as the number of cores in the design. This will automatically
generate the correct software runtime and the correct hardware.

The `config.mk` file includes other configuration files, which represent specific
flavors of MemPool. We currently support three flavors:
- `terapool`: 1024 cores, organized into 128 tiles with eight cores each
- `mempool`: 256 cores, organized into 64 tiles with four cores each (default)
- `minpool`: 16 cores, organized into 4 tiles with four cores each

Use the `config` variable to define which configuration to take. For example,
to run a simulation with the `minpool` configuration, you would run
```
config=minpool make -C hardware verilate
```
Alternatively, you can also define the `MEMPOOL_CONFIGURATION` environment
variable, which has less priority than an explicit `config=` configuration.
Please run `make clean` before changing configurations.

To avoid constantly having a dirty git environment when working with a
configuration that differs from the default one, you can ignore changes to the
configuration file with the following command:

```bash
git update-index --assume-unchanged config/config.mk
```

In case you want to change the default and commit your changes to `config.mk`,
you can use the following command to make git pick up tracking the file again:

```bash
git update-index --no-assume-unchanged config/config.mk
```

## Back2Local

Back2Local reuses upper-level tile ports for TCDM requests that remain in the
source group or subgroup. It changes the route to memory, not the address
mapping, and can be used with or without DAS.

| Variable                | Default | Description                                |
|-------------------------|---------|--------------------------------------------|
| `back2local`            | `0`     | Enable Back2Local for the selected setup   |
| `back2local_tera_group` | `0`     | Also use TeraPool's group-level tile ports |

For TeraPool, `back2local=1` uses the subgroup-level ports by default. Setting
`back2local_tera_group=1` also makes the group-level ports available and may
contend with inter-group traffic.

The current port selection uses the core index modulo the available ports. It
is a simple baseline policy that can be adapted in
`hardware/src/mempool_tile.sv`.

## Dynamic Address Scrambling (DAS)

Dynamic Address Scrambling (DAS) is a runtime-configurable address mapping
technique. DAS remaps contiguous address spaces to physically adjacent memory
banks based on the workload's memory access patterns, placing data physically
close to PEs.

### Build-time configuration

DAS is controlled by three variables in `config.mk`:

| Variable             | Default | Description                                |
|----------------------|---------|--------------------------------------------|
| `das`                | `1`     | Enable (`1`) or disable (`0`) DAS support  |
| `num_das_partitions` | `4`     | Number of independent DAS regions          |
| `das_mem_size`       | `2048`  | DAS heap size per core (bytes)             |

### DAS registers

Each DAS partition `i` (0 .. `num_das_partitions - 1`) is programmed through
three memory-mapped registers:

| Register       | Description                                                |
|----------------|------------------------------------------------------------|
| `tiles_das[i]` | Folding granularity: number of tiles in this DAS partition |
| `start_das[i]` | Allocated start address of this DAS partition              |
| `rows_das[i]`  | Allocated size of this DAS partition (in rows)             |

The hardware address scrambler uses these registers to remap addresses within
each partition so that consecutive words land on adjacent banks within
`tiles_das[i]` tiles, rather than being interleaved across all tiles.

### Software usage

The runtime provides a convenience API to configure DAS partitions. A typical
flow (see `software/apps/baremetal/das_gemm_f32/main.c` for a full example):

```c
// 1. Initialize the DAS heap allocator
mempool_dynamic_heap_alloc_init(core_id);
alloc_t *das_alloc = get_dynamic_heap_alloc();

// 2. Allocate buffers from the DAS heap
float *a = (float *)partition_malloc(das_alloc, a_size);
float *b = (float *)partition_malloc(das_alloc, b_size);

// 3. Configure DAS partitions
//    das_config(partition_id, tiles_per_partition, start_addr, size_bytes)
//    - Setting tiles_per_partition = 1 maps the region to a single tile (local).
//    - Setting tiles_per_partition = NUM_TILES keeps the default full interleaving.
das_config(0, 1,         (uint32_t)a, a_size);  // a: local to one tile
das_config(1, NUM_TILES, (uint32_t)b, b_size);  // b: fully interleaved

// 4. Use the buffers normally — the hardware handles address remapping

// 5. Free when done
partition_free(das_alloc, b);
partition_free(das_alloc, a);
```
