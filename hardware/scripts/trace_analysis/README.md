# Benchmark Trace Analysis

Two stages, and you can run them independently:

```
result_dir=<run> make benchmark  ->  <run>/{data,topology.env,...}
result_dir=<run> make plots      ->  <run>/plots
```

Run both commands from `hardware/`. `make benchmark` builds and simulates an
application, converts its traces, and saves the analysis inputs. `make plots`
only reads the selected result directory, including its recorded topology.

## Quick Start

Use the [normal MemPool toolchain setup](../../../README.md#get-started). From
the repository root, run:

```bash
python3 -m pip install -r python-requirements.txt
cd hardware
result_dir=results/example make benchmark
result_dir=results/example make plots
```

The workflow defaults to `app=matmul_i32`, `config=mempool`, `das=1`,
`back2local=0` (see the [configuration guide](../../../config/README.md#back2local)),
and the QuestaSim target `simc`. Without `result_dir`, it uses:

```
results/<app>_<config>/<baseline|das>[_back2local]
```

This suffix is only a run label derived from `das` and `back2local`. Setting
`variant` changes the directory name, not the hardware configuration.

## Options

Normal Make configuration variables, such as `config`, `das`, topology sizes,
and application-specific build variables, configure the benchmark stage. These
variables control the workflow itself:

| Variable | Default | Effect |
|----------|---------|--------|
| `app` | `matmul_i32` | Bare-metal application to build and simulate |
| `python` | `python3` | Python interpreter used by the workflow |
| `result_dir` | path above | Result directory written or read |
| `benchmark_sim` | `simc` | Simulator target; use `simcvcs` for VCS |
| `extract_jobs` | `16` | Parallel trace conversion and extraction jobs |
| `force` | off | Set `force=1` to replace existing benchmark CSVs |
| `plot_section` | `1` | [Benchmark section](#sections-and-addresses) selected by both plotters |
| `plot_indiv_tiles` | `0` | Set to `1` to add every per-tile page |
| `plot_window_cycles` | `64` | Time-series bin width in cycles |
| `plot_comm` | `1` | Set to `0` to omit communication figures |
| `plot_jobs` | `1` | Parallel workers for per-tile pages |

Both scripts take `--help`. `plot_comm.py --figures ...` renders selected
communication figure families.

## Result Directory

`make benchmark` produces:

```
<run>/
  <app>, <app>.dump
  results.csv, avg.txt
  topology.env
  transcript                 # when available
  data/
    comm_events_benchmark.csv
    stall_timeseries_benchmark.csv
```

Raw trace intermediates are removed after extraction. The two files under
`data/` and `topology.env` are the inputs to `make plots`. Performance summaries
and the application binary are kept for reference.

`make plots` adds:

```
<run>/plots/
  overview/
    overview_workload.png
    group_ipc_breakdown.png
    overview_temporal.png
  communication/
    traffic_matrix.png
    traffic_matrix_groups.png
    latency_timeseries.png
    latency_tile_g<N>.png
    latency_matrix.png
    latency_excess_matrix.png
  group<N>/
    tile_detail_tile<N>.png
    subgroup<N>/tile_detail_tile<N>.png
```

Tile-detail plots are generated only with `plot_indiv_tiles=1`. Topologies
without subgroups place them directly under `group<N>`; other topologies use
the intermediate `subgroup<N>` directory. Existing plots are overwritten, but
files from figure families that are no longer selected are not removed.

`make benchmark` refuses to replace either analysis CSV unless `force=1` is
set. `make plots` requires the saved inputs but does not use the current RTL
configuration. If `result_dir` is omitted, the current Make variables only
select its default path.

## Sections and Addresses

The standard workflow extracts section 1, delimited by writes to the `trace`
CSR. It therefore expects one `mempool_start_benchmark()` and
`mempool_stop_benchmark()` bracket. Applications with another section layout
must use `scripts/trace_analysis/extract/extract_benchmark_csvs.py` directly
with `--section`.

For `make benchmark`, a testbench observer records the physical address of
every accepted Snitch LSU request after RTL scrambling. The address trace is
joined to the core trace by cycle. Any mismatch aborts extraction. This makes
the destination fields valid for runtime DAS configurations without modelling
the scrambler in Python.

The observer covers core LSU traffic in `simc` and `simcvcs`. DMA traffic and
other memory masters are not part of these CSVs. A plain `make trace` uses the
logical core-trace address. This is enough for stall analysis, but not for
physical DAS locality. Because the observer is a compile-time testbench option,
switching between `make benchmark` and a plain simulation in one build directory
can rebuild the simulation model.

## CSV Contract

`stall_timeseries_benchmark.csv`:

```
core,group,tile,tile_in_group,core_in_tile,core_in_group,section,cycle,state,pc,insn,stall_interval_id,stall_interval_start,stall_interval_end,stall_interval_cycles,stall_interval_offset,stall_kind,stall_kind_exact,stall_tot,stall_ins,stall_raw,stall_raw_lsu,stall_raw_acc,stall_lsu,stall_acc,stall_wfi
```

`comm_events_benchmark.csv`:

```
section,cycle,core,group,subgroup,tile,tile_in_group,tile_in_subgroup,core_in_tile,core_in_group,event_type,request_id,pc,insn,origin_pc,origin_insn,rd,size_bytes,address,region,dest_tile,dest_group,dest_subgroup,is_local,is_same_group,is_same_subgroup,issue_cycle,return_cycle,latency
```

The stall CSV contains one `issue` or `stall` row per represented core cycle.
Reported stall causes can overlap and need not add up to `stall_tot`.
`stall_raw_lsu` and `stall_raw_acc` are inferred from register dependencies.
Plots divide mixed-cause cycles between their reported causes. The
`stall_interval_*` fields identify each reconstructed stall interval and the
row's offset within it. For stall rows, `stall_kind_exact` is `1` when at most
one cause was reported.

The communication CSV contains `load_issue`, `store_issue`, and `load_return`
rows. `request_id` joins a load return to its issue. Traffic figures count load
and store issues, while latency figures use load returns. Requests outside the
decoded TCDM regions have empty destination and locality fields. `region`
classifies the logical address as `sequential`, `interleaved`, or `other`.

`address` is the logical `alu_result` value inherited from the core trace. For
post-increment operations this is the updated base address, not the address
accessed. The `dest_*` and locality fields still use the physical TCDM address
observed for the accepted request.

## Topology Metadata

Every result needs `topology.env` beside its `data` directory. The required
keys are `NUM_CORES`, `NUM_GROUPS`, `NUM_CORES_PER_TILE`, `SEQ_MEM_SIZE`,
`BANKING_FACTOR`, `L1_BANK_SIZE`, and `NUM_SUB_GROUPS_PER_GROUP`. `CONFIG` is
informational. `REMOTE_GROUP_LATENCY_CYCLES` is optional for old runs and
defaults to 7.

Values must be positive and describe an evenly divisible core, tile, group,
and subgroup hierarchy. `make benchmark` writes this file automatically. For
data produced elsewhere, create it manually or pass `--topology-env` to the
extractor.

## Extending the Workflow

Keep the result directory as the boundary between simulation, extraction, and
plotting:

- Make targets and recorded metadata live in `benchmark.mk`.
- Topology validation and derived geometry live in `_workflow_metadata.py`.
- Add trace events or CSV fields in `extract/extract_benchmark_csvs.py`.
- Add stall figures in `plot/_stall_plots.py` and communication figures in
  `plot/plot_comm.py`.
- Keep plotters dependent on the saved CSVs and `topology.env`, not the current
  build directory or Make configuration.

Python names prefixed with an underscore are internal. The public interfaces
are `make benchmark`, `make plots`, the two CSV schemas, and `topology.env`.
