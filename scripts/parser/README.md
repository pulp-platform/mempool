# Parser — Pipeline performance model & app generator

Analytical tooling for **NN inference on the SoftHier x TeraPool/TensorPool**
architecture. From a single description of the model's layers plus a hardware
config it:

1. computes per-layer **latency / L1 performance tables** for each compute pool
   (e.g. *Terapool*, *TensorPool*),
2. optionally splits the work across clusters to meet a throughput budget, and
3. generates ready-to-build **multi-cluster apps** (`pipeline_<mode>_<pool>/main.c`)
   under `software/apps/multi_cluster/`.

## Files

| File                 | Role                                                                                              |
| -------------------- | ------------------------------------------------------------------------------------------------- |
| `pipeline.py`      | Core model: parses the template, prints performance tables, and generates the GVSOC pipeline apps |
| `config.json`      | Hardware configuration                                                                            |
| `L1_transformer.csv` | Example layer template (L1 transformer)                                                         |

`pipeline.py` is a single script. Each run prints the performance tables and
emits per-pool GVSOC pipeline apps. With no `--mode` it covers all three
flavours; `--mode {seq,ctt,cwt}` restricts to one:

- **seq** — sequential pipeline: one stage per cluster, gated by `if (cid == i)`
  + a barrier after each, so stages run one after another and a single item
    flows through.
- **ctt** — **compute-then-transfer** streaming pipeline (single L1 buffer,
  compute & DMA serialized); `--iterations N` items streamed as a wavefront.
- **cwt** — **compute-while-transfer** streaming pipeline (double-buffered L1,
  compute & DMA overlap); `--iterations N` items streamed as a wavefront. Its
  `max(compute, transfer)` per-stage cost is a *steady-state* figure — for few
  iterations the longer fill/drain can make it slower than `ctt` (see the
  steady-state note under [`config.json`](#configjson-hardware)).

## Requirements

Python 3. CSV templates work with the standard library only. Other formats need
extra packages (imported lazily): `openpyxl` for `*.xlsx` / `*.xlsm`,
`pandas` (with the `odf` engine) for `*.ods`, and `matplotlib` for `--plot`:

```bash
pip install openpyxl pandas matplotlib
```

## Inputs

### Template (`.csv`, `.xlsx`, `.xlsm`, `.ods`)

The **header row** (the one labelling `N_repetitions` / `Kernel` /
`FLOPs` / `Weights` / `Data_in` / `Data_out`) is found automatically; layers are
read from the row below it until the trailing parameter block — reading **stops
at the first row whose block-name cell (column A) is filled but whose operation
cell (column C) is empty**. Parameter tables, notes or totals above the header or
below that stop point are ignored, so they can sit at the top or bottom of the
file.

- **Block name** → column A (a real block header carries its first operation on the same row)
- **Operation name** → column C
- **Kernel**, **N_repetitions**, **FLOPs**, **Weights**, **Data_in**, **Data_out** → located by their header names

A layer is costed at **`GEMM_peak`** when its **`Kernel`** is one of `GEMM_KERNELS`
(`dense`, `matmul`, `conv1d` — the last is lowered to a GEMM via im2col); every other
kernel (`layernorm`, `softmax`, `gelu`, `add`, `reshape`, `split`, `transpose`, …)
runs on the PE path at `PE_peak × PE_utilization`. To change which kernels map to the
GEMM engine, edit `GEMM_KERNELS` in `pipeline.py`.

`CEViT_64PRBs.csv` and `L1_transformer.csv` are both working examples.

### `config.json` (hardware)

```json
{
    "PE_peak":   { "Terapool": 3.7, "TensorPool": 1.0 },   // non-GEMM peak, TFLOPS
    "GEMM_peak": { "Terapool": 1.1, "TensorPool": 6.62 },  // GEMM peak, TFLOPS
    "PE_utilization": 0.5,        // fraction in [0,1], applied to PE_peak only (non-GEMM ops); GEMM_peak is unscaled
    "throughput": 1.0,            // per-cluster wall-clock budget [ms]; seq/ctt: compute+transfer, cwt: max(compute,transfer); omit to skip cluster splitting
    "bandwidth_gbs": 4,           // inter-cluster/HBM bandwidth [GB/s] for transfer-time estimate; omit or 0 to count compute only
    "frequency": 1000000000       // clock in Hz
}
```

| Key                | Meaning                                                                                                                                                                                                                                                                                                                                                                                                                                                  |
| ------------------ | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `PE_peak`        | Per-pool non-GEMM peak throughput, TFLOPS                                                                                                                                                                                                                                                                                                                                                                                                                |
| `GEMM_peak`      | Per-pool GEMM peak throughput, TFLOPS (not scaled by`PE_utilization`)                                                                                                                                                                                                                                                                                                                                                                                  |
| `PE_utilization` | Fraction in`[0, 1]` applied to `PE_peak` only                                                                                                                                                                                                                                                                                                                                                                                                        |
| `throughput`     | Per-cluster wall-clock budget [ms]. The split is computed per mode:`seq`/`ctt` use `compute + transfer` (serialized), `cwt` uses `max(compute, transfer)` (overlapped), so `cwt` generally yields fewer, larger clusters. It **fixes the cluster count `N`**; the work is then rebalanced within those `N` clusters to minimise the real bottleneck (see [Throughput rebalancing](#throughput-rebalancing)). Omit to skip splitting |
| `bandwidth_gbs`  | Inter-cluster / HBM bandwidth [GB/s]. Transfer time =`bytes / (bandwidth_gbs * 1e6)` ms. Omit or `0` to count compute only                                                                                                                                                                                                                                                                                                                           |
| `frequency`      | Clock in Hz; used to convert latencies into cycles for the generated apps                                                                                                                                                                                                                                                                                                                                                                                |

### Note

> `throughput` is **required** to generate apps (it drives the per-cluster
> split). Without it the tables still print but you get "no cluster splits found".
>
> Each cluster's transfer cost is its last layer's `Data_out` hand-off, plus the
> HBM `Data_in` load on cluster 0. With `bandwidth_gbs` unset, only compute time
> counts toward `throughput` (and both splits coincide).
>
> The printed "Pipeline cluster split" section shows **both** splits — serialized
> (`seq`/`ctt`) and overlapped (`cwt`). Each is the **rebalanced** split and is headed
> by a `>>> Best throughput found = … ms` line (the minimised bottleneck for that
> pool/mode); see [Throughput rebalancing](#throughput-rebalancing).
>
> **The `cwt` budget `max(compute, transfer)` is a *steady-state* figure.** It is
> the amortized per-item cost only once the pipeline is full. The generated
> schedules run `N_ITER + N − 1` steps for `ctt` and `N_ITER + 2·(N − 1) + 1` for
> `cwt` (`N` = cluster count), each step ≈ the budget. So the per-item cost is:
>
> - `ctt` → `(1 + (N − 1)/N_ITER) × (compute + transfer)`
> - `cwt` → `(1 + (2N − 1)/N_ITER) × max(compute, transfer)`
>
> Because double buffering gives an inter-stage offset of **2**, `cwt`'s
> fill/drain transient (`2·(N − 1)` steps) is **twice** as long as `ctt`'s
> (`N − 1`), and a single item has nothing to overlap. For small `--iterations`
> (worst case `1`) the transient dominates and `cwt` can be **slower** than `ctt`;
> the `max(compute, transfer)` split only pays off as `N_ITER ≫ N`. So `cwt`'s
> benefit is *fewer clusters at the same steady-state throughput*, not lower
> single-item latency — raise `--iterations` to amortize the longer warm-up.

### Throughput rebalancing

`throughput` is a *starting budget*, not the final answer. For each pool and mode the
tool runs two phases:

1. **Split levels over clusters** — the greedy left-to-right packer fills clusters up to
   the budget, which fixes the cluster count `N`.
2. **Rebalance within `N`** — holding `N` constant, it pushes the per-cluster wall as low
   as possible so the work (compute **and** hand-off transfers) is spread evenly,
   minimising the slowest stage. Because a pipeline's throughput is set by its slowest
   stage, this is the best achievable throughput for that `N`.

The optimum is found by binary-searching the budget while reusing the same greedy as a
feasibility test — the smallest budget that still fits the work into `N` clusters. The
result is printed as `>>> Best throughput found = X ms` at the head of each pool/mode
split, and the generated apps use the rebalanced distribution. This step **never
changes `N`**.

## Usage

Run from inside this folder so the default paths resolve. Each run **prints the
performance tables and generates the GVSOC pipeline apps** — there is no separate
"tables only" or "generate only" step.

### Default — both splits, all three modes

```bash
python3 pipeline.py <template> <config>
# e.g.
python3 pipeline.py L1_transformer.csv config.json
```

Prints **both** cluster splits (serialized for `seq`/`ctt`, overlapped for
`cwt`) and generates one app per (mode, pool) under
`software/apps/multi_cluster/` — e.g. `pipeline_seq_Terapool`,
`pipeline_ctt_TensorPool`, `pipeline_cwt_Terapool`. Generation requires
`throughput` in the config (without it the tables still print).

Each generated app builds with the standard multi-cluster flow:

```bash
make -C software/apps/multi_cluster pipeline_ctt_TensorPool
# -> software/bin/multi_cluster/pipeline_ctt_TensorPool (+ .dump)
```

### One flavour — `--mode {seq,ctt,cwt}`

`--mode` restricts everything to a single flavour: it prints only that mode's
cluster split and generates only its apps. `ctt`/`cwt` stream
`--iterations N` items through the pipeline (fill → steady state → drain):

```bash
# sequential             -> pipeline_seq_<pool>/
python3 pipeline.py L1_transformer.csv config.json --mode seq

# compute-then-transfer  -> pipeline_ctt_<pool>/
python3 pipeline.py L1_transformer.csv config.json --mode ctt --iterations 8

# compute-while-transfer -> pipeline_cwt_<pool>/
python3 pipeline.py L1_transformer.csv config.json --mode cwt --iterations 8
```

| Option                   | Description                                                                                                         |
| ------------------------ | ------------------------------------------------------------------------------------------------------------------- |
| `template`             | Layer template (positional)                                                                                         |
| `config`               | Hardware JSON config, must contain`throughput` (positional)                                                       |
| `--mode {seq,ctt,cwt}` | Restrict to one flavour: print only its split and generate only its apps. Omit for both splits + all three modes    |
| `--iterations N`       | Items streamed through the pipeline for`ctt`/`cwt` (default `1`; ignored by `seq`)                          |
| `--out DIR`            | Apps root under which the`pipeline_<mode>_<pool>/` dirs are created (default: `software/apps/multi_cluster/`)   |
| `--plot`               | Save per-pool bar plots of the cluster split(s) as PNGs under`./split_plots/` (needs `matplotlib`) — see below |

Each generated app directory holds a single `main.c` (timing-only: one
`mempool_wait()` placeholder per layer) — one app per compute pool. The flat
`pipeline_<mode>_<pool>/main.c` layout is what the multi-cluster Makefile
discovers (`find $(APPS_DIR) -name "main.c"`), and the app name doubles as the
make target and the binary name. The apps run on placeholder data, so they need
no HBM preload and no `data_<app>.h`.

### 3. Split plots (`--plot`)

`--plot` saves one bar plot per pool and per relevant split to `./split_plots/`
(`CTT_split_<pool>.png`, `CWT_split_<pool>.png`). x-axis is cluster ID,
y-axis is wall time in ms capped at `throughput`; **red = compute, green =
transfer**:

- **serialized** (`seq`/`ctt`) — **stacked** bars, so the bar height is the wall
  time `compute + transfer`;
- **overlapped** (`cwt`) — **side-by-side** bars, where the wall time is the
  taller of the two (`max(compute, transfer)`).

Without `--mode` both splits are plotted; with `--mode` only the matching one.
Needs `matplotlib` (`pip install matplotlib`); if missing, plotting is skipped
with a warning.
