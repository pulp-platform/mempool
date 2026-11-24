# TensorPool tutorial

This Tutorial on TensorPool consists of three steps:
1. build and run an application,
2. run a test app where TensorPool introduces itself,
3. write a multi-head attention (MHA) application.

To run the tutorial, clone MemPool and compile its toolchain, then clone GVSoC
and install its Python requirements. Both repositories are cloned side by side
in the same parent directory (the commands below assume it).

```bash
# MemPool
git clone https://github.com/pulp-platform/mempool.git
cd mempool
git submodule update --init --recursive
git submodule sync --recursive
pip3 install -r python-requirements.txt
make bender
make tc-riscv-gcc
make tc-llvm
cd ..

# GVSoC
git clone https://github.com/gvsoc/gvsoc.git
cd gvsoc
git submodule update --init --recursive -j8
pip3 install -r core/requirements.txt
pip3 install -r gapy/requirements.txt
pip3 install -r pulp/requirements.txt
cd ..
```

---

## 1. Compile and run

### 1.1 Software (MemPool repo)

The architecture is chosen with make variables; defaults are in
`config/tensorpool.mk`.

```bash
cd ./mempool/software/tests/baremetal
make COMPILER=llvm config=tensorpool tensorpool_intro
# binary: ./mempool/software/bin/tests/baremetal/tensorpool_intro
```

### 1.2 Simulator (gvsoc repo)

Without the runner (plain gvsoc, e.g. on `gvsoc/main`, where `nextran_AI` does
not exist), build the software as in 1.1 and run:

```bash
cd ./gvsoc
source sourceme.sh && source sourceme_systemc.sh
make TARGETS=tensorpool build                    # once
export NUM_CORES=256 \
       NUM_CORES_PER_TILE=4 \
       NUM_SUB_GROUPS_PER_GROUP=4 \
       BANK_FACTOR=8 \
       BANK_SIZE=2048 \
       TENSOR_ENGINE=redmule \
       NUM_REDMULE_TILES=16 \
       REDMULE_HEIGHT=8 REDMULE_WIDTH=32 REDMULE_REGS=3
./install/bin/gvsoc --target tensorpool --work-dir /tmp/wd \
  --param mempool_soc/binary=../mempool/software/bin/tests/baremetal/tensorpool_intro run
```

---

## 2. Test app: TensorPool introduces itself

Source: `software/tests/baremetal/tensorpool_intro/main.c` (read it first). It is
built with the other bare-metal tests; it needs no generated data header.

### 2.1 Who am I? (PEs)

```c
uint32_t pe_id   = mempool_get_core_id(); // CSR mhartid, 0..NUM_CORES-1
uint32_t num_pes = mempool_get_core_count();
printf("PE %u: tile %u, sub-group %u, group %u\n", pe_id,
       mempool_get_tile_id(), mempool_get_sg_id(), mempool_get_group_id());
```

Every PE runs `main()` (SPMD). Helpers from `runtime/runtime.h`:
`mempool_get_{tile,group,sg}_{id,count}()`. Call `mempool_init(pe_id)` and
`mempool_barrier_init(pe_id)` first, and use `mempool_barrier(num_pes)` to
synchronize. Print only from a few PEs, otherwise the log is enormous.

### 2.2 Which tensor engine do I drive?

```c
uint32_t te_id  = mempool_get_redmule_id();   // (uint32_t)-1 if none
uint32_t num_te = mempool_get_redmule_count();
if (te_id < num_te) printf("PE %u programs tensor engine %u\n", pe_id, te_id);
```

One TE sits in a tile; the **first PE of that tile** is the one allowed to
program it. The 16 TEs are spread evenly over the 16 sub-groups. All other PEs
get `-1`, so `te_id < num_te` is the idiom for "I am a TE driver".

### 2.3 A parallel for-loop on PEs *and* TEs

```c
// (a) TE drivers launch an asynchronous job: C(16x16) = A(16x16) * B(16x16)
if (te_id < num_te)
  redmule_start(&A[te_id*256], &B[te_id*256], &C[te_id*256], 16,16,16, 0, GEMM);
// (b) meanwhile all the PEs run y = 3*x + y, strided over the PEs
for (uint32_t i = pe_id; i < LEN; i += num_pes) y[i] += 3 * x[i];
// (c) TE drivers sleep until the TE interrupt, then everybody synchronizes
if (te_id < num_te) mempool_wfi();
mempool_barrier(num_pes);
```

Take-aways

* **Work split**: PEs use the strided loop
`for (i = pe_id; i < N; i += num_pes)`; TEs split the *data* by `te_id` (each
one gets its own slice of the batch).
* **Asynchronous TE**: `redmule_start` returns immediately, `mempool_wfi()`
waits for the end-of-job event. Compute on the PEs between the two to overlap
them.
* **Memory**: data touched by TEs must live in L1; use
`__attribute__((section(".l1_prio")))` (see the top of the file) and
`dma_memcpy_blocking(l1_dst, l2_src, bytes)` from PE 0 to bring it from L2.
* `mempool_start_benchmark()` / `mempool_stop_benchmark()` delimit a region
measured by the simulator (cycle counts).

Output (simulated, 256 PEs / 16 TEs; also prints `[BENCH]` lines, one per PE):

```
TensorPool: 256 PEs, 64 tiles, 16 sub-groups, 4 groups, 16 tensor-engines
PE 0: tile 0, sub-group 0, group 0
PE 1: tile 0, sub-group 0, group 0
...
PE 7: tile 1, sub-group 0, group 0
PE 0 programs tensor engine 0
PE 16 programs tensor engine 1
...
PE 112 programs tensor engine 7
Done, 0 errors
```

**Exercises**:
(i) print the sub-group id for the TE drivers;
(ii) make the PEs compute a dot product with a reduction instead of AXPY;
(iii) let each TE multiply a 32x32 problem and check the cycle count with the
benchmark region.

---

## 3. Build a multi-head attention app

Reference solution: `software/apps/nn/multihead_f16/main.c`. Build the app
yourself step by step by editing that file (the solution is always available
with `git show HEAD:software/apps/nn/multihead_f16/main.c`).

### 3.1 The algorithm

`H` heads, `M` tokens, `N` features per head (here `H=4, M=32, N=32`).

```
Q = X Wq    K = X Wk    V = X Wv     X: (H*M x N), W: (N x N)   -> TE (GEMM)
Kt = transpose(K) per head                                      -> PEs
A  = Q Kt        (H x M x M)                                    -> TE, one head per TE
S  = softmax(A)  (row-wise)                                     -> PEs
Z  = S V         (H x M x N)                                    -> TE, one head per TE
```

Each stage maps to the unit that is best at it: matrix products on TEs,
transpose and softmax on PEs.

### 3.2 Step 0: reference data

`software/data/gendatalib_nn.py::generate_fmultihead` produces `X, Wq, Wk, Wv`
and the golden output `Z` in numpy; sizes are in
`software/data/gendata_params.hjson` (`"multihead_f16"`, defines `H, M, N`).
The header `data_multihead_f16.h` is regenerated by make (`data_%.h` rule in
`runtime/runtime.mk`) and puts the arrays in L2 (`l2_X`, `l2_Wq`, ..., `l2_Y` =
output reference/buffer). Change `H, M, N` in the hjson to change the problem
size.

### 3.3 Step 1: L1 buffers and transfers

Declare everything the TEs touch in `.l1_prio`: `l1_X [H*M*N]`,
`l1_Wq/Wk/Wv [N*N]`, `l1_QKV [3*H*M*N]` (Q, K, V are three slices of it),
`l1_A, l1_S [H*M*M]`. PE 0 copies in X and the weights with
`dma_memcpy_blocking`, then `mempool_barrier`. (Check: print `l1_X[0]`.)

### 3.4 Step 2: Q, K, V on all the TEs

The following function splits the `H*M` rows of X evenly over all TEs
(`M / num_redmules` rows each), computing `Y(MxP) = X(MxN) * W(NxP)`.
Repeat for Wk and Wv.
```c
redmule_synch_parallel(l1_X, l1_Wq, Q, H*M, N, N, MATMUL, SHIFT, PORT_WIDTH);
```

### 3.5 Step 3: transpose K with the PEs

Write `Kt` into its own buffer (`l1_Kt`).
NB In the example PEs loop over 16-element chunks (`transpose_K` in the
reference): 16 loads then 16 post-increment stores (`p.sh.rrpost`) with stride
`M*2` bytes. Each PE handles `idx = pe_id*16; idx += num_pes*16`.

### 3.6 Step 4: A = Q Kt, one head per TE

```c
uint32_t id = mempool_get_redmule_id();
uint32_t n = mempool_get_redmule_count();
if (id < n)
  for (uint32_t h = id; h < H; h += n)
    redmule_asynch_single(&Q[h*M*N], &K[h*N*M], &A[h*M*M], M, N, M, MATMUL, id);
mempool_barrier(num_pes);
```

### 3.7 Step 5: softmax with the PEs

`softmax_parallel_2x4_f16vec(A, S, H*M, M, pe_id, num_pes)` from
`kernels/baremetal/mempool_softmax_f16.h`: row-wise softmax over `H*M` rows of
length `M`, rows distributed over the PEs. Barrier afterwards.

### 3.8 Step 6: Z = S V, then write back

Same as Step 4 with `S` and `V`, output in `l1_X` (it is free by now), then PE 0
copies the result to L2 with `dma_memcpy_blocking`.
Compare with the numpy `Z` stored in the header (tolerance ~1e-2 in fp16).

### 3.9 Verify and run

Call `mempool_check_f16(l2_Y, l2_Z, H*M*N, 0.01, 0)` at the end; it prints
`<n> ERRORS out of 4096 CHECKS`.
Note that the data header is regenerated with new random data at every build.

Checkout the example. How does it compare to your solution?
Look at the cycles of each `mempool_start/stop_benchmark` region in the log:
which stage dominates? Now you can try the following:

(i) `DEFINES=-DDOUBLE_BUFFERING` to overlap the transpose and Q computation,
(ii) more heads than TEs,
(iii) fewer TEs (`NUM_TE_TILES=8`) and observe the scaling.
