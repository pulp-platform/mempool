// Copyright 2024 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "mempool/mempool.svh"

/* verilator lint_off DECLFILENAME */
module mempool_tile
  import mempool_pkg::*;
  import cf_math_pkg::idx_width;
#(
  // TCDM
  parameter addr_t       TCDMBaseAddr = 32'b0,
  // Boot address
  parameter logic [31:0] BootAddr     = 32'h0000_1000,
  // Dependent parameters. DO NOT CHANGE.
  parameter int unsigned NumCaches    = NumCoresPerTile / NumCoresPerCache,
  // If NumDivsqrtPerTile is set, otherwise the parameter defaults to 1.
  parameter int unsigned NumCoresPerDivsqrt = |NumDivsqrtPerTile ? (NumCoresPerTile/NumDivsqrtPerTile) : NumCoresPerTile
) (
  // Clock and reset
  input  logic                                                                    clk_i,
  input  logic                                                                    rst_ni,
  // Scan chain
  input  logic                                                                    scan_enable_i,
  input  logic                                                                    scan_data_i,
  output logic                                                                    scan_data_o,
  // Tile ID
  input  logic                            [idx_width(NumTiles)-1:0]               tile_id_i,
  // TCDM Master interfaces
  output `STRUCT_VECT(tcdm_master_req_t,  [NumRemoteReqPortsPerTile-1:0])         tcdm_master_req_o,
  output logic                            [NumRemoteReqPortsPerTile-1:0]          tcdm_master_req_valid_o,
  input  logic                            [NumRemoteReqPortsPerTile-1:0]          tcdm_master_req_ready_i,
  input  `STRUCT_VECT(tcdm_master_resp_t, [NumRemoteRespPortsPerTile-1:0])        tcdm_master_resp_i,
  input  logic                            [NumRemoteRespPortsPerTile-1:0]         tcdm_master_resp_valid_i,
  output logic                            [NumRemoteRespPortsPerTile-1:0]         tcdm_master_resp_ready_o,
  // TCDM slave interfaces
  input  `STRUCT_VECT(tcdm_slave_req_t,   [NumRemoteReqPortsPerTile-1:0])         tcdm_slave_req_i,
  input  logic                            [NumRemoteReqPortsPerTile-1:0]          tcdm_slave_req_valid_i,
  output logic                            [NumRemoteReqPortsPerTile-1:0]          tcdm_slave_req_ready_o,
  output `STRUCT_VECT(tcdm_slave_resp_t,  [NumRemoteRespPortsPerTile-1:0])        tcdm_slave_resp_o,
  output logic                            [NumRemoteRespPortsPerTile-1:0]         tcdm_slave_resp_valid_o,
  input  logic                            [NumRemoteRespPortsPerTile-1:0]         tcdm_slave_resp_ready_i,
  // TCDM DMA interfaces
  input  `STRUCT_PORT(tcdm_dma_req_t)                                             tcdm_dma_req_i,
  input  logic                                                                    tcdm_dma_req_valid_i,
  output logic                                                                    tcdm_dma_req_ready_o,
  output `STRUCT_PORT(tcdm_dma_resp_t)                                            tcdm_dma_resp_o,
  output logic                                                                    tcdm_dma_resp_valid_o,
  input  logic                                                                    tcdm_dma_resp_ready_i,
  // AXI Interface
  output `STRUCT_PORT(axi_tile_req_t)                                             axi_mst_req_o,
  input  `STRUCT_PORT(axi_tile_resp_t)                                            axi_mst_resp_i,
  // Wake up interface
  input  logic                            [NumCoresPerTile-1:0]                   wake_up_i
);

  /****************
   *   Includes   *
   ****************/

  `include "common_cells/registers.svh"

  /*****************
   *  Definitions  *
   *****************/

  import snitch_pkg::dreq_t;
  import snitch_pkg::dresp_t;

  typedef logic [idx_width(NumRemoteReqPortsPerTile)-1:0] remote_ports_index_t;

  // Local interconnect address width
  typedef logic [idx_width(NumCoresPerTile + NumRemoteReqPortsPerTile)-1:0] local_req_interco_addr_t;
  typedef logic [idx_width(NumCoresPerTile + NumRemoteRespPortsPerTile)-1:0] local_resp_interco_addr_t;

  /*********************
   *  Control Signals  *
   *********************/
  logic [NumCoresPerTile-1:0] wake_up_q;
  `FF(wake_up_q, wake_up_i, '0, clk_i, rst_ni);

  // Group ID
  group_id_t group_id;
  if (NumGroups != 1) begin: gen_group_id
    assign group_id = tile_id_i[$clog2(NumTiles)-1 -: $clog2(NumGroups)];
  end else begin: gen_group_id
    assign group_id = '0;
  end: gen_group_id

  /************************
   *  Bank Address Remap  *
   ************************/
  tcdm_dma_req_t                               tcdm_dma_req_remapped;
  tcdm_slave_req_t [NumRemoteReqPortsPerTile-1:0] tcdm_slave_req_remapped;
  tcdm_slave_req_t [NumCoresPerTile-1:0]       local_req_interco_payload_remapped;

  /***********
   *  Cores  *
   ***********/

  // Instruction interfaces
  addr_t [NumCaches-1:0][NumCoresPerCache-1:0] snitch_inst_addr;
  data_t [NumCaches-1:0][NumCoresPerCache-1:0] snitch_inst_data;
  logic  [NumCaches-1:0][NumCoresPerCache-1:0] snitch_inst_valid;
  logic  [NumCaches-1:0][NumCoresPerCache-1:0] snitch_inst_ready;

  // Shared operational units interfaces
  logic       [NumCoresPerTile-1:0] sh_acc_req_valid;
  logic       [NumCoresPerTile-1:0] sh_acc_req_ready;
  logic       [NumCoresPerTile-1:0] sh_acc_resp_valid;
  logic       [NumCoresPerTile-1:0] sh_acc_resp_ready;
  snitch_pkg::acc_req_t      [NumCoresPerTile-1:0] acc_req;
  snitch_pkg::acc_resp_t     [NumCoresPerTile-1:0] acc_resp;
  snitch_pkg::sh_acc_req_t   [NumCoresPerTile-1:0] sh_acc_req;
  snitch_pkg::sh_acc_resp_t  [NumCoresPerTile-1:0] sh_acc_resp;

  // Data interfaces
  addr_t    [NumCoresPerTile-1:0] snitch_data_qaddr;
  addr_t    [NumCoresPerTile-1:0] snitch_data_qaddr_scrambled;
  logic     [NumCoresPerTile-1:0] snitch_data_qwrite;
  amo_t     [NumCoresPerTile-1:0] snitch_data_qamo;
  data_t    [NumCoresPerTile-1:0] snitch_data_qdata;
  strb_t    [NumCoresPerTile-1:0] snitch_data_qstrb;
  meta_id_t [NumCoresPerTile-1:0] snitch_data_qid;
  logic     [NumCoresPerTile-1:0] snitch_data_qvalid;
  logic     [NumCoresPerTile-1:0] snitch_data_qready;
  data_t    [NumCoresPerTile-1:0] snitch_data_pdata;
  logic     [NumCoresPerTile-1:0] snitch_data_perror;
  meta_id_t [NumCoresPerTile-1:0] snitch_data_pid;
  logic     [NumCoresPerTile-1:0] snitch_data_pvalid;
  logic     [NumCoresPerTile-1:0] snitch_data_pready;

  if (snitch_pkg::XDIVSQRT && !TrafficGeneration) begin: gen_divsqrt
    for (genvar c = 0; unsigned'(c) < NumDivsqrtPerTile; c++) begin: gen_divsqrt
      logic                     divsqrt_req_valid;
      logic                     divsqrt_req_ready;
      logic                     divsqrt_resp_valid;
      logic                     divsqrt_resp_ready;
      snitch_pkg::sh_acc_req_t  divsqrt_req;
      snitch_pkg::sh_acc_resp_t divsqrt_resp;

      // Assign output to shared response
      for (genvar i = 0; unsigned'(i) < NumCoresPerDivsqrt; i++) begin
        assign sh_acc_resp[c*NumCoresPerDivsqrt + i] = divsqrt_resp;
      end

      // Shared accelerator arbiter
      stream_arbiter #(
        .DATA_T      ( snitch_pkg::sh_acc_req_t    ),
        .N_INP       ( NumCoresPerDivsqrt          ),
        .ARBITER     ( "rr"                        )
      ) i_stream_arbiter_offload (
        .clk_i       ( clk_i                                                                  ),
        .rst_ni      ( rst_ni                                                                 ),
        .inp_data_i  ( sh_acc_req[((c+1)*NumCoresPerDivsqrt)-1:(c*NumCoresPerDivsqrt)]        ),
        .inp_valid_i ( sh_acc_req_valid[((c+1)*NumCoresPerDivsqrt)-1:(c*NumCoresPerDivsqrt)]  ),
        .inp_ready_o ( sh_acc_req_ready[((c+1)*NumCoresPerDivsqrt)-1:(c*NumCoresPerDivsqrt)]  ),
        .oup_data_o  ( divsqrt_req                                                            ),
        .oup_valid_o ( divsqrt_req_valid                                                      ),
        .oup_ready_i ( divsqrt_req_ready                                                      )
      );

      // Shared accelerator output demux
      stream_demux #(
        .N_OUP ( NumCoresPerDivsqrt )
      ) i_stream_demux_offload (
        .inp_valid_i  ( divsqrt_resp_valid                                                        ),
        .inp_ready_o  ( divsqrt_resp_ready                                                        ),
        .oup_sel_i    ( sh_acc_resp[c*NumCoresPerDivsqrt].hart_id[$clog2(NumCoresPerDivsqrt)-1:0] ),
        .oup_valid_o  ( sh_acc_resp_valid[((c+1)*NumCoresPerDivsqrt)-1:(c*NumCoresPerDivsqrt)]    ),
        .oup_ready_i  ( sh_acc_resp_ready[((c+1)*NumCoresPerDivsqrt)-1:(c*NumCoresPerDivsqrt)]    )
      );

      // Tile shared divsqrt unit
      snitch_fp_divsqrt #(
        .FPUImplementation       (snitch_pkg::DIVSQRT_IMPLEMENTATION)
      ) i_snitch_divsqrt (
        .clk_i,
        .rst_i                   (!rst_ni             ),
        // pragma translate_off
        .trace_port_o            (                    ),
        // pragma translate_on
        .acc_req_i               ( divsqrt_req        ),
        .acc_req_valid_i         ( divsqrt_req_valid  ),
        .acc_req_ready_o         ( divsqrt_req_ready  ),
        .acc_resp_o              ( divsqrt_resp       ),
        .acc_resp_valid_o        ( divsqrt_resp_valid ),
        .acc_resp_ready_i        ( divsqrt_resp_ready ),
        .divsqrt_rnd_mode_i      ( fpnew_pkg::RNE     ),
        .divsqrt_status_o        (                    ),
        .core_events_o           (                    )
      );
    end
  end

  for (genvar c = 0; unsigned'(c) < NumCoresPerTile; c++) begin: gen_cores
    logic [31:0] hart_id;
    assign hart_id = {unsigned'(tile_id_i), c[idx_width(NumCoresPerTile)-1:0]};

    if (!TrafficGeneration) begin: gen_mempool_cc
      mempool_cc #(
        .BootAddr (BootAddr)
      ) riscv_core (
        .clk_i         (clk_i                                                    ),
        .rst_i         (!rst_ni                                                  ),
        .hart_id_i     (hart_id                                                  ),
        // IMEM Port
        .inst_addr_o   (snitch_inst_addr[c/NumCoresPerCache][c%NumCoresPerCache] ),
        .inst_data_i   (snitch_inst_data[c/NumCoresPerCache][c%NumCoresPerCache] ),
        .inst_valid_o  (snitch_inst_valid[c/NumCoresPerCache][c%NumCoresPerCache]),
        .inst_ready_i  (snitch_inst_ready[c/NumCoresPerCache][c%NumCoresPerCache]),
        // Shared operational-units ports
        .sh_acc_req_o         (acc_req[c]                                        ),
        .sh_acc_req_valid_o   (sh_acc_req_valid[c]                               ),
        .sh_acc_req_ready_i   (sh_acc_req_ready[c]                               ),
        .sh_acc_resp_i        (acc_resp[c]                                       ),
        .sh_acc_resp_valid_i  (sh_acc_resp_valid[c]                              ),
        .sh_acc_resp_ready_o  (sh_acc_resp_ready[c]                              ),
        // Data Ports
        .data_qaddr_o  (snitch_data_qaddr[c]                                     ),
        .data_qwrite_o (snitch_data_qwrite[c]                                    ),
        .data_qamo_o   (snitch_data_qamo[c]                                      ),
        .data_qdata_o  (snitch_data_qdata[c]                                     ),
        .data_qstrb_o  (snitch_data_qstrb[c]                                     ),
        .data_qid_o    (snitch_data_qid[c]                                       ),
        .data_qvalid_o (snitch_data_qvalid[c]                                    ),
        .data_qready_i (snitch_data_qready[c]                                    ),
        .data_pdata_i  (snitch_data_pdata[c]                                     ),
        .data_perror_i (snitch_data_perror[c]                                    ),
        .data_pid_i    (snitch_data_pid[c]                                       ),
        .data_pvalid_i (snitch_data_pvalid[c]                                    ),
        .data_pready_o (snitch_data_pready[c]                                    ),
        .wake_up_sync_i(wake_up_q[c]                                             ),
        // Core Events
        .core_events_o (/* Unused */                                             )
      );
      if (snitch_pkg::XDIVSQRT) begin: gen_sh_acc_interface
        // Assign the cores' hart_id to the corresponding shared accelerator
        assign sh_acc_req[c].addr      = acc_req[c].addr;
        assign sh_acc_req[c].id        = acc_req[c].id;
        assign sh_acc_req[c].hart_id   = hart_id[$clog2(NumCoresPerDivsqrt)-1:0];
        assign sh_acc_req[c].data_op   = acc_req[c].data_op;
        assign sh_acc_req[c].data_arga = acc_req[c].data_arga;
        assign sh_acc_req[c].data_argb = acc_req[c].data_argb;
        assign sh_acc_req[c].data_argc = acc_req[c].data_argc;
        // Redistribute shared response to cores
        assign acc_resp[c].id     = sh_acc_resp[c].id;
        assign acc_resp[c].error  = sh_acc_resp[c].error;
        assign acc_resp[c].data   = sh_acc_resp[c].data;
      end else begin: silence_sh_acc_interface
        assign acc_resp[c]          = '0;
        assign sh_acc_req[c]        = '0;
        assign sh_acc_req_ready[c]  = '0;
        assign sh_acc_resp[c]       = '0;
        assign sh_acc_resp_valid[c] = '0;
      end
    end else begin
      // Silence acc interfaces
      assign acc_req[c]                                                = '0;
      assign sh_acc_req[c]                                             = '0;
      assign sh_acc_req_valid[c]                                       = '0;
      assign sh_acc_req_ready[c]                                       = '0;
      assign sh_acc_resp[c]                                            = '0;
      assign sh_acc_resp_valid[c]                                      = '0;
      assign sh_acc_resp_ready[c]                                      = '0;
      // Silence memory interfaces
      assign snitch_data_qaddr[c]                                      = '0;
      assign snitch_data_qwrite[c]                                     = '0;
      assign snitch_data_qamo[c]                                       = '0;
      assign snitch_data_qdata[c]                                      = '0;
      assign snitch_data_qstrb[c]                                      = '0;
      assign snitch_data_qid[c]                                        = '0;
      assign snitch_data_qvalid[c]                                     = '0;
      assign snitch_data_pready[c]                                     = '0;
      assign snitch_inst_addr[c/NumCoresPerCache][c%NumCoresPerCache]  = '0;
      assign snitch_inst_valid[c/NumCoresPerCache][c%NumCoresPerCache] = '0;
    end
  end

  /***********************
   *  Instruction Cache  *
   ***********************/
  // Instruction interface
  axi_core_req_t  [NumCaches-1:0] axi_cache_req_d, axi_cache_req_q;
  axi_core_resp_t [NumCaches-1:0] axi_cache_resp_d, axi_cache_resp_q;

  for (genvar c = 0; unsigned'(c) < NumCaches; c++) begin: gen_caches
    snitch_icache #(
      .NR_FETCH_PORTS     (NumCoresPerCache                                    ),
      /// Cache Line Width
      .L0_LINE_COUNT      (4                                                   ),
      .LINE_WIDTH         (ICacheLineWidth                                     ),
      .LINE_COUNT         (ICacheSizeByte / (ICacheSets * ICacheLineWidth / 8) ),
      .SET_COUNT          (ICacheSets                                          ),
      .FETCH_AW           (AddrWidth                                           ),
      .FETCH_DW           (DataWidth                                           ),
      .FILL_AW            (AddrWidth                                           ),
      .FILL_DW            (AxiDataWidth                                        ),
      .L1_TAG_SCM         (1                                                   ),
      /// Make the early cache latch-based. This reduces latency at the cost of
      /// increased combinatorial path lengths and the hassle of having latches in
      /// the design.
      .EARLY_LATCH        (1                                                   ),
      .L0_EARLY_TAG_WIDTH (11                                                  ),
      .ISO_CROSSING       (0                                                   ),
      .axi_req_t          (axi_core_req_t                                      ),
      .axi_rsp_t          (axi_core_resp_t                                     )
    ) i_snitch_icache (
      .clk_i                (clk_i                   ),
      .clk_d2_i             (clk_i                   ),
      .rst_ni               (rst_ni                  ),
      .enable_prefetching_i (1'b1                    ),
      .icache_events_o      (/* Unused */            ),
      .flush_valid_i        (1'b0                    ),
      .flush_ready_o        (/* Unused */            ),
      .inst_addr_i          (snitch_inst_addr[c]     ),
      .inst_data_o          (snitch_inst_data[c]     ),
      .inst_cacheable_i     ({NumCoresPerCache{1'b1}}),
      .inst_valid_i         (snitch_inst_valid[c]    ),
      .inst_ready_o         (snitch_inst_ready[c]    ),
      .inst_error_o         (/* Unused */            ),
      .axi_req_o            (axi_cache_req_d[c]      ),
      .axi_rsp_i            (axi_cache_resp_q[c]     )
    );
    axi_cut #(
      .aw_chan_t (axi_core_aw_t  ),
      .w_chan_t  (axi_core_w_t   ),
      .b_chan_t  (axi_core_b_t   ),
      .ar_chan_t (axi_core_ar_t  ),
      .r_chan_t  (axi_core_r_t   ),
      .axi_req_t (axi_core_req_t ),
      .axi_resp_t(axi_core_resp_t)
    ) axi_cache_slice (
      .clk_i     (clk_i              ),
      .rst_ni    (rst_ni             ),
      .slv_req_i (axi_cache_req_d[c] ),
      .slv_resp_o(axi_cache_resp_q[c]),
      .mst_req_o (axi_cache_req_q[c] ),
      .mst_resp_i(axi_cache_resp_d[c])
    );
  end

  /******************
   *  Memory Banks  *
   ******************/

  // Bank metadata
  typedef struct packed {
    local_req_interco_addr_t ini_addr;
    meta_id_t meta_id;
    group_id_t group_id;
    tile_group_id_t tile_id;
    tile_core_id_t core_id;
    logic wide;
  } bank_metadata_t;

  // Memory interfaces
  tcdm_dma_req_t           [NumSuperbanks-1:0]   tcdm_dma_req;
  logic                    [NumSuperbanks-1:0]   tcdm_dma_req_valid;
  logic                    [NumSuperbanks-1:0]   tcdm_dma_req_ready;
  tcdm_dma_resp_t          [NumSuperbanks-1:0]   tcdm_dma_resp;
  logic                    [NumSuperbanks-1:0]   tcdm_dma_resp_valid;
  logic                    [NumSuperbanks-1:0]   tcdm_dma_resp_ready;

  logic                    [NumBanksPerTile-1:0] superbank_req_valid;
  logic                    [NumBanksPerTile-1:0] superbank_req_ready;
  local_req_interco_addr_t [NumBanksPerTile-1:0] superbank_req_ini_addr;
  tcdm_slave_req_t         [NumBanksPerTile-1:0] superbank_req_payload;
  logic                    [NumBanksPerTile-1:0] superbank_resp_valid;
  logic                    [NumBanksPerTile-1:0] superbank_resp_ready;
  tcdm_slave_resp_t        [NumBanksPerTile-1:0] superbank_resp_payload;
  local_resp_interco_addr_t[NumBanksPerTile-1:0] superbank_resp_ini_addr;

  logic                    [NumBanksPerTile-1:0] bank_req_valid;
  logic                    [NumBanksPerTile-1:0] bank_req_ready;
  local_req_interco_addr_t [NumBanksPerTile-1:0] bank_req_ini_addr;
  logic                    [NumBanksPerTile-1:0] bank_req_wide;
  tcdm_slave_req_t         [NumBanksPerTile-1:0] bank_req_payload;
  logic                    [NumBanksPerTile-1:0] bank_resp_valid;
  logic                    [NumBanksPerTile-1:0] bank_resp_ready;
  tcdm_slave_resp_t        [NumBanksPerTile-1:0] bank_resp_payload;
  logic                    [NumBanksPerTile-1:0] bank_resp_wide;
  local_resp_interco_addr_t[NumBanksPerTile-1:0] bank_resp_ini_addr;

  tcdm_dma_req_t tcdm_dma_req_i_struct;
  assign tcdm_dma_req_i_struct = tcdm_dma_req_remapped;

  if (NumSuperbanks == 1) begin : gen_dma_interco_bypass
    assign tcdm_dma_req = tcdm_dma_req_i_struct;
    assign tcdm_dma_req_valid = tcdm_dma_req_valid_i;
    assign tcdm_dma_req_ready_o = tcdm_dma_req_ready;

    assign tcdm_dma_resp_o = tcdm_dma_resp;
    assign tcdm_dma_resp_valid_o = tcdm_dma_resp_valid;
    assign tcdm_dma_resp_ready = tcdm_dma_resp_ready_i;
  end else begin : gen_dma_interco
    stream_xbar #(
      .NumInp   (1             ),
      .NumOut   (NumSuperbanks ),
      .payload_t(tcdm_dma_req_t)
    ) i_dma_req_interco (
      .clk_i  (clk_i                                                  ),
      .rst_ni (rst_ni                                                 ),
      .flush_i(1'b0                                                   ),
      // External priority flag
      .rr_i   ('0                                                     ),
      // Master
      .data_i (tcdm_dma_req_i_struct                                  ),
      .valid_i(tcdm_dma_req_valid_i                                   ),
      .ready_o(tcdm_dma_req_ready_o                                   ),
      .sel_i  (tcdm_dma_req_i_struct.tgt_addr[idx_width(NumBanksPerTile)-1:$clog2(DmaNumWords)]),
      // Slave
      .data_o (tcdm_dma_req                                           ),
      .valid_o(tcdm_dma_req_valid                                     ),
      .ready_i(tcdm_dma_req_ready                                     ),
      .idx_o  (/* Unused */                                           )
    );

    stream_xbar #(
      .NumInp   (NumSuperbanks  ),
      .NumOut   (1              ),
      .payload_t(tcdm_dma_resp_t)
    ) i_dma_resp_interco (
      .clk_i  (clk_i                           ),
      .rst_ni (rst_ni                          ),
      .flush_i(1'b0                            ),
      // External priority flag
      .rr_i   ('0                              ),
      // Master
      .data_i (tcdm_dma_resp                   ),
      .valid_i(tcdm_dma_resp_valid             ),
      .ready_o(tcdm_dma_resp_ready             ),
      .sel_i  ('0                              ),
      // Slave
      .data_o (tcdm_dma_resp_o                 ),
      .valid_o(tcdm_dma_resp_valid_o           ),
      .ready_i(tcdm_dma_resp_ready_i           ),
      .idx_o  (/* Unused */                    )
    );
  end

  assign bank_req_ini_addr = superbank_req_ini_addr;
  for (genvar b = 0; unsigned'(b) < NumBanksPerTile; b++) begin: gen_superbank_resp_ini_addr
    if(NumRemoteReqPortsPerTile > NumRemoteRespPortsPerTile ) begin
      always_comb begin
        superbank_resp_ini_addr[b] = '0;
        superbank_resp_ini_addr[b] = bank_resp_ini_addr[b];
        if(bank_resp_ini_addr[b] > (NumCoresPerTile + NumRemoteRespPortsPerTile - 1)) begin
          superbank_resp_ini_addr[b] = bank_resp_ini_addr[b] - (NumRemoteReqPortsPerTile - NumRemoteRespPortsPerTile);
        end
      end
    end else if (NumRemoteReqPortsPerTile == NumRemoteRespPortsPerTile) begin
      always_comb begin
        superbank_resp_ini_addr[b] = '0;
        superbank_resp_ini_addr[b] = bank_resp_ini_addr[b];
      end
    end
    else begin
      localparam int unsigned bank_resp_payload_width = $bits(tcdm_slave_resp_t);
      localparam int unsigned hash_width = $clog2(NumRemoteRespPortsPerTile - 1) + 2;
      localparam int unsigned hash_binning_step = (1 << hash_width) / (NumRemoteRespPortsPerTile - 1);
      logic [bank_resp_payload_width-1:0] bank_resp_payload_raw;
      logic [hash_width-1:0] hash;
      assign bank_resp_payload_raw = bank_resp_payload[b];
      assign hash = bank_resp_payload_raw[bank_resp_payload_width-1 -: hash_width];
      always_comb begin
        superbank_resp_ini_addr[b] = '0;
        superbank_resp_ini_addr[b] = bank_resp_ini_addr[b];
        if(bank_resp_ini_addr[b] > NumCoresPerTile) begin
          for (int i = NumRemoteRespPortsPerTile-2; i >= 0; i--) begin
            if (hash >= i * hash_binning_step) begin
              superbank_resp_ini_addr[b] = NumCoresPerTile + 1 + i;
            end
          end
        end
      end
    end
  end

  for (genvar d = 0; unsigned'(d) < NumSuperbanks; d++) begin: gen_dma_mux
    tcdm_wide_narrow_mux #(
      .NarrowDataWidth(DataWidth        ),
      .WideDataWidth  (DmaDataWidth     ),
      .narrow_req_t   (tcdm_slave_req_t ),
      .narrow_rsp_t   (tcdm_slave_resp_t),
      .wide_req_t     (tcdm_dma_req_t   ),
      .wide_rsp_t     (tcdm_dma_resp_t  ),
      .group_id_t     (group_id_t       )
    ) i_tcdm_wide_narrow_mux (
      .clk_i                 (clk_i                                             ),
      .rst_ni                (rst_ni                                            ),
      .group_id_i            (group_id                                          ), // FlooNoC Added
      .slv_narrow_req_i      (superbank_req_payload[d*DmaNumWords+:DmaNumWords] ),
      .slv_narrow_req_valid_i(superbank_req_valid[d*DmaNumWords+:DmaNumWords]   ),
      .slv_narrow_req_ready_o(superbank_req_ready[d*DmaNumWords+:DmaNumWords]   ),
      .slv_narrow_rsp_o      (superbank_resp_payload[d*DmaNumWords+:DmaNumWords]),
      .slv_narrow_rsp_valid_o(superbank_resp_valid[d*DmaNumWords+:DmaNumWords]  ),
      .slv_narrow_rsp_ready_i(superbank_resp_ready[d*DmaNumWords+:DmaNumWords]  ),
      .slv_wide_req_i        (tcdm_dma_req[d]                                   ),
      .slv_wide_req_valid_i  (tcdm_dma_req_valid[d]                             ),
      .slv_wide_req_ready_o  (tcdm_dma_req_ready[d]                             ),
      .slv_wide_rsp_o        (tcdm_dma_resp[d]                                  ),
      .slv_wide_rsp_valid_o  (tcdm_dma_resp_valid[d]                            ),
      .slv_wide_rsp_ready_i  (tcdm_dma_resp_ready[d]                            ),
      .mst_req_o             (bank_req_payload[d*DmaNumWords+:DmaNumWords]      ),
      .mst_req_wide_o        (bank_req_wide[d*DmaNumWords+:DmaNumWords]         ),
      .mst_req_valid_o       (bank_req_valid[d*DmaNumWords+:DmaNumWords]        ),
      .mst_req_ready_i       (bank_req_ready[d*DmaNumWords+:DmaNumWords]        ),
      .mst_rsp_i             (bank_resp_payload[d*DmaNumWords+:DmaNumWords]     ),
      .mst_rsp_wide_i        (bank_resp_wide[d*DmaNumWords+:DmaNumWords]        ),
      .mst_rsp_valid_i       (bank_resp_valid[d*DmaNumWords+:DmaNumWords]       ),
      .mst_rsp_ready_o       (bank_resp_ready[d*DmaNumWords+:DmaNumWords]       )
    );
  end

  `ifndef TARGET_SYNTHESIS
  `ifndef TARGET_VERILATOR
  `ifdef SPM_PROFILING
    logic [63:0] cycle_q;

    profile_t profile_d [NumBanksPerTile-1:0][2**TCDMAddrMemWidth-1:0];
    // profile_t profile_q [NumBanksPerTile-1:0][2**TCDMAddrMemWidth-1:0];

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if(~rst_ni) begin
        cycle_q   <= '0;
        // profile_q <= '0;
      end else begin
        cycle_q   <= cycle_q + 64'd1;
        // profile_q <= profile_d;
      end
    end
  `endif
  `endif
  `endif

  for (genvar b = 0; unsigned'(b) < NumBanksPerTile; b++) begin: gen_banks
    bank_metadata_t meta_in;
    bank_metadata_t meta_out;
    logic req_valid;
    logic req_write;
    bank_addr_t req_addr;
    data_t req_wdata;
    data_t resp_rdata;
    strb_t req_be;

    // Un/Pack metadata
    assign meta_in = '{
      ini_addr  : bank_req_ini_addr[b],
      meta_id   : bank_req_payload[b].wdata.meta_id,
      core_id   : bank_req_payload[b].wdata.core_id,
      tile_id   : bank_req_payload[b].ini_addr,
      group_id  : bank_req_payload[b].src_group_id,
      wide      : bank_req_wide[b]
    };
    always_comb begin
      bank_resp_ini_addr[b] = '0;
      bank_resp_ini_addr[b] = meta_out.ini_addr;
    end
    assign bank_resp_payload[b].rdata.meta_id = meta_out.meta_id;
    assign bank_resp_payload[b].ini_addr      = meta_out.tile_id;
    assign bank_resp_payload[b].rdata.core_id = meta_out.core_id;
    assign bank_resp_payload[b].src_group_id  = meta_out.group_id;
    assign bank_resp_payload[b].rdata.amo     = '0; // Don't care
    assign bank_resp_wide[b]                  = meta_out.wide;

    tcdm_adapter #(
      .AddrWidth  (TCDMAddrMemWidth),
      .DataWidth  (DataWidth       ),
      .metadata_t (bank_metadata_t ),
      .LrScEnable (LrScEnable      ),
      .RegisterAmo(1'b0            )
    ) i_tcdm_adapter (
      .clk_i       (clk_i                                                                       ),
      .rst_ni      (rst_ni                                                                      ),
      .in_valid_i  (bank_req_valid[b]                                                           ),
      .in_ready_o  (bank_req_ready[b]                                                           ),
      .in_address_i(bank_req_payload[b].tgt_addr[idx_width(NumBanksPerTile) +: TCDMAddrMemWidth]),
      .in_amo_i    (bank_req_payload[b].wdata.amo                                               ),
      .in_write_i  (bank_req_payload[b].wen                                                     ),
      .in_wdata_i  (bank_req_payload[b].wdata.data                                              ),
      .in_meta_i   (meta_in                                                                     ),
      .in_be_i     (bank_req_payload[b].be                                                      ),
      .in_valid_o  (bank_resp_valid[b]                                                          ),
      .in_ready_i  (bank_resp_ready[b]                                                          ),
      .in_rdata_o  (bank_resp_payload[b].rdata.data                                             ),
      .in_meta_o   (meta_out                                                                    ),
      .out_req_o   (req_valid                                                                   ),
      .out_add_o   (req_addr                                                                    ),
      .out_write_o (req_write                                                                   ),
      .out_wdata_o (req_wdata                                                                   ),
      .out_be_o    (req_be                                                                      ),
      .out_rdata_i (resp_rdata                                                                  )
    );

    // Bank
    tc_sram #(
      .DataWidth(DataWidth          ),
      .NumWords (2**TCDMAddrMemWidth),
      .NumPorts (1                  )
    ) mem_bank (
      .clk_i  (clk_i     ),
      .rst_ni (rst_ni    ),
      .req_i  (req_valid ),
      .we_i   (req_write ),
      .addr_i (req_addr  ),
      .wdata_i(req_wdata ),
      .be_i   (req_be    ),
      .rdata_o(resp_rdata)
    );

  `ifndef TARGET_SYNTHESIS
  `ifndef TARGET_VERILATOR
  `ifdef SPM_PROFILING
    always_ff @(posedge clk_i or negedge rst_ni) begin
      // profile_d[b] = profile_q[b];
      if(~rst_ni) begin
        for(int j = 0; j < 2**TCDMAddrMemWidth; j++) begin
          profile_d[b][j].initiated = 0;
          profile_d[b][j].initial_cycle = 0;
          profile_d[b][j].last_read_cycle = 0;
          profile_d[b][j].last_write_cycle = 0;
          profile_d[b][j].last_access_cycle = 0;
          profile_d[b][j].access_read_number = 0;
          profile_d[b][j].access_write_number = 0;
          profile_d[b][j].access_number = 0;
        end
      end else begin
        if(req_valid) begin
          profile_d[b][req_addr].last_access_cycle = cycle_q;
          profile_d[b][req_addr].access_number     = profile_d[b][req_addr].access_number + 1;
          if(req_write) begin
            profile_d[b][req_addr].last_write_cycle = cycle_q;
            profile_d[b][req_addr].access_write_number = profile_d[b][req_addr].access_write_number + 1;
            profile_d[b][req_addr].write_cycles.push_back(cycle_q);
            if(!profile_d[b][req_addr].initiated) begin
              profile_d[b][req_addr].initiated = 1;
              profile_d[b][req_addr].initial_cycle = cycle_q;
            end
          end else begin
            profile_d[b][req_addr].last_read_cycle = cycle_q;
            profile_d[b][req_addr].access_read_number = profile_d[b][req_addr].access_read_number + 1;
            profile_d[b][req_addr].read_cycles.push_back(cycle_q);
          end
        end
      end
    end
  `endif
  `endif
  `endif
  end

  /***************
   *  Registers  *
   ***************/

  // These are required to break dependencies between request and response, establishing a correct
  // valid/ready handshake.
  tcdm_master_req_t  [NumRemoteReqPortsPerTile-1:0] prereg_tcdm_master_req;
  logic              [NumRemoteReqPortsPerTile-1:0] prereg_tcdm_master_req_valid;
  logic              [NumRemoteReqPortsPerTile-1:0] prereg_tcdm_master_req_ready;
  tcdm_slave_req_t   [NumRemoteReqPortsPerTile-1:0] postreg_tcdm_slave_req;
  logic              [NumRemoteReqPortsPerTile-1:0] postreg_tcdm_slave_req_valid;
  logic              [NumRemoteReqPortsPerTile-1:0] postreg_tcdm_slave_req_ready;
  tcdm_slave_resp_t  [NumRemoteRespPortsPerTile-1:0] prereg_tcdm_slave_resp;
  logic              [NumRemoteRespPortsPerTile-1:0] prereg_tcdm_slave_resp_valid;
  logic              [NumRemoteRespPortsPerTile-1:0] prereg_tcdm_slave_resp_ready;
  tcdm_master_resp_t [NumRemoteRespPortsPerTile-1:0] postreg_tcdm_master_resp;
  tile_core_id_t     [NumRemoteRespPortsPerTile-1:0] postreg_tcdm_master_resp_ini_sel;
  logic              [NumRemoteRespPortsPerTile-1:0] postreg_tcdm_master_resp_valid;
  logic              [NumRemoteRespPortsPerTile-1:0] postreg_tcdm_master_resp_ready;

  // Break paths between request and response with registers
  for (genvar h = 0; unsigned'(h) < NumRemoteReqPortsPerTile; h++) begin: gen_tcdm_registers_req
    spill_register #(
      .T(tcdm_master_req_t)
    ) i_tcdm_master_req_register (
      .clk_i  (clk_i                          ),
      .rst_ni (rst_ni                         ),
      .data_i (prereg_tcdm_master_req[h]      ),
      .valid_i(prereg_tcdm_master_req_valid[h]),
      .ready_o(prereg_tcdm_master_req_ready[h]),
      .data_o (tcdm_master_req_o[h]           ),
      .valid_o(tcdm_master_req_valid_o[h]     ),
      .ready_i(tcdm_master_req_ready_i[h]     )
    );

    fall_through_register #(
      .T(tcdm_slave_req_t)
    ) i_tcdm_slave_req_register (
      .clk_i     (clk_i                          ),
      .rst_ni    (rst_ni                         ),
      .clr_i     (1'b0                           ),
      .testmode_i(1'b0                           ),
      .data_i    (tcdm_slave_req_remapped[h]     ),
      .valid_i   (tcdm_slave_req_valid_i[h]      ),
      .ready_o   (tcdm_slave_req_ready_o[h]      ),
      .data_o    (postreg_tcdm_slave_req[h]      ),
      .valid_o   (postreg_tcdm_slave_req_valid[h]),
      .ready_i   (postreg_tcdm_slave_req_ready[h])
    );
  end: gen_tcdm_registers_req

  for (genvar h = 0; unsigned'(h) < NumRemoteRespPortsPerTile; h++) begin: gen_tcdm_registers_resp
    fall_through_register #(
      .T(tcdm_master_resp_t)
    ) i_tcdm_master_resp_register (
      .clk_i     (clk_i                            ),
      .rst_ni    (rst_ni                           ),
      .clr_i     (1'b0                             ),
      .testmode_i(1'b0                             ),
      .data_i    (tcdm_master_resp_i[h]            ),
      .valid_i   (tcdm_master_resp_valid_i[h]      ),
      .ready_o   (tcdm_master_resp_ready_o[h]      ),
      .data_o    (postreg_tcdm_master_resp[h]      ),
      .valid_o   (postreg_tcdm_master_resp_valid[h]),
      .ready_i   (postreg_tcdm_master_resp_ready[h])
    );

    // Helper signal to drive the remote response interconnect
    assign postreg_tcdm_master_resp_ini_sel[h] = postreg_tcdm_master_resp[h].rdata.core_id;

    spill_register #(
      .T(tcdm_slave_resp_t)
    ) i_tcdm_slave_resp_register (
      .clk_i  (clk_i                          ),
      .rst_ni (rst_ni                         ),
      .data_i (prereg_tcdm_slave_resp[h]      ),
      .valid_i(prereg_tcdm_slave_resp_valid[h]),
      .ready_o(prereg_tcdm_slave_resp_ready[h]),
      .data_o (tcdm_slave_resp_o[h]           ),
      .valid_o(tcdm_slave_resp_valid_o[h]     ),
      .ready_i(tcdm_slave_resp_ready_i[h]     )
    );
  end: gen_tcdm_registers_resp

  /****************************
   *   Remote Interconnects   *
   ****************************/

  tcdm_master_req_t    [NumCoresPerTile-1:0] remote_req_interco;
  logic                [NumCoresPerTile-1:0] remote_req_interco_valid;
  logic                [NumCoresPerTile-1:0] remote_req_interco_ready;
  logic                [NumCoresPerTile-1:0] remote_req_interco_hsk;
  logic                [NumCoresPerTile-1:0] remote_req_interco_hsk_q;
  addr_t               [NumCoresPerTile-1:0] prescramble_tcdm_req_tgt_addr;
  logic                [NumCoresPerTile-1:0] remote_req_interco_wen;
  logic                [NumCoresPerTile-1:0] remote_req_interco_amoen;
  group_id_t           [NumCoresPerTile-1:0] tgt_group_id;
  logic                [NumCoresPerTile-1:0] group_id_is_local;
  remote_ports_index_t [NumCoresPerTile-1:0] remote_req_interco_tgt_sel;
  remote_ports_index_t [NumCoresPerTile-1:0] remote_req_interco_tgt_sel_q;
  logic                [NumCoresPerTile-1:0] remote_req_interco_tgt_sel_q_update;
  remote_ports_index_t [NumCoresPerTile-1:0] remote_req_interco_tgt_sel_remapped;

  tcdm_master_resp_t   [NumCoresPerTile-1:0] remote_resp_interco;
  logic                [NumCoresPerTile-1:0] remote_resp_interco_valid;
  logic                [NumCoresPerTile-1:0] remote_resp_interco_ready;



  logic                [NumCoresPerTile-1:0] remote_req_interco_to_xbar_valid;
  logic                [NumCoresPerTile-1:0] remote_req_interco_to_xbar_valid_q;
  logic                [NumCoresPerTile-1:0] remote_req_interco_to_xbar_ready;

  stream_xbar #(
    .NumInp   (NumCoresPerTile           ),
    .NumOut   (NumRemoteReqPortsPerTile     ),
    .payload_t(tcdm_master_req_t         ),
    .ExtPrio  (1                         ),
    .AxiVldRdy(0                         ), // the sel_i can be changed before the hsk happen, as the priority of cores can be different
    .LockIn   (0                         )
  ) i_remote_req_interco (
    .clk_i  (clk_i                       ),
    .rst_ni (rst_ni                      ),
    .flush_i(1'b0                        ),
    // External priority flag
    .rr_i   ('0                          ),
    // Master
    .data_i (remote_req_interco          ),
    .valid_i(remote_req_interco_to_xbar_valid),
    .ready_o(remote_req_interco_ready    ),
    .sel_i  (remote_req_interco_tgt_sel  ),
    // Slave
    .data_o (prereg_tcdm_master_req      ),
    .valid_o(prereg_tcdm_master_req_valid),
    .ready_i(prereg_tcdm_master_req_ready),
    .idx_o  (/* Unused */                )
  );

  stream_xbar #(
    .NumInp   (NumRemoteRespPortsPerTile     ),
    .NumOut   (NumCoresPerTile               ),
    .payload_t(tcdm_master_resp_t            )
  ) i_remote_resp_interco (
    .clk_i  (clk_i                           ),
    .rst_ni (rst_ni                          ),
    .flush_i(1'b0                            ),
    // External priority flag
    .rr_i   ('0                              ),
    // Master
    .data_i (postreg_tcdm_master_resp        ),
    .valid_i(postreg_tcdm_master_resp_valid  ),
    .ready_o(postreg_tcdm_master_resp_ready  ),
    .sel_i  (postreg_tcdm_master_resp_ini_sel),
    // Slave
    .data_o (remote_resp_interco             ),
    .valid_o(remote_resp_interco_valid       ),
    .ready_i(remote_resp_interco_ready       ),
    .idx_o  (/* Unused */                    )
  );

  /**********************
   *   Local Intercos   *
   **********************/

  logic             [NumCoresPerTile-1:0] local_req_interco_valid;
  logic             [NumCoresPerTile-1:0] local_req_interco_ready;
  tcdm_slave_req_t  [NumCoresPerTile-1:0] local_req_interco_payload;
  logic             [NumCoresPerTile-1:0] local_resp_interco_valid;
  logic             [NumCoresPerTile-1:0] local_resp_interco_ready;
  tcdm_slave_resp_t [NumCoresPerTile-1:0] local_resp_interco_payload;
  addr_t            [NumCoresPerTile-1:0] local_req_interco_addr_int;

  logic [NumCoresPerTile+NumRemoteReqPortsPerTile-1:0][idx_width(NumBanksPerTile)-1:0] local_req_interco_tgt_sel;
  for (genvar j = 0; unsigned'(j) < NumCoresPerTile; j++) begin: gen_local_req_interco_tgt_sel_local
    assign local_req_interco_tgt_sel[j]  = local_req_interco_payload_remapped[j].tgt_addr[idx_width(NumBanksPerTile)-1:0];
  end: gen_local_req_interco_tgt_sel_local
  for (genvar j = 0; unsigned'(j) < NumRemoteReqPortsPerTile; j++) begin: gen_local_req_interco_tgt_sel_remote
    assign local_req_interco_tgt_sel[j + NumCoresPerTile]  = postreg_tcdm_slave_req[j].tgt_addr[idx_width(NumBanksPerTile)-1:0];
  end: gen_local_req_interco_tgt_sel_remote

  stream_xbar #(
    .NumInp   (NumCoresPerTile + NumRemoteReqPortsPerTile              ),
    .NumOut   (NumBanksPerTile                                      ),
    .payload_t(tcdm_slave_req_t                                     )
  ) i_local_req_interco (
    .clk_i  (clk_i                                                  ),
    .rst_ni (rst_ni                                                 ),
    .flush_i(1'b0                                                   ),
    // External priority flag
    .rr_i   ('0                                                     ),
    // Master
    .data_i ({postreg_tcdm_slave_req, local_req_interco_payload_remapped}),
    .valid_i({postreg_tcdm_slave_req_valid, local_req_interco_valid}),
    .ready_o({postreg_tcdm_slave_req_ready, local_req_interco_ready}),
    .sel_i  (local_req_interco_tgt_sel                              ),
    // Slave
    .data_o (superbank_req_payload                                  ),
    .valid_o(superbank_req_valid                                    ),
    .ready_i(superbank_req_ready                                    ),
    .idx_o  (superbank_req_ini_addr                                 )
  );

  stream_xbar #(
    .NumInp   (NumBanksPerTile                                       ),
    .NumOut   (NumCoresPerTile + NumRemoteRespPortsPerTile           ),
    .payload_t(tcdm_slave_resp_t                                     )
  ) i_local_resp_interco (
    .clk_i  (clk_i                                                   ),
    .rst_ni (rst_ni                                                  ),
    .flush_i(1'b0                                                    ),
    // External priority flag
    .rr_i   ('0                                                      ),
    // Master
    .data_i (superbank_resp_payload                                  ),
    .valid_i(superbank_resp_valid                                    ),
    .ready_o(superbank_resp_ready                                    ),
    .sel_i  (superbank_resp_ini_addr                                 ),
    // Slave
    .data_o ({prereg_tcdm_slave_resp, local_resp_interco_payload}    ),
    .valid_o({prereg_tcdm_slave_resp_valid, local_resp_interco_valid}),
    .ready_i({prereg_tcdm_slave_resp_ready, local_resp_interco_ready}),
    .idx_o  (/* Unused */                                            )
  );

  /********************
   *   ID Remapping   *
   ********************/
  mempool_tile_id_remapper #(
    .NumCoresPerTile              (NumCoresPerTile              ),
    .NumRemoteReqPortsPerTile     (NumRemoteReqPortsPerTile     ),
    .NumRdRemoteReqPortsPerTile   (NumRdRemoteReqPortsPerTile   ),
    .NumWrRemoteReqPortsPerTile   (NumWrRemoteReqPortsPerTile   ),
    .NumWideRemoteReqPortsPerTile (NumWideRemoteReqPortsPerTile ),
    .NumRdWrRemoteReqPortsPerTile (NumRdWrRemoteReqPortsPerTile ),
    .NumBanksPerTile              (NumBanksPerTile              ),
    .NumTilesPerGroup             (NumTilesPerGroup             ),
    .NumGroups                    (NumGroups                    ),
    .TCDMAddrMemWidth             (TCDMAddrMemWidth             ),
    .ByteOffset                   (ByteOffset                   ),
    .SpmBankIdRemap               (SpmBankIdRemap               )
  ) i_mempool_tile_id_remapper (
    .clk_i              (clk_i      ),
    .rst_ni             (rst_ni     ),

    .group_id_i         (group_id   ),

    .tcdm_dma_req_i           (tcdm_dma_req_i     ),
    .tcdm_slave_req_i         (tcdm_slave_req_i   ),
    .local_req_interco_payload_i  (local_req_interco_payload),

    .remote_req_interco_valid_i (remote_req_interco_valid   ),
    .remote_req_interco_ready_i (remote_req_interco_ready   ),
    .remote_req_interco_wen_i   (remote_req_interco_wen     ),
    .remote_req_interco_amoen_i (remote_req_interco_amoen   ),
    // .remote_req_interco_tgt_sel_i (remote_req_interco_tgt_sel),

    .prescramble_tcdm_req_tgt_addr_i  (prescramble_tcdm_req_tgt_addr),

    .tcdm_dma_req_remapped_o    (tcdm_dma_req_remapped),
    .tcdm_slave_req_remapped_o  (tcdm_slave_req_remapped),
    .local_req_interco_payload_remapped_o  (local_req_interco_payload_remapped),

    .remote_req_interco_to_xbar_valid_o (remote_req_interco_to_xbar_valid),
    .remote_req_interco_to_xbar_ready_o (remote_req_interco_to_xbar_ready),
    .remote_req_interco_tgt_sel_o (remote_req_interco_tgt_sel_remapped)
  );

  /*******************
   *   Core De/mux   *
   *******************/

  // SoC requests
  dreq_t  [NumCoresPerTile-1:0] soc_data_q;
  logic   [NumCoresPerTile-1:0] soc_data_qvalid;
  logic   [NumCoresPerTile-1:0] soc_data_qready;
  dresp_t [NumCoresPerTile-1:0] soc_data_p;
  logic   [NumCoresPerTile-1:0] soc_data_pvalid;
  logic   [NumCoresPerTile-1:0] soc_data_pready;

  // Address map
  typedef enum int unsigned {
    TCDM_EXTERNAL = 0, TCDM_LOCAL, SOC
  } addr_map_slave_t;

  address_map_t [2:0] mask_map;
  assign mask_map = '{
    // Lowest priority: send request through the SoC port
    '{slave_idx: SOC,
      mask     : '0,
      value    : '0
    },
    // Send request through the external TCDM port
    '{slave_idx: TCDM_EXTERNAL,
      mask     : TCDMMask,
      value    : TCDMBaseAddr
    },
    // Highest priority: send request through the local TCDM port
    '{slave_idx: TCDM_LOCAL,
      mask     : TCDMMask | ({idx_width(NumTiles){1'b1}} << (ByteOffset + $clog2(NumBanksPerTile))),
      value    : TCDMBaseAddr | (tile_id_i << (ByteOffset + $clog2(NumBanksPerTile)))
    }
  };

  for (genvar c = 0; c < NumCoresPerTile; c++) begin: gen_core_mux
      // Remove tile index from local_req_interco_addr_int, since it will not be used for routing.
      // addr_t local_req_interco_addr_int;
      assign local_req_interco_payload[c].tgt_addr =
       tcdm_addr_t'({local_req_interco_addr_int[c][ByteOffset + idx_width(NumBanksPerTile) + $clog2(NumTiles) +: TCDMAddrMemWidth], // Bank address
               local_req_interco_addr_int[c][ByteOffset +: idx_width(NumBanksPerTile)]}); // Bank

      // Switch tile and bank indexes for correct upper level routing, and remove the group index
      // addr_t prescramble_tcdm_req_tgt_addr;
      if (NumTilesPerGroup == 1) begin : gen_remote_req_interco_tgt_addr
        assign remote_req_interco[c].tgt_addr =
        tcdm_addr_t'({prescramble_tcdm_req_tgt_addr[c][ByteOffset + idx_width(NumBanksPerTile) + $clog2(NumGroups) +: TCDMAddrMemWidth], // Bank address
           prescramble_tcdm_req_tgt_addr[c][ByteOffset +: idx_width(NumBanksPerTile)]}); // Tile
      end else begin : gen_remote_req_interco_tgt_addr
        assign remote_req_interco[c].tgt_addr =
        tcdm_addr_t'({prescramble_tcdm_req_tgt_addr[c][ByteOffset + idx_width(NumBanksPerTile) + $clog2(NumTilesPerGroup) + $clog2(NumGroups) +: TCDMAddrMemWidth], // Bank address
           prescramble_tcdm_req_tgt_addr[c][ByteOffset +: idx_width(NumBanksPerTile)],                                                                              // Bank
           prescramble_tcdm_req_tgt_addr[c][ByteOffset + idx_width(NumBanksPerTile) +: $clog2(NumTilesPerGroup)]}); // Tile
      end
      if (NumGroups == 1) begin : gen_remote_req_interco_tgt_sel
        assign remote_req_interco_tgt_sel[c] = 1'b0;
        assign remote_req_interco[c].tgt_group_id = '0;
      end else begin : gen_remote_req_interco_tgt_sel
        // Output port depends on both the target and initiator group
        // If the target group is the same as the initiator group, the target is the local Group, through port 0
        // Otherwise, the target is a remote group, through port 1 to NumRemoteReqPortsPerTile, used in a round-robin fashion by modulus
        assign tgt_group_id[c] = prescramble_tcdm_req_tgt_addr[c][ByteOffset + $clog2(NumBanksPerTile) + $clog2(NumTilesPerGroup) +: $clog2(NumGroups)];
        assign remote_req_interco_tgt_sel[c] = remote_req_interco_tgt_sel_remapped[c];
        assign remote_req_interco[c].tgt_group_id = tgt_group_id[c];
      end

    // We don't care about these
    assign local_req_interco_payload[c].wdata.core_id = '0;
    assign local_req_interco_payload[c].ini_addr      = '0;
    assign local_req_interco_payload[c].src_group_id  = '0;
    assign soc_data_q[c].id                           = '0;

    // Constant value
    assign remote_req_interco[c].wdata.core_id = c[idx_width(NumCoresPerTile)-1:0];

    // The wen of the req
    assign remote_req_interco_wen   [c] = remote_req_interco[c].wen;
    assign remote_req_interco_amoen [c] = |remote_req_interco[c].wdata.amo;

    // Scramble address before entering TCDM shim for sequential+interleaved memory map
    address_scrambler #(
      .AddrWidth         (AddrWidth        ),
      .ByteOffset        (ByteOffset       ),
      .NumTiles          (NumTiles         ),
      .NumBanksPerTile   (NumBanksPerTile  ),
      .Bypass            (0                ),
      .SeqMemSizePerTile (SeqMemSizePerTile),
      .TCDMBaseAddr      (TCDMBaseAddr     ),
      .TCDMMask          (TCDMMask         )
    ) i_address_scrambler (
      .address_i (snitch_data_qaddr[c]          ),
      .address_o (snitch_data_qaddr_scrambled[c])
    );

    if (!TrafficGeneration) begin: gen_tcdm_shim
      tcdm_shim #(
        .AddrWidth           (AddrWidth                         ),
        .DataWidth           (DataWidth                         ),
        .MaxOutStandingTrans (snitch_pkg::NumIntOutstandingLoads),
        .NrTCDM              (2                                 ),
        .NrSoC               (1                                 ),
        .NumRules            (3                                 ),
        .ByteOffset          (ByteOffset                        ),
        .NumTiles            (NumTiles                          ),
        .NumTilesPerDma      (NumTilesPerDma                    ),
        .NumBanksPerTile     (NumBanksPerTile                   ),
        .SeqMemSizePerTile   (SeqMemSizePerTile                 )
      ) i_tcdm_shim (
        .clk_i              (clk_i                                                                              ),
        .rst_ni             (rst_ni                                                                             ),
        // to TCDM --> FF Connection to outside of tile
        .tcdm_req_valid_o   ({local_req_interco_valid[c], remote_req_interco_valid[c]}                          ),
        .tcdm_req_tgt_addr_o({local_req_interco_addr_int[c], prescramble_tcdm_req_tgt_addr[c]}                  ),
        .tcdm_req_wen_o     ({local_req_interco_payload[c].wen, remote_req_interco[c].wen}                      ),
        .tcdm_req_wdata_o   ({local_req_interco_payload[c].wdata.data, remote_req_interco[c].wdata.data}        ),
        .tcdm_req_amo_o     ({local_req_interco_payload[c].wdata.amo, remote_req_interco[c].wdata.amo}          ),
        .tcdm_req_id_o      ({local_req_interco_payload[c].wdata.meta_id, remote_req_interco[c].wdata.meta_id}  ),
        .tcdm_req_be_o      ({local_req_interco_payload[c].be, remote_req_interco[c].be}                        ),
        .tcdm_req_ready_i   ({local_req_interco_ready[c], remote_req_interco_to_xbar_ready[c]}                  ),
        .tcdm_resp_valid_i  ({local_resp_interco_valid[c], remote_resp_interco_valid[c]}                        ),
        .tcdm_resp_ready_o  ({local_resp_interco_ready[c], remote_resp_interco_ready[c]}                        ),
        .tcdm_resp_rdata_i  ({local_resp_interco_payload[c].rdata.data, remote_resp_interco[c].rdata.data}      ),
        .tcdm_resp_id_i     ({local_resp_interco_payload[c].rdata.meta_id, remote_resp_interco[c].rdata.meta_id}),
        // to SoC
        .soc_qaddr_o        (soc_data_q[c].addr                                                                 ),
        .soc_qwrite_o       (soc_data_q[c].write                                                                ),
        .soc_qamo_o         (soc_data_q[c].amo                                                                  ),
        .soc_qdata_o        (soc_data_q[c].data                                                                 ),
        .soc_qstrb_o        (soc_data_q[c].strb                                                                 ),
        .soc_qvalid_o       (soc_data_qvalid[c]                                                                 ),
        .soc_qready_i       (soc_data_qready[c]                                                                 ),
        .soc_pdata_i        (soc_data_p[c].data                                                                 ),
        .soc_pwrite_i       (soc_data_p[c].write                                                                ),
        .soc_perror_i       (soc_data_p[c].error                                                                ),
        .soc_pvalid_i       (soc_data_pvalid[c]                                                                 ),
        .soc_pready_o       (soc_data_pready[c]                                                                 ),
        // from core
        .data_qaddr_i       (snitch_data_qaddr_scrambled[c]                                                     ),
        .data_qwrite_i      (snitch_data_qwrite[c]                                                              ),
        .data_qamo_i        (snitch_data_qamo[c]                                                                ),
        .data_qdata_i       (snitch_data_qdata[c]                                                               ),
        .data_qstrb_i       (snitch_data_qstrb[c]                                                               ),
        .data_qid_i         (snitch_data_qid[c]                                                                 ),
        .data_qvalid_i      (snitch_data_qvalid[c]                                                              ),
        .data_qready_o      (snitch_data_qready[c]                                                              ),
        .data_pdata_o       (snitch_data_pdata[c]                                                               ),
        .data_perror_o      (snitch_data_perror[c]                                                              ),
        .data_pid_o         (snitch_data_pid[c]                                                                 ),
        .data_pvalid_o      (snitch_data_pvalid[c]                                                              ),
        .data_pready_i      (snitch_data_pready[c]                                                              ),
        .address_map_i      (mask_map                                                                           )
      );
    end else begin: gen_traffic_generator
      traffic_generator #(
        .NumRules           (3                                 ),
        .TCDMBaseAddr       (TCDMBaseAddr                      ),
        .MaxOutStandingReads(snitch_pkg::NumIntOutstandingLoads)
      ) i_traffic_gen (
        .clk_i              (clk_i                                                        ),
        .rst_ni             (rst_ni                                                       ),
        .core_id_i          ({tile_id_i, c[idx_width(NumCoresPerTile)-1:0]}               ),
        // Address map
        .address_map_i      (mask_map                                                     ),
        // To TCDM
        .tcdm_req_valid_o   ({local_req_interco_valid[c], remote_req_interco_valid[c]}    ),
        .tcdm_req_tgt_addr_o({local_req_interco_addr_int[c], prescramble_tcdm_req_tgt_addr[c]}),
        .tcdm_req_wen_o     ({local_req_interco_payload[c].wen, remote_req_interco[c].wen}),
        .tcdm_req_wdata_o   ({local_req_interco_payload[c].wdata.data,
            remote_req_interco[c].wdata.data}),
        .tcdm_req_amo_o({local_req_interco_payload[c].wdata.amo,
            remote_req_interco[c].wdata.amo}),
        .tcdm_req_id_o({local_req_interco_payload[c]
            .wdata.meta_id, remote_req_interco[c].wdata.meta_id}),
        .tcdm_req_be_o    ({local_req_interco_payload[c].be, remote_req_interco[c].be}),
        .tcdm_req_ready_i ({local_req_interco_ready[c], remote_req_interco_to_xbar_ready[c]}  ),
        .tcdm_resp_valid_i({local_resp_interco_valid[c], remote_resp_interco_valid[c]}),
        .tcdm_resp_ready_o({local_resp_interco_ready[c], remote_resp_interco_ready[c]}),
        .tcdm_resp_rdata_i({local_resp_interco_payload[c].rdata.data,
            remote_resp_interco[c].rdata.data} ),
        .tcdm_resp_id_i ({local_resp_interco_payload[c].rdata.meta_id,
            remote_resp_interco[c].rdata.meta_id})
      );

      // Tie unused signals
      assign soc_data_q[c].addr    = '0;
      assign soc_data_q[c].write   = '0;
      assign soc_data_q[c].amo     = '0;
      assign soc_data_q[c].data    = '0;
      assign soc_data_q[c].strb    = '0;
      assign soc_data_qvalid[c]    = '0;
      assign soc_data_pready[c]    = '0;
      assign snitch_data_qready[c] = '0;
      assign snitch_data_pdata[c]  = '0;
      assign snitch_data_perror[c] = '0;
      assign snitch_data_pid[c]    = '0;
      assign snitch_data_pvalid[c] = '0;
    end
  end

  /****************
   *   AXI Plug   *
   ****************/

  snitch_pkg::dreq_t soc_req_o;
  snitch_pkg::dresp_t soc_resp_i;

  logic soc_qvalid;
  logic soc_qready;
  logic soc_pvalid;
  logic soc_pready;

  // We don't care about this
  assign soc_resp_i.id = 'x;

  snitch_demux #(
    .NrPorts (NumCoresPerTile    ),
    .req_t   (snitch_pkg::dreq_t ),
    .resp_t  (snitch_pkg::dresp_t)
  ) i_snitch_demux_data (
    .clk_i         (clk_i          ),
    .rst_ni        (rst_ni         ),
    // Inputs
    .req_payload_i (soc_data_q     ),
    .req_valid_i   (soc_data_qvalid),
    .req_ready_o   (soc_data_qready),
    .resp_payload_o(soc_data_p     ),
    .resp_last_o   (/* Unused */   ),
    .resp_valid_o  (soc_data_pvalid),
    .resp_ready_i  (soc_data_pready),
    // Output
    .req_payload_o (soc_req_o      ),
    .req_valid_o   (soc_qvalid     ),
    .req_ready_i   (soc_qready     ),
    .resp_payload_i(soc_resp_i     ),
    .resp_last_i   (1'b1           ),
    .resp_valid_i  (soc_pvalid     ),
    .resp_ready_o  (soc_pready     )
  );

  // Core request
  axi_core_req_t  axi_cores_req_d, axi_cores_req_q;
  axi_core_resp_t axi_cores_resp_d, axi_cores_resp_q;

  snitch_axi_adapter #(
    .addr_t         (snitch_pkg::addr_t),
    .data_t         (snitch_pkg::data_t),
    .strb_t         (snitch_pkg::strb_t),
    .axi_mst_req_t  (axi_core_req_t    ),
    .axi_mst_resp_t (axi_core_resp_t   )
  ) i_snitch_core_axi_adapter (
    .clk_i       (clk_i           ),
    .rst_ni      (rst_ni          ),
    .slv_qaddr_i (soc_req_o.addr  ),
    .slv_qwrite_i(soc_req_o.write ),
    .slv_qamo_i  (soc_req_o.amo   ),
    .slv_qdata_i (soc_req_o.data  ),
    .slv_qsize_i (3'b010          ),
    .slv_qstrb_i (soc_req_o.strb  ),
    .slv_qrlen_i ('0              ),
    .slv_qvalid_i(soc_qvalid      ),
    .slv_qready_o(soc_qready      ),
    .slv_pdata_o (soc_resp_i.data ),
    .slv_pwrite_o(soc_resp_i.write),
    .slv_perror_o(soc_resp_i.error),
    .slv_plast_o (/* Unused */    ),
    .slv_pvalid_o(soc_pvalid      ),
    .slv_pready_i(soc_pready      ),
    .axi_req_o   (axi_cores_req_d ),
    .axi_resp_i  (axi_cores_resp_q)
  );

  axi_cut #(
    .aw_chan_t (axi_core_aw_t  ),
    .w_chan_t  (axi_core_w_t   ),
    .b_chan_t  (axi_core_b_t   ),
    .ar_chan_t (axi_core_ar_t  ),
    .r_chan_t  (axi_core_r_t   ),
    .axi_req_t (axi_core_req_t ),
    .axi_resp_t(axi_core_resp_t)
  ) axi_core_slice (
    .clk_i     (clk_i           ),
    .rst_ni    (rst_ni          ),
    .slv_req_i (axi_cores_req_d ),
    .slv_resp_o(axi_cores_resp_q),
    .mst_req_o (axi_cores_req_q ),
    .mst_resp_i(axi_cores_resp_d)
  );

  axi_mux #(
    .SlvAxiIDWidth (AxiCoreIdWidth ),
    .slv_aw_chan_t (axi_core_aw_t  ),
    .mst_aw_chan_t (axi_tile_aw_t  ),
    .w_chan_t      (axi_tile_w_t   ),
    .slv_b_chan_t  (axi_core_b_t   ),
    .mst_b_chan_t  (axi_tile_b_t   ),
    .slv_ar_chan_t (axi_core_ar_t  ),
    .mst_ar_chan_t (axi_tile_ar_t  ),
    .slv_r_chan_t  (axi_core_r_t   ),
    .mst_r_chan_t  (axi_tile_r_t   ),
    .slv_req_t     (axi_core_req_t ),
    .slv_resp_t    (axi_core_resp_t),
    .mst_req_t     (axi_tile_req_t ),
    .mst_resp_t    (axi_tile_resp_t),
    .NoSlvPorts    (1+NumCaches    ),
    .MaxWTrans     (8              ),
    .FallThrough   (1              )
  ) i_axi_mux (
    .clk_i      (clk_i                               ),
    .rst_ni     (rst_ni                              ),
    .test_i     (1'b0                                ),
    .slv_reqs_i ({axi_cores_req_q, axi_cache_req_q}  ),
    .slv_resps_o({axi_cores_resp_d, axi_cache_resp_d}),
    .mst_req_o  (axi_mst_req_o                       ),
    .mst_resp_i (axi_mst_resp_i                      )
  );

  /******************
   *   Assertions   *
   ******************/

  // Check invariants.
  if (BootAddr[1:0] != 2'b00)
    $fatal(1, "[mempool_tile] Boot address should be aligned in a 4-byte boundary.");

  if (NumCoresPerTile != 2**$clog2(NumCoresPerTile))
    $fatal(1, "[mempool_tile] The number of cores per tile must be a power of two.");

  if (NumCores != unsigned'(2**$clog2(NumCores)))
    $fatal(1, "[mempool_tile] The number of cores must be a power of two.");

  if (NumBanksPerTile < 1)
    $fatal(1, "[mempool_tile] The number of banks per tile must be larger than one");

  if (NumCaches != 1)
    $error("NumCaches > 1 is not supported!");

  if (DataWidth > AxiDataWidth)
    $error("AxiDataWidth needs to be larger than DataWidth!");

endmodule : mempool_tile
