// Copyright 2021 ETH Zurich and University of Bologna.
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
  input  logic              [idx_width(NumTiles)-1:0]                             tile_id_i,
  // TCDM Master interfaces
  output `STRUCT_VECT(tcdm_master_req_t,  [NumGroups+NumSubGroupsPerGroup-1-1:0]) tcdm_master_req_o,
  output logic              [NumGroups+NumSubGroupsPerGroup-1-1:0]                tcdm_master_req_valid_o,
  input  logic              [NumGroups+NumSubGroupsPerGroup-1-1:0]                tcdm_master_req_ready_i,
  input  `STRUCT_VECT(tcdm_master_resp_t, [NumGroups+NumSubGroupsPerGroup-1-1:0]) tcdm_master_resp_i,
  input  logic              [NumGroups+NumSubGroupsPerGroup-1-1:0]                tcdm_master_resp_valid_i,
  output logic              [NumGroups+NumSubGroupsPerGroup-1-1:0]                tcdm_master_resp_ready_o,
  // TCDM slave interfaces
  input  `STRUCT_VECT(tcdm_slave_req_t,   [NumGroups+NumSubGroupsPerGroup-1-1:0]) tcdm_slave_req_i,
  input  logic              [NumGroups+NumSubGroupsPerGroup-1-1:0]                tcdm_slave_req_valid_i,
  output logic              [NumGroups+NumSubGroupsPerGroup-1-1:0]                tcdm_slave_req_ready_o,
  output `STRUCT_VECT(tcdm_slave_resp_t,  [NumGroups+NumSubGroupsPerGroup-1-1:0]) tcdm_slave_resp_o,
  output logic              [NumGroups+NumSubGroupsPerGroup-1-1:0]                tcdm_slave_resp_valid_o,
  input  logic              [NumGroups+NumSubGroupsPerGroup-1-1:0]                tcdm_slave_resp_ready_i,
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
  input  logic              [NumCoresPerTile-1:0]                                 wake_up_i
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
  import tcdm_burst_pkg::*;

  typedef logic [idx_width(NumGroups)-1:0] group_id_t;

  // Local interconnect address width
  typedef logic [idx_width(NumCoresPerTile*NumDataPortsPerCore + NumGroups + NumSubGroupsPerGroup-1)-1:0] local_req_interco_addr_t;

  /*********************
   *  Control Signals  *
   *********************/
  logic [NumCoresPerTile-1:0] wake_up_q;
  `FF(wake_up_q, wake_up_i, '0, clk_i, rst_ni);

  // Group ID
  logic [idx_width(NumGroups)-1:0] group_id;
  if (NumGroups != 1) begin: gen_group_id
    assign group_id = tile_id_i[$clog2(NumTiles)-1 -: $clog2(NumGroups)];
  end else begin: gen_group_id
    assign group_id = '0;
  end: gen_group_id

  `ifdef TERAPOOL
    // SubGroup ID
    logic [idx_width(NumSubGroupsPerGroup)-1:0] sub_group_id;
    if (NumSubGroupsPerGroup != 1) begin: gen_sub_group_id
      assign sub_group_id = tile_id_i[$clog2(NumTiles)-$clog2(NumGroups)-1 -: $clog2(NumSubGroupsPerGroup)];
    end else begin: gen_sub_group_id
      assign sub_group_id = '0;
    end: gen_sub_group_id
  `endif

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
  addr_t      [NumCoresPerTile-1:0][NumDataPortsPerCore-1:0] precut_qaddr,    snitch_data_qaddr;
  logic       [NumCoresPerTile-1:0][NumDataPortsPerCore-1:0] precut_qwrite,   snitch_data_qwrite;
  amo_t       [NumCoresPerTile-1:0][NumDataPortsPerCore-1:0] precut_qamo,     snitch_data_qamo;
  data_t      [NumCoresPerTile-1:0][NumDataPortsPerCore-1:0] precut_qdata,    snitch_data_qdata;
  tcdm_breq_t [NumCoresPerTile-1:0][NumDataPortsPerCore-1:0] precut_qburst,   snitch_data_qburst;
  strb_t      [NumCoresPerTile-1:0][NumDataPortsPerCore-1:0] precut_qstrb,    snitch_data_qstrb;
  meta_id_t   [NumCoresPerTile-1:0][NumDataPortsPerCore-1:0] precut_qid,      snitch_data_qid;
  logic       [NumCoresPerTile-1:0][NumDataPortsPerCore-1:0] precut_qvalid,   snitch_data_qvalid;
  logic       [NumCoresPerTile-1:0][NumDataPortsPerCore-1:0] precut_qready,   snitch_data_qready;
  data_t      [NumCoresPerTile-1:0][NumDataPortsPerCore-1:0] snitch_data_pdata;
  logic       [NumCoresPerTile-1:0][NumDataPortsPerCore-1:0] snitch_data_pwrite;
  logic       [NumCoresPerTile-1:0][NumDataPortsPerCore-1:0] snitch_data_perror;
  meta_id_t   [NumCoresPerTile-1:0][NumDataPortsPerCore-1:0] snitch_data_pid;
  tcdm_gre_t  [NumCoresPerTile-1:0][NumDataPortsPerCore-1:0] snitch_data_pgdata;
  logic       [NumCoresPerTile-1:0][NumDataPortsPerCore-1:0] snitch_data_pvalid;
  logic       [NumCoresPerTile-1:0][NumDataPortsPerCore-1:0] snitch_data_pready;

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
        .rst_i                   (!rst_ni                ),
        // pragma translate_off
        .trace_port_o            (                       ),
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
    if (NumCoresPerTile == 1) begin
      assign hart_id = unsigned'(tile_id_i);
    end else begin
      assign hart_id = {unsigned'(tile_id_i), c[idx_width(NumCoresPerTile)-1:0]};
    end

    if (!TrafficGeneration) begin: gen_mempool_cc
    `ifndef TARGET_SPATZ
      mempool_cc #(
        .BootAddr (BootAddr)
      )
    `else
      spatz_mempool_cc #(
        .BootAddr             ( BootAddr            ),
        .RVE                  ( 0                   ),
        .RVM                  ( 1                   ),
        .RVV                  ( RVV                 ),
        .XFVEC                ( XFVEC               ),
        .XFDOTP               ( XFDOTP              ),
        .XFAUX                ( XFAUX               ),
        .RVF                  ( RVF                 ),
        .RVD                  ( RVD                 ),
        .XF16                 ( XF16                ),
        .XF16ALT              ( XF16ALT             ),
        .XF8                  ( XF8                 ),
        .XDivSqrt             ( XDivSqrt            ),
        .NumMemPortsPerSpatz  ( NumMemPortsPerSpatz ),
        .TCDMPorts            ( NumDataPortsPerCore ),
        .BankOffset           ( ByteOffset+$clog2(NumBanksPerTile)),
        .NumCoresPerTile      ( NumCoresPerTile     ),
        .TileLen              ( $clog2(NumTiles)    ),
        .NumBanks             ( NumBanks            )
      )
    `endif
      riscv_core (
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
        .data_qaddr_o  (precut_qaddr[c]                                          ),
        .data_qwrite_o (precut_qwrite[c]                                         ),
        .data_qamo_o   (precut_qamo[c]                                           ),
        .data_qdata_o  (precut_qdata[c]                                          ),
        .data_qburst_o (precut_qburst[c]                                         ),
        .data_qstrb_o  (precut_qstrb[c]                                          ),
        .data_qid_o    (precut_qid[c]                                            ),
        .data_qvalid_o (precut_qvalid[c]                                         ),
        .data_qready_i (precut_qready[c]                                         ),
        .data_pdata_i  (snitch_data_pdata[c]                                     ),
        .data_pwrite_i (snitch_data_pwrite[c]                                    ),
        .data_perror_i (snitch_data_perror[c]                                    ),
        .data_pid_i    (snitch_data_pid[c]                                       ),
    `ifdef TARGET_SPATZ
        .data_pgre_i   (snitch_data_pgdata[c]                                    ),
    `endif
        .data_pvalid_i (snitch_data_pvalid[c]                                    ),
        .data_pready_o (snitch_data_pready[c]                                    ),
        .wake_up_sync_i(wake_up_q[c]                                             ),
        // Core Events
        .core_events_o (/* Unused */                                             )
      );

      if (UseBurst) begin : gen_burst_cutter
        assign snitch_data_qaddr [c][0] = precut_qaddr [c][0];
        assign snitch_data_qwrite[c][0] = precut_qwrite[c][0];
        assign snitch_data_qamo  [c][0] = precut_qamo  [c][0];
        assign snitch_data_qdata [c][0] = precut_qdata [c][0];
        assign snitch_data_qstrb [c][0] = precut_qstrb [c][0];
        assign snitch_data_qid   [c][0] = precut_qid   [c][0];
        assign snitch_data_qburst[c][0] = precut_qburst[c][0];
        assign snitch_data_qvalid[c][0] = precut_qvalid[c][0];
        assign precut_qready     [c][0] = snitch_data_qready[c][0];

        localparam CutLen = (RspGF > 1) ? RspGF : NumBanksPerTile;

        burst_cutter #(
          .NrCut           ( 1'b1                   ),
          .AddrWidth       ( AddrWidth              ),
          .ByteOffset      ( ByteOffset             ),
          .NumTiles        ( NumTiles               ),
          .CutLen          ( CutLen                 ),
          .BLenWidth       ( tcdm_burst_pkg::BurstLenWidth ),
          .tcdm_breq_t     ( tcdm_breq_t            ),
          .meta_id_t       ( meta_id_t              )
        ) i_burst_cutter (
          .clk_i         ( clk_i                    ),
          .rst_ni        ( rst_ni                   ),
          // Payload Input Side
          .req_addr_i    ( precut_qaddr [c][1]      ),
          .req_write_i   ( precut_qwrite[c][1]      ),
          .req_amo_i     ( precut_qamo  [c][1]      ),
          .req_data_i    ( precut_qdata [c][1]      ),
          .req_strb_i    ( precut_qstrb [c][1]      ),
          .req_id_i      ( precut_qid   [c][1]      ),
          .req_burst_i   ( precut_qburst[c][1]      ),
          .req_valid_i   ( precut_qvalid[c][1]      ),
          .req_ready_o   ( precut_qready[c][1]      ),
          // Payload Output Side
          .req_addr_o    ( snitch_data_qaddr [c][1] ),
          .req_write_o   ( snitch_data_qwrite[c][1] ),
          .req_amo_o     ( snitch_data_qamo  [c][1] ),
          .req_data_o    ( snitch_data_qdata [c][1] ),
          .req_strb_o    ( snitch_data_qstrb [c][1] ),
          .req_id_o      ( snitch_data_qid   [c][1] ),
          .req_burst_o   ( snitch_data_qburst[c][1] ),
          .req_valid_o   ( snitch_data_qvalid[c][1] ),
          .req_ready_i   ( snitch_data_qready[c][1] )
        );

        for (genvar p = 2; unsigned'(p) < NumDataPortsPerCore; p++) begin
          assign snitch_data_qaddr [c][p] = precut_qaddr [c][p];
          assign snitch_data_qwrite[c][p] = precut_qwrite[c][p];
          assign snitch_data_qamo  [c][p] = precut_qamo  [c][p];
          assign snitch_data_qdata [c][p] = precut_qdata [c][p];
          assign snitch_data_qstrb [c][p] = precut_qstrb [c][p];
          assign snitch_data_qid   [c][p] = precut_qid   [c][p];
          assign snitch_data_qburst[c][p] = precut_qburst[c][p];
          assign snitch_data_qvalid[c][p] = precut_qvalid[c][p];
          assign precut_qready     [c][p] = snitch_data_qready[c][p];
        end
      end else begin: gen_bypass_cutter
        assign snitch_data_qaddr [c] = precut_qaddr [c];
        assign snitch_data_qwrite[c] = precut_qwrite[c];
        assign snitch_data_qamo  [c] = precut_qamo  [c];
        assign snitch_data_qdata [c] = precut_qdata [c];
        assign snitch_data_qstrb [c] = precut_qstrb [c];
        assign snitch_data_qid   [c] = precut_qid   [c];
        assign snitch_data_qburst[c] = precut_qburst[c];
        assign snitch_data_qvalid[c] = precut_qvalid[c];
        assign precut_qready     [c] = snitch_data_qready[c];
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
      assign snitch_data_qburst[c]                                     = '0;
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
    tile_group_id_t tile_id;
    tile_core_id_t core_id;
    logic wide;
    logic write;
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
  local_req_interco_addr_t [NumBanksPerTile-1:0] superbank_resp_ini_addr;

  logic                    [NumBanksPerTile-1:0] prebank_req_valid;
  logic                    [NumBanksPerTile-1:0] prebank_req_ready;
  local_req_interco_addr_t [NumBanksPerTile-1:0] prebank_req_ini_addr;
  logic                    [NumBanksPerTile-1:0] prebank_req_wide;
  tcdm_slave_req_t         [NumBanksPerTile-1:0] prebank_req_payload;
  logic                    [NumBanksPerTile-1:0] prebank_resp_valid;
  logic                    [NumBanksPerTile-1:0] prebank_resp_ready;
  tcdm_slave_resp_t        [NumBanksPerTile-1:0] prebank_resp_payload;
  logic                    [NumBanksPerTile-1:0] prebank_resp_wide;
  local_req_interco_addr_t [NumBanksPerTile-1:0] prebank_resp_ini_addr;

  tcdm_dma_req_t tcdm_dma_req_i_struct;
  assign tcdm_dma_req_i_struct = tcdm_dma_req_i;

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

  assign prebank_req_ini_addr = superbank_req_ini_addr;
  assign superbank_resp_ini_addr = prebank_resp_ini_addr;

  for (genvar d = 0; unsigned'(d) < NumSuperbanks; d++) begin: gen_dma_mux
    tcdm_wide_narrow_mux #(
      .NarrowDataWidth(DataWidth        ),
      .WideDataWidth  (DmaDataWidth     ),
      .narrow_req_t   (tcdm_slave_req_t ),
      .narrow_rsp_t   (tcdm_slave_resp_t),
      .wide_req_t     (tcdm_dma_req_t   ),
      .wide_rsp_t     (tcdm_dma_resp_t  )
    ) i_tcdm_wide_narrow_mux (
      .clk_i                 (clk_i                                             ),
      .rst_ni                (rst_ni                                            ),
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
      .mst_req_o             (prebank_req_payload[d*DmaNumWords+:DmaNumWords]      ),
      .mst_req_wide_o        (prebank_req_wide[d*DmaNumWords+:DmaNumWords]         ),
      .mst_req_valid_o       (prebank_req_valid[d*DmaNumWords+:DmaNumWords]        ),
      .mst_req_ready_i       (prebank_req_ready[d*DmaNumWords+:DmaNumWords]        ),
      .mst_rsp_i             (prebank_resp_payload[d*DmaNumWords+:DmaNumWords]     ),
      .mst_rsp_wide_i        (prebank_resp_wide[d*DmaNumWords+:DmaNumWords]        ),
      .mst_rsp_valid_i       (prebank_resp_valid[d*DmaNumWords+:DmaNumWords]       ),
      .mst_rsp_ready_o       (prebank_resp_ready[d*DmaNumWords+:DmaNumWords]       )
    );
  end

  logic                    [NumBanksPerTile-1:0] bank_req_valid;
  logic                    [NumBanksPerTile-1:0] bank_req_ready;
  local_req_interco_addr_t [NumBanksPerTile-1:0] bank_req_ini_addr;
  logic                    [NumBanksPerTile-1:0] bank_req_wide;
  tcdm_slave_req_t         [NumBanksPerTile-1:0] bank_req_payload;
  logic                    [NumBanksPerTile-1:0] bank_resp_valid;
  logic                    [NumBanksPerTile-1:0] bank_resp_ready;
  tcdm_slave_resp_t        [NumBanksPerTile-1:0] bank_resp_payload;
  logic                    [NumBanksPerTile-1:0] bank_resp_wide;
  local_req_interco_addr_t [NumBanksPerTile-1:0] bank_resp_ini_addr;

  localparam NrManager = NumBanksPerTile / RspGF;

  if (ParallelManager) begin : gen_burst_manager
    for (genvar d = 0; unsigned'(d) < NrManager; d++) begin : gen_parallel_manager
      burst_manager #(
        .NrInOut        ( RspGF                    ),
        .ByteOffset     ( ByteOffset               ),
        .MetaIdWidth    ( snitch_pkg::MetaIdWidth  ),
        .TCDMAddrWidth  ( TCDMTileAddrWidth        ),
        .RspGF          ( RspGF                    ),
        .req_payload_t  ( tcdm_slave_req_t         ),
        .rsp_payload_t  ( tcdm_slave_resp_t        ),
        .addr_t         ( local_req_interco_addr_t ),
        .tile_addr_t    ( tile_addr_t              )
      ) i_burst_manager (
        .clk_i          ( clk_i                    ),
        .rst_ni         ( rst_ni                   ),
        // xbar side
        .req_payload_i  ( prebank_req_payload  [d*RspGF+:RspGF]),
        .req_addr_i     ( prebank_req_ini_addr [d*RspGF+:RspGF]),
        .req_wide_i     ( prebank_req_wide     [d*RspGF+:RspGF]),
        .req_valid_i    ( prebank_req_valid    [d*RspGF+:RspGF]),
        .req_ready_o    ( prebank_req_ready    [d*RspGF+:RspGF]),

        .rsp_payload_o  ( prebank_resp_payload [d*RspGF+:RspGF]),
        .rsp_addr_o     ( prebank_resp_ini_addr[d*RspGF+:RspGF]),
        .rsp_wide_o     ( prebank_resp_wide    [d*RspGF+:RspGF]),
        .rsp_valid_o    ( prebank_resp_valid   [d*RspGF+:RspGF]),
        .rsp_ready_i    ( prebank_resp_ready   [d*RspGF+:RspGF]),

        // bank side
        .req_payload_o  ( bank_req_payload  [d*RspGF+:RspGF] ),
        .req_addr_o     ( bank_req_ini_addr [d*RspGF+:RspGF] ),
        .req_wide_o     ( bank_req_wide     [d*RspGF+:RspGF] ),
        .req_valid_o    ( bank_req_valid    [d*RspGF+:RspGF] ),
        .req_ready_i    ( bank_req_ready    [d*RspGF+:RspGF] ),

        .rsp_payload_i  ( bank_resp_payload [d*RspGF+:RspGF] ),
        .rsp_addr_i     ( bank_resp_ini_addr[d*RspGF+:RspGF] ),
        .rsp_wide_i     ( bank_resp_wide    [d*RspGF+:RspGF] ),
        .rsp_valid_i    ( bank_resp_valid   [d*RspGF+:RspGF] ),
        .rsp_ready_o    ( bank_resp_ready   [d*RspGF+:RspGF] )
      );
    end
  end else if (GroupRsp) begin : gen_single_manager
    burst_manager #(
      .NrInOut        ( NumBanksPerTile          ),
      .ByteOffset     ( ByteOffset               ),
      .MetaIdWidth    ( snitch_pkg::MetaIdWidth  ),
      .TCDMAddrWidth  ( TCDMTileAddrWidth        ),
      .RspGF          ( RspGF                    ),
      .req_payload_t  ( tcdm_slave_req_t         ),
      .rsp_payload_t  ( tcdm_slave_resp_t        ),
      .addr_t         ( local_req_interco_addr_t ),
      .tile_addr_t    ( tile_addr_t              )
    ) i_burst_manager (
      .clk_i          ( clk_i                    ),
      .rst_ni         ( rst_ni                   ),
      // xbar side
      .req_payload_i  ( prebank_req_payload  ),
      .req_addr_i     ( prebank_req_ini_addr ),
      .req_wide_i     ( prebank_req_wide     ),
      .req_valid_i    ( prebank_req_valid    ),
      .req_ready_o    ( prebank_req_ready    ),

      .rsp_payload_o  ( prebank_resp_payload ),
      .rsp_addr_o     ( prebank_resp_ini_addr),
      .rsp_wide_o     ( prebank_resp_wide    ),
      .rsp_valid_o    ( prebank_resp_valid   ),
      .rsp_ready_i    ( prebank_resp_ready   ),

      // bank side
      .req_payload_o  ( bank_req_payload     ),
      .req_addr_o     ( bank_req_ini_addr    ),
      .req_wide_o     ( bank_req_wide        ),
      .req_valid_o    ( bank_req_valid       ),
      .req_ready_i    ( bank_req_ready       ),

      .rsp_payload_i  ( bank_resp_payload    ),
      .rsp_addr_i     ( bank_resp_ini_addr   ),
      .rsp_wide_i     ( bank_resp_wide       ),
      .rsp_valid_i    ( bank_resp_valid      ),
      .rsp_ready_o    ( bank_resp_ready      )
    );
  end else begin : gen_bypass_manager
    // request
    assign bank_req_payload  = prebank_req_payload;
    assign bank_req_ini_addr = prebank_req_ini_addr;
    assign bank_req_wide     = prebank_req_wide;
    assign bank_req_valid    = prebank_req_valid;
    assign prebank_req_ready = bank_req_ready;
    // response
    assign prebank_resp_payload  = bank_resp_payload;
    assign prebank_resp_ini_addr = bank_resp_ini_addr;
    assign prebank_resp_wide     = bank_resp_wide;
    assign prebank_resp_valid    = bank_resp_valid;
    assign bank_resp_ready       = prebank_resp_ready;
  end

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
      wide      : bank_req_wide[b],
      write     : bank_req_payload[b].wen
    };
    assign bank_resp_ini_addr[b]              = meta_out.ini_addr;
    assign bank_resp_payload[b].rdata.meta_id = meta_out.meta_id;
    assign bank_resp_payload[b].ini_addr      = meta_out.tile_id;
    assign bank_resp_payload[b].rdata.core_id = meta_out.core_id;
    assign bank_resp_payload[b].wen           = meta_out.write;
    assign bank_resp_payload[b].gdata         = '0; // Will be assigned in Burst Manager
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

    logic sram_clk;

`ifndef VERILATOR
    // Clock gate
    logic sram_active_q;
    `FF(sram_active_q, req_valid, 1'b0)

    tc_clk_gating i_ckg (
      .clk_i    (clk_i                     ),
      .test_en_i(1'b0                      ),
      .en_i     (req_valid || sram_active_q),
      .clk_o    (sram_clk                  )
    );
`else
    assign sram_clk = clk_i;
`endif

    // Bank
    tc_sram #(
      .DataWidth(DataWidth          ),
      .NumWords (2**TCDMAddrMemWidth),
      .NumPorts (1                  )
    ) mem_bank (
      .clk_i  (sram_clk  ),
      .rst_ni (rst_ni    ),
      .req_i  (req_valid ),
      .we_i   (req_write ),
      .addr_i (req_addr  ),
      .wdata_i(req_wdata ),
      .be_i   (req_be    ),
      .rdata_o(resp_rdata)
    );
  end

  /***************
   *  Registers  *
   ***************/

  // These are required to break dependencies between request and response, establishing a correct
  // valid/ready handshake.
  tcdm_master_req_t  [NumGroups+NumSubGroupsPerGroup-1-1:0] prereg_tcdm_master_req;
  logic              [NumGroups+NumSubGroupsPerGroup-1-1:0] prereg_tcdm_master_req_valid;
  logic              [NumGroups+NumSubGroupsPerGroup-1-1:0] prereg_tcdm_master_req_ready;
  tcdm_slave_req_t   [NumGroups+NumSubGroupsPerGroup-1-1:0] postreg_tcdm_slave_req;
  logic              [NumGroups+NumSubGroupsPerGroup-1-1:0] postreg_tcdm_slave_req_valid;
  logic              [NumGroups+NumSubGroupsPerGroup-1-1:0] postreg_tcdm_slave_req_ready;
  tcdm_slave_resp_t  [NumGroups+NumSubGroupsPerGroup-1-1:0] prereg_tcdm_slave_resp;
  logic              [NumGroups+NumSubGroupsPerGroup-1-1:0] prereg_tcdm_slave_resp_valid;
  logic              [NumGroups+NumSubGroupsPerGroup-1-1:0] prereg_tcdm_slave_resp_ready;
  tcdm_master_resp_t [NumGroups+NumSubGroupsPerGroup-1-1:0] postreg_tcdm_master_resp;
  tile_core_id_t     [NumGroups+NumSubGroupsPerGroup-1-1:0] postreg_tcdm_master_resp_ini_sel;
  logic              [NumGroups+NumSubGroupsPerGroup-1-1:0] postreg_tcdm_master_resp_valid;
  logic              [NumGroups+NumSubGroupsPerGroup-1-1:0] postreg_tcdm_master_resp_ready;

  // Break paths between request and response with registers
  for (genvar h = 0; unsigned'(h) < NumGroups+NumSubGroupsPerGroup-1; h++) begin: gen_tcdm_registers
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

    fall_through_register #(
      .T(tcdm_slave_req_t)
    ) i_tcdm_slave_req_register (
      .clk_i     (clk_i                          ),
      .rst_ni    (rst_ni                         ),
      .clr_i     (1'b0                           ),
      .testmode_i(1'b0                           ),
      .data_i    (tcdm_slave_req_i[h]            ),
      .valid_i   (tcdm_slave_req_valid_i[h]      ),
      .ready_o   (tcdm_slave_req_ready_o[h]      ),
      .data_o    (postreg_tcdm_slave_req[h]      ),
      .valid_o   (postreg_tcdm_slave_req_valid[h]),
      .ready_i   (postreg_tcdm_slave_req_ready[h])
    );

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
  end: gen_tcdm_registers

  /****************************
   *   Remote Interconnects   *
   ****************************/

  tcdm_master_req_t  [NumCoresPerTile*NumDataPortsPerCore-1:0] remote_req_interco;
  logic              [NumCoresPerTile*NumDataPortsPerCore-1:0] remote_req_interco_valid;
  logic              [NumCoresPerTile*NumDataPortsPerCore-1:0] remote_req_interco_ready;
  tcdm_master_resp_t [NumCoresPerTile*NumDataPortsPerCore-1:0] remote_resp_interco;
  logic              [NumCoresPerTile*NumDataPortsPerCore-1:0] remote_resp_interco_valid;
  logic              [NumCoresPerTile*NumDataPortsPerCore-1:0] remote_resp_interco_ready;

  `ifdef TERAPOOL
    tile_remote_sel_t  [NumCoresPerTile*NumDataPortsPerCore-1:0] remote_req_interco_tgt_sel;
    group_id_t         [NumCoresPerTile*NumDataPortsPerCore-1:0] remote_req_interco_tgt_g_sel_tmp;
    sgroup_group_id_t  [NumCoresPerTile*NumDataPortsPerCore-1:0] remote_req_interco_tgt_sg_sel_tmp;
  `else
    group_id_t         [NumCoresPerTile*NumDataPortsPerCore-1:0] remote_req_interco_tgt_sel;
  `endif

  stream_xbar #(
    .NumInp   (NumCoresPerTile*NumDataPortsPerCore  ),
    .NumOut   (NumGroups+NumSubGroupsPerGroup-1     ),
    .payload_t(tcdm_master_req_t                    )
  ) i_remote_req_interco (
    .clk_i  (clk_i                       ),
    .rst_ni (rst_ni                      ),
    .flush_i(1'b0                        ),
    // External priority flag
    .rr_i   ('0                          ),
    // Master
    .data_i (remote_req_interco          ),
    .valid_i(remote_req_interco_valid    ),
    .ready_o(remote_req_interco_ready    ),
    .sel_i  (remote_req_interco_tgt_sel  ),
    // Slave
    .data_o (prereg_tcdm_master_req      ),
    .valid_o(prereg_tcdm_master_req_valid),
    .ready_i(prereg_tcdm_master_req_ready),
    .idx_o  (/* Unused */                )
  );

  stream_xbar #(
    .NumInp   (NumGroups+NumSubGroupsPerGroup-1     ),
    .NumOut   (NumCoresPerTile*NumDataPortsPerCore  ),
    .payload_t(tcdm_master_resp_t                   )
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

  logic             [NumCoresPerTile*NumDataPortsPerCore-1:0] local_req_interco_valid;
  logic             [NumCoresPerTile*NumDataPortsPerCore-1:0] local_req_interco_ready;
  tcdm_slave_req_t  [NumCoresPerTile*NumDataPortsPerCore-1:0] local_req_interco_payload;
  logic             [NumCoresPerTile*NumDataPortsPerCore-1:0] local_resp_interco_valid;
  logic             [NumCoresPerTile*NumDataPortsPerCore-1:0] local_resp_interco_ready;
  tcdm_slave_resp_t [NumCoresPerTile*NumDataPortsPerCore-1:0] local_resp_interco_payload;

  logic [NumCoresPerTile*NumDataPortsPerCore+NumGroups+NumSubGroupsPerGroup-1-1:0][idx_width(NumBanksPerTile)-1:0] local_req_interco_tgt_sel;
  for (genvar j = 0; unsigned'(j) < NumCoresPerTile*NumDataPortsPerCore; j++) begin: gen_local_req_interco_tgt_sel_local
    assign local_req_interco_tgt_sel[j]  = local_req_interco_payload[j].tgt_addr[idx_width(NumBanksPerTile)-1:0];
  end: gen_local_req_interco_tgt_sel_local
  for (genvar j = 0; unsigned'(j) < NumGroups+NumSubGroupsPerGroup-1; j++) begin: gen_local_req_interco_tgt_sel_remote
    assign local_req_interco_tgt_sel[j + NumCoresPerTile*NumDataPortsPerCore]  = postreg_tcdm_slave_req[j].tgt_addr[idx_width(NumBanksPerTile)-1:0];
  end: gen_local_req_interco_tgt_sel_remote

  stream_xbar #(
    .NumInp   (NumCoresPerTile*NumDataPortsPerCore+NumGroups+NumSubGroupsPerGroup-1),
    .NumOut   (NumBanksPerTile                                 ),
    .payload_t(tcdm_slave_req_t                                )
  ) i_local_req_interco (
    .clk_i  (clk_i                                                  ),
    .rst_ni (rst_ni                                                 ),
    .flush_i(1'b0                                                   ),
    // External priority flag
    .rr_i   ('0                                                     ),
    // Master
    .data_i ({postreg_tcdm_slave_req, local_req_interco_payload}    ),
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
    .NumInp   (NumBanksPerTile                                                     ),
    .NumOut   (NumCoresPerTile*NumDataPortsPerCore+NumGroups+NumSubGroupsPerGroup-1),
    .payload_t(tcdm_slave_resp_t                                                   )
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

  /*******************
   *   Core De/mux   *
   *******************/

  // SoC requests
  dreq_t  [NumCoresPerTile*NumDataPortsPerCore-1:0] soc_data_q;
  logic   [NumCoresPerTile*NumDataPortsPerCore-1:0] soc_data_qvalid;
  logic   [NumCoresPerTile*NumDataPortsPerCore-1:0] soc_data_qready;
  dresp_t [NumCoresPerTile*NumDataPortsPerCore-1:0] soc_data_p;
  logic   [NumCoresPerTile*NumDataPortsPerCore-1:0] soc_data_pvalid;
  logic   [NumCoresPerTile*NumDataPortsPerCore-1:0] soc_data_pready;

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
    for (genvar p = 0; p < NumDataPortsPerCore; p++) begin: gen_core_port_mux
      localparam int unsigned idx = NumDataPortsPerCore*c + p;
`ifdef TERAPOOL
      // Remove tile index from local_req_interco_addr_int, since it will not be used for routing.
      addr_t local_req_interco_addr_int;
      assign local_req_interco_payload[idx].tgt_addr =
       tcdm_addr_t'({local_req_interco_addr_int[ByteOffset + idx_width(NumBanksPerTile) + $clog2(NumTiles) +: TCDMAddrMemWidth], // Bank address
               local_req_interco_addr_int[ByteOffset +: idx_width(NumBanksPerTile)]}); // Bank

      // Switch tile and bank indexes for correct upper level routing, and remove the group index
      addr_t prescramble_tcdm_req_tgt_addr;
      if (NumTilesPerGroup == 1) begin : gen_remote_req_interco_tgt_addr
        assign remote_req_interco[idx].tgt_addr =
        tcdm_addr_t'({prescramble_tcdm_req_tgt_addr[ByteOffset + idx_width(NumBanksPerTile) + $clog2(NumGroups) +: TCDMAddrMemWidth], // Bank address
           prescramble_tcdm_req_tgt_addr[ByteOffset +: idx_width(NumBanksPerTile)]}); // Tile
      end else begin : gen_remote_req_interco_tgt_addr
        always_comb begin
          if (remote_req_interco_tgt_g_sel_tmp[idx] == 'b0) begin
            remote_req_interco[idx].tgt_addr =
            tcdm_addr_t'({prescramble_tcdm_req_tgt_addr[ByteOffset + idx_width(NumBanksPerTile) + $clog2(NumTilesPerGroup) + $clog2(NumGroups) +: TCDMAddrMemWidth], // Bank address
            prescramble_tcdm_req_tgt_addr[ByteOffset +: idx_width(NumBanksPerTile)], // Bank
            prescramble_tcdm_req_tgt_addr[ByteOffset + idx_width(NumBanksPerTile) +: $clog2(NumTilesPerSubGroup)]}); // Tile
          end else begin
            remote_req_interco[idx].tgt_addr =
            tcdm_addr_t'({prescramble_tcdm_req_tgt_addr[ByteOffset + idx_width(NumBanksPerTile) + $clog2(NumTilesPerGroup) + $clog2(NumGroups) +: TCDMAddrMemWidth], // Bank address
            prescramble_tcdm_req_tgt_addr[ByteOffset +: idx_width(NumBanksPerTile)], // Bank
            prescramble_tcdm_req_tgt_addr[ByteOffset + idx_width(NumBanksPerTile) +: $clog2(NumTilesPerGroup)]}); // Tile
          end
        end
      end

      // Remote selection signal
      if (NumGroups == 1) begin : gen_remote_req_interco_tgt_sel
        if (NumSubGroupsPerGroup == 1) begin : gen_const_sel
          assign remote_req_interco_tgt_sel[idx] = 1'b0;
        end else begin : gen_const_sel
          assign remote_req_interco_tgt_sel[idx] = (prescramble_tcdm_req_tgt_addr[ByteOffset + $clog2(NumBanksPerTile) + $clog2(NumTilesPerSubGroup) +: $clog2(NumSubGroupsPerGroup)]) ^ sub_group_id;
        end
      end else begin : gen_remote_req_interco_tgt_sel
        // Output port depends on both the target and initiator group and sub-group
        if (NumSubGroupsPerGroup == 1) begin : gen_remote_group_sel
          assign remote_req_interco_tgt_sel[idx] = (prescramble_tcdm_req_tgt_addr[ByteOffset + $clog2(NumBanksPerTile) + $clog2(NumTilesPerGroup) +: $clog2(NumGroups)]) ^ group_id;
        end else begin : gen_remote_group_sel
          assign remote_req_interco_tgt_g_sel_tmp[idx]  = (prescramble_tcdm_req_tgt_addr[ByteOffset + $clog2(NumBanksPerTile) + $clog2(NumTilesPerGroup) +: $clog2(NumGroups)]) ^ group_id;
          assign remote_req_interco_tgt_sg_sel_tmp[idx] = (prescramble_tcdm_req_tgt_addr[ByteOffset + $clog2(NumBanksPerTile) + $clog2(NumTilesPerSubGroup) +: $clog2(NumSubGroupsPerGroup)]) ^ sub_group_id;
          always_comb begin : gen_remote_sub_group_sel
            if (remote_req_interco_tgt_g_sel_tmp[idx] == 'b0) begin: gen_local_group_sel
              remote_req_interco_tgt_sel[idx] = remote_req_interco_tgt_sg_sel_tmp[idx];
            end else begin: gen_remote_group_sel
              remote_req_interco_tgt_sel[idx] = remote_req_interco_tgt_g_sel_tmp[idx] + {(idx_width(NumSubGroupsPerGroup)){1'b1}};
            end
          end
        end
      end
`else
      // Remove tile index from local_req_interco_addr_int, since it will not be used for routing.
      addr_t local_req_interco_addr_int;
      assign local_req_interco_payload[idx].tgt_addr =
       tcdm_addr_t'({local_req_interco_addr_int[ByteOffset + idx_width(NumBanksPerTile) + $clog2(NumTiles) +: TCDMAddrMemWidth], // Bank address
               local_req_interco_addr_int[ByteOffset +: idx_width(NumBanksPerTile)]}); // Bank

      // Switch tile and bank indexes for correct upper level routing, and remove the group index
      addr_t prescramble_tcdm_req_tgt_addr;
      if (NumTilesPerGroup == 1) begin : gen_remote_req_interco_tgt_addr
        assign remote_req_interco[idx].tgt_addr =
        tcdm_addr_t'({prescramble_tcdm_req_tgt_addr[ByteOffset + idx_width(NumBanksPerTile) + $clog2(NumGroups) +: TCDMAddrMemWidth], // Bank address
           prescramble_tcdm_req_tgt_addr[ByteOffset +: idx_width(NumBanksPerTile)]}); // Tile
      end else begin : gen_remote_req_interco_tgt_addr
        assign remote_req_interco[idx].tgt_addr =
        tcdm_addr_t'({prescramble_tcdm_req_tgt_addr[ByteOffset + idx_width(NumBanksPerTile) + $clog2(NumTilesPerGroup) + $clog2(NumGroups) +: TCDMAddrMemWidth], // Bank address
           prescramble_tcdm_req_tgt_addr[ByteOffset +: idx_width(NumBanksPerTile)],                                                                              // Bank
           prescramble_tcdm_req_tgt_addr[ByteOffset + idx_width(NumBanksPerTile) +: $clog2(NumTilesPerGroup)]}); // Tile
      end
      if (NumGroups == 1) begin : gen_remote_req_interco_tgt_sel
        assign remote_req_interco_tgt_sel[idx] = 1'b0;
      end else begin : gen_remote_req_interco_tgt_sel
        // Output port depends on both the target and initiator group
        assign remote_req_interco_tgt_sel[idx] = (prescramble_tcdm_req_tgt_addr[ByteOffset + $clog2(NumBanksPerTile) + $clog2(NumTilesPerGroup) +: $clog2(NumGroups)]) ^ group_id;
      end
`endif

    // We don't care about these
      assign local_req_interco_payload[idx].wdata.core_id = idx;
      assign local_req_interco_payload[idx].ini_addr      = '0;
      assign soc_data_q[idx].id                           = '0;
      assign soc_data_q[idx].rburst                       = '0;

      // Constant value
      // assign remote_req_interco[c].wdata.core_id = c[idx_width(NumCoresPerTile)-1:0];
      assign remote_req_interco[idx].wdata.core_id = idx;

      // Scramble address before entering TCDM shim for sequential+interleaved memory map
      addr_t snitch_data_qaddr_scrambled;
      address_scrambler #(
        .AddrWidth         (AddrWidth        ),
        .ByteOffset        (ByteOffset       ),
        .NumTiles          (NumTiles         ),
        .NumBanksPerTile   (NumBanksPerTile  ),
        .Bypass            (0                ),
        .SeqMemSizePerTile (SeqMemSizePerTile)
      ) i_address_scrambler (
        .address_i (snitch_data_qaddr[c][p]    ),
        .address_o (snitch_data_qaddr_scrambled)
      );

      if (!TrafficGeneration) begin: gen_tcdm_shim
        tcdm_shim #(
          .AddrWidth           (AddrWidth                         ),
          .DataWidth           (DataWidth                         ),
          .MaxOutStandingTrans (snitch_pkg::NumIntOutstandingLoads),
          .NrTCDM              (2                                 ),
          .NrSoC               (1                                 ),
          .NumRules            (3                                 ),
          .MetaIdWidth         (snitch_pkg::MetaIdWidth           )
        ) i_tcdm_shim (
          .clk_i              (clk_i                                                                                  ),
          .rst_ni             (rst_ni                                                                                 ),
          // to TCDM --> FF Connection to outside of tile
          .tcdm_req_valid_o   ({local_req_interco_valid[idx],                  remote_req_interco_valid[idx]}         ),
          .tcdm_req_tgt_addr_o({local_req_interco_addr_int,                    prescramble_tcdm_req_tgt_addr}         ),
          .tcdm_req_wen_o     ({local_req_interco_payload[idx].wen,            remote_req_interco[idx].wen}           ),
          .tcdm_req_wdata_o   ({local_req_interco_payload[idx].wdata.data,     remote_req_interco[idx].wdata.data}    ),
          .tcdm_req_amo_o     ({local_req_interco_payload[idx].wdata.amo,      remote_req_interco[idx].wdata.amo}     ),
          .tcdm_req_id_o      ({local_req_interco_payload[idx].wdata.meta_id,  remote_req_interco[idx].wdata.meta_id} ),
          .tcdm_req_burst_o   ({local_req_interco_payload[idx].rburst,         remote_req_interco[idx].rburst}        ),
          .tcdm_req_be_o      ({local_req_interco_payload[idx].be,             remote_req_interco[idx].be}            ),
          .tcdm_req_ready_i   ({local_req_interco_ready[idx],                  remote_req_interco_ready[idx]}         ),
          .tcdm_resp_valid_i  ({local_resp_interco_valid[idx],                 remote_resp_interco_valid[idx]}        ),
          .tcdm_resp_ready_o  ({local_resp_interco_ready[idx],                 remote_resp_interco_ready[idx]}        ),
          .tcdm_resp_rdata_i  ({local_resp_interco_payload[idx].rdata.data,    remote_resp_interco[idx].rdata.data}   ),
          .tcdm_resp_id_i     ({local_resp_interco_payload[idx].rdata.meta_id, remote_resp_interco[idx].rdata.meta_id}),
          .tcdm_resp_wen_i    ({local_resp_interco_payload[idx].wen,           remote_resp_interco[idx].wen}          ),
          .tcdm_resp_gdata_i  ({local_resp_interco_payload[idx].gdata,         remote_resp_interco[idx].gdata}        ),
          // to SoC
          .soc_qaddr_o        (soc_data_q[idx].addr                                                                 ),
          .soc_qwrite_o       (soc_data_q[idx].write                                                                ),
          .soc_qamo_o         (soc_data_q[idx].amo                                                                  ),
          .soc_qdata_o        (soc_data_q[idx].data                                                                 ),
          .soc_qstrb_o        (soc_data_q[idx].strb                                                                 ),
          .soc_qburst_o       (/*unused*/                                                                           ),
          .soc_qvalid_o       (soc_data_qvalid[idx]                                                                 ),
          .soc_qready_i       (soc_data_qready[idx]                                                                 ),
          .soc_pdata_i        (soc_data_p[idx].data                                                                 ),
          .soc_pwrite_i       (soc_data_p[idx].write                                                                ),
          .soc_perror_i       (soc_data_p[idx].error                                                                ),
          .soc_pvalid_i       (soc_data_pvalid[idx]                                                                 ),
          .soc_pready_o       (soc_data_pready[idx]                                                                 ),
          // from core
          .data_qaddr_i       (snitch_data_qaddr_scrambled                                                          ),
          .data_qwrite_i      (snitch_data_qwrite[c][p]                                                             ),
          .data_qamo_i        (snitch_data_qamo[c][p]                                                               ),
          .data_qdata_i       (snitch_data_qdata[c][p]                                                              ),
          .data_qstrb_i       (snitch_data_qstrb[c][p]                                                              ),
          .data_qid_i         (snitch_data_qid[c][p]                                                                ),
          .data_qburst_i      (snitch_data_qburst[c][p]                                                             ),
          .data_qvalid_i      (snitch_data_qvalid[c][p]                                                             ),
          .data_qready_o      (snitch_data_qready[c][p]                                                             ),
          .data_pdata_o       (snitch_data_pdata[c][p]                                                              ),
          .data_pwrite_o      (snitch_data_pwrite[c][p]                                                             ),
          .data_perror_o      (snitch_data_perror[c][p]                                                             ),
          .data_pid_o         (snitch_data_pid[c][p]                                                                ),
          .data_pgdata_o      (snitch_data_pgdata[c][p]                                                             ),
          .data_pvalid_o      (snitch_data_pvalid[c][p]                                                             ),
          .data_pready_i      (snitch_data_pready[c][p]                                                             ),
          .address_map_i      (mask_map                                                                             )
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
          .tcdm_req_valid_o   ({local_req_interco_valid[idx], remote_req_interco_valid[idx]}    ),
          .tcdm_req_tgt_addr_o({local_req_interco_addr_int, prescramble_tcdm_req_tgt_addr}  ),
          .tcdm_req_wen_o     ({local_req_interco_payload[idx].wen, remote_req_interco[idx].wen}),
          .tcdm_req_wdata_o   ({local_req_interco_payload[idx].wdata.data,
              remote_req_interco[idx].wdata.data}),
          .tcdm_req_amo_o({local_req_interco_payload[idx].wdata.amo,
              remote_req_interco[idx].wdata.amo}),
          .tcdm_req_id_o({local_req_interco_payload[idx].wdata.meta_id,
              remote_req_interco[idx].wdata.meta_id}),
          .tcdm_req_be_o    ({local_req_interco_payload[idx].be, remote_req_interco[idx].be}),
          .tcdm_req_ready_i ({local_req_interco_ready[idx], remote_req_interco_ready[idx]}  ),
          .tcdm_resp_valid_i({local_resp_interco_valid[idx], remote_resp_interco_valid[idx]}),
          .tcdm_resp_ready_o({local_resp_interco_ready[idx], remote_resp_interco_ready[idx]}),
          .tcdm_resp_rdata_i({local_resp_interco_payload[idx].rdata.data,
              remote_resp_interco[idx].rdata.data} ),
          .tcdm_resp_id_i ({local_resp_interco_payload[idx].rdata.meta_id,
              remote_resp_interco[idx].rdata.meta_id})
        );

        // Tie unused signals
        assign soc_data_q[idx].addr    = '0;
        assign soc_data_q[idx].write   = '0;
        assign soc_data_q[idx].amo     = '0;
        assign soc_data_q[idx].data    = '0;
        assign soc_data_q[idx].strb    = '0;
        assign soc_data_qvalid[idx]    = '0;
        assign soc_data_pready[idx]    = '0;
        assign snitch_data_qready[idx] = '0;
        assign snitch_data_pdata[idx]  = '0;
        assign snitch_data_pwrite[idx] = '0;
        assign snitch_data_perror[idx] = '0;
        assign snitch_data_pid[idx]    = '0;
        assign snitch_data_pvalid[idx] = '0;
      end
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
  // assign soc_resp_i.id = 'x;
  assign soc_resp_i.id = '0;
  assign soc_resp_i.gdata = '0;

  snitch_demux #(
    .NrPorts (NumCoresPerTile*NumDataPortsPerCore ),
    .req_t   (snitch_pkg::dreq_t                  ),
    .resp_t  (snitch_pkg::dresp_t                 )
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
