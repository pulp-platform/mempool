// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "mempool/mempool.svh"
`include "hci_helpers.svh"

/* verilator lint_off DECLFILENAME */
module mempool_redmule_tile
  import mempool_pkg::*;
  import hci_package::*;
  import cv32e40x_pkg::*;
  import burst_pkg::*;
  import hci_package::*;
  import cv32e40x_pkg::*;
  import cf_math_pkg::idx_width;
#(
  // TCDM
  parameter addr_t       TCDMBaseAddr = 32'b0,
  // Boot address
  parameter logic [31:0] BootAddr     = 32'h0000_1000,
  // Dependent parameters. DO NOT CHANGE.
  parameter int unsigned NumCaches    = 1
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
  input  logic                                                                    wake_up_i
);

  /****************
   *   Includes   *
   ****************/

  `include "common_cells/registers.svh"
  `include "reqrsp_interface/typedef.svh"

  /*****************
   *  Definitions  *
   *****************/

  import snitch_pkg::dreq_t;
  import snitch_pkg::dresp_t;

  typedef logic [idx_width(NumGroups)-1:0] group_id_t;

  // Local interconnect address width
  typedef logic [idx_width(RMMasterPorts + 1 + NumGroups + NumSubGroupsPerGroup - 1)-1:0] local_req_interco_addr_t;

  /*********************
   *  Control Signals  *
   *********************/
  logic wake_up_q;
  `FF(wake_up_q, wake_up_i, '0, clk_i, rst_ni);

  /*************
   *  Redmule  *
   *************/

  // RedMule interfaces
  logic [1:0]                                 redmule_evt;
  rm_dreq_t [RMMasterPorts-1:0]               redmule_hwpe_req;
  logic [RMMasterPorts-1:0]                   redmule_hwpe_req_valid;
  logic [RMMasterPorts-1:0]                   redmule_hwpe_req_ready;

  rm_dresp_t [RMMasterPorts-1:0]              redmule_hwpe_resp;
  logic [RMMasterPorts-1:0]                   redmule_hwpe_resp_valid;
  logic [RMMasterPorts-1:0]                   redmule_hwpe_resp_ready;

  localparam hci_size_parameter_t `HCI_SIZE_PARAM(tcdm) = '{
    DW:  RMDataWidth,
    AW:  AddrWidth,
    BW:  BeWidth,
    UW:  idx_width(RMOutstandingTransactions),
    IW:  idx_width(RMNumStreams),
    EW:  0,
    EHW: 0
  };

  hwpe_ctrl_intf_periph redmule_periph ( .clk( clk_i ) );
  hci_outstanding_intf #(
    .DW (RMDataWidth),
    .UW (idx_width(RMOutstandingTransactions)),
    .IW (idx_width(RMNumStreams))
  ) tcdm (
    .clk ( clk_i )
  );

  // TODO: This interface port is unused in this context, but it is still required as module input.
  // The interface connection should be removed upstream and inserted in a wrapper module.
  localparam int unsigned NumRs = 3;
  localparam int unsigned XifIdWidth = 3;
  localparam int unsigned XifMemWidth = 32;
  localparam int unsigned XifRFReadWidth = 32;
  localparam int unsigned XifRFWriteWidth = 32;
  localparam logic [31:0] XifMisa = '0;
  localparam logic [ 1:0] XifEcsXs = '0;
  cv32e40x_if_xif#(
  .X_NUM_RS    ( NumRs           ),
  .X_ID_WIDTH  ( XifIdWidth      ),
  .X_MEM_WIDTH ( XifMemWidth     ),
  .X_RFR_WIDTH ( XifRFReadWidth  ),
  .X_RFW_WIDTH ( XifRFWriteWidth ),
  .X_MISA      ( XifMisa         ),
  .X_ECS_XS    ( XifEcsXs        )
  ) core_xif ();

  redmule_top #(
    .N_CORES               ( 1                                    ),
    .DW                    ( RMDataWidth                          ),
    .UW                    ( idx_width(RMOutstandingTransactions) ),
    .X_EXT                 ( 0                                    ),
    .`HCI_SIZE_PARAM(tcdm) ( `HCI_SIZE_PARAM(tcdm)                )
  ) i_redmule_top       (
    .clk_i              ( clk_i          ),
    .rst_ni             ( rst_ni         ),
    .test_mode_i        ( '0             ),
    .evt_o              ( redmule_evt    ),
    .busy_o             ( /*Unused*/     ),
    .tcdm               ( tcdm           ),
    .xif_issue_if_i     ( core_xif.coproc_issue      ),
    .xif_result_if_o    ( core_xif.coproc_result     ),
    .xif_compressed_if_i( core_xif.coproc_compressed ),
    .xif_mem_if_o       ( core_xif.coproc_mem        ),
    .periph             ( redmule_periph             )
  );

  for(genvar ii=0; ii<RMMasterPorts; ii++) begin : tcdm_binding
    assign redmule_hwpe_req[ii].addr    = tcdm.req_add + ii*4;
    assign redmule_hwpe_req[ii].write   = ~tcdm.req_wen;
    assign redmule_hwpe_req[ii].strb    = tcdm.req_be[(ii+1)*4-1:ii*4];
    assign redmule_hwpe_req[ii].data    = tcdm.req_data[(ii+1)*DataWidth-1:ii*DataWidth];
    assign redmule_hwpe_req[ii].id[mempool_pkg::MetaIdWidth-1:idx_width(RMOutstandingTransactions)] = tcdm.req_id;
    assign redmule_hwpe_req[ii].id[idx_width(RMOutstandingTransactions)-1:0] = tcdm.req_user;
    assign redmule_hwpe_req[ii].amo     = '0;
    assign redmule_hwpe_req_valid[ii]   = tcdm.req_valid;
    assign tcdm.resp_data[(ii+1)*DataWidth-1:ii*DataWidth] = redmule_hwpe_resp[ii].data;
    assign redmule_hwpe_resp_ready[ii]                     = tcdm.resp_ready;
  end
  assign tcdm.req_ready  = &(redmule_hwpe_req_ready);
  assign tcdm.resp_id    = redmule_hwpe_resp[0].id[mempool_pkg::MetaIdWidth-1:idx_width(RMOutstandingTransactions)];
  assign tcdm.resp_user  = redmule_hwpe_resp[0].id[idx_width(RMOutstandingTransactions)-1:0];
  assign tcdm.resp_valid = &(redmule_hwpe_resp_valid);

  /***********
   *  Core   *
   ***********/

  // Instruction interfaces
  addr_t snitch_inst_addr;
  data_t snitch_inst_data;
  logic  snitch_inst_valid;
  logic  snitch_inst_ready;

  // Data interfaces
  addr_t    snitch_data_qaddr;
  logic     snitch_data_qwrite;
  amo_t     snitch_data_qamo;
  data_t    snitch_data_qdata;
  strb_t    snitch_data_qstrb;
  meta_id_t snitch_data_qid;
  logic     snitch_data_qvalid;
  logic     snitch_data_qready;
  data_t    snitch_data_pdata;
  logic     snitch_data_perror;
  meta_id_t snitch_data_pid;
  logic     snitch_data_pvalid;
  logic     snitch_data_pready;

  logic [31:0] hart_id;
`ifdef TERAPOOL
  assign hart_id = (NumCores-NumRMTiles) + (tile_id_i/NumTilesPerGroup)*NumRMTilesPerGroup + (tile_id_i%NumTilesPerGroup);
`else
  assign hart_id = (NumCores-NumRMTiles) + (tile_id_i/NumTilesPerSubGroup)*NumRMTilesPerSubGroup + (tile_id_i%NumTilesPerSubGroup);
`endif

  mempool_cc #(
    .BootAddr (BootAddr)
  ) riscv_core (
    .clk_i         (clk_i                                                 ),
    .rst_i         (!rst_ni                                               ),
    .hart_id_i     (hart_id                                               ),
    // IMEM Port
    .inst_addr_o   (snitch_inst_addr                                      ),
    .inst_data_i   (snitch_inst_data                                      ),
    .inst_valid_o  (snitch_inst_valid                                     ),
    .inst_ready_i  (snitch_inst_ready                                     ),
    // Shared operational-units ports
    .sh_acc_req_o         ( /* Unused in RedMule Tile */                  ),
    .sh_acc_req_valid_o   ( /* Unused in RedMule Tile */                  ),
    .sh_acc_req_ready_i   ( /* Unused in RedMule Tile */                  ),
    .sh_acc_resp_i        ( /* Unused in RedMule Tile */                  ),
    .sh_acc_resp_valid_i  ( /* Unused in RedMule Tile */                  ),
    .sh_acc_resp_ready_o  ( /* Unused in RedMule Tile */                  ),
    // Data Ports
    .data_qaddr_o  (snitch_data_qaddr                                     ),
    .data_qwrite_o (snitch_data_qwrite                                    ),
    .data_qamo_o   (snitch_data_qamo                                      ),
    .data_qdata_o  (snitch_data_qdata                                     ),
    .data_qstrb_o  (snitch_data_qstrb                                     ),
    .data_qid_o    (snitch_data_qid[snitch_pkg::SnitchIdWidth-1:0]        ),
    .data_qvalid_o (snitch_data_qvalid                                    ),
    .data_qready_i (snitch_data_qready                                    ),
    .data_pdata_i  (snitch_data_pdata                                     ),
    .data_perror_i (snitch_data_perror                                    ),
    .data_pid_i    (snitch_data_pid[snitch_pkg::SnitchIdWidth-1:0]        ),
    .data_pvalid_i (snitch_data_pvalid                                    ),
    .data_pready_o (snitch_data_pready                                    ),
    .wake_up_sync_i(wake_up_q | redmule_evt[0]                            ),
    // Core Events
    .core_events_o (/* Unused */                                          )
  );

  /***********************
   *  Instruction Cache  *
   ***********************/

  // Instruction interface
  axi_cache_req_t  axi_cache_req_d, axi_cache_req_q;
  axi_cache_resp_t axi_cache_resp_d, axi_cache_resp_q;

  snitch_icache #(
    .NR_FETCH_PORTS     (1                                                   ),
    /// Cache Line Width
    .L0_LINE_COUNT      (4                                                   ),
    .LINE_WIDTH         (ICacheLineWidth                                     ),
    .LINE_COUNT         (ICacheSizeByte / (ICacheSets * ICacheLineWidth / 8) ),
    .SET_COUNT          (ICacheSets                                          ),
    .FETCH_AW           (AddrWidth                                           ),
    .FETCH_DW           (DataWidth                                           ),
    .FILL_AW            (AddrWidth                                           ),
    .FILL_DW            (AxiDataWidth                                        ),
    .FETCH_PRIORITY     (1                                                   ),
    .MERGE_FETCHES      (1                                                   ),
    .SERIAL_LOOKUP      (1                                                   ),
    .L1_TAG_SCM         (1                                                   ),
    .NUM_AXI_OUTSTANDING(8                                                   ),
    /// Make the early cache latch-based. This reduces latency at the cost of
    /// increased combinatorial path lengths and the hassle of having latches in
    /// the design.
    .EARLY_LATCH        (1                                                   ),
    .L0_EARLY_TAG_WIDTH (11                                                  ),
    .ISO_CROSSING       (0                                                   ),
    .axi_req_t          (axi_cache_req_t                                     ),
    .axi_rsp_t          (axi_cache_resp_t                                    )
  ) i_snitch_icache (
    .clk_i                (clk_i                   ),
    .clk_d2_i             (clk_i                   ),
    .rst_ni               (rst_ni                  ),
    .enable_prefetching_i (1'b1                    ),
    .icache_events_o      (/* Unused */            ),
    .flush_valid_i        (1'b0                    ),
    .flush_ready_o        (/* Unused */            ),
    .inst_addr_i          (snitch_inst_addr        ),
    .inst_data_o          (snitch_inst_data        ),
    .inst_cacheable_i     (1'b1                    ),
    .inst_valid_i         (snitch_inst_valid       ),
    .inst_ready_o         (snitch_inst_ready       ),
    .inst_error_o         (/* Unused */            ),
    .sram_cfg_data_i      ('0                      ),
    .sram_cfg_tag_i       ('0                      ),
    .axi_req_o            (axi_cache_req_d         ),
    .axi_rsp_i            (axi_cache_resp_q        )
  );
  axi_cut #(
    .aw_chan_t (axi_cache_aw_t  ),
    .w_chan_t  (axi_cache_w_t   ),
    .b_chan_t  (axi_cache_b_t   ),
    .ar_chan_t (axi_cache_ar_t  ),
    .r_chan_t  (axi_cache_r_t   ),
    .axi_req_t (axi_cache_req_t ),
    .axi_resp_t(axi_cache_resp_t)
  ) axi_cache_slice (
    .clk_i     (clk_i              ),
    .rst_ni    (rst_ni             ),
    .slv_req_i (axi_cache_req_d    ),
    .slv_resp_o(axi_cache_resp_q   ),
    .mst_req_o (axi_cache_req_q    ),
    .mst_resp_i(axi_cache_resp_d   )
  );

  /******************
   *  Core-DMA Mux  *
   ******************/

  // Memory interfaces
  tcdm_dma_req_t           [NumSuperbanks-1:0] tcdm_dma_req;
  logic                    [NumSuperbanks-1:0] tcdm_dma_req_valid;
  logic                    [NumSuperbanks-1:0] tcdm_dma_req_ready;
  tcdm_dma_resp_t          [NumSuperbanks-1:0] tcdm_dma_resp;
  logic                    [NumSuperbanks-1:0] tcdm_dma_resp_valid;
  logic                    [NumSuperbanks-1:0] tcdm_dma_resp_ready;

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
    // From DMA request to Superbank request
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
    // From Superbank response to DMA response
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
      .mst_req_o             (prebank_req_payload[d*DmaNumWords+:DmaNumWords]   ),
      .mst_req_wide_o        (prebank_req_wide[d*DmaNumWords+:DmaNumWords]      ),
      .mst_req_valid_o       (prebank_req_valid[d*DmaNumWords+:DmaNumWords]     ),
      .mst_req_ready_i       (prebank_req_ready[d*DmaNumWords+:DmaNumWords]     ),
      .mst_rsp_i             (prebank_resp_payload[d*DmaNumWords+:DmaNumWords]  ),
      .mst_rsp_wide_i        (prebank_resp_wide[d*DmaNumWords+:DmaNumWords]     ),
      .mst_rsp_valid_i       (prebank_resp_valid[d*DmaNumWords+:DmaNumWords]    ),
      .mst_rsp_ready_o       (prebank_resp_ready[d*DmaNumWords+:DmaNumWords]    )
    );
  end

  /******************
   *  Memory Banks  *
   ******************/

  // Bank metadata
  typedef struct packed {
    meta_id_t meta_id;                 // Outstanding transaction ID
    tile_core_id_t core_id;            // Address of initiator in the issuing Tile
    tile_group_id_t tile_id;           // Addres of initiator in the issuing Group
    local_req_interco_addr_t ini_addr; // Address of initiator port in the destination Tile
    logic wide;                        // Address of superbank initiator (cores/DMA)
  } bank_metadata_t;

  logic           [NumBanksPerTile-1:0] bank_req_valid;
  logic           [NumBanksPerTile-1:0] bank_req_ready;
  strb_t          [NumBanksPerTile-1:0] bank_req_be;
  logic           [NumBanksPerTile-1:0] bank_req_wen;
  amo_t           [NumBanksPerTile-1:0] bank_req_amo;
  data_t          [NumBanksPerTile-1:0] bank_req_data;
  tile_addr_t     [NumBanksPerTile-1:0] bank_req_tgt_addr;
  bank_metadata_t [NumBanksPerTile-1:0] bank_req_payload;

  logic           [NumBanksPerTile-1:0] bank_resp_valid;
  logic           [NumBanksPerTile-1:0] bank_resp_ready;
  data_t          [NumBanksPerTile-1:0] bank_resp_data;
  bank_metadata_t [NumBanksPerTile-1:0] bank_resp_payload;

  if (UseBurst) begin : gen_burst_manager

    typedef struct packed {
      meta_id_t meta_id;
      tile_group_id_t tile_id;
      local_req_interco_addr_t local_id;
      logic wide;
      amo_t amo;
      data_t data;
    } manager_payload_t;

    typedef struct packed {
      logic isburst;
      manager_payload_t[RspGF-2:0] gdata;
    } burst_manager_t;

    manager_payload_t [NumBanksPerTile-1:0] manager_req, postmanager_req;
    tile_core_id_t    [NumBanksPerTile-1:0] manager_req_ini, postmanager_req_ini;
    tile_addr_t       [NumBanksPerTile-1:0] manager_req_tgt;
    logic             [NumBanksPerTile-1:0] manager_req_wen;
    strb_t            [NumBanksPerTile-1:0] manager_req_be;
    burst_t           [NumBanksPerTile-1:0] manager_req_burst;

    manager_payload_t [NumBanksPerTile-1:0] manager_resp, postmanager_resp;
    tile_core_id_t    [NumBanksPerTile-1:0] manager_resp_ini, postmanager_resp_ini;
    burst_manager_t   [NumBanksPerTile-1:0] manager_resp_burst;

    // Connecting to burst manager
    burst_manager #(
      .NumIn          ( RMMasterPorts+1                               ),
      .NumOut         ( NumBanksPerTile                               ),
      .AddrWidth      ( TCDMAddrMemWidth + idx_width(NumBanksPerTile) ),
      .DataWidth      ( $bits(manager_payload_t)                      ),
      .BeWidth        ( DataWidth/8                                   ),
      .ByteOffWidth   ( 0                                             ),
      .RspGF          ( RspGF                                         ),
      .burst_resp_t   ( burst_manager_t                               )
    ) i_burst_manager (
      .clk_i          ( clk_i                 ),
      .rst_ni         ( rst_ni                ),
      .req_ini_addr_i ( manager_req_ini       ),
      .req_tgt_addr_i ( manager_req_tgt       ),
      .req_wdata_i    ( manager_req           ),
      .req_wen_i      ( manager_req_wen       ),
      .req_be_i       ( manager_req_be        ),
      .req_burst_i    ( manager_req_burst     ),
      .req_valid_i    ( prebank_req_valid     ),
      .req_ready_o    ( prebank_req_ready     ),
      .req_ini_addr_o ( postmanager_req_ini   ),
      .req_tgt_addr_o ( bank_req_tgt_addr     ),
      .req_wdata_o    ( postmanager_req       ),
      .req_wen_o      ( bank_req_wen          ),
      .req_be_o       ( bank_req_be           ),
      .req_valid_o    ( bank_req_valid        ),
      .req_ready_i    ( bank_req_ready        ),
      .resp_ini_addr_o( manager_resp_ini      ),
      .resp_rdata_o   ( manager_resp          ),
      .resp_burst_o   ( manager_resp_burst    ),
      .resp_valid_o   ( prebank_resp_valid    ),
      .resp_ready_i   ( prebank_resp_ready    ),
      .resp_ini_addr_i( postmanager_resp_ini  ),
      .resp_rdata_i   ( postmanager_resp      ),
      .resp_valid_i   ( bank_resp_valid       ),
      .resp_ready_o   ( bank_resp_ready       )
    );

    for (genvar b = 0; b < NumBanksPerTile; b++) begin : gen_burst_manager_connections
      // Premanager requests
      assign manager_req_ini[b]           = prebank_req_payload[b].wdata.core_id;
      assign manager_req_tgt[b]           = prebank_req_payload[b].tgt_addr;
      assign manager_req_wen[b]           = prebank_req_payload[b].wen;
      assign manager_req_be[b]            = prebank_req_payload[b].be;
      assign manager_req_burst[b]         = prebank_req_payload[b].burst;
      assign manager_req[b].meta_id       = prebank_req_payload[b].wdata.meta_id;
      assign manager_req[b].tile_id       = prebank_req_payload[b].tile_id;
      assign manager_req[b].local_id      = prebank_req_ini_addr[b];
      assign manager_req[b].wide          = prebank_req_wide[b];
      assign manager_req[b].amo           = prebank_req_payload[b].wdata.amo;
      assign manager_req[b].data          = prebank_req_payload[b].wdata.data;
      // Postmanager requests
      assign bank_req_payload[b].meta_id  = postmanager_req[b].meta_id;
      assign bank_req_payload[b].core_id  = postmanager_req_ini[b];
      assign bank_req_payload[b].tile_id  = postmanager_req[b].tile_id;
      assign bank_req_payload[b].ini_addr = postmanager_req[b].local_id;
      assign bank_req_payload[b].wide     = postmanager_req[b].wide;
      assign bank_req_amo[b]              = postmanager_req[b].amo;
      assign bank_req_data[b]             = postmanager_req[b].data;
      // Postmanager responses
      assign postmanager_resp_ini[b]      = bank_resp_payload[b].core_id;
      assign postmanager_resp[b].meta_id  = bank_resp_payload[b].meta_id;
      assign postmanager_resp[b].tile_id  = bank_resp_payload[b].tile_id;
      assign postmanager_resp[b].local_id = bank_resp_payload[b].ini_addr;
      assign postmanager_resp[b].wide     = bank_resp_payload[b].wide;
      assign postmanager_resp[b].amo      = '0;
      assign postmanager_resp[b].data     = bank_resp_data[b];
      // Premanager responses
      assign prebank_resp_payload[b].rdata.meta_id  = manager_resp[b].meta_id;
      assign prebank_resp_payload[b].rdata.core_id  = manager_resp_ini[b];
      assign prebank_resp_payload[b].tile_id        = manager_resp[b].tile_id;
      assign prebank_resp_ini_addr[b]               = manager_resp[b].local_id;
      assign prebank_resp_wide[b]                   = manager_resp[b].wide;
      assign prebank_resp_payload[b].rdata.amo      = manager_resp[b].amo;
      assign prebank_resp_payload[b].rdata.data     = manager_resp[b].data;
      // Assign burst
      assign prebank_resp_payload[b].burst.isburst = (RspGF > 1) ? manager_resp_burst[b].isburst : 1'b0;
      for (genvar j = 0; j < RspGF-1; j++) begin
        assign prebank_resp_payload[b].burst.gdata[j] = (RspGF > 1) ? manager_resp_burst[b].gdata[j].data : '0;
      end
    end

  end else begin : gen_bypass_manager

    for (genvar b = 0; b < NumBanksPerTile; b++) begin : gen_bank_connections
      // request
      assign bank_req_be[b]               = prebank_req_payload[b].be;
      assign bank_req_wen[b]              = prebank_req_payload[b].wen;
      assign bank_req_amo[b]              = prebank_req_payload[b].wdata.amo;
      assign bank_req_data[b]             = prebank_req_payload[b].wdata.data;
      assign bank_req_tgt_addr[b]         = prebank_req_payload[b].tgt_addr;
      assign bank_req_payload[b].meta_id  = prebank_req_payload[b].wdata.meta_id;
      assign bank_req_payload[b].core_id  = prebank_req_payload[b].wdata.core_id;
      assign bank_req_payload[b].tile_id  = prebank_req_payload[b].tile_id;
      assign bank_req_payload[b].ini_addr = prebank_req_ini_addr[b];
      assign bank_req_payload[b].wide     = prebank_req_wide[b];
      assign bank_req_valid[b]            = prebank_req_valid[b];
      assign prebank_req_ready[b]         = bank_req_ready[b];
      // response
      assign prebank_req_payload[b].rdata.amo         = '0;
      assign prebank_req_payload[b].rdata.data        = bank_resp_data[b];
      assign prebank_req_payload[b].rdata.meta_id     = bank_resp_payload[b].meta_id;
      assign prebank_req_payload[b].rdata.core_id     = bank_resp_payload[b].core_id;
      assign prebank_req_payload[b].tile_id           = bank_resp_payload[b].tile_id;
      assign prebank_req_ini_addr[b]                  = bank_resp_payload[b].ini_addr;
      assign prebank_req_wide[b]                      = bank_resp_payload[b].wide;
    end

  end

  for (genvar b = 0; unsigned'(b) < NumBanksPerTile; b++) begin: gen_banks
    bank_metadata_t meta_out;
    logic req_valid;
    logic req_write;
    bank_addr_t req_addr;
    data_t req_wdata;
    data_t resp_rdata;
    strb_t req_be;
    tcdm_adapter #(
      .AddrWidth     (TCDMAddrMemWidth+ByteOffset),
      .BankAddrWidth (TCDMAddrMemWidth           ),
      .DataWidth     (DataWidth                  ),
      .metadata_t    (bank_metadata_t            ),
      .LrScEnable    (LrScEnable                 ),
      .RegisterAmo   (1'b0                       )
    ) i_tcdm_adapter (
      .clk_i       (clk_i                        ),
      .rst_ni      (rst_ni                       ),
      .in_valid_i  (bank_req_valid[b]            ),
      .in_ready_o  (bank_req_ready[b]            ),
      .in_address_i({bank_req_tgt_addr[b][idx_width(NumBanksPerTile) +: TCDMAddrMemWidth],{ByteOffset{1'b0}}}),
      .in_amo_i    (bank_req_amo[b]              ),
      .in_write_i  (bank_req_wen[b]              ),
      .in_wdata_i  (bank_req_data[b]             ),
      .in_meta_i   (bank_req_payload[b]          ),
      .in_be_i     (bank_req_be[b]               ),
      .in_valid_o  (bank_resp_valid[b]           ),
      .in_ready_i  (bank_resp_ready[b]           ),
      .in_rdata_o  (bank_resp_data[b]            ),
      .in_meta_o   (bank_resp_payload[b]         ),
      .out_req_o   (req_valid                    ),
      .out_add_o   (req_addr                     ),
      .out_write_o (req_write                    ),
      .out_wdata_o (req_wdata                    ),
      .out_be_o    (req_be                       ),
      .out_rdata_i (resp_rdata                   )
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
  logic              [NumGroups+NumSubGroupsPerGroup-1-1:0][idx_width(RMMasterPorts+1)-1:0] postreg_tcdm_master_resp_ini_sel;
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
    assign postreg_tcdm_master_resp_ini_sel[h] = postreg_tcdm_master_resp[h].rdata.core_id[idx_width(RMMasterPorts+1)-1:0];

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

  tcdm_master_req_t  [(RMMasterPorts+1)-1:0] remote_req_interco;
  logic              [(RMMasterPorts+1)-1:0] remote_req_interco_valid;
  logic              [(RMMasterPorts+1)-1:0] remote_req_interco_ready;
  tcdm_master_resp_t [(RMMasterPorts+1)-1:0] remote_resp_interco;
  logic              [(RMMasterPorts+1)-1:0] remote_resp_interco_valid;
  logic              [(RMMasterPorts+1)-1:0] remote_resp_interco_ready;

  `ifdef TERAPOOL
    tile_remote_sel_t  [(RMMasterPorts+1)-1:0] remote_req_interco_tgt_sel;
  `else
    group_id_t         [(RMMasterPorts+1)-1:0] remote_req_interco_tgt_sel;
  `endif

  stream_xbar #(
    .NumInp   (RMMasterPorts+1                 ),
    .NumOut   (NumGroups+NumSubGroupsPerGroup-1),
    .payload_t(tcdm_master_req_t               )
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
    .NumInp   (NumGroups+NumSubGroupsPerGroup-1),
    .NumOut   (RMMasterPorts+1                 ),
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

  logic             [(RMMasterPorts+1)-1:0] local_req_interco_valid;
  logic             [(RMMasterPorts+1)-1:0] local_req_interco_ready;
  tcdm_slave_req_t  [(RMMasterPorts+1)-1:0] local_req_interco_payload;
  logic             [(RMMasterPorts+1)-1:0] local_resp_interco_valid;
  logic             [(RMMasterPorts+1)-1:0] local_resp_interco_ready;
  tcdm_slave_resp_t [(RMMasterPorts+1)-1:0] local_resp_interco_payload;

  logic [RMMasterPorts+1+NumGroups+NumSubGroupsPerGroup-1-1:0][idx_width(NumBanksPerTile)-1:0] local_req_interco_tgt_sel;
  for (genvar j = 0; unsigned'(j) < RMMasterPorts+1; j++) begin: gen_local_req_interco_tgt_sel_local
    assign local_req_interco_tgt_sel[j]  = local_req_interco_payload[j].tgt_addr[idx_width(NumBanksPerTile)-1:0];
  end: gen_local_req_interco_tgt_sel_local
  for (genvar j = 0; unsigned'(j) < NumGroups+NumSubGroupsPerGroup-1; j++) begin: gen_local_req_interco_tgt_sel_remote
    assign local_req_interco_tgt_sel[j + RMMasterPorts+1]  = postreg_tcdm_slave_req[j].tgt_addr[idx_width(NumBanksPerTile)-1:0];
  end: gen_local_req_interco_tgt_sel_remote

  stream_xbar #(
    .NumInp   (RMMasterPorts+1+NumGroups+NumSubGroupsPerGroup-1),
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
    .NumInp   (NumBanksPerTile                                 ),
    .NumOut   (RMMasterPorts+1+NumGroups+NumSubGroupsPerGroup-1),
    .payload_t(tcdm_slave_resp_t                               )
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

  // Address map
  typedef enum int unsigned {
    TCDM_EXTERNAL = 0, TCDM_LOCAL, PER
  } addr_map_slave_t;

  address_map_t [2:0] mask_map;
  assign mask_map = '{
    // Lowest priority: send request through the SoC port
    '{slave_idx: PER,
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

  /*************************
   *   RedMule TCDM Plug   *
   *************************/

  addr_t [RMMasterPorts-1:0] redmule_hwpe_addr_scrambled;

  rm_dreq_t [RMMasterPorts-1:0] redmule_tcdm_req;
  logic     [RMMasterPorts-1:0] redmule_tcdm_req_valid;
  logic     [RMMasterPorts-1:0] redmule_tcdm_req_ready;
  logic     [RMMasterPorts-1:0] redmule_tcdm_handshake_p;
  logic     [RMMasterPorts-1:0] redmule_tcdm_handshake_q;

  logic                          redmule_resp_allvalid;
  rm_dresp_t [RMMasterPorts-1:0] redmule_tcdm_resp;
  logic      [RMMasterPorts-1:0] redmule_tcdm_resp_valid;
  logic      [RMMasterPorts-1:0] redmule_tcdm_resp_ready;

  // Burst requests/responses
  tcdm_payload_t [RMMasterPorts-1:0] remote_req_preburst_payload, remote_req_postburst_payload;
  logic          [RMMasterPorts-1:0] remote_req_preburst_wen, remote_req_postburst_we;
  strb_t         [RMMasterPorts-1:0] remote_req_preburst_be, remote_req_postburst_be;
  addr_t         [RMMasterPorts-1:0] remote_req_preburst_addr, remote_req_postburst_addr;
  logic          [RMMasterPorts-1:0] remote_req_preburst_valid, remote_req_postburst_valid;
  logic          [RMMasterPorts-1:0] remote_req_preburst_ready, remote_req_postburst_ready;
  burst_t        [RMMasterPorts-1:0] remote_req_postburst_burst;
  //
  tcdm_payload_t [RMMasterPorts-1:0] remote_resp_preburst_payload, remote_resp_postburst_payload;
  logic          [RMMasterPorts-1:0] remote_resp_preburst_valid, remote_resp_preburst_ready;
  burst_gresp_t  [RMMasterPorts-1:0] remote_resp_postburst_burst;

  // Handshake separately on each request port
  assign redmule_hwpe_req_ready = redmule_tcdm_handshake_q | (redmule_tcdm_req_valid & redmule_tcdm_req_ready);
  assign redmule_tcdm_handshake_p = &redmule_hwpe_req_ready ? '0 : redmule_tcdm_handshake_q | (redmule_tcdm_req_valid & redmule_tcdm_req_ready);
  `FF(redmule_tcdm_handshake_q, redmule_tcdm_handshake_p, '0, clk_i, rst_ni);

  // Signal ready only when all ports are valid
  assign redmule_resp_allvalid = &redmule_tcdm_resp_valid;

  // RedMulE response
  transactions_table #(
    .NumPorts        (RMMasterPorts),
    .NumTransactions (RMNumStreams*RMOutstandingTransactions),
    .resp_t          (rm_dresp_t)
  ) i_transactions_table (
    .clk_i         (clk_i     ),
    .rst_ni        (rst_ni    ),
    .resp_payload_i(redmule_tcdm_resp),
    .resp_valid_i  (redmule_tcdm_resp_valid),
    .resp_ready_o  (redmule_tcdm_resp_ready),
    .resp_payload_o(redmule_hwpe_resp),
    .resp_valid_o  (redmule_hwpe_resp_valid),
    .resp_ready_i  (redmule_hwpe_resp_ready)
  );

  for (genvar c = 0; c < RMMasterPorts; c++) begin: gen_redmule_mux

    // Scramble address before entering TCDM shim for sequential+interleaved memory map
    address_scrambler #(
      .AddrWidth         (AddrWidth        ),
      .ByteOffset        (ByteOffset       ),
      .NumTiles          (NumTiles         ),
      .NumBanksPerTile   (NumBanksPerTile  ),
      .Bypass            (0                ),
      .SeqMemSizePerTile (SeqMemSizePerTile)
    ) i_address_scrambler (
      .address_i (redmule_hwpe_req[c].addr      ),
      .address_o (redmule_hwpe_addr_scrambled[c])
    );

   /*************************
    *   RedMule Handshakes  *
    *************************/

    assign redmule_tcdm_req[c].addr  = redmule_hwpe_addr_scrambled[c];
    assign redmule_tcdm_req[c].write = redmule_hwpe_req[c].write;
    assign redmule_tcdm_req[c].data  = redmule_hwpe_req[c].data;
    assign redmule_tcdm_req[c].strb  = redmule_hwpe_req[c].strb;
    assign redmule_tcdm_req[c].id    = redmule_hwpe_req[c].id;
    assign redmule_tcdm_req[c].amo   = '0;
    assign redmule_tcdm_req_valid[c] = redmule_tcdm_handshake_q[c] ? 1'b0 : redmule_hwpe_req_valid[c];

    // Signals for type conversions
    rm_dreq_t local_tcdm_req, remote_tcdm_req;
    rm_dresp_t local_tcdm_resp, remote_tcdm_resp;

    snitch_addr_demux #(
      .NrOutput     (2),
      .AddressWidth (AddrWidth),
      .NumRules     (2 ), // TODO
      .req_t        (rm_dreq_t   ),
      .resp_t       (rm_dresp_t  )
    ) i_snitch_addr_demux (
      .clk_i         (clk_i                            ),
      .rst_ni        (rst_ni                           ),
      .req_addr_i    (redmule_tcdm_req[c].addr         ),
      .req_payload_i (redmule_tcdm_req[c]              ),
      .req_valid_i   (redmule_tcdm_req_valid[c]        ),
      .req_ready_o   (redmule_tcdm_req_ready[c]        ),
      .resp_payload_o(redmule_tcdm_resp[c]             ),
      .resp_valid_o  (redmule_tcdm_resp_valid[c]       ),
      .resp_ready_i  (redmule_tcdm_resp_ready[c]       ),
      .req_payload_o ({local_tcdm_req, remote_tcdm_req}),
      .req_valid_o   ({local_req_interco_valid[c+1], remote_req_preburst_valid[c]}),
      .req_ready_i   ({local_req_interco_ready[c+1], remote_req_preburst_ready[c]}),
      .resp_payload_i({local_tcdm_resp, remote_tcdm_resp}),
      .resp_valid_i  ({local_resp_interco_valid[c+1], remote_resp_preburst_valid[c]}),
      .resp_ready_o  ({local_resp_interco_ready[c+1], remote_resp_preburst_ready[c]}),
      .address_map_i (mask_map[1:0])
    );

    /* LOCAL REQ./RESP. */

    // Local request
    assign local_req_interco_payload[c+1].wdata.meta_id = local_tcdm_req.id;
    assign local_req_interco_payload[c+1].wdata.amo = local_tcdm_req.amo;
    assign local_req_interco_payload[c+1].wdata.data = local_tcdm_req.data;
    assign local_req_interco_payload[c+1].wen = local_tcdm_req.write;
    assign local_req_interco_payload[c+1].be = local_tcdm_req.strb;
    assign local_req_interco_payload[c+1].burst.isburst = 1'b0;
    assign local_req_interco_payload[c+1].burst.blen = '0;
    // Remove tile index from local_req_tgt_address_i, since it will not be used for routing.
    logic [TCDMAddrMemWidth-1:0] local_req_row_addr;
    logic [$clog2(NumBanksPerTile)-1:0] local_req_bank_addr;
    assign local_req_row_addr = local_tcdm_req.addr[ByteOffset + $clog2(NumBanksPerTile) + $clog2(NumTiles) +: TCDMAddrMemWidth];
    assign local_req_bank_addr = local_tcdm_req.addr[ByteOffset +: $clog2(NumBanksPerTile)];
    assign local_req_interco_payload[c+1].tgt_addr = tcdm_addr_t'({local_req_row_addr, local_req_bank_addr});
    // We don't care about these
    assign local_req_interco_payload[c+1].wdata.core_id = '0;
    assign local_req_interco_payload[c+1].tile_id       = '0;

    // Local response
    assign local_tcdm_resp.id = local_resp_interco_payload[c+1].rdata.meta_id;
    assign local_tcdm_resp.data = local_resp_interco_payload[c+1].rdata.data;
    assign local_tcdm_resp.write = 1'b0; // Don't care
    assign local_tcdm_resp.error = 1'b0; // Don't care

    /* REMOTE REQ./RESP. */

    // Address slicer
    tcdm_addr_slicer i_tcdm_addr_slicer (
      .remote_req_tgt_addr_i  (remote_req_postburst_addr[c]       ),
      .remote_req_tgt_addr_o  (remote_req_interco[c+1].tgt_addr       ),
      .tile_id_i              (tile_id_i                              ),
      .remote_req_tgt_sel_o   (remote_req_interco_tgt_sel[c+1]        )
    );

    // Remote request
    assign remote_req_preburst_payload[c].meta_id = remote_tcdm_req.id;
    assign remote_req_preburst_payload[c].amo = remote_tcdm_req.amo;
    assign remote_req_preburst_payload[c].data = remote_tcdm_req.data;
    localparam unsigned port_id = c+1;
    assign remote_req_preburst_payload[c].core_id = port_id[idx_width(RMMasterPorts+1)-1:0];
    assign remote_req_preburst_wen[c] = remote_tcdm_req.write;
    assign remote_req_preburst_be[c] = remote_tcdm_req.strb;
    assign remote_req_preburst_addr[c] = remote_tcdm_req.addr;
    // Remote request post burst
    assign remote_req_interco[c+1].wdata = remote_req_postburst_payload[c];
    assign remote_req_interco[c+1].wen = remote_req_postburst_we[c];
    assign remote_req_interco[c+1].be = remote_req_postburst_be[c];
    assign remote_req_interco[c+1].burst = remote_req_postburst_burst[c];
    assign remote_req_interco_valid[c+1] = remote_req_postburst_valid[c];
    assign remote_req_postburst_ready[c] = remote_req_interco_ready[c+1];

    // Remote response
    assign remote_tcdm_resp.id = remote_resp_preburst_payload[c].meta_id;
    assign remote_tcdm_resp.data = remote_resp_preburst_payload[c].data;
    assign remote_tcdm_resp.write = 1'b0; // Don't care
    assign remote_tcdm_resp.error = 1'b0; // Don't care
    // Remote response post burst
    assign remote_resp_postburst_payload[c] = remote_resp_interco[c+1].rdata;
    assign remote_resp_postburst_burst[c] = remote_resp_interco[c+1].burst;

  end

  /************************
   *   Burst remote req   *
   ************************/

  burst_req_grouper #(
    .NumIn        ( RMMasterPorts                           ),
    .NumOut       ( NumBanksPerTile                         ),
    .AddrWidth    ( AddrWidth                               ),
    .DataWidth    ( $bits(tcdm_payload_t)                   ),
    .BeWidth      ( DataWidth/8                             ),
    .AddrMemWidth ( idx_width(NumBanksPerTile) + ByteOffset ),
    .RspGF        ( RspGF                                   ),
    .ByteOffWidth ( ByteOffset                              )
  ) i_burst_req_grouper (
    .clk_i,
    .rst_ni,
    .req_ini_addr_i ( /* Unused */                 ),
    .req_tgt_addr_i ( remote_req_preburst_addr     ),
    .req_wdata_i    ( remote_req_preburst_payload  ),
    .req_wen_i      ( remote_req_preburst_wen      ),
    .req_be_i       ( remote_req_preburst_be       ),
    .req_valid_i    ( remote_req_preburst_valid    ),
    .req_ready_o    ( remote_req_preburst_ready    ),
    .req_ini_addr_o ( /* Unused */                 ),
    .req_tgt_addr_o ( remote_req_postburst_addr    ),
    .req_wdata_o    ( remote_req_postburst_payload ),
    .req_wen_o      ( remote_req_postburst_we      ),
    .req_be_o       ( remote_req_postburst_be      ),
    .req_burst_o    ( remote_req_postburst_burst   ),
    .req_valid_o    ( remote_req_postburst_valid   ),
    .req_ready_i    ( remote_req_postburst_ready   ),
    // Response out
    .resp_ini_addr_o ( /* Unused */                ),
    .resp_rdata_o    (remote_resp_preburst_payload ),
    .resp_valid_o    (remote_resp_preburst_valid   ),
    .resp_ready_i    (remote_resp_preburst_ready   ),
    // Response in
    .resp_ini_addr_i ( /* Unused */                              ),
    .resp_rdata_i    (remote_resp_postburst_payload              ),
    .resp_burst_i    (remote_resp_postburst_burst                ),
    .resp_valid_i    (remote_resp_interco_valid[RMMasterPorts:1] ),
    .resp_ready_o    (remote_resp_interco_ready[RMMasterPorts:1] )
  );

  /************************
   *   Snitch TCDM Plug   *
   ************************/

  // Core De/mux
  dreq_t  per_data_q;
  logic   per_data_qvalid;
  logic   per_data_qready;
  dresp_t per_data_p;
  logic   per_data_pvalid;
  logic   per_data_pready;

  // SoC requests
  dreq_t  soc_data_q;
  logic   soc_data_qvalid;
  logic   soc_data_qready;
  dresp_t soc_data_p;
  logic   soc_data_pvalid;
  logic   soc_data_pready;

  // Redmule requests
  dreq_t  redmule_data_q;
  logic   redmule_data_qvalid;
  logic   redmule_data_qready;
  dresp_t redmule_data_p;
  logic   redmule_data_pvalid;
  logic   redmule_data_pready;

  // Unsliced addresses
  addr_t local_req_presliced_tgt_addr;
  addr_t remote_req_presliced_tgt_addr;
  logic [TCDMAddrMemWidth-1:0] local_req_presliced_row_addr;
  logic [$clog2(NumBanksPerTile)-1:0] local_req_presliced_bank_addr;

  // Scramble address before entering TCDM shim for sequential+interleaved memory map
  addr_t snitch_data_qaddr_scrambled;
  address_scrambler #(
    .AddrWidth         (AddrWidth        ),
    .ByteOffset        (ByteOffset       ),
    .NumTiles          (NumTiles         ),
    .NumBanksPerTile   (NumBanksPerTile  ),
    .Bypass            (0                ),
    .SeqMemSizePerTile (SeqMemSizePerTile)
  ) i_sn_address_scrambler (
    .address_i (snitch_data_qaddr          ),
    .address_o (snitch_data_qaddr_scrambled)
  );

  tcdm_shim #(
    .AddrWidth           (AddrWidth                         ),
    .DataWidth           (DataWidth                         ),
    .MaxOutStandingTrans (snitch_pkg::NumIntOutstandingLoads),
    .NrTCDM              (2                                 ),
    .NrSoC               (1                                 ),
    .NumRules            (3                                 )
  ) i_sn_tcdm_shim (
    .clk_i              (clk_i                                                                              ),
    .rst_ni             (rst_ni                                                                             ),
    // to TCDM --> FF Connection to outside of tile
    .tcdm_req_valid_o   ({local_req_interco_valid[0], remote_req_interco_valid[0]}                          ),
    .tcdm_req_tgt_addr_o({local_req_presliced_tgt_addr, remote_req_presliced_tgt_addr}                      ),
    .tcdm_req_wen_o     ({local_req_interco_payload[0].wen, remote_req_interco[0].wen}                      ),
    .tcdm_req_wdata_o   ({local_req_interco_payload[0].wdata.data, remote_req_interco[0].wdata.data}        ),
    .tcdm_req_amo_o     ({local_req_interco_payload[0].wdata.amo, remote_req_interco[0].wdata.amo}          ),
    .tcdm_req_id_o      ({local_req_interco_payload[0].wdata.meta_id, remote_req_interco[0].wdata.meta_id}  ),
    .tcdm_req_be_o      ({local_req_interco_payload[0].be, remote_req_interco[0].be}                        ),
    .tcdm_req_ready_i   ({local_req_interco_ready[0], remote_req_interco_ready[0]}                          ),
    .tcdm_resp_valid_i  ({local_resp_interco_valid[0], remote_resp_interco_valid[0]}                        ),
    .tcdm_resp_ready_o  ({local_resp_interco_ready[0], remote_resp_interco_ready[0]}                        ),
    .tcdm_resp_rdata_i  ({local_resp_interco_payload[0].rdata.data, remote_resp_interco[0].rdata.data}      ),
    .tcdm_resp_id_i     ({local_resp_interco_payload[0].rdata.meta_id, remote_resp_interco[0].rdata.meta_id}),
    // to SoC or RedMule
    .soc_qaddr_o        (per_data_q.addr            ),
    .soc_qwrite_o       (per_data_q.write           ),
    .soc_qamo_o         (per_data_q.amo             ),
    .soc_qdata_o        (per_data_q.data            ),
    .soc_qstrb_o        (per_data_q.strb            ),
    .soc_qvalid_o       (per_data_qvalid            ),
    .soc_qready_i       (per_data_qready            ),
    .soc_pdata_i        (per_data_p.data            ),
    .soc_perror_i       (per_data_p.error           ),
    .soc_pvalid_i       (per_data_pvalid            ),
    .soc_pready_o       (per_data_pready            ),
    // from core
    .data_qaddr_i       (snitch_data_qaddr_scrambled),
    .data_qwrite_i      (snitch_data_qwrite         ),
    .data_qamo_i        (snitch_data_qamo           ),
    .data_qdata_i       (snitch_data_qdata          ),
    .data_qstrb_i       (snitch_data_qstrb          ),
    .data_qid_i         (snitch_data_qid            ),
    .data_qvalid_i      (snitch_data_qvalid         ),
    .data_qready_o      (snitch_data_qready         ),
    .data_pdata_o       (snitch_data_pdata          ),
    .data_perror_o      (snitch_data_perror         ),
    .data_pid_o         (snitch_data_pid            ),
    .data_pvalid_o      (snitch_data_pvalid         ),
    .data_pready_i      (snitch_data_pready         ),
    .address_map_i      (mask_map                   )
  );

  /* LOCAL REQUESTS */

  // We don't care about these
  assign local_req_interco_payload[0].wdata.core_id = '0;
  assign local_req_interco_payload[0].tile_id       = '0;
  assign per_data_q.id                              = '0;
  // Remove tile index from local_req_tgt_address_i, since it will not be used for routing.
  assign local_req_presliced_row_addr = local_req_presliced_tgt_addr[ByteOffset + $clog2(NumBanksPerTile) + $clog2(NumTiles) +: TCDMAddrMemWidth];
  assign local_req_presliced_bank_addr = local_req_presliced_tgt_addr[ByteOffset +: $clog2(NumBanksPerTile)];
  assign local_req_interco_payload[0].tgt_addr = tcdm_addr_t'({local_req_presliced_row_addr, local_req_presliced_bank_addr});
  // requests from Snitch are not bursted
  assign local_req_interco_payload[0].burst.isburst = 1'b0;
  assign local_req_interco_payload[0].burst.blen = '0;

  /* REMOTE REQUESTS */

  // Address slicer
  tcdm_addr_slicer i_tcdm_addr_slicer (
    .remote_req_tgt_addr_i  (remote_req_presliced_tgt_addr          ),
    .remote_req_tgt_addr_o  (remote_req_interco[0].tgt_addr         ),
    .tile_id_i              (tile_id_i                              ),
    .remote_req_tgt_sel_o   (remote_req_interco_tgt_sel[0]          )
  );

  // Constant value
  assign remote_req_interco[0].wdata.core_id = '0;
  // Requests from Snitch are not bursted
  assign remote_req_interco[0].burst.isburst = 1'b0;
  assign remote_req_interco[0].burst.blen = '0;

  /************************
   *   Peripheral demux   *
   ************************/

  // Address map
  typedef enum int unsigned {
    REDMULE = 0, SOC
  } addr_map_per_t;

  address_map_t [1:0] per_mask_map;
  assign per_mask_map = '{
    // Lowest priority: send request through the SoC port
    '{slave_idx: SOC,
      mask     : '0,
      value    : '0
    },
    // Send request to RedMule configuration registers
    '{slave_idx: REDMULE,
      mask     : RMMask,
      value    : RMBaseAddr
    }
  };

  // Redmule configuration register writes
  assign redmule_periph.req = redmule_data_qvalid;
  assign redmule_periph.add = redmule_data_q.addr;
  assign redmule_periph.wen = ~redmule_data_q.write;
  assign redmule_periph.be = redmule_data_q.strb;
  assign redmule_periph.data = redmule_data_q.data;
  assign redmule_periph.id = redmule_data_q.id;
  assign redmule_data_qready = redmule_periph.gnt;
  assign redmule_data_p.data = redmule_periph.r_data;
  assign redmule_data_pvalid = redmule_periph.r_valid;

  // Demux according to address peripheral requests to RedMule/SoC
  snitch_addr_demux #(
    .NrOutput     (2        ),
    .AddressWidth (DataWidth),
    .NumRules     (2        ),
    .req_t        (dreq_t   ),
    .resp_t       (dresp_t  )
  ) i_snitch_addr_demux (
    .clk_i         (clk_i                                    ),
    .rst_ni        (rst_ni                                   ),
    .req_addr_i    (per_data_q.addr                          ),
    .req_payload_i (per_data_q                               ),
    .req_valid_i   (per_data_qvalid                          ),
    .req_ready_o   (per_data_qready                          ),
    .resp_payload_o(per_data_p                               ),
    .resp_valid_o  (per_data_pvalid                          ),
    .resp_ready_i  (per_data_pready                          ),
    .req_payload_o ({soc_data_q, redmule_data_q}             ),
    .req_valid_o   ({soc_data_qvalid, redmule_data_qvalid}   ),
    .req_ready_i   ({soc_data_qready, redmule_data_qready}   ),
    .resp_payload_i({soc_data_p, redmule_data_p}             ),
    .resp_valid_i  ({soc_data_pvalid, redmule_data_pvalid}   ),
    .resp_ready_o  ({soc_data_pready, redmule_data_pready}   ),
    .address_map_i (per_mask_map                             )
  );

  /****************
   *   AXI Plug   *
   ****************/

  `REQRSP_TYPEDEF_ALL(soc, snitch_pkg::addr_t, snitch_pkg::data_t, snitch_pkg::strb_t)

  // Pack the Snitch soc_req/rsp into a reqrsp bus
  soc_req_t snitch_to_soc_req;
  soc_rsp_t snitch_to_soc_rsp;
  // AXI core request
  axi_core_req_t  axi_core_req_d, axi_core_req_q;
  axi_core_resp_t axi_core_resp_d, axi_core_resp_q;
  axi_cache_req_t  axi_core_wide_req;
  axi_cache_resp_t axi_core_wide_resp;

  assign snitch_to_soc_req.q.addr  = soc_data_q.addr;
  assign snitch_to_soc_req.q.write = soc_data_q.write;
  assign snitch_to_soc_req.q.amo   = reqrsp_pkg::amo_op_e'(soc_data_q.amo);
  assign snitch_to_soc_req.q.data  = soc_data_q.data;
  assign snitch_to_soc_req.q.strb  = soc_data_q.strb;
  assign snitch_to_soc_req.q.size  = 3'b010; // AXI-style size: 2^x bytes
  assign snitch_to_soc_req.q_valid = soc_data_qvalid;
  assign soc_data_qready           = snitch_to_soc_rsp.q_ready;
  assign soc_data_p.data           = snitch_to_soc_rsp.p.data;
  assign soc_data_p.error          = snitch_to_soc_rsp.p.error;
  assign soc_data_p.id             = '0; // Don't care
  assign soc_data_p.write          = '0; // Don't care
  assign soc_data_pvalid           = snitch_to_soc_rsp.p_valid;
  assign snitch_to_soc_req.p_ready = soc_data_pready;

  reqrsp_to_axi #(
    .MaxTrans     (NumCoresPerTile),
    .DataWidth    (DataWidth      ),
    .reqrsp_req_t (soc_req_t      ),
    .reqrsp_rsp_t (soc_rsp_t      ),
    .axi_req_t    (axi_core_req_t ),
    .axi_rsp_t    (axi_core_resp_t)
  ) i_reqrsp_snitch_to_axi (
    .clk_i        (clk_i            ),
    .rst_ni       (rst_ni           ),
    .reqrsp_req_i (snitch_to_soc_req),
    .reqrsp_rsp_o (snitch_to_soc_rsp),
    .axi_req_o    (axi_core_req_d   ),
    .axi_rsp_i    (axi_core_resp_q  )
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
    .clk_i     (clk_i          ),
    .rst_ni    (rst_ni         ),
    .slv_req_i (axi_core_req_d ),
    .slv_resp_o(axi_core_resp_q),
    .mst_req_o (axi_core_req_q ),
    .mst_resp_i(axi_core_resp_d)
  );

  axi_dw_converter #(
    .AxiMaxReads         (NumCoresPerTile ),
    .AxiSlvPortDataWidth (DataWidth       ),
    .AxiMstPortDataWidth (AxiDataWidth    ),
    .AxiAddrWidth        (AddrWidth       ),
    .AxiIdWidth          (AxiCoreIdWidth  ),
    .aw_chan_t           (axi_core_aw_t   ),
    .mst_w_chan_t        (axi_cache_w_t   ),
    .slv_w_chan_t        (axi_core_w_t    ),
    .b_chan_t            (axi_core_b_t    ),
    .ar_chan_t           (axi_core_ar_t   ),
    .mst_r_chan_t        (axi_cache_r_t   ),
    .slv_r_chan_t        (axi_core_r_t    ),
    .axi_mst_req_t       (axi_cache_req_t ),
    .axi_mst_resp_t      (axi_cache_resp_t),
    .axi_slv_req_t       (axi_core_req_t  ),
    .axi_slv_resp_t      (axi_core_resp_t )
  ) i_axi_dw_converter_cores (
    .clk_i      (clk_i             ),
    .rst_ni     (rst_ni            ),
    .slv_req_i  (axi_core_req_q    ),
    .slv_resp_o (axi_core_resp_d   ),
    .mst_req_o  (axi_core_wide_req ),
    .mst_resp_i (axi_core_wide_resp)
  );

  axi_mux #(
    .SlvAxiIDWidth (AxiCoreIdWidth  ),
    .slv_aw_chan_t (axi_cache_aw_t  ),
    .mst_aw_chan_t (axi_tile_aw_t   ),
    .w_chan_t      (axi_cache_w_t   ),
    .slv_b_chan_t  (axi_cache_b_t   ),
    .mst_b_chan_t  (axi_tile_b_t    ),
    .slv_ar_chan_t (axi_cache_ar_t  ),
    .mst_ar_chan_t (axi_tile_ar_t   ),
    .slv_r_chan_t  (axi_cache_r_t   ),
    .mst_r_chan_t  (axi_tile_r_t    ),
    .slv_req_t     (axi_cache_req_t ),
    .slv_resp_t    (axi_cache_resp_t),
    .mst_req_t     (axi_tile_req_t  ),
    .mst_resp_t    (axi_tile_resp_t ),
    .NoSlvPorts    (1+NumCaches     ),
    .MaxWTrans     (NumCoresPerTile ),
    .FallThrough   (1               )
  ) i_axi_mux (
    .clk_i      (clk_i                                 ),
    .rst_ni     (rst_ni                                ),
    .test_i     (1'b0                                  ),
    .slv_reqs_i ({axi_core_wide_req, axi_cache_req_q}  ),
    .slv_resps_o({axi_core_wide_resp, axi_cache_resp_d}),
    .mst_req_o  (axi_mst_req_o                         ),
    .mst_resp_i (axi_mst_resp_i                        )
  );

  /******************
   *   Assertions   *
   ******************/

  // Check invariants.
  if (BootAddr[1:0] != 2'b00)
    $fatal(1, "[mempool_tile] Boot address should be aligned in a 4-byte boundary.");

  if (NumCoresPerTile != 2**$clog2(NumCoresPerTile))
    $fatal(1, "[mempool_tile] The number of cores per tile must be a power of two.");

  if (NumCores != unsigned'(2**$clog2(NumCores)) && (NumRMTiles == 0))
    $fatal(1, "[mempool_tile] The number of cores must be a power of two.");

  if (NumBanksPerTile < 1)
    $fatal(1, "[mempool_tile] The number of banks per tile must be larger than one");

  if (DataWidth > AxiDataWidth)
    $error("AxiDataWidth needs to be larger than DataWidth!");

endmodule : mempool_redmule_tile
