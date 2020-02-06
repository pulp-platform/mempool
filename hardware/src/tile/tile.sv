// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

import mempool_pkg::*     ;
import snitch_pkg::dreq_t ;
import snitch_pkg::dresp_t;

module tile #(
    // Boot address
    parameter logic [31:0] BootAddr        = 32'h0000_1000         ,
    // Instruction cache
    parameter int unsigned ICacheSizeByte  = 1024 * NumCoresPerTile, // Total Size of instruction cache in bytes
    parameter int unsigned ICacheSets      = NumCoresPerTile       ,
    parameter int unsigned ICacheLineWidth = NumCoresPerTile * 32
  ) (
    // Clock and reset
    input  logic                             clk_i,
    input  logic                             rst_ni,
    // Scan chain
    input  logic                             scan_enable_i,
    input  logic                             scan_data_i,
    output logic                             scan_data_o,
    // Tile ID
    input  logic       [31:0]                tile_id_i,
    // Core data interface
    output logic       [NumCoresPerTile-1:0] tcdm_master_req_o,
    output addr_t      [NumCoresPerTile-1:0] tcdm_master_addr_o,
    output logic       [NumCoresPerTile-1:0] tcdm_master_wen_o,
    output data_t      [NumCoresPerTile-1:0] tcdm_master_wdata_o,
    output be_t        [NumCoresPerTile-1:0] tcdm_master_be_o,
    input  logic       [NumCoresPerTile-1:0] tcdm_master_gnt_i,
    input  logic       [NumCoresPerTile-1:0] tcdm_master_vld_i,
    input  data_t      [NumCoresPerTile-1:0] tcdm_master_rdata_i,
    // TCDM banks interface
    input  logic       [NumCoresPerTile-1:0] mem_req_i,
    input  core_addr_t [NumCoresPerTile-1:0] mem_ret_addr_i,
    output logic       [NumCoresPerTile-1:0] mem_gnt_o,
    input  tile_addr_t [NumCoresPerTile-1:0] mem_addr_i,
    input  logic       [NumCoresPerTile-1:0] mem_wen_i,
    input  data_t      [NumCoresPerTile-1:0] mem_wdata_i,
    input  be_t        [NumCoresPerTile-1:0] mem_be_i,
    output logic       [NumCoresPerTile-1:0] mem_vld_o,
    output core_addr_t [NumCoresPerTile-1:0] mem_resp_addr_o,
    output data_t      [NumCoresPerTile-1:0] mem_rdata_o,
    // AXI Interface
    output axi_req_t                         axi_mst_req_o ,
    input  axi_resp_t                        axi_mst_resp_i,
    // Instruction interface
    output addr_t                            refill_qaddr_o,
    output logic       [7:0]                 refill_qlen_o,      // AXI signal
    output logic                             refill_qvalid_o,
    input  logic                             refill_qready_i,
    input  logic       [ICacheLineWidth-1:0] refill_pdata_i,
    input  logic                             refill_perror_i,
    input  logic                             refill_pvalid_i,
    input  logic                             refill_plast_i,
    output logic                             refill_pready_o
  );

  /***********
   *  Cores  *
   ***********/

  // Instruction interfaces
  addr_t [NumCoresPerTile-1:0] inst_addr;
  data_t [NumCoresPerTile-1:0] inst_data;
  logic  [NumCoresPerTile-1:0] inst_valid;
  logic  [NumCoresPerTile-1:0] inst_ready;

  // Data interfaces
  addr_t [NumCoresPerTile-1:0] data_qaddr;
  logic  [NumCoresPerTile-1:0] data_qwrite;
  amo_t  [NumCoresPerTile-1:0] data_qamo;
  data_t [NumCoresPerTile-1:0] data_qdata;
  be_t   [NumCoresPerTile-1:0] data_qstrb;
  logic  [NumCoresPerTile-1:0] data_qvalid;
  logic  [NumCoresPerTile-1:0] data_qready;
  data_t [NumCoresPerTile-1:0] data_pdata;
  logic  [NumCoresPerTile-1:0] data_perror;
  logic  [NumCoresPerTile-1:0] data_pvalid;
  logic  [NumCoresPerTile-1:0] data_pready;

  for (genvar c = 0; c < NumCoresPerTile; c++) begin: gen_cores
    logic [31:0] hart_id;
    assign hart_id = {tile_id_i, c[$clog2(NumCoresPerTile)-1:0]};

    mempool_cc #(
      .BootAddr ( BootAddr )
    ) riscv_core (
      .clk_i          ( clk_i          ),
      .rst_i          ( ~rst_ni        ),
      .hart_id_i      ( hart_id        ),
      // IMEM Port
      .inst_addr_o    ( inst_addr[c]   ),
      .inst_data_i    ( inst_data[c]   ),
      .inst_valid_o   ( inst_valid[c]  ),
      .inst_ready_i   ( inst_ready[c]  ),
      // Data Ports
      .data_qaddr_o   ( data_qaddr[c]  ),
      .data_qwrite_o  ( data_qwrite[c] ),
      .data_qamo_o    ( data_qamo[c]   ),
      .data_qdata_o   ( data_qdata[c]  ),
      .data_qstrb_o   ( data_qstrb[c]  ),
      .data_qvalid_o  ( data_qvalid[c] ),
      .data_qready_i  ( data_qready[c] ),
      .data_pdata_i   ( data_pdata[c]  ),
      .data_perror_i  ( data_perror[c] ),
      .data_pvalid_i  ( data_pvalid[c] ),
      .data_pready_o  ( data_pready[c] ),
      .wake_up_sync_i ( '0             ),
      // Core Events
      .core_events_o  ( /* Unused */   )
    );
  end

  /***********************
   *  Instruction Cache  *
   ***********************/

  snitch_icache #(
    .NR_FETCH_PORTS    ( NumCoresPerTile                                          ),
    /// Cache Line Width
    .L0_LINE_COUNT     ( 4                                                        ),
    .LINE_WIDTH        ( ICacheLineWidth                                          ),
    .LINE_COUNT        ( ICacheSizeByte / (NumCoresPerTile * NumCoresPerTile * 4) ),
    .SET_COUNT         ( ICacheSets                                               ),
    .FETCH_AW          ( AddrWidth                                                ),
    .FETCH_DW          ( DataWidth                                                ),
    .FILL_AW           ( AddrWidth                                                ),
    .FILL_DW           ( ICacheLineWidth                                          ),
    .EARLY_ENABLED     ( 1                                                        ),
    /// Make the early cache latch-based. This reduces latency at the cost of
    /// increased combinatorial path lengths and the hassle of having latches in
    /// the design.
    .EARLY_LATCH       ( 0                                                        ),
    /// Make the early cache serve responses combinatorially if possible. Set
    /// this to 0 to cut combinatorial paths into the fetch interface.
    .EARLY_FALLTHROUGH ( 0                                                        )
  ) i_snitch_icache (
    .clk_i           ( clk_i           ),
    .rst_ni          ( rst_ni          ),
    .inst_addr_i     ( inst_addr       ),
    .inst_data_o     ( inst_data       ),
    .inst_valid_i    ( inst_valid      ),
    .inst_ready_o    ( inst_ready      ),
    .inst_error_o    ( /* Unused */    ),
    .refill_qaddr_o  ( refill_qaddr_o  ),
    .refill_qlen_o   ( refill_qlen_o   ),
    .refill_qvalid_o ( refill_qvalid_o ),
    .refill_qready_i ( refill_qready_i ),
    .refill_pdata_i  ( refill_pdata_i  ),
    .refill_perror_i ( refill_perror_i ),
    .refill_pvalid_i ( refill_pvalid_i ),
    .refill_plast_i  ( refill_plast_i  ),
    .refill_pready_o ( refill_pready_o )
  );

  /***********************
   *  TCDM Memory Banks  *
   ***********************/

  // Memory interfaces
  logic       [NumBanksPerTile-1:0] tile_mem_req;
  tcdm_addr_t [NumBanksPerTile-1:0] tile_mem_addr;
  logic       [NumBanksPerTile-1:0] tile_mem_wen;
  data_t      [NumBanksPerTile-1:0] tile_mem_wdata;
  be_t        [NumBanksPerTile-1:0] tile_mem_be;
  data_t      [NumBanksPerTile-1:0] tile_mem_rdata;

  for (genvar b = 0; b < NumBanksPerTile; b++) begin: gen_banks
    data_t tile_mem_be_int;
    for (genvar be_byte = 0; be_byte < BeWidth; be_byte++) begin: gen_mem_be
      assign tile_mem_be_int[8*be_byte+:8] = {8{tile_mem_be[b][be_byte]}};
    end

    sram #(
      .DATA_WIDTH(DataWidth          ),
      .NUM_WORDS (2**TCDMAddrMemWidth)
    ) mem_bank (
      .clk_i  (clk_i            ),
      .req_i  (tile_mem_req[b]  ),
      .we_i   (tile_mem_wen[b]  ),
      .addr_i (tile_mem_addr[b] ),
      .wdata_i(tile_mem_wdata[b]),
      .be_i   (tile_mem_be_int  ),
      .rdata_o(tile_mem_rdata[b])
    );
  end

  /*************************
   *   Internal Crossbar   *
   *************************/

  // TCDM request
  logic  [NumCoresPerTile-1:0] local_xbar_req;
  logic  [NumCoresPerTile-1:0] local_xbar_gnt;
  logic  [NumCoresPerTile-1:0] local_xbar_vld;
  addr_t [NumCoresPerTile-1:0] local_xbar_addr;
  data_t [NumCoresPerTile-1:0] local_xbar_rdata;
  logic  [NumCoresPerTile-1:0] local_xbar_wen;
  data_t [NumCoresPerTile-1:0] local_xbar_wdata;
  be_t   [NumCoresPerTile-1:0] local_xbar_be;

  addr_t [NumCoresPerTile-1:0] mem_addr;
  for (genvar c = 0; c < NumCoresPerTile; c++) begin: gen_mem_addr
    assign mem_addr[c] = {mem_addr_i[c], {ByteOffset{1'b0}}};
  end

  tcdm_interconnect #(
    .NumIn       ( 2*NumCoresPerTile          ),
    .NumOut      ( NumBanksPerTile            ),
    .AddrWidth   ( AddrWidth                  ),
    .AddrMemWidth( TCDMAddrMemWidth           ),
    .RespLat     ( 1                          ),
    .WriteRespOn ( 1'b0                       ),
    .Topology    ( tcdm_interconnect_pkg::LIC )
  ) local_xbar (
    .clk_i  (clk_i                           ),
    .rst_ni (rst_ni                          ),
    .req_i  ({local_xbar_req, mem_req_i}     ),
    .add_i  ({local_xbar_addr, mem_addr}     ),
    .wen_i  ({local_xbar_wen, mem_wen_i}     ),
    .wdata_i({local_xbar_wdata, mem_wdata_i} ),
    .be_i   ({local_xbar_be, mem_be_i}       ),
    .gnt_o  ({local_xbar_gnt, mem_gnt_o}     ),
    .vld_o  ({local_xbar_vld, mem_vld_o}     ),
    .rdata_o({local_xbar_rdata, mem_rdata_o} ),
    .req_o  (tile_mem_req                    ),
    .gnt_i  (tile_mem_req                    ), // Memories always grant the requests
    .add_o  (tile_mem_addr                   ),
    .wen_o  (tile_mem_wen                    ),
    .wdata_o(tile_mem_wdata                  ),
    .be_o   (tile_mem_be                     ),
    .rdata_i(tile_mem_rdata                  )
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      mem_resp_addr_o <= '0;
    end else begin
      mem_resp_addr_o <= mem_ret_addr_i;
    end
  end

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

  // Signals for FFing tile boundaries
  logic  [NumCoresPerTile-1:0] tcdm_master_req;
  addr_t [NumCoresPerTile-1:0] tcdm_master_addr;
  logic  [NumCoresPerTile-1:0] tcdm_master_wen;
  data_t [NumCoresPerTile-1:0] tcdm_master_wdata;
  be_t   [NumCoresPerTile-1:0] tcdm_master_be;
  logic  [NumCoresPerTile-1:0] tcdm_master_gnt;

  // Address map
  typedef enum int unsigned {
    TCDM_EXTERNAL = 0, TCDM_LOCAL, SOC
  } addr_map_slave_t;

  address_map_t [2:0] mask_map;
  assign mask_map = '{
    // Lowest priority: send request through the SoC port
    '{slave_idx: SOC ,
      mask     : '0  ,
      value    : '0
    },
    // Send request through the external TCDM port
    '{slave_idx: TCDM_EXTERNAL ,
      mask     : TCDMMask      ,
      value    : TCDMBaseAddr
    },
    // Highest priority: send request through the local TCDM port
    '{slave_idx: TCDM_LOCAL                                                                     ,
      mask     : TCDMMask | ({$clog2(NumTiles){1'b1}} << (ByteOffset + $clog2(NumBanksPerTile))),
      value    : TCDMBaseAddr | (tile_id_i << (ByteOffset + $clog2(NumBanksPerTile)))
    }
  };

  for (genvar c = 0; c < NumCoresPerTile; c++) begin: gen_core_mux
    // Remove tile index from local_xbar_addr_int, since it will not be used for routing.
    addr_t local_xbar_addr_int;
    assign local_xbar_addr[c] = addr_t'({local_xbar_addr_int[AddrWidth:ByteOffset+$clog2(NumBanks)], local_xbar_addr_int[0 +: ByteOffset + $clog2(NumBanksPerTile)]});

    tcdm_shim #(
      .AddrWidth          (AddrWidth),
      .DataWidth          (DataWidth),
      .MaxOutStandingReads(2        ),
      .InclDemux          (1'b1     ),
      .NrTCDM             (2        ),
      .NrSoC              (1        ),
      .NumRules           (3        )
    ) i_tcdm_shim (
      .clk_i        (clk_i                                        ),
      .rst_i        (!rst_ni                                      ),
      // to TCDM --> FF Connection to outside of tile
      .tcdm_req_o   ({local_xbar_req[c], tcdm_master_req[c]}      ),
      .tcdm_add_o   ({local_xbar_addr_int, tcdm_master_addr[c]}   ),
      .tcdm_wen_o   ({local_xbar_wen[c], tcdm_master_wen[c]}      ),
      .tcdm_wdata_o ({local_xbar_wdata[c], tcdm_master_wdata[c]}  ),
      .tcdm_be_o    ({local_xbar_be[c], tcdm_master_be[c]}        ),
      .tcdm_gnt_i   ({local_xbar_gnt[c], tcdm_master_gnt[c]}      ),
      .tcdm_vld_i   ({local_xbar_vld[c], tcdm_master_vld_i[c]}    ),
      .tcdm_rdata_i ({local_xbar_rdata[c], tcdm_master_rdata_i[c]}),
      // to SoC
      .soc_qaddr_o  (soc_data_q[c].addr                           ),
      .soc_qwrite_o (soc_data_q[c].write                          ),
      .soc_qamo_o   (soc_data_q[c].amo                            ),
      .soc_qdata_o  (soc_data_q[c].data                           ),
      .soc_qstrb_o  (soc_data_q[c].strb                           ),
      .soc_qvalid_o (soc_data_qvalid[c]                           ),
      .soc_qready_i (soc_data_qready[c]                           ),
      .soc_pdata_i  (soc_data_p[c].data                           ),
      .soc_perror_i (soc_data_p[c].error                          ),
      .soc_pvalid_i (soc_data_pvalid[c]                           ),
      .soc_pready_o (soc_data_pready[c]                           ),
      // from core
      .data_qaddr_i (data_qaddr[c]                                ),
      .data_qwrite_i(data_qwrite[c]                               ),
      .data_qamo_i  (data_qamo[c]                                 ),
      .data_qdata_i (data_qdata[c]                                ),
      .data_qstrb_i (data_qstrb[c]                                ),
      .data_qvalid_i(data_qvalid[c]                               ),
      .data_qready_o(data_qready[c]                               ),
      .data_pdata_o (data_pdata[c]                                ),
      .data_perror_o(data_perror[c]                               ),
      .data_pvalid_o(data_pvalid[c]                               ),
      .data_pready_i(data_pready[c]                               ),
      .address_map_i(mask_map                                     )
    );

    // Switch tile and bank indexes for correct upper level routing
    addr_t tcdm_master_addr_int;
    assign tcdm_master_addr_int =
      addr_t'({tcdm_master_addr[c][ByteOffset + $clog2(NumBanksPerTile) +: TCDMAddrMemWidth] , // Bank address
          tcdm_master_addr[c][ByteOffset +: $clog2(NumBanksPerTile)]                         , // Bank
          tcdm_master_addr[c][ByteOffset + $clog2(NumBanksPerTile) +: $clog2(NumTiles)]      , // Tile
          c[$clog2(NumCoresPerTile)-1:0]                                                     , // TCDM slave port
          tcdm_master_addr[c][0 +: ByteOffset]});

    // Register request to the TCDM interconnect
    spill_register #(
      .T(logic[AddrWidth + 1 + DataWidth + BeWidth - 1:0])
    ) i_register_tcdm_req (
      .clk_i  (clk_i                                                                                      ),
      .rst_ni (rst_ni                                                                                     ),
      .data_i ({tcdm_master_addr_int, tcdm_master_wen[c], tcdm_master_wdata[c], tcdm_master_be[c] }       ),
      .valid_i(tcdm_master_req[c]                                                                         ),
      .ready_o(tcdm_master_gnt[c]                                                                         ),
      .data_o ({tcdm_master_addr_o[c], tcdm_master_wen_o[c], tcdm_master_wdata_o[c], tcdm_master_be_o[c]} ),
      .valid_o(tcdm_master_req_o[c]                                                                       ),
      .ready_i(tcdm_master_gnt_i[c]                                                                       )
    );
  end

  /****************
   *   AXI Plug   *
   ****************/

  snitch_pkg::dreq_t soc_req_o  ;
  snitch_pkg::dresp_t soc_resp_i;

  logic soc_qvalid;
  logic soc_qready;
  logic soc_pvalid;
  logic soc_pready;

  snitch_demux #(
    .NrPorts (NumCoresPerTile    ),
    .req_t   (snitch_pkg::dreq_t ),
    .resp_t  (snitch_pkg::dresp_t)
  ) i_snitch_demux_data (
    .clk_i         ( clk_i          ),
    .rst_ni        ( rst_ni         ),
    // Inputs
    .req_payload_i ( soc_data_q     ),
    .req_valid_i   ( soc_data_qvalid),
    .req_ready_o   ( soc_data_qready),
    .resp_payload_o( soc_data_p     ),
    .resp_last_o   (                ),
    .resp_valid_o  ( soc_data_pvalid),
    .resp_ready_i  ( soc_data_pready),
    // Output
    .req_payload_o ( soc_req_o      ),
    .req_valid_o   ( soc_qvalid     ),
    .req_ready_i   ( soc_qready     ),
    .resp_payload_i( soc_resp_i     ),
    .resp_last_i   ( 1'b1           ),
    .resp_valid_i  ( soc_pvalid     ),
    .resp_ready_o  ( soc_pready     )
  );

  // Core request
  axi_req_t  axi_mst_req;
  axi_resp_t axi_mst_resp;

  snitch_axi_adapter #(
    .axi_mst_req_t  ( axi_req_t  ),
    .axi_mst_resp_t ( axi_resp_t )
  ) i_snitch_core_axi_adapter (
    .clk_i        ( clk_i            ),
    .rst_ni       ( rst_ni           ),
    .slv_qaddr_i  ( soc_req_o.addr   ),
    .slv_qwrite_i ( soc_req_o.write  ),
    .slv_qamo_i   ( soc_req_o.amo    ),
    .slv_qdata_i  ( soc_req_o.data   ),
    .slv_qstrb_i  ( soc_req_o.strb   ),
    .slv_qrlen_i  ( '0               ),
    .slv_qvalid_i ( soc_qvalid       ),
    .slv_qready_o ( soc_qready       ),
    .slv_pdata_o  ( soc_resp_i.data  ),
    .slv_perror_o ( soc_resp_i.error ),
    .slv_plast_o  (                  ),
    .slv_pvalid_o ( soc_pvalid       ),
    .slv_pready_i ( soc_pready       ),
    .axi_req_o    ( axi_mst_req      ),
    .axi_resp_i   ( axi_mst_resp     )
  );

  axi_slice #(
    .AXI_ADDR_WIDTH(AddrWidth    ),
    .AXI_DATA_WIDTH(DataWidth    ),
    .AXI_ID_WIDTH  (AxiMstIdWidth),
    .AXI_USER_WIDTH(1            )
  ) axi_mst_slice (
    .clk_i                 (clk_i                  ),
    .rst_ni                (rst_ni                 ),
    .test_en_i             (1'b0                   ),
    .axi_slave_aw_valid_i  (axi_mst_req.aw_valid   ),
    .axi_slave_aw_addr_i   (axi_mst_req.aw.addr    ),
    .axi_slave_aw_prot_i   (axi_mst_req.aw.prot    ),
    .axi_slave_aw_region_i (axi_mst_req.aw.region  ),
    .axi_slave_aw_len_i    (axi_mst_req.aw.len     ),
    .axi_slave_aw_size_i   (axi_mst_req.aw.size    ),
    .axi_slave_aw_burst_i  (axi_mst_req.aw.burst   ),
    .axi_slave_aw_lock_i   (axi_mst_req.aw.lock    ),
    .axi_slave_aw_atop_i   (axi_mst_req.aw.atop    ),
    .axi_slave_aw_cache_i  (axi_mst_req.aw.cache   ),
    .axi_slave_aw_qos_i    (axi_mst_req.aw.qos     ),
    .axi_slave_aw_id_i     (axi_mst_req.aw.id      ),
    .axi_slave_aw_user_i   (axi_mst_req.aw.user    ),
    .axi_slave_aw_ready_o  (axi_mst_resp.aw_ready  ),
    .axi_slave_ar_valid_i  (axi_mst_req.ar_valid   ),
    .axi_slave_ar_addr_i   (axi_mst_req.ar.addr    ),
    .axi_slave_ar_prot_i   (axi_mst_req.ar.prot    ),
    .axi_slave_ar_region_i (axi_mst_req.ar.region  ),
    .axi_slave_ar_len_i    (axi_mst_req.ar.len     ),
    .axi_slave_ar_size_i   (axi_mst_req.ar.size    ),
    .axi_slave_ar_burst_i  (axi_mst_req.ar.burst   ),
    .axi_slave_ar_lock_i   (axi_mst_req.ar.lock    ),
    .axi_slave_ar_cache_i  (axi_mst_req.ar.cache   ),
    .axi_slave_ar_qos_i    (axi_mst_req.ar.qos     ),
    .axi_slave_ar_id_i     (axi_mst_req.ar.id      ),
    .axi_slave_ar_user_i   (axi_mst_req.ar.user    ),
    .axi_slave_ar_ready_o  (axi_mst_resp.ar_ready  ),
    .axi_slave_w_valid_i   (axi_mst_req.w_valid    ),
    .axi_slave_w_data_i    (axi_mst_req.w.data     ),
    .axi_slave_w_strb_i    (axi_mst_req.w.strb     ),
    .axi_slave_w_user_i    (axi_mst_req.w.user     ),
    .axi_slave_w_last_i    (axi_mst_req.w.last     ),
    .axi_slave_w_ready_o   (axi_mst_resp.w_ready   ),
    .axi_slave_r_valid_o   (axi_mst_resp.r_valid   ),
    .axi_slave_r_data_o    (axi_mst_resp.r.data    ),
    .axi_slave_r_resp_o    (axi_mst_resp.r.resp    ),
    .axi_slave_r_last_o    (axi_mst_resp.r.last    ),
    .axi_slave_r_id_o      (axi_mst_resp.r.id      ),
    .axi_slave_r_user_o    (axi_mst_resp.r.user    ),
    .axi_slave_r_ready_i   (axi_mst_req.r_ready    ),
    .axi_slave_b_valid_o   (axi_mst_resp.b_valid   ),
    .axi_slave_b_resp_o    (axi_mst_resp.b.resp    ),
    .axi_slave_b_id_o      (axi_mst_resp.b.id      ),
    .axi_slave_b_user_o    (axi_mst_resp.b.user    ),
    .axi_slave_b_ready_i   (axi_mst_req.b_ready    ),
    .axi_master_aw_valid_o (axi_mst_req_o.aw_valid ),
    .axi_master_aw_addr_o  (axi_mst_req_o.aw.addr  ),
    .axi_master_aw_prot_o  (axi_mst_req_o.aw.prot  ),
    .axi_master_aw_region_o(axi_mst_req_o.aw.region),
    .axi_master_aw_len_o   (axi_mst_req_o.aw.len   ),
    .axi_master_aw_size_o  (axi_mst_req_o.aw.size  ),
    .axi_master_aw_burst_o (axi_mst_req_o.aw.burst ),
    .axi_master_aw_lock_o  (axi_mst_req_o.aw.lock  ),
    .axi_master_aw_atop_o  (axi_mst_req_o.aw.atop  ),
    .axi_master_aw_cache_o (axi_mst_req_o.aw.cache ),
    .axi_master_aw_qos_o   (axi_mst_req_o.aw.qos   ),
    .axi_master_aw_id_o    (axi_mst_req_o.aw.id    ),
    .axi_master_aw_user_o  (axi_mst_req_o.aw.user  ),
    .axi_master_aw_ready_i (axi_mst_resp_i.aw_ready),
    .axi_master_ar_valid_o (axi_mst_req_o.ar_valid ),
    .axi_master_ar_addr_o  (axi_mst_req_o.ar.addr  ),
    .axi_master_ar_prot_o  (axi_mst_req_o.ar.prot  ),
    .axi_master_ar_region_o(axi_mst_req_o.ar.region),
    .axi_master_ar_len_o   (axi_mst_req_o.ar.len   ),
    .axi_master_ar_size_o  (axi_mst_req_o.ar.size  ),
    .axi_master_ar_burst_o (axi_mst_req_o.ar.burst ),
    .axi_master_ar_lock_o  (axi_mst_req_o.ar.lock  ),
    .axi_master_ar_cache_o (axi_mst_req_o.ar.cache ),
    .axi_master_ar_qos_o   (axi_mst_req_o.ar.qos   ),
    .axi_master_ar_id_o    (axi_mst_req_o.ar.id    ),
    .axi_master_ar_user_o  (axi_mst_req_o.ar.user  ),
    .axi_master_ar_ready_i (axi_mst_resp_i.ar_ready),
    .axi_master_w_valid_o  (axi_mst_req_o.w_valid  ),
    .axi_master_w_data_o   (axi_mst_req_o.w.data   ),
    .axi_master_w_strb_o   (axi_mst_req_o.w.strb   ),
    .axi_master_w_user_o   (axi_mst_req_o.w.user   ),
    .axi_master_w_last_o   (axi_mst_req_o.w.last   ),
    .axi_master_w_ready_i  (axi_mst_resp_i.w_ready ),
    .axi_master_r_valid_i  (axi_mst_resp_i.r_valid ),
    .axi_master_r_data_i   (axi_mst_resp_i.r.data  ),
    .axi_master_r_resp_i   (axi_mst_resp_i.r.resp  ),
    .axi_master_r_last_i   (axi_mst_resp_i.r.last  ),
    .axi_master_r_id_i     (axi_mst_resp_i.r.id    ),
    .axi_master_r_user_i   (axi_mst_resp_i.r.user  ),
    .axi_master_r_ready_o  (axi_mst_req_o.r_ready  ),
    .axi_master_b_valid_i  (axi_mst_resp_i.b_valid ),
    .axi_master_b_resp_i   (axi_mst_resp_i.b.resp  ),
    .axi_master_b_id_i     (axi_mst_resp_i.b.id    ),
    .axi_master_b_user_i   (axi_mst_resp_i.b.user  ),
    .axi_master_b_ready_o  (axi_mst_req_o.b_ready  )
  );

  /******************
   *   Assertions   *
   ******************/

  `ifndef SYNTHESIS
  `ifndef VERILATOR
  // Check invariants.
  initial begin
    assert (BootAddr[1:0] == 2'b00);

    assert (2**$clog2(NumCoresPerTile) == NumCoresPerTile || NumCoresPerTile == 1) else
      $fatal(1, "Number of cores must be a power of two");

    assert (2**$clog2(ICacheSizeByte) == ICacheSizeByte);
  end
  `endif
  `endif

endmodule : tile
