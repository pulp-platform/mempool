// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

import mempool_pkg::*;

module mempool_tile #(
    parameter int unsigned NumCoresPerTile  = 1                                             ,
    parameter int unsigned NumBanksPerTile  = 1                                             ,
    parameter int unsigned NumTiles         = 1                                             ,
    parameter int unsigned NumBanks         = 1                                             ,
    // TCDM
    parameter addr_t TCDMBaseAddr           = 32'b0                                         ,
    parameter int unsigned TCDMSizePerBank  = 1024 /* [B] */                                ,
    // Boot address
    parameter logic [31:0] BootAddr         = 32'h0000_1000                                 ,
    // Instruction cache
    parameter int unsigned ICacheSizeByte   = 1024 * NumCoresPerTile                        , // Total Size of instruction cache in bytes
    parameter int unsigned ICacheSets       = NumCoresPerTile                               ,
    parameter int unsigned ICacheLineWidth  = NumCoresPerTile * 32                          ,
    // AXI
    parameter type axi_aw_t                 = logic                                         ,
    parameter type axi_w_t                  = logic                                         ,
    parameter type axi_b_t                  = logic                                         ,
    parameter type axi_ar_t                 = logic                                         ,
    parameter type axi_r_t                  = logic                                         ,
    parameter type axi_req_t                = logic                                         ,
    parameter type axi_resp_t               = logic                                         ,
    // Dependent parameters. DO NOT CHANGE.
    parameter int unsigned NumCores         = NumCoresPerTile * NumTiles                    ,
    parameter int unsigned TCDMAddrMemWidth = $clog2(TCDMSizePerBank / mempool_pkg::BeWidth),
    parameter type core_id_t                = logic [$clog2(NumCores)-1:0]                  ,
    parameter type tcdm_addr_t              = logic [TCDMAddrMemWidth-1:0]                  ,
    parameter type tile_addr_t              = logic [TCDMAddrMemWidth + $clog2(NumBanksPerTile)-1:0]
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
    output strb_t      [NumCoresPerTile-1:0] tcdm_master_be_o,
    input  logic       [NumCoresPerTile-1:0] tcdm_master_gnt_i,
    input  logic       [NumCoresPerTile-1:0] tcdm_master_vld_i,
    input  data_t      [NumCoresPerTile-1:0] tcdm_master_rdata_i,
    // TCDM banks interface
    input  logic       [NumCoresPerTile-1:0] mem_req_i,
    input  core_id_t   [NumCoresPerTile-1:0] mem_core_addr_i,
    output logic       [NumCoresPerTile-1:0] mem_gnt_o,
    input  tile_addr_t [NumCoresPerTile-1:0] mem_addr_i,
    input  logic       [NumCoresPerTile-1:0] mem_wen_i,
    input  data_t      [NumCoresPerTile-1:0] mem_wdata_i,
    input  strb_t      [NumCoresPerTile-1:0] mem_be_i,
    output logic       [NumCoresPerTile-1:0] mem_vld_o,
    output core_id_t   [NumCoresPerTile-1:0] mem_core_addr_o,
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

  /*****************
   *  Definitions  *
   *****************/

  import snitch_pkg::dreq_t ;
  import snitch_pkg::dresp_t;

  // TCDM Memory Region
  localparam addr_t TCDMSize    = NumBanks * TCDMSizePerBank;
  localparam addr_t TCDMMask    = ~(TCDMSize - 1);
  localparam addr_t TCDMEndAddr = TCDMBaseAddr + TCDMSize;

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
  strb_t [NumCoresPerTile-1:0] data_qstrb;
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
      .BootAddr (BootAddr)
    ) riscv_core (
      .clk_i         (clk_i         ),
      .rst_i         (!rst_ni       ),
      .hart_id_i     (hart_id       ),
      // IMEM Port
      .inst_addr_o   (inst_addr[c]  ),
      .inst_data_i   (inst_data[c]  ),
      .inst_valid_o  (inst_valid[c] ),
      .inst_ready_i  (inst_ready[c] ),
      // Data Ports
      .data_qaddr_o  (data_qaddr[c] ),
      .data_qwrite_o (data_qwrite[c]),
      .data_qamo_o   (data_qamo[c]  ),
      .data_qdata_o  (data_qdata[c] ),
      .data_qstrb_o  (data_qstrb[c] ),
      .data_qvalid_o (data_qvalid[c]),
      .data_qready_i (data_qready[c]),
      .data_pdata_i  (data_pdata[c] ),
      .data_perror_i (data_perror[c]),
      .data_pvalid_i (data_pvalid[c]),
      .data_pready_o (data_pready[c]),
      .wake_up_sync_i('0            ),
      // Core Events
      .core_events_o (/* Unused */  )
    );
  end

  /***********************
   *  Instruction Cache  *
   ***********************/

  snitch_icache #(
    .NR_FETCH_PORTS    (NumCoresPerTile                                         ),
    /// Cache Line Width
    .L0_LINE_COUNT     (4                                                       ),
    .LINE_WIDTH        (ICacheLineWidth                                         ),
    .LINE_COUNT        (ICacheSizeByte / (NumCoresPerTile * NumCoresPerTile * 4)),
    .SET_COUNT         (ICacheSets                                              ),
    .FETCH_AW          (AddrWidth                                               ),
    .FETCH_DW          (DataWidth                                               ),
    .FILL_AW           (AddrWidth                                               ),
    .FILL_DW           (ICacheLineWidth                                         ),
    .EARLY_ENABLED     (1                                                       ),
    /// Make the early cache latch-based. This reduces latency at the cost of
    /// increased combinatorial path lengths and the hassle of having latches in
    /// the design.
    .EARLY_LATCH       (0                                                       ),
    /// Make the early cache serve responses combinatorially if possible. Set
    /// this to 0 to cut combinatorial paths into the fetch interface.
    .EARLY_FALLTHROUGH (0                                                       )
  ) i_snitch_icache (
    .clk_i           (clk_i          ),
    .rst_ni          (rst_ni         ),
    .inst_addr_i     (inst_addr      ),
    .inst_data_o     (inst_data      ),
    .inst_valid_i    (inst_valid     ),
    .inst_ready_o    (inst_ready     ),
    .inst_error_o    (/* Unused */   ),
    .refill_qaddr_o  (refill_qaddr_o ),
    .refill_qlen_o   (refill_qlen_o  ),
    .refill_qvalid_o (refill_qvalid_o),
    .refill_qready_i (refill_qready_i),
    .refill_pdata_i  (refill_pdata_i ),
    .refill_perror_i (refill_perror_i),
    .refill_pvalid_i (refill_pvalid_i),
    .refill_plast_i  (refill_plast_i ),
    .refill_pready_o (refill_pready_o)
  );

  /***********************
   *  TCDM Memory Banks  *
   ***********************/

  // Memory interfaces
  logic       [NumBanksPerTile-1:0] tile_mem_req;
  tcdm_addr_t [NumBanksPerTile-1:0] tile_mem_addr;
  logic       [NumBanksPerTile-1:0] tile_mem_wen;
  data_t      [NumBanksPerTile-1:0] tile_mem_wdata;
  strb_t      [NumBanksPerTile-1:0] tile_mem_be;
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
  strb_t [NumCoresPerTile-1:0] local_xbar_be;

  addr_t [NumCoresPerTile-1:0] mem_addr;
  for (genvar c = 0; c < NumCoresPerTile; c++) begin: gen_mem_addr
    assign mem_addr[c] = {mem_addr_i[c], {ByteOffset{1'b0}}};
  end

  tcdm_interconnect #(
    .NumIn       (2*NumCoresPerTile         ),
    .NumOut      (NumBanksPerTile           ),
    .AddrWidth   (AddrWidth                 ),
    .AddrMemWidth(TCDMAddrMemWidth          ),
    .RespLat     (1                         ),
    .WriteRespOn (1'b0                      ),
    .Topology    (tcdm_interconnect_pkg::LIC)
  ) local_xbar (
    .clk_i  (clk_i                          ),
    .rst_ni (rst_ni                         ),
    .req_i  ({local_xbar_req, mem_req_i}    ),
    .add_i  ({local_xbar_addr, mem_addr}    ),
    .wen_i  ({local_xbar_wen, mem_wen_i}    ),
    .wdata_i({local_xbar_wdata, mem_wdata_i}),
    .be_i   ({local_xbar_be, mem_be_i}      ),
    .gnt_o  ({local_xbar_gnt, mem_gnt_o}    ),
    .vld_o  ({local_xbar_vld, mem_vld_o}    ),
    .rdata_o({local_xbar_rdata, mem_rdata_o}),
    .req_o  (tile_mem_req                   ),
    .gnt_i  (tile_mem_req                   ), // Memories always grant the requests
    .add_o  (tile_mem_addr                  ),
    .wen_o  (tile_mem_wen                   ),
    .wdata_o(tile_mem_wdata                 ),
    .be_o   (tile_mem_be                    ),
    .rdata_i(tile_mem_rdata                 )
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      mem_core_addr_o <= '0;
    end else begin
      mem_core_addr_o <= mem_core_addr_i;
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
  strb_t [NumCoresPerTile-1:0] tcdm_master_be;
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
    assign local_xbar_addr[c] = addr_t'({local_xbar_addr_int[AddrWidth-1:ByteOffset+$clog2(NumBanksPerTile)], local_xbar_addr_int[0 +: ByteOffset + $clog2(NumBanksPerTile)]});

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
      .clk_i  (clk_i                                                                                     ),
      .rst_ni (rst_ni                                                                                    ),
      .data_i ({tcdm_master_addr_int, tcdm_master_wen[c], tcdm_master_wdata[c], tcdm_master_be[c] }      ),
      .valid_i(tcdm_master_req[c]                                                                        ),
      .ready_o(tcdm_master_gnt[c]                                                                        ),
      .data_o ({tcdm_master_addr_o[c], tcdm_master_wen_o[c], tcdm_master_wdata_o[c], tcdm_master_be_o[c]}),
      .valid_o(tcdm_master_req_o[c]                                                                      ),
      .ready_i(tcdm_master_gnt_i[c]                                                                      )
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
  axi_req_t  axi_mst_req;
  axi_resp_t axi_mst_resp;

  snitch_axi_adapter #(
    .axi_mst_req_t  (axi_req_t ),
    .axi_mst_resp_t (axi_resp_t)
  ) i_snitch_core_axi_adapter (
    .clk_i        (clk_i           ),
    .rst_ni       (rst_ni          ),
    .slv_qaddr_i  (soc_req_o.addr  ),
    .slv_qwrite_i (soc_req_o.write ),
    .slv_qamo_i   (soc_req_o.amo   ),
    .slv_qdata_i  (soc_req_o.data  ),
    .slv_qstrb_i  (soc_req_o.strb  ),
    .slv_qrlen_i  ('0              ),
    .slv_qvalid_i (soc_qvalid      ),
    .slv_qready_o (soc_qready      ),
    .slv_pdata_o  (soc_resp_i.data ),
    .slv_perror_o (soc_resp_i.error),
    .slv_plast_o  (/* Unused */    ),
    .slv_pvalid_o (soc_pvalid      ),
    .slv_pready_i (soc_pready      ),
    .axi_req_o    (axi_mst_req     ),
    .axi_resp_i   (axi_mst_resp    )
  );

  axi_cut #(
    .aw_chan_t(axi_aw_t  ),
    .w_chan_t (axi_w_t   ),
    .b_chan_t (axi_b_t   ),
    .ar_chan_t(axi_ar_t  ),
    .r_chan_t (axi_r_t   ),
    .req_t    (axi_req_t ),
    .resp_t   (axi_resp_t)
  ) axi_mst_slice (
    .clk_i     (clk_i         ),
    .rst_ni    (rst_ni        ),
    .slv_req_i (axi_mst_req   ),
    .slv_resp_o(axi_mst_resp  ),
    .mst_req_o (axi_mst_req_o ),
    .mst_resp_i(axi_mst_resp_i)
  );

  /******************
   *   Assertions   *
   ******************/

  // Check invariants.
  if (BootAddr[1:0] != 2'b00)
    $fatal(1, "[mempool_tile] Boot address should be aligned in a 4-byte boundary.");

  if (NumCoresPerTile != 2**$clog2(NumCoresPerTile))
    $fatal(1, "[mempool_tile] The number of cores per tile must be a power of two.");

  if (NumCores != 2**$clog2(NumCores))
    $fatal(1, "[mempool_tile] The number of cores must be a power of two.");

endmodule : mempool_tile
