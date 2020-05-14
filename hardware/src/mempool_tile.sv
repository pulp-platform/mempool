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
    parameter int unsigned ICacheLineWidth  = 64                                            ,
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
    parameter int unsigned TileAddrWidth    = TCDMAddrMemWidth + $clog2(NumBanksPerTile)    ,
    localparam LocalXbarAddrWidth           = $clog2(2*NumCoresPerTile)                     ,
    parameter type tile_id_t                = logic [$clog2(NumTiles)-1:0]                  ,
    parameter type core_id_t                = logic [$clog2(NumCores)-1:0]                  ,
    parameter type tcdm_addr_t              = logic [TCDMAddrMemWidth-1:0]                  ,
    parameter type tcdm_payload_t           = logic [DataWidth-1:0]                         ,
    parameter type tile_addr_t              = logic [TileAddrWidth-1:0]                     ,
    parameter type local_xbar_addr_t        = logic [LocalXbarAddrWidth-1:0]
  ) (
    // Clock and reset
    input  logic                                 clk_i,
    input  logic                                 rst_ni,
    // Scan chain
    input  logic                                 scan_enable_i,
    input  logic                                 scan_data_i,
    output logic                                 scan_data_o,
    // Tile ID
    input  logic          [$clog2(NumTiles)-1:0] tile_id_i,
    // Core data interface
    output logic          [NumCoresPerTile-1:0]  tcdm_master_req_valid_o,
    input  logic          [NumCoresPerTile-1:0]  tcdm_master_req_ready_i,
    output addr_t         [NumCoresPerTile-1:0]  tcdm_master_req_tgt_addr_o,
    output logic          [NumCoresPerTile-1:0]  tcdm_master_req_wen_o,
    output tcdm_payload_t [NumCoresPerTile-1:0]  tcdm_master_req_wdata_o,
    output strb_t         [NumCoresPerTile-1:0]  tcdm_master_req_be_o,
    input  logic          [NumCoresPerTile-1:0]  tcdm_master_resp_valid_i,
    input  tcdm_payload_t [NumCoresPerTile-1:0]  tcdm_master_resp_rdata_i,
    // TCDM banks interface
    input  logic          [NumCoresPerTile-1:0]  tcdm_slave_req_valid_i,
    output logic          [NumCoresPerTile-1:0]  tcdm_slave_req_ready_o,
    input  tile_id_t      [NumCoresPerTile-1:0]  tcdm_slave_req_ini_addr_i,
    input  tile_addr_t    [NumCoresPerTile-1:0]  tcdm_slave_req_tgt_addr_i,
    input  logic          [NumCoresPerTile-1:0]  tcdm_slave_req_wen_i,
    input  tcdm_payload_t [NumCoresPerTile-1:0]  tcdm_slave_req_wdata_i,
    input  strb_t         [NumCoresPerTile-1:0]  tcdm_slave_req_be_i,
    output logic          [NumCoresPerTile-1:0]  tcdm_slave_resp_valid_o,
    input  logic          [NumCoresPerTile-1:0]  tcdm_slave_resp_ready_i,
    output tile_id_t      [NumCoresPerTile-1:0]  tcdm_slave_resp_ini_addr_o,
    output tcdm_payload_t [NumCoresPerTile-1:0]  tcdm_slave_resp_rdata_o,
    // AXI Interface
    output axi_req_t                             axi_mst_req_o ,
    input  axi_resp_t                            axi_mst_resp_i,
    // Instruction interface
    output addr_t                                refill_qaddr_o,
    output logic          [7:0]                  refill_qlen_o,             // AXI signal
    output logic                                 refill_qvalid_o,
    input  logic                                 refill_qready_i,
    input  logic          [ICacheLineWidth-1:0]  refill_pdata_i,
    input  logic                                 refill_perror_i,
    input  logic                                 refill_pvalid_i,
    input  logic                                 refill_plast_i,
    output logic                                 refill_pready_o
  );

  /****************
   *   Includes   *
   ****************/

  `include "common_cells/registers.svh"

  /*****************
   *  Definitions  *
   *****************/

  import snitch_pkg::dreq_t ;
  import snitch_pkg::dresp_t;

  // TCDM Memory Region
  localparam addr_t TCDMSize = NumBanks * TCDMSizePerBank;
  localparam addr_t TCDMMask = ~(TCDMSize - 1);

  // Local crossbar payload
  typedef struct packed {
    reorder_id_t id   ;
    data_t data       ;
    core_id_t ini_addr;
  } local_xbar_payload_t;

  /***********
   *  Cores  *
   ***********/

  // Instruction interfaces
  addr_t [NumCoresPerTile-1:0] snitch_inst_addr;
  data_t [NumCoresPerTile-1:0] snitch_inst_data;
  logic  [NumCoresPerTile-1:0] snitch_inst_valid;
  logic  [NumCoresPerTile-1:0] snitch_inst_ready;

  // Data interfaces
  addr_t [NumCoresPerTile-1:0] snitch_data_qaddr;
  logic  [NumCoresPerTile-1:0] snitch_data_qwrite;
  amo_t  [NumCoresPerTile-1:0] snitch_data_qamo;
  data_t [NumCoresPerTile-1:0] snitch_data_qdata;
  strb_t [NumCoresPerTile-1:0] snitch_data_qstrb;
  logic  [NumCoresPerTile-1:0] snitch_data_qvalid;
  logic  [NumCoresPerTile-1:0] snitch_data_qready;
  data_t [NumCoresPerTile-1:0] snitch_data_pdata;
  logic  [NumCoresPerTile-1:0] snitch_data_perror;
  logic  [NumCoresPerTile-1:0] snitch_data_pvalid;
  logic  [NumCoresPerTile-1:0] snitch_data_pready;

  for (genvar c = 0; c < unsigned'(NumCoresPerTile); c++) begin: gen_cores
    logic [31:0] hart_id;
    assign hart_id = {unsigned'(tile_id_i), c[$clog2(NumCoresPerTile)-1:0]};

    mempool_cc #(
      .BootAddr (BootAddr)
    ) riscv_core (
      .clk_i         (clk_i                ),
      .rst_i         (!rst_ni              ),
      .hart_id_i     (hart_id              ),
      // IMEM Port
      .inst_addr_o   (snitch_inst_addr[c]  ),
      .inst_data_i   (snitch_inst_data[c]  ),
      .inst_valid_o  (snitch_inst_valid[c] ),
      .inst_ready_i  (snitch_inst_ready[c] ),
      // Data Ports
      .data_qaddr_o  (snitch_data_qaddr[c] ),
      .data_qwrite_o (snitch_data_qwrite[c]),
      .data_qamo_o   (snitch_data_qamo[c]  ),
      .data_qdata_o  (snitch_data_qdata[c] ),
      .data_qstrb_o  (snitch_data_qstrb[c] ),
      .data_qvalid_o (snitch_data_qvalid[c]),
      .data_qready_i (snitch_data_qready[c]),
      .data_pdata_i  (snitch_data_pdata[c] ),
      .data_perror_i (snitch_data_perror[c]),
      .data_pvalid_i (snitch_data_pvalid[c]),
      .data_pready_o (snitch_data_pready[c]),
      .wake_up_sync_i('0                   ),
      // Core Events
      .core_events_o (/* Unused */         )
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
    .clk_i           (clk_i            ),
    .rst_ni          (rst_ni           ),
    .inst_addr_i     (snitch_inst_addr ),
    .inst_data_o     (snitch_inst_data ),
    .inst_valid_i    (snitch_inst_valid),
    .inst_ready_o    (snitch_inst_ready),
    .inst_error_o    (/* Unused */     ),
    .refill_qaddr_o  (refill_qaddr_o   ),
    .refill_qlen_o   (refill_qlen_o    ),
    .refill_qvalid_o (refill_qvalid_o  ),
    .refill_qready_i (refill_qready_i  ),
    .refill_pdata_i  (refill_pdata_i   ),
    .refill_perror_i (refill_perror_i  ),
    .refill_pvalid_i (refill_pvalid_i  ),
    .refill_plast_i  (refill_plast_i   ),
    .refill_pready_o (refill_pready_o  )
  );

  /***********************
   *  TCDM Memory Banks  *
   ***********************/

  // Memory interfaces
  logic                [NumBanksPerTile-1:0] bank_req_valid;
  logic                [NumBanksPerTile-1:0] bank_req_ready;
  tcdm_addr_t          [NumBanksPerTile-1:0] bank_req_tgt_addr;
  local_xbar_addr_t    [NumBanksPerTile-1:0] bank_req_ini_addr;
  logic                [NumBanksPerTile-1:0] bank_req_wen;
  local_xbar_payload_t [NumBanksPerTile-1:0] bank_req_payload;
  strb_t               [NumBanksPerTile-1:0] bank_req_be;
  logic                [NumBanksPerTile-1:0] bank_resp_valid;
  logic                [NumBanksPerTile-1:0] bank_resp_ready;
  local_xbar_payload_t [NumBanksPerTile-1:0] bank_resp_payload;
  local_xbar_addr_t    [NumBanksPerTile-1:0] bank_resp_ini_addr;

  for (genvar b = 0; b < unsigned'(NumBanksPerTile); b++) begin: gen_banks
    // Expand byte-enable into bit-enable
    data_t bank_req_be_expanded;
    for (genvar be_byte = 0; be_byte < unsigned'(BeWidth); be_byte++) begin: gen_mem_be
      assign bank_req_be_expanded[8*be_byte+:8] = {8{bank_req_be[b][be_byte]}};
    end

    // Banks are ready if they are idle, or if their answer was received
    assign bank_req_ready[b] = !bank_resp_valid[b] || (bank_resp_valid[b] && bank_resp_ready[b]);

    // Metadata
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        bank_resp_valid[b]            <= 1'b0;
        bank_resp_ini_addr[b]         <= '0  ;
        bank_resp_payload[b].ini_addr <= '0  ;
        bank_resp_payload[b].id       <= '0  ;
      end else begin
        // One cycle latency
        if (bank_req_ready[b]) begin
          bank_resp_payload[b].ini_addr <= bank_req_payload[b].ini_addr         ;
          bank_resp_payload[b].id       <= bank_req_payload[b].id               ;
          bank_resp_valid[b]            <= bank_req_valid[b] && !bank_req_wen[b];
          bank_resp_ini_addr[b]         <= bank_req_ini_addr[b]                 ;
        end
      end
    end

    // Bank
    sram #(
      .DATA_WIDTH(DataWidth          ),
      .NUM_WORDS (2**TCDMAddrMemWidth)
    ) mem_bank (
      .clk_i  (clk_i                                ),
      .req_i  (bank_req_valid[b] & bank_req_ready[b]),
      .we_i   (bank_req_wen[b]                      ),
      .addr_i (bank_req_tgt_addr[b]                 ),
      .wdata_i(bank_req_payload[b].data             ),
      .be_i   (bank_req_be_expanded                 ),
      .rdata_o(bank_resp_payload[b].data            )
    );
  end

  /***************
   *  Registers  *
   ***************/

  // These are required to break dependencies between request and response, establishing a correct valid/ready handshake.
  logic          [NumCoresPerTile-1:0] postreg_tcdm_slave_req_valid;
  logic          [NumCoresPerTile-1:0] postreg_tcdm_slave_req_ready;
  tile_addr_t    [NumCoresPerTile-1:0] postreg_tcdm_slave_req_tgt_addr;
  logic          [NumCoresPerTile-1:0] postreg_tcdm_slave_req_wen;
  tcdm_payload_t [NumCoresPerTile-1:0] postreg_tcdm_slave_req_wdata;
  tile_id_t      [NumCoresPerTile-1:0] postreg_tcdm_slave_req_ini_addr;
  strb_t         [NumCoresPerTile-1:0] postreg_tcdm_slave_req_be;
  logic          [NumCoresPerTile-1:0] prereg_tcdm_slave_resp_valid;
  logic          [NumCoresPerTile-1:0] prereg_tcdm_slave_resp_ready;
  tcdm_payload_t [NumCoresPerTile-1:0] prereg_tcdm_slave_resp_rdata;
  tile_id_t      [NumCoresPerTile-1:0] prereg_tcdm_slave_resp_ini_addr;

  // Break paths between request and response with registers
  for (genvar c = 0; c < unsigned'(NumCoresPerTile); c++) begin: gen_tcdm_registers
    fall_through_register #(
      .T(logic[TileAddrWidth + BeWidth + 1 + $bits(tcdm_payload_t) + $clog2(NumTiles) - 1:0])
    ) i_tcdm_slave_req_register (
      .clk_i     (clk_i                                                                                                                                                                 ),
      .rst_ni    (rst_ni                                                                                                                                                                ),
      .clr_i     (1'b0                                                                                                                                                                  ),
      .testmode_i(1'b0                                                                                                                                                                  ),
      .data_i    ({tcdm_slave_req_tgt_addr_i[c], tcdm_slave_req_be_i[c], tcdm_slave_req_wen_i[c], tcdm_slave_req_wdata_i[c], tcdm_slave_req_ini_addr_i[c]}                              ),
      .valid_i   (tcdm_slave_req_valid_i[c]                                                                                                                                             ),
      .ready_o   (tcdm_slave_req_ready_o[c]                                                                                                                                             ),
      .data_o    ({postreg_tcdm_slave_req_tgt_addr[c], postreg_tcdm_slave_req_be[c], postreg_tcdm_slave_req_wen[c], postreg_tcdm_slave_req_wdata[c], postreg_tcdm_slave_req_ini_addr[c]}),
      .valid_o   (postreg_tcdm_slave_req_valid[c]                                                                                                                                       ),
      .ready_i   (postreg_tcdm_slave_req_ready[c]                                                                                                                                       )
    );

    fall_through_register #(
      .T(logic[$bits(tcdm_payload_t) + $clog2(NumTiles) - 1:0])
    ) i_tcdm_slave_resp_register (
      .clk_i     (clk_i                                                                ),
      .rst_ni    (rst_ni                                                               ),
      .clr_i     (1'b0                                                                 ),
      .testmode_i(1'b0                                                                 ),
      .data_i    ({prereg_tcdm_slave_resp_rdata[c], prereg_tcdm_slave_resp_ini_addr[c]}),
      .valid_i   (prereg_tcdm_slave_resp_valid[c]                                      ),
      .ready_o   (prereg_tcdm_slave_resp_ready[c]                                      ),
      .data_o    ({tcdm_slave_resp_rdata_o[c], tcdm_slave_resp_ini_addr_o[c]}          ),
      .valid_o   (tcdm_slave_resp_valid_o[c]                                           ),
      .ready_i   (tcdm_slave_resp_ready_i[c]                                           )
    );
  end: gen_tcdm_registers


  /*************************
   *   Internal Crossbar   *
   *************************/

  // TCDM request
  logic                [NumCoresPerTile-1:0] local_xbar_req_valid;
  logic                [NumCoresPerTile-1:0] local_xbar_req_ready;
  addr_t               [NumCoresPerTile-1:0] local_xbar_req_addr;
  logic                [NumCoresPerTile-1:0] local_xbar_req_wen;
  local_xbar_payload_t [NumCoresPerTile-1:0] local_xbar_req_payload;
  strb_t               [NumCoresPerTile-1:0] local_xbar_req_be;
  logic                [NumCoresPerTile-1:0] local_xbar_resp_valid;
  logic                [NumCoresPerTile-1:0] local_xbar_resp_ready;
  local_xbar_payload_t [NumCoresPerTile-1:0] local_xbar_resp_payload;
  local_xbar_payload_t [NumCoresPerTile-1:0] postreg_tcdm_slave_req_payload;
  local_xbar_payload_t [NumCoresPerTile-1:0] prereg_tcdm_slave_resp_payload;

  addr_t [NumCoresPerTile-1:0] tcdm_slave_req_tgt_addr_int;
  for (genvar c = 0; c < NumCoresPerTile; c++) begin: gen_mem_addr
    assign tcdm_slave_req_tgt_addr_int[c] = {postreg_tcdm_slave_req_tgt_addr[c], {ByteOffset{1'b0}}};
  end

  for (genvar c = 0; c < unsigned'(NumCoresPerTile); c++) begin: gen_tcdm_slave_payload
    assign postreg_tcdm_slave_req_payload[c] = '{
      data    : postreg_tcdm_slave_req_wdata[c].data,
      id      : postreg_tcdm_slave_req_wdata[c].id  ,
      ini_addr: {postreg_tcdm_slave_req_ini_addr[c], c[$clog2(NumCoresPerTile)-1:0]}
    };
    assign prereg_tcdm_slave_resp_rdata[c].data = prereg_tcdm_slave_resp_payload[c].data                               ;
    assign prereg_tcdm_slave_resp_rdata[c].id   = prereg_tcdm_slave_resp_payload[c].id                                 ;
    assign prereg_tcdm_slave_resp_ini_addr[c]   = prereg_tcdm_slave_resp_payload[c].ini_addr >> $clog2(NumCoresPerTile);
  end: gen_tcdm_slave_payload

  // Local crossbar
  variable_latency_interconnect #(
    .NumIn       (2*NumCoresPerTile          ),
    .NumOut      (NumBanksPerTile            ),
    .AddrWidth   (AddrWidth                  ),
    .AddrMemWidth(TCDMAddrMemWidth           ),
    .Topology    (tcdm_interconnect_pkg::LIC ),
    .DataWidth   ($bits(local_xbar_payload_t)),
    .BeWidth     (DataWidth / 8              ),
    .ByteOffWidth(ByteOffset                 ),
    .AxiVldRdy   (1'b1                       )
  ) i_local_xbar (
    .clk_i          (clk_i                                                    ),
    .rst_ni         (rst_ni                                                   ),
    .req_valid_i    ({local_xbar_req_valid, postreg_tcdm_slave_req_valid}     ),
    .req_ready_o    ({local_xbar_req_ready, postreg_tcdm_slave_req_ready}     ),
    .req_tgt_addr_i ({local_xbar_req_addr, tcdm_slave_req_tgt_addr_int}       ),
    .req_wen_i      ({local_xbar_req_wen, postreg_tcdm_slave_req_wen}         ),
    .req_be_i       ({local_xbar_req_be, postreg_tcdm_slave_req_be}           ),
    .req_wdata_i    ({local_xbar_req_payload, postreg_tcdm_slave_req_payload} ),
    .resp_valid_o   ({local_xbar_resp_valid, prereg_tcdm_slave_resp_valid}    ),
    .resp_rdata_o   ({local_xbar_resp_payload, prereg_tcdm_slave_resp_payload}),
    .resp_ready_i   ({local_xbar_resp_ready, prereg_tcdm_slave_resp_ready}    ),
    .req_valid_o    (bank_req_valid                                           ),
    .req_ready_i    (bank_req_ready                                           ),
    .req_tgt_addr_o (bank_req_tgt_addr                                        ),
    .req_be_o       (bank_req_be                                              ),
    .req_wen_o      (bank_req_wen                                             ),
    .req_wdata_o    (bank_req_payload                                         ),
    .req_ini_addr_o (bank_req_ini_addr                                        ),
    .resp_valid_i   (bank_resp_valid                                          ),
    .resp_ini_addr_i(bank_resp_ini_addr                                       ),
    .resp_ready_o   (bank_resp_ready                                          ),
    .resp_rdata_i   (bank_resp_payload                                        )
  );

  /*******************
   *   Core De/mux   *
   *******************/

  // SoC requests
  dreq_t  [NumCoresPerTile-1:0] soc_data_q ;
  logic   [NumCoresPerTile-1:0] soc_data_qvalid;
  logic   [NumCoresPerTile-1:0] soc_data_qready;
  dresp_t [NumCoresPerTile-1:0] soc_data_p ;
  logic   [NumCoresPerTile-1:0] soc_data_pvalid;
  logic   [NumCoresPerTile-1:0] soc_data_pready;

  // Unused ready signals for the remote TCDM response
  logic [NumCoresPerTile-1:0] tcdm_master_resp_ready;

  // Address map
  typedef enum int unsigned {
    TCDM_EXTERNAL = 0, TCDM_LOCAL, SOC
  } addr_map_slave_t;

  address_map_t [2:0] mask_map;
  assign mask_map = '{
        // Lowest priority: send request through the SoC port
        '{slave_idx: SOC,
          mask     : '0 ,
          value    : '0
        },
        // Send request through the external TCDM port
        '{slave_idx: TCDM_EXTERNAL,
          mask     : TCDMMask     ,
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
    assign local_xbar_req_addr[c] =
     addr_t'({local_xbar_addr_int[ByteOffset + $clog2(NumBanksPerTile) + $clog2(NumTiles) +: TCDMAddrMemWidth], // Bank address
             local_xbar_addr_int[ByteOffset +: $clog2(NumBanksPerTile)]                                       , // Bank
             local_xbar_addr_int[0 +: ByteOffset]});

    addr_t prescramble_tcdm_req_tgt_addr;
    // Switch tile and bank indexes for correct upper level routing
    assign tcdm_master_req_tgt_addr_o[c] =
     addr_t'({prescramble_tcdm_req_tgt_addr[ByteOffset + $clog2(NumBanksPerTile) + $clog2(NumTiles) +: TCDMAddrMemWidth], // Bank address
       prescramble_tcdm_req_tgt_addr[ByteOffset +: $clog2(NumBanksPerTile)]                                             , // Bank
       prescramble_tcdm_req_tgt_addr[ByteOffset + $clog2(NumBanksPerTile) +: $clog2(NumTiles)]                          , // Tile
       prescramble_tcdm_req_tgt_addr[0 +: ByteOffset]});

    // Initialize request ini_addr
    assign local_xbar_req_payload[c].ini_addr = '0;
    assign soc_data_q[c].id                   = '0;

    tcdm_shim #(
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth),
      .NrTCDM   (2        ),
      .NrSoC    (1        ),
      .NumRules (3        )
    ) i_tcdm_shim (
      .clk_i              (clk_i                                                              ),
      .rst_ni             (rst_ni                                                             ),
      // to TCDM --> FF Connection to outside of tile
      .tcdm_req_valid_o   ({local_xbar_req_valid[c], tcdm_master_req_valid_o[c]}              ),
      .tcdm_req_tgt_addr_o({local_xbar_addr_int, prescramble_tcdm_req_tgt_addr}               ),
      .tcdm_req_wen_o     ({local_xbar_req_wen[c], tcdm_master_req_wen_o[c]}                  ),
      .tcdm_req_wdata_o   ({local_xbar_req_payload[c].data, tcdm_master_req_wdata_o[c].data}  ),
      .tcdm_req_id_o      ({local_xbar_req_payload[c].id, tcdm_master_req_wdata_o[c].id}      ),
      .tcdm_req_be_o      ({local_xbar_req_be[c], tcdm_master_req_be_o[c]}                    ),
      .tcdm_req_ready_i   ({local_xbar_req_ready[c], tcdm_master_req_ready_i[c]}              ),
      .tcdm_resp_valid_i  ({local_xbar_resp_valid[c], tcdm_master_resp_valid_i[c]}            ),
      .tcdm_resp_ready_o  ({local_xbar_resp_ready[c], tcdm_master_resp_ready[c]}              ),
      .tcdm_resp_rdata_i  ({local_xbar_resp_payload[c].data, tcdm_master_resp_rdata_i[c].data}),
      .tcdm_resp_id_i     ({local_xbar_resp_payload[c].id, tcdm_master_resp_rdata_i[c].id}    ),
      // to SoC
      .soc_qaddr_o        (soc_data_q[c].addr                                                 ),
      .soc_qwrite_o       (soc_data_q[c].write                                                ),
      .soc_qamo_o         (soc_data_q[c].amo                                                  ),
      .soc_qdata_o        (soc_data_q[c].data                                                 ),
      .soc_qstrb_o        (soc_data_q[c].strb                                                 ),
      .soc_qvalid_o       (soc_data_qvalid[c]                                                 ),
      .soc_qready_i       (soc_data_qready[c]                                                 ),
      .soc_pdata_i        (soc_data_p[c].data                                                 ),
      .soc_perror_i       (soc_data_p[c].error                                                ),
      .soc_pvalid_i       (soc_data_pvalid[c]                                                 ),
      .soc_pready_o       (soc_data_pready[c]                                                 ),
      // from core
      .data_qaddr_i       (snitch_data_qaddr[c]                                               ),
      .data_qwrite_i      (snitch_data_qwrite[c]                                              ),
      .data_qamo_i        (snitch_data_qamo[c]                                                ),
      .data_qdata_i       (snitch_data_qdata[c]                                               ),
      .data_qstrb_i       (snitch_data_qstrb[c]                                               ),
      .data_qvalid_i      (snitch_data_qvalid[c]                                              ),
      .data_qready_o      (snitch_data_qready[c]                                              ),
      .data_pdata_o       (snitch_data_pdata[c]                                               ),
      .data_perror_o      (snitch_data_perror[c]                                              ),
      .data_pvalid_o      (snitch_data_pvalid[c]                                              ),
      .data_pready_i      (snitch_data_pready[c]                                              ),
      .address_map_i      (mask_map                                                           )
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

  // Tie the response id to zero
  assign soc_resp_i.id = '0;

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
  axi_req_t  axi_mst_req ;
  axi_resp_t axi_mst_resp;

  snitch_axi_adapter #(
    .axi_mst_req_t  (axi_req_t ),
    .axi_mst_resp_t (axi_resp_t)
  ) i_snitch_core_axi_adapter (
    .clk_i       (clk_i           ),
    .rst_ni      (rst_ni          ),
    .slv_qaddr_i (soc_req_o.addr  ),
    .slv_qwrite_i(soc_req_o.write ),
    .slv_qamo_i  (soc_req_o.amo   ),
    .slv_qdata_i (soc_req_o.data  ),
    .slv_qstrb_i (soc_req_o.strb  ),
    .slv_qrlen_i ('0              ),
    .slv_qvalid_i(soc_qvalid      ),
    .slv_qready_o(soc_qready      ),
    .slv_pdata_o (soc_resp_i.data ),
    .slv_perror_o(soc_resp_i.error),
    .slv_plast_o (/* Unused */    ),
    .slv_pvalid_o(soc_pvalid      ),
    .slv_pready_i(soc_pready      ),
    .axi_req_o   (axi_mst_req     ),
    .axi_resp_i  (axi_mst_resp    )
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

  for (genvar c = 0; c < NumCoresPerTile; c++) begin: gen_tcdm_resp_ready_assertion
    `ifndef VERILATOR
    tcdm_resp_ready_assertion : assert property (
        @(posedge clk_i) disable iff (!rst_ni) (tcdm_master_resp_valid_i[c] |-> tcdm_master_resp_ready[c]))
    else $fatal (1, "[mempool_tile] Remote TCDM response was not accepted.");
    `endif
  end

endmodule : mempool_tile
