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
    parameter int unsigned NumBanksPerTile = 1                                                    ,
    parameter int unsigned NumTiles        = 1                                                    ,
    parameter int unsigned NumHives        = 1                                                    ,
    parameter int unsigned NumBanks        = 1                                                    ,
    // TCDM
    parameter addr_t TCDMBaseAddr          = 32'b0                                                ,
    // Boot address
    parameter logic [31:0] BootAddr        = 32'h0000_1000                                        ,
    // Instruction cache
    parameter int unsigned ICacheSizeByte   = 512 * NumCoresPerTile                         , // Total Size of instruction cache in bytes
    parameter int unsigned ICacheSets       = NumCoresPerTile                               , // Number of sets
    parameter int unsigned ICacheLineWidth  = 32 * NumCoresPerTile                          , // Size of each cache line in bits
    // Dependent parameters. DO NOT CHANGE.
    parameter int unsigned NumCores        = NumCoresPerTile * NumTiles                           ,
    parameter int unsigned NumBanksPerHive = NumBanks / NumHives                                  ,
    parameter int unsigned NumTilesPerHive = NumTiles / NumHives                                  ,
    parameter int unsigned TileAddrWidth   = TCDMAddrMemWidth + unsigned'($clog2(NumBanksPerTile)),
    parameter int unsigned TCDMAddrWidth   = TCDMAddrMemWidth + unsigned'($clog2(NumBanksPerHive)),
    parameter type hive_tile_id_t          = logic [$clog2(NumTilesPerHive)-1:0]                  ,
    parameter type tcdm_addr_t             = logic [TCDMAddrWidth-1:0]                            ,
    parameter type tile_addr_t             = logic [TileAddrWidth-1:0]
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
    output logic          [NumHives-1:0]         tcdm_master_req_valid_o,
    input  logic          [NumHives-1:0]         tcdm_master_req_ready_i,
    output tcdm_addr_t    [NumHives-1:0]         tcdm_master_req_tgt_addr_o,
    output logic          [NumHives-1:0]         tcdm_master_req_wen_o,
    output tcdm_payload_t [NumHives-1:0]         tcdm_master_req_wdata_o,
    output strb_t         [NumHives-1:0]         tcdm_master_req_be_o,
    input  logic          [NumHives-1:0]         tcdm_master_resp_valid_i,
    output logic          [NumHives-1:0]         tcdm_master_resp_ready_o,
    input  tcdm_payload_t [NumHives-1:0]         tcdm_master_resp_rdata_i,
    // TCDM banks interface
    input  logic          [NumHives-1:0]         tcdm_slave_req_valid_i ,
    output logic          [NumHives-1:0]         tcdm_slave_req_ready_o ,
    input  hive_tile_id_t [NumHives-1:0]         tcdm_slave_req_ini_addr_i ,
    input  tile_addr_t    [NumHives-1:0]         tcdm_slave_req_tgt_addr_i ,
    input  logic          [NumHives-1:0]         tcdm_slave_req_wen_i ,
    input  tcdm_payload_t [NumHives-1:0]         tcdm_slave_req_wdata_i ,
    input  strb_t         [NumHives-1:0]         tcdm_slave_req_be_i ,
    output logic          [NumHives-1:0]         tcdm_slave_resp_valid_o ,
    input  logic          [NumHives-1:0]         tcdm_slave_resp_ready_i ,
    output hive_tile_id_t [NumHives-1:0]         tcdm_slave_resp_ini_addr_o ,
    output tcdm_payload_t [NumHives-1:0]         tcdm_slave_resp_rdata_o,
    // AXI Interface
    output axi_req_t                             axi_mst_req_o ,
    input  axi_resp_t                            axi_mst_resp_i ,
    // Instruction interface
    output addr_t                                refill_qaddr_o ,
    output logic          [7:0]                  refill_qlen_o ,            // AXI signal
    output logic                                 refill_qvalid_o ,
    input  logic                                 refill_qready_i ,
    input  logic          [ICacheLineWidth-1:0]  refill_pdata_i ,
    input  logic                                 refill_perror_i ,
    input  logic                                 refill_pvalid_i ,
    input  logic                                 refill_plast_i ,
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

  typedef logic [(NumHives == 1 ? 1 : $clog2(NumHives))-1:0] hive_id_t;

  // TCDM Memory Region
  localparam addr_t TCDMSize = NumBanks * TCDMSizePerBank;
  localparam addr_t TCDMMask = ~(TCDMSize - 1);

  // Local crossbar
  localparam LocalSlaveXbarAddrWidth = $clog2(NumCoresPerTile + NumHives);
  typedef logic [LocalSlaveXbarAddrWidth-1:0] local_slave_xbar_addr_t;
  typedef struct packed {
    reorder_id_t reorder_id;
    hive_tile_id_t tile_id ;
    tile_core_id_t core_id ;
    amo_t amo              ;
    data_t data            ;
  } local_slave_xbar_payload_t;

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

  for (genvar c = 0; unsigned'(c) < NumCoresPerTile; c++) begin: gen_cores
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
    .NR_FETCH_PORTS     (NumCoresPerTile                                     ),
    /// Cache Line Width
    .L0_LINE_COUNT      (4                                                   ),
    .LINE_WIDTH         (ICacheLineWidth                                     ),
    .LINE_COUNT         (ICacheSizeByte / (ICacheSets * ICacheLineWidth / 8) ),
    .SET_COUNT          (ICacheSets                                          ),
    .FETCH_AW           (AddrWidth                                           ),
    .FETCH_DW           (DataWidth                                           ),
    .FILL_AW            (AddrWidth                                           ),
    .FILL_DW            (ICacheLineWidth                                     ),
    /// Make the early cache latch-based. This reduces latency at the cost of
    /// increased combinatorial path lengths and the hassle of having latches in
    /// the design.
    .EARLY_LATCH        (0                                                   ),
    .L0_EARLY_TAG_WIDTH (11                                                  ),
    .ISO_CROSSING       (0                                                   )
  ) i_snitch_icache (
    .clk_i                (clk_i                  ),
    .clk_d2_i             (clk_i                  ),
    .rst_ni               (rst_ni                 ),
    .enable_prefetching_i (1'b1                   ),
    .icache_events_o      (                       ),
    .flush_valid_i        (1'b0                   ),
    .flush_ready_o        (                       ),
    .inst_addr_i          (snitch_inst_addr       ),
    .inst_data_o          (snitch_inst_data       ),
    .inst_cacheable_i     ({NumCoresPerTile{1'b1}}),
    .inst_valid_i         (snitch_inst_valid      ),
    .inst_ready_o         (snitch_inst_ready      ),
    .inst_error_o         (/* Unused */           ),
    .refill_qaddr_o       (refill_qaddr_o         ),
    .refill_qlen_o        (refill_qlen_o          ),
    .refill_qvalid_o      (refill_qvalid_o        ),
    .refill_qready_i      (refill_qready_i        ),
    .refill_pdata_i       (refill_pdata_i         ),
    .refill_perror_i      (refill_perror_i        ),
    .refill_pvalid_i      (refill_pvalid_i        ),
    .refill_plast_i       (refill_plast_i         ),
    .refill_pready_o      (refill_pready_o        )
  );

  /******************
   *  Memory Banks  *
   ******************/

  // Bank metadata
  typedef struct packed {
    local_slave_xbar_addr_t ini_addr;
    reorder_id_t reorder_id         ;
    hive_tile_id_t tile_id          ;
    tile_core_id_t core_id          ;
  } bank_metadata_t;

  // Memory interfaces
  logic                      [NumBanksPerTile-1:0] bank_req_valid;
  logic                      [NumBanksPerTile-1:0] bank_req_ready;
  bank_addr_t                [NumBanksPerTile-1:0] bank_req_tgt_addr;
  local_slave_xbar_addr_t    [NumBanksPerTile-1:0] bank_req_ini_addr;
  logic                      [NumBanksPerTile-1:0] bank_req_wen;
  local_slave_xbar_payload_t [NumBanksPerTile-1:0] bank_req_payload;
  strb_t                     [NumBanksPerTile-1:0] bank_req_be;
  logic                      [NumBanksPerTile-1:0] bank_resp_valid;
  logic                      [NumBanksPerTile-1:0] bank_resp_ready;
  local_slave_xbar_payload_t [NumBanksPerTile-1:0] bank_resp_payload;
  local_slave_xbar_addr_t    [NumBanksPerTile-1:0] bank_resp_ini_addr;

  for (genvar b = 0; unsigned'(b) < NumBanksPerTile; b++) begin: gen_banks
    bank_metadata_t meta_in ;
    bank_metadata_t meta_out;
    logic req_valid         ;
    logic req_write         ;
    bank_addr_t req_addr    ;
    data_t req_wdata        ;
    data_t resp_rdata       ;
    data_t req_be           ;

    // Un/Pack metadata
    assign meta_in = '{
      ini_addr  : bank_req_ini_addr[b]          ,
      reorder_id: bank_req_payload[b].reorder_id,
      core_id   : bank_req_payload[b].core_id   ,
      tile_id   : bank_req_payload[b].tile_id
    };
    assign bank_resp_ini_addr[b]           = meta_out.ini_addr  ;
    assign bank_resp_payload[b].reorder_id = meta_out.reorder_id;
    assign bank_resp_payload[b].tile_id    = meta_out.tile_id   ;
    assign bank_resp_payload[b].core_id    = meta_out.core_id   ;
    assign bank_resp_payload[b].amo        = '0                 ; // Don't care

    tcdm_adapter #(
      .AddrWidth  (TCDMAddrMemWidth                 ),
      .DataWidth  (DataWidth                        ),
      .metadata_t (logic[$bits(bank_metadata_t)-1:0]),
      .RegisterAmo(1'b0                             )
    ) i_tcdm_adapter (
      .clk_i       (clk_i                    ),
      .rst_ni      (rst_ni                   ),
      .in_valid_i  (bank_req_valid[b]        ),
      .in_ready_o  (bank_req_ready[b]        ),
      .in_address_i(bank_req_tgt_addr[b]     ),
      .in_amo_i    (bank_req_payload[b].amo  ),
      .in_write_i  (bank_req_wen[b]          ),
      .in_wdata_i  (bank_req_payload[b].data ),
      .in_meta_i   (meta_in                  ),
      .in_be_i     (bank_req_be[b]           ),
      .in_valid_o  (bank_resp_valid[b]       ),
      .in_ready_i  (bank_resp_ready[b]       ),
      .in_rdata_o  (bank_resp_payload[b].data),
      .in_meta_o   (meta_out                 ),
      .out_req_o   (req_valid                ),
      .out_add_o   (req_addr                 ),
      .out_write_o (req_write                ),
      .out_wdata_o (req_wdata                ),
      .out_be_o    (req_be                   ),
      .out_rdata_i (resp_rdata               )
    );

    // Bank
    sram #(
      .DATA_WIDTH(DataWidth          ),
      .NUM_WORDS (2**TCDMAddrMemWidth)
    ) mem_bank (
      .clk_i  (clk_i     ),
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

  // These are required to break dependencies between request and response, establishing a correct valid/ready handshake.
  logic          [NumHives-1:0] postreg_tcdm_slave_req_valid;
  logic          [NumHives-1:0] postreg_tcdm_slave_req_ready;
  tile_addr_t    [NumHives-1:0] postreg_tcdm_slave_req_tgt_addr;
  logic          [NumHives-1:0] postreg_tcdm_slave_req_wen;
  tcdm_payload_t [NumHives-1:0] postreg_tcdm_slave_req_wdata;
  hive_tile_id_t [NumHives-1:0] postreg_tcdm_slave_req_ini_addr;
  strb_t         [NumHives-1:0] postreg_tcdm_slave_req_be;
  logic          [NumHives-1:0] prereg_tcdm_slave_resp_valid;
  logic          [NumHives-1:0] prereg_tcdm_slave_resp_ready;
  tcdm_payload_t [NumHives-1:0] prereg_tcdm_slave_resp_rdata;
  hive_tile_id_t [NumHives-1:0] prereg_tcdm_slave_resp_ini_addr;
  logic          [NumHives-1:0] prereg_tcdm_master_req_valid;
  logic          [NumHives-1:0] prereg_tcdm_master_req_ready;
  tcdm_addr_t    [NumHives-1:0] prereg_tcdm_master_req_tgt_addr;
  logic          [NumHives-1:0] prereg_tcdm_master_req_wen;
  tcdm_payload_t [NumHives-1:0] prereg_tcdm_master_req_wdata;
  strb_t         [NumHives-1:0] prereg_tcdm_master_req_be;
  logic          [NumHives-1:0] postreg_tcdm_master_resp_valid;
  logic          [NumHives-1:0] postreg_tcdm_master_resp_ready;
  tcdm_payload_t [NumHives-1:0] postreg_tcdm_master_resp_rdata;

  // Break paths between request and response with registers
  for (genvar h = 0; unsigned'(h) < NumHives; h++) begin: gen_tcdm_registers
    spill_register #(
      .T(logic[TCDMAddrWidth + BeWidth + unsigned'($bits(tcdm_payload_t)):0])
    ) i_tcdm_master_req_register (
      .clk_i  (clk_i                                                                                                                             ),
      .rst_ni (rst_ni                                                                                                                            ),
      .data_i ({prereg_tcdm_master_req_tgt_addr[h], prereg_tcdm_master_req_be[h], prereg_tcdm_master_req_wen[h], prereg_tcdm_master_req_wdata[h]}),
      .valid_i(prereg_tcdm_master_req_valid[h]                                                                                                   ),
      .ready_o(prereg_tcdm_master_req_ready[h]                                                                                                   ),
      .data_o ({tcdm_master_req_tgt_addr_o[h], tcdm_master_req_be_o[h], tcdm_master_req_wen_o[h], tcdm_master_req_wdata_o[h]}                    ),
      .valid_o(tcdm_master_req_valid_o[h]                                                                                                        ),
      .ready_i(tcdm_master_req_ready_i[h]                                                                                                        )
    );

    fall_through_register #(
      .T(tcdm_payload_t)
    ) i_tcdm_master_resp_register (
      .clk_i     (clk_i                            ),
      .rst_ni    (rst_ni                           ),
      .clr_i     (1'b0                             ),
      .testmode_i(1'b0                             ),
      .data_i    (tcdm_master_resp_rdata_i[h]      ),
      .valid_i   (tcdm_master_resp_valid_i[h]      ),
      .ready_o   (tcdm_master_resp_ready_o[h]      ),
      .data_o    (postreg_tcdm_master_resp_rdata[h]),
      .valid_o   (postreg_tcdm_master_resp_valid[h]),
      .ready_i   (postreg_tcdm_master_resp_ready[h])
    );

    fall_through_register #(
      .T(logic[TileAddrWidth + BeWidth + unsigned'($bits(tcdm_payload_t)) + unsigned'($clog2(NumTilesPerHive)):0])
    ) i_tcdm_slave_req_register (
      .clk_i     (clk_i                                                                                                                                                                 ),
      .rst_ni    (rst_ni                                                                                                                                                                ),
      .clr_i     (1'b0                                                                                                                                                                  ),
      .testmode_i(1'b0                                                                                                                                                                  ),
      .data_i    ({tcdm_slave_req_tgt_addr_i[h], tcdm_slave_req_be_i[h], tcdm_slave_req_wen_i[h], tcdm_slave_req_wdata_i[h], tcdm_slave_req_ini_addr_i[h]}                              ),
      .valid_i   (tcdm_slave_req_valid_i[h]                                                                                                                                             ),
      .ready_o   (tcdm_slave_req_ready_o[h]                                                                                                                                             ),
      .data_o    ({postreg_tcdm_slave_req_tgt_addr[h], postreg_tcdm_slave_req_be[h], postreg_tcdm_slave_req_wen[h], postreg_tcdm_slave_req_wdata[h], postreg_tcdm_slave_req_ini_addr[h]}),
      .valid_o   (postreg_tcdm_slave_req_valid[h]                                                                                                                                       ),
      .ready_i   (postreg_tcdm_slave_req_ready[h]                                                                                                                                       )
    );

    spill_register #(
      .T(logic[$bits(tcdm_payload_t) + $clog2(NumTilesPerHive) - 1:0])
    ) i_tcdm_slave_resp_register (
      .clk_i  (clk_i                                                                ),
      .rst_ni (rst_ni                                                               ),
      .data_i ({prereg_tcdm_slave_resp_rdata[h], prereg_tcdm_slave_resp_ini_addr[h]}),
      .valid_i(prereg_tcdm_slave_resp_valid[h]                                      ),
      .ready_o(prereg_tcdm_slave_resp_ready[h]                                      ),
      .data_o ({tcdm_slave_resp_rdata_o[h], tcdm_slave_resp_ini_addr_o[h]}          ),
      .valid_o(tcdm_slave_resp_valid_o[h]                                           ),
      .ready_i(tcdm_slave_resp_ready_i[h]                                           )
    );
  end: gen_tcdm_registers

  /************************
   *   Request Crossbar   *
   ************************/

  typedef struct packed {
    logic wen             ;
    strb_t be             ;
    tcdm_addr_t tgt_addr  ;
    tcdm_payload_t payload;
  } local_master_xbar_req_payload_t;

  logic                           [NumCoresPerTile-1:0]                                                    local_master_xbar_req_valid;
  logic                           [NumCoresPerTile-1:0]                                                    local_master_xbar_req_ready;
  tcdm_addr_t                     [NumCoresPerTile-1:0]                                                    local_master_xbar_req_tgt_addr;
  logic                           [NumCoresPerTile-1:0]                                                    local_master_xbar_req_wen;
  tcdm_payload_t                  [NumCoresPerTile-1:0]                                                    local_master_xbar_req_wdata;
  strb_t                          [NumCoresPerTile-1:0]                                                    local_master_xbar_req_be;
  local_master_xbar_req_payload_t [NumCoresPerTile-1:0]                                                    local_master_xbar_req_data_agg;
  logic                           [NumCoresPerTile-1:0][(NumHives == 1 ? 1 : $clog2(NumHives))-1:0]        local_master_xbar_req_tgt_sel;
  logic                           [NumCoresPerTile-1:0]                                                    local_master_xbar_resp_valid;
  logic                           [NumCoresPerTile-1:0]                                                    local_master_xbar_resp_ready;
  tcdm_payload_t                  [NumCoresPerTile-1:0]                                                    local_master_xbar_resp_rdata;
  logic                           [NumHives-1:0][(NumCoresPerTile == 1 ? 1 : $clog2(NumCoresPerTile))-1:0] local_master_xbar_resp_ini_addr;
  local_master_xbar_req_payload_t [NumHives-1:0]                                                           local_master_xbar_resp_data_agg;

  for (genvar c = 0; c < NumCoresPerTile; c++) begin: gen_local_master_xbar_req_data_agg
    assign local_master_xbar_req_data_agg[c].be                 = local_master_xbar_req_be[c]              ;
    assign local_master_xbar_req_data_agg[c].wen                = local_master_xbar_req_wen[c]             ;
    assign local_master_xbar_req_data_agg[c].tgt_addr           = local_master_xbar_req_tgt_addr[c]        ;
    assign local_master_xbar_req_data_agg[c].payload.amo        = local_master_xbar_req_wdata[c].amo       ;
    assign local_master_xbar_req_data_agg[c].payload.data       = local_master_xbar_req_wdata[c].data      ;
    assign local_master_xbar_req_data_agg[c].payload.reorder_id = local_master_xbar_req_wdata[c].reorder_id;
    assign local_master_xbar_req_data_agg[c].payload.core_id    = c[$clog2(NumCoresPerTile)-1:0]           ;
  end

  for (genvar h = 0; h < NumHives; h++) begin: gen_local_master_xbar_resp_data_agg
    assign prereg_tcdm_master_req_wen[h]      = local_master_xbar_resp_data_agg[h].wen      ;
    assign prereg_tcdm_master_req_be[h]       = local_master_xbar_resp_data_agg[h].be       ;
    assign prereg_tcdm_master_req_tgt_addr[h] = local_master_xbar_resp_data_agg[h].tgt_addr ;
    assign prereg_tcdm_master_req_wdata[h]    = local_master_xbar_resp_data_agg[h].payload  ;
    assign local_master_xbar_resp_ini_addr[h] = postreg_tcdm_master_resp_rdata[h].core_id   ;
  end

  full_duplex_xbar #(
    .NumIn        (NumCoresPerTile                       ),
    .NumOut       (NumHives                              ),
    .ReqDataWidth ($bits(local_master_xbar_req_payload_t)),
    .RespDataWidth($bits(tcdm_payload_t)                 ),
    .AxiVldRdy    (1'b1                                  )
  ) i_local_master_xbar (
    .clk_i          (clk_i                          ),
    .rst_ni         (rst_ni                         ),
    // Extern priority flags
    .req_rr_i       ('0                             ),
    .resp_rr_i      ('0                             ),
    // Initiator side
    .req_valid_i    (local_master_xbar_req_valid    ),
    .req_ready_o    (local_master_xbar_req_ready    ),
    .req_tgt_addr_i (local_master_xbar_req_tgt_sel  ),
    .req_wdata_i    (local_master_xbar_req_data_agg ),
    .resp_valid_o   (local_master_xbar_resp_valid   ),
    .resp_ready_i   (local_master_xbar_resp_ready   ),
    .resp_rdata_o   (local_master_xbar_resp_rdata   ),
    // Target side
    .req_valid_o    (prereg_tcdm_master_req_valid   ),
    .req_ini_addr_o (/* Unused */                   ),
    .req_ready_i    (prereg_tcdm_master_req_ready   ),
    .req_wdata_o    (local_master_xbar_resp_data_agg),
    .resp_valid_i   (postreg_tcdm_master_resp_valid ),
    .resp_ready_o   (postreg_tcdm_master_resp_ready ),
    .resp_ini_addr_i(local_master_xbar_resp_ini_addr),
    .resp_rdata_i   (postreg_tcdm_master_resp_rdata )
  );

  /**********************
   *   Slave Crossbar   *
   **********************/

  logic                      [NumCoresPerTile-1:0] local_slave_xbar_req_valid;
  logic                      [NumCoresPerTile-1:0] local_slave_xbar_req_ready;
  tcdm_addr_t                [NumCoresPerTile-1:0] local_slave_xbar_req_addr;
  logic                      [NumCoresPerTile-1:0] local_slave_xbar_req_wen;
  local_slave_xbar_payload_t [NumCoresPerTile-1:0] local_slave_xbar_req_payload;
  strb_t                     [NumCoresPerTile-1:0] local_slave_xbar_req_be;
  logic                      [NumCoresPerTile-1:0] local_slave_xbar_resp_valid;
  logic                      [NumCoresPerTile-1:0] local_slave_xbar_resp_ready;
  local_slave_xbar_payload_t [NumCoresPerTile-1:0] local_slave_xbar_resp_payload;
  local_slave_xbar_payload_t [NumHives-1:0]        postreg_tcdm_slave_req_payload;
  local_slave_xbar_payload_t [NumHives-1:0]        prereg_tcdm_slave_resp_payload;

  for (genvar h = 0; unsigned'(h) < NumHives; h++) begin: gen_tcdm_slave_payload
    assign postreg_tcdm_slave_req_payload[h] = '{
      data       : postreg_tcdm_slave_req_wdata[h].data      ,
      amo        : postreg_tcdm_slave_req_wdata[h].amo       ,
      reorder_id : postreg_tcdm_slave_req_wdata[h].reorder_id,
      tile_id    : postreg_tcdm_slave_req_ini_addr[h]        ,
      core_id    : postreg_tcdm_slave_req_wdata[h].core_id
    };
    assign prereg_tcdm_slave_resp_rdata[h].data       = prereg_tcdm_slave_resp_payload[h].data      ;
    assign prereg_tcdm_slave_resp_rdata[h].reorder_id = prereg_tcdm_slave_resp_payload[h].reorder_id;
    assign prereg_tcdm_slave_resp_rdata[h].core_id    = prereg_tcdm_slave_resp_payload[h].core_id   ;
    assign prereg_tcdm_slave_resp_rdata[h].amo        = '0                                          ; // Don't care
    assign prereg_tcdm_slave_resp_ini_addr[h]         = prereg_tcdm_slave_resp_payload[h].tile_id   ;
  end: gen_tcdm_slave_payload

  localparam int unsigned RespXbarAggDataWidth = 1 + BeWidth + TCDMAddrMemWidth + $bits(local_slave_xbar_payload_t);

  logic [NumCoresPerTile+NumHives-1:0][RespXbarAggDataWidth-1:0]    local_slave_xbar_data_agg;
  logic [NumCoresPerTile+NumHives-1:0][$clog2(NumBanksPerTile)-1:0] local_slave_xbar_tgt_sel;
  logic [NumBanksPerTile-1:0][RespXbarAggDataWidth-1:0]             bank_data_agg;

  for (genvar j = 0; unsigned'(j) < NumCoresPerTile; j++) begin: gen_local_slave_xbar_data_agg_local
    assign local_slave_xbar_data_agg[j] = {local_slave_xbar_req_wen[j], local_slave_xbar_req_be[j], local_slave_xbar_req_addr[j][$clog2(NumBanksPerTile) +: TCDMAddrMemWidth], local_slave_xbar_req_payload[j]};
    assign local_slave_xbar_tgt_sel[j]  = local_slave_xbar_req_addr[j][$clog2(NumBanksPerTile)-1:0]                                                                                                            ;
  end: gen_local_slave_xbar_data_agg_local

  for (genvar j = 0; unsigned'(j) < NumHives; j++) begin: gen_local_slave_xbar_data_agg_remote
    assign local_slave_xbar_data_agg[j + NumCoresPerTile] = {postreg_tcdm_slave_req_wen[j], postreg_tcdm_slave_req_be[j], postreg_tcdm_slave_req_tgt_addr[j][$clog2(NumBanksPerTile) +: TCDMAddrMemWidth], postreg_tcdm_slave_req_payload[j]};
    assign local_slave_xbar_tgt_sel[j + NumCoresPerTile]  = postreg_tcdm_slave_req_tgt_addr[j][$clog2(NumBanksPerTile)-1:0]                                                                                                                  ;
  end: gen_local_slave_xbar_data_agg_remote

  for (genvar j = 0; unsigned'(j) < NumBanksPerTile; j++) begin: gen_bank_data_agg
    assign {bank_req_wen[j], bank_req_be[j], bank_req_tgt_addr[j], bank_req_payload[j]} = bank_data_agg[j];
  end: gen_bank_data_agg

  full_duplex_xbar #(
    .NumIn        (NumCoresPerTile + NumHives       ),
    .NumOut       (NumBanksPerTile                  ),
    .ReqDataWidth (RespXbarAggDataWidth             ),
    .RespDataWidth($bits(local_slave_xbar_payload_t)),
    .AxiVldRdy    (1'b1                             )
  ) i_local_slave_xbar (
    .clk_i          (clk_i                                                          ),
    .rst_ni         (rst_ni                                                         ),
    // Extern priority flags
    .req_rr_i       ('0                                                             ),
    .resp_rr_i      ('0                                                             ),
    // Initiator side
    .req_valid_i    ({postreg_tcdm_slave_req_valid, local_slave_xbar_req_valid}     ),
    .req_ready_o    ({postreg_tcdm_slave_req_ready, local_slave_xbar_req_ready}     ),
    .req_tgt_addr_i (local_slave_xbar_tgt_sel                                       ),
    .req_wdata_i    (local_slave_xbar_data_agg                                      ),
    .resp_valid_o   ({prereg_tcdm_slave_resp_valid, local_slave_xbar_resp_valid}    ),
    .resp_ready_i   ({prereg_tcdm_slave_resp_ready, local_slave_xbar_resp_ready}    ),
    .resp_rdata_o   ({prereg_tcdm_slave_resp_payload, local_slave_xbar_resp_payload}),
    // Target side
    .req_valid_o    (bank_req_valid                                                 ),
    .req_ini_addr_o (bank_req_ini_addr                                              ),
    .req_ready_i    (bank_req_ready                                                 ),
    .req_wdata_o    (bank_data_agg                                                  ),
    .resp_valid_i   (bank_resp_valid                                                ),
    .resp_ready_o   (bank_resp_ready                                                ),
    .resp_ini_addr_i(bank_resp_ini_addr                                             ),
    .resp_rdata_i   (bank_resp_payload                                              )
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
    // Remove tile index from local_slave_xbar_addr_int, since it will not be used for routing.
    addr_t local_slave_xbar_addr_int;
    assign local_slave_xbar_req_addr[c] =
     tcdm_addr_t'({local_slave_xbar_addr_int[ByteOffset + $clog2(NumBanksPerTile) + $clog2(NumTiles) +: TCDMAddrMemWidth], // Bank address
             local_slave_xbar_addr_int[ByteOffset +: $clog2(NumBanksPerTile)]}); // Bank

    // Switch tile and bank indexes for correct upper level routing
    addr_t prescramble_tcdm_req_tgt_addr;
    assign local_master_xbar_req_tgt_addr[c] =
    tcdm_addr_t'({prescramble_tcdm_req_tgt_addr[ByteOffset + $clog2(NumBanksPerTile) + $clog2(NumTilesPerHive) + $clog2(NumHives) +: TCDMAddrMemWidth], // Bank address
       prescramble_tcdm_req_tgt_addr[ByteOffset +: $clog2(NumBanksPerTile)]                                                                           , // Bank
       prescramble_tcdm_req_tgt_addr[ByteOffset + $clog2(NumBanksPerTile) +: $clog2(NumTilesPerHive)]}); // Tile
    if (NumHives == 1) begin: gen_local_master_xbar_req_tgt_sel_degen
      assign local_master_xbar_req_tgt_sel[c] = 1'b0;
    end else begin
      assign local_master_xbar_req_tgt_sel[c] = prescramble_tcdm_req_tgt_addr[ByteOffset + $clog2(NumBanksPerTile) + $clog2(NumTilesPerHive) +: $clog2(NumHives)]; // Hive
    end

    // We don't care about these
    assign local_slave_xbar_req_payload[c].core_id = '0;
    assign local_slave_xbar_req_payload[c].tile_id = '0;
    assign soc_data_q[c].id                        = '0;

    // Constant value
    assign local_master_xbar_req_wdata[c].core_id = c[$clog2(NumCoresPerTile)-1:0];

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
      .address_i (snitch_data_qaddr[c]       ),
      .address_o (snitch_data_qaddr_scrambled)
    );

    tcdm_shim #(
      .AddrWidth(AddrWidth),
      .DataWidth(DataWidth),
      .NrTCDM   (2        ),
      .NrSoC    (1        ),
      .NumRules (3        )
    ) i_tcdm_shim (
      .clk_i              (clk_i                                                                                    ),
      .rst_ni             (rst_ni                                                                                   ),
      // to TCDM --> FF Connection to outside of tile
      .tcdm_req_valid_o   ({local_slave_xbar_req_valid[c], local_master_xbar_req_valid[c]}                          ),
      .tcdm_req_tgt_addr_o({local_slave_xbar_addr_int, prescramble_tcdm_req_tgt_addr}                               ),
      .tcdm_req_wen_o     ({local_slave_xbar_req_wen[c], local_master_xbar_req_wen[c]}                              ),
      .tcdm_req_wdata_o   ({local_slave_xbar_req_payload[c].data, local_master_xbar_req_wdata[c].data}              ),
      .tcdm_req_amo_o     ({local_slave_xbar_req_payload[c].amo, local_master_xbar_req_wdata[c].amo}                ),
      .tcdm_req_id_o      ({local_slave_xbar_req_payload[c].reorder_id, local_master_xbar_req_wdata[c].reorder_id}  ),
      .tcdm_req_be_o      ({local_slave_xbar_req_be[c], local_master_xbar_req_be[c]}                                ),
      .tcdm_req_ready_i   ({local_slave_xbar_req_ready[c], local_master_xbar_req_ready[c]}                          ),
      .tcdm_resp_valid_i  ({local_slave_xbar_resp_valid[c], local_master_xbar_resp_valid[c]}                        ),
      .tcdm_resp_ready_o  ({local_slave_xbar_resp_ready[c], local_master_xbar_resp_ready[c]}                        ),
      .tcdm_resp_rdata_i  ({local_slave_xbar_resp_payload[c].data, local_master_xbar_resp_rdata[c].data}            ),
      .tcdm_resp_id_i     ({local_slave_xbar_resp_payload[c].reorder_id, local_master_xbar_resp_rdata[c].reorder_id}),
      // to SoC
      .soc_qaddr_o        (soc_data_q[c].addr                                                                       ),
      .soc_qwrite_o       (soc_data_q[c].write                                                                      ),
      .soc_qamo_o         (soc_data_q[c].amo                                                                        ),
      .soc_qdata_o        (soc_data_q[c].data                                                                       ),
      .soc_qstrb_o        (soc_data_q[c].strb                                                                       ),
      .soc_qvalid_o       (soc_data_qvalid[c]                                                                       ),
      .soc_qready_i       (soc_data_qready[c]                                                                       ),
      .soc_pdata_i        (soc_data_p[c].data                                                                       ),
      .soc_perror_i       (soc_data_p[c].error                                                                      ),
      .soc_pvalid_i       (soc_data_pvalid[c]                                                                       ),
      .soc_pready_o       (soc_data_pready[c]                                                                       ),
      // from core
      .data_qaddr_i       (snitch_data_qaddr_scrambled                                                              ),
      .data_qwrite_i      (snitch_data_qwrite[c]                                                                    ),
      .data_qamo_i        (snitch_data_qamo[c]                                                                      ),
      .data_qdata_i       (snitch_data_qdata[c]                                                                     ),
      .data_qstrb_i       (snitch_data_qstrb[c]                                                                     ),
      .data_qvalid_i      (snitch_data_qvalid[c]                                                                    ),
      .data_qready_o      (snitch_data_qready[c]                                                                    ),
      .data_pdata_o       (snitch_data_pdata[c]                                                                     ),
      .data_perror_o      (snitch_data_perror[c]                                                                    ),
      .data_pvalid_o      (snitch_data_pvalid[c]                                                                    ),
      .data_pready_i      (snitch_data_pready[c]                                                                    ),
      .address_map_i      (mask_map                                                                                 )
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
  axi_req_t  axi_mst_req;
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

  if (NumCores != unsigned'(2**$clog2(NumCores)))
    $fatal(1, "[mempool_tile] The number of cores must be a power of two.");

endmodule : mempool_tile
