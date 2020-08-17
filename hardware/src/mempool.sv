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

module mempool #(
    parameter int unsigned NumCores        = 1                         ,
    parameter int unsigned NumHives        = 1                         ,
    parameter int unsigned BankingFactor   = 1                         ,
    // TCDM
    parameter addr_t TCDMBaseAddr          = 32'b0                     ,
    // Boot address
    parameter logic [31:0] BootAddr        = 32'h0000_0000             ,
    // Dependent parameters. DO NOT CHANGE!
    parameter int unsigned NumTiles        = NumCores / NumCoresPerTile,
    parameter int unsigned NumBanks        = NumCores * BankingFactor  ,
    parameter int unsigned NumBanksPerTile = NumBanks / NumTiles       ,
    parameter int unsigned NumBanksPerHive = NumBanks / NumHives       ,
    parameter int unsigned TCDMAddrWidth   = TCDMAddrMemWidth + $clog2(NumBanksPerHive)
  ) (
    // Clock and reset
    input  logic                     clk_i,
    input  logic                     rst_ni,
    input  logic                     testmode_i,
    // Scan chain
    input  logic                     scan_enable_i,
    input  logic                     scan_data_i,
    output logic                     scan_data_o,
    // AXI Plugs for testbench
    output axi_req_t  [NumTiles-1:0] axi_mst_req_o,
    input  axi_resp_t [NumTiles-1:0] axi_mst_resp_i
  );

  /*****************
   *  Definitions  *
   *****************/

  localparam NumTilesPerHive = NumTiles / NumHives;

  typedef logic [$clog2(NumTiles)-1:0] tile_id_t                            ;
  typedef logic [$clog2(NumTilesPerHive)-1:0] hive_tile_id_t                ;
  typedef logic [TCDMAddrMemWidth + $clog2(NumBanksPerTile)-1:0] tile_addr_t;
  typedef logic [TCDMAddrWidth-1:0] tcdm_addr_t                             ;

  typedef struct packed {
    tcdm_payload_t wdata;
    logic wen           ;
    strb_t be           ;
    tcdm_addr_t tgt_addr;
  } tcdm_master_req_t;

  typedef struct packed {
    tcdm_payload_t rdata;
  } tcdm_master_resp_t;

  typedef struct packed {
    tcdm_payload_t wdata   ;
    logic wen              ;
    strb_t be              ;
    tile_addr_t tgt_addr   ;
    hive_tile_id_t ini_addr;
  } tcdm_slave_req_t;

  typedef struct packed {
    tcdm_payload_t rdata   ;
    hive_tile_id_t ini_addr;
  } tcdm_slave_resp_t;

  /***********
   *  Reset  *
   ***********/

  logic rst_n;
  rstgen_bypass i_rstgen (
    .clk_i           (clk_i       ),
    .rst_ni          (rst_ni      ),
    .rst_test_mode_ni(rst_ni      ),
    .test_mode_i     (testmode_i  ),
    .init_no         (/* Unused */),
    .rst_no          (rst_n       )
  );

  /***********
   *  Tiles  *
   ***********/

  // TCDM interfaces
  // North
  tcdm_master_req_t  [NumTiles-1:0] tcdm_master_north_req;
  logic              [NumTiles-1:0] tcdm_master_north_req_valid;
  logic              [NumTiles-1:0] tcdm_master_north_req_ready;
  tcdm_master_resp_t [NumTiles-1:0] tcdm_master_north_resp;
  logic              [NumTiles-1:0] tcdm_master_north_resp_valid;
  logic              [NumTiles-1:0] tcdm_master_north_resp_ready;
  tcdm_slave_req_t   [NumTiles-1:0] tcdm_slave_north_req;
  logic              [NumTiles-1:0] tcdm_slave_north_req_valid;
  logic              [NumTiles-1:0] tcdm_slave_north_req_ready;
  tcdm_slave_resp_t  [NumTiles-1:0] tcdm_slave_north_resp;
  logic              [NumTiles-1:0] tcdm_slave_north_resp_valid;
  logic              [NumTiles-1:0] tcdm_slave_north_resp_ready;
  // East
  tcdm_master_req_t  [NumTiles-1:0] tcdm_master_east_req;
  logic              [NumTiles-1:0] tcdm_master_east_req_valid;
  logic              [NumTiles-1:0] tcdm_master_east_req_ready;
  tcdm_master_resp_t [NumTiles-1:0] tcdm_master_east_resp;
  logic              [NumTiles-1:0] tcdm_master_east_resp_valid;
  logic              [NumTiles-1:0] tcdm_master_east_resp_ready;
  tcdm_slave_req_t   [NumTiles-1:0] tcdm_slave_east_req;
  logic              [NumTiles-1:0] tcdm_slave_east_req_valid;
  logic              [NumTiles-1:0] tcdm_slave_east_req_ready;
  tcdm_slave_resp_t  [NumTiles-1:0] tcdm_slave_east_resp;
  logic              [NumTiles-1:0] tcdm_slave_east_resp_valid;
  logic              [NumTiles-1:0] tcdm_slave_east_resp_ready;
  // Northeast
  tcdm_master_req_t  [NumTiles-1:0] tcdm_master_northeast_req;
  logic              [NumTiles-1:0] tcdm_master_northeast_req_valid;
  logic              [NumTiles-1:0] tcdm_master_northeast_req_ready;
  tcdm_master_resp_t [NumTiles-1:0] tcdm_master_northeast_resp;
  logic              [NumTiles-1:0] tcdm_master_northeast_resp_valid;
  logic              [NumTiles-1:0] tcdm_master_northeast_resp_ready;
  tcdm_slave_req_t   [NumTiles-1:0] tcdm_slave_northeast_req;
  logic              [NumTiles-1:0] tcdm_slave_northeast_req_valid;
  logic              [NumTiles-1:0] tcdm_slave_northeast_req_ready;
  tcdm_slave_resp_t  [NumTiles-1:0] tcdm_slave_northeast_resp;
  logic              [NumTiles-1:0] tcdm_slave_northeast_resp_valid;
  logic              [NumTiles-1:0] tcdm_slave_northeast_resp_ready;
  // Center
  tcdm_master_req_t  [NumTiles-1:0] tcdm_master_center_req;
  logic              [NumTiles-1:0] tcdm_master_center_req_valid;
  logic              [NumTiles-1:0] tcdm_master_center_req_ready;
  tcdm_master_resp_t [NumTiles-1:0] tcdm_master_center_resp;
  logic              [NumTiles-1:0] tcdm_master_center_resp_valid;
  logic              [NumTiles-1:0] tcdm_master_center_resp_ready;
  tcdm_slave_req_t   [NumTiles-1:0] tcdm_slave_center_req;
  logic              [NumTiles-1:0] tcdm_slave_center_req_valid;
  logic              [NumTiles-1:0] tcdm_slave_center_req_ready;
  tcdm_slave_resp_t  [NumTiles-1:0] tcdm_slave_center_resp;
  logic              [NumTiles-1:0] tcdm_slave_center_resp_valid;
  logic              [NumTiles-1:0] tcdm_slave_center_resp_ready;

  for (genvar t = 0; unsigned'(t) < NumTiles; t++) begin: gen_tiles
    mempool_tile_wrap_NumHives4 #(
      .NumBanksPerTile   (NumBanksPerTile   ),
      .NumTiles          (NumTiles          ),
      .NumBanks          (NumBanks          ),
      .TCDMBaseAddr      (TCDMBaseAddr      ),
      .BootAddr          (BootAddr          ),
      .tcdm_master_req_t (tcdm_master_req_t ),
      .tcdm_master_resp_t(tcdm_master_resp_t),
      .tcdm_slave_req_t  (tcdm_slave_req_t  ),
      .tcdm_slave_resp_t (tcdm_slave_resp_t )
    ) i_tile (
      .clk_i                             (clk_i                               ),
      .rst_ni                            (rst_n                               ),
      .scan_enable_i                     (scan_enable_i                       ),
      .scan_data_i                       (/* Unconnected */                   ),
      .scan_data_o                       (/* Unconnected */                   ),
      .tile_id_i                         (t[$clog2(NumTiles)-1:0]             ),
      // TCDM Master interfaces
      .tcdm_master_north_req_o           (tcdm_master_north_req[t]            ),
      .tcdm_master_north_req_valid_o     (tcdm_master_north_req_valid[t]      ),
      .tcdm_master_north_req_ready_i     (tcdm_master_north_req_ready[t]      ),
      .tcdm_master_north_resp_i          (tcdm_master_north_resp[t]           ),
      .tcdm_master_north_resp_valid_i    (tcdm_master_north_resp_valid[t]     ),
      .tcdm_master_north_resp_ready_o    (tcdm_master_north_resp_ready[t]     ),
      .tcdm_master_east_req_o            (tcdm_master_east_req[t]             ),
      .tcdm_master_east_req_valid_o      (tcdm_master_east_req_valid[t]       ),
      .tcdm_master_east_req_ready_i      (tcdm_master_east_req_ready[t]       ),
      .tcdm_master_east_resp_i           (tcdm_master_east_resp[t]            ),
      .tcdm_master_east_resp_valid_i     (tcdm_master_east_resp_valid[t]      ),
      .tcdm_master_east_resp_ready_o     (tcdm_master_east_resp_ready[t]      ),
      .tcdm_master_northeast_req_o       (tcdm_master_northeast_req[t]        ),
      .tcdm_master_northeast_req_valid_o (tcdm_master_northeast_req_valid[t]  ),
      .tcdm_master_northeast_req_ready_i (tcdm_master_northeast_req_ready[t]  ),
      .tcdm_master_northeast_resp_i      (tcdm_master_northeast_resp[t]       ),
      .tcdm_master_northeast_resp_valid_i(tcdm_master_northeast_resp_valid[t] ),
      .tcdm_master_northeast_resp_ready_o(tcdm_master_northeast_resp_ready[t] ),
      .tcdm_master_center_req_o          (tcdm_master_center_req[t]           ),
      .tcdm_master_center_req_valid_o    (tcdm_master_center_req_valid[t]     ),
      .tcdm_master_center_req_ready_i    (tcdm_master_center_req_ready[t]     ),
      .tcdm_master_center_resp_i         (tcdm_master_center_resp[t]          ),
      .tcdm_master_center_resp_valid_i   (tcdm_master_center_resp_valid[t]    ),
      .tcdm_master_center_resp_ready_o   (tcdm_master_center_resp_ready[t]    ),
      // TCDM banks interface
      .tcdm_slave_north_req_i            (tcdm_slave_north_req[t]             ),
      .tcdm_slave_north_req_valid_i      (tcdm_slave_north_req_valid[t]       ),
      .tcdm_slave_north_req_ready_o      (tcdm_slave_north_req_ready[t]       ),
      .tcdm_slave_north_resp_o           (tcdm_slave_north_resp[t]            ),
      .tcdm_slave_north_resp_valid_o     (tcdm_slave_north_resp_valid[t]      ),
      .tcdm_slave_north_resp_ready_i     (tcdm_slave_north_resp_ready[t]      ),
      .tcdm_slave_east_req_i             (tcdm_slave_east_req[t]              ),
      .tcdm_slave_east_req_valid_i       (tcdm_slave_east_req_valid[t]        ),
      .tcdm_slave_east_req_ready_o       (tcdm_slave_east_req_ready[t]        ),
      .tcdm_slave_east_resp_o            (tcdm_slave_east_resp[t]             ),
      .tcdm_slave_east_resp_valid_o      (tcdm_slave_east_resp_valid[t]       ),
      .tcdm_slave_east_resp_ready_i      (tcdm_slave_east_resp_ready[t]       ),
      .tcdm_slave_northeast_req_i        (tcdm_slave_northeast_req[t]         ),
      .tcdm_slave_northeast_req_valid_i  (tcdm_slave_northeast_req_valid[t]   ),
      .tcdm_slave_northeast_req_ready_o  (tcdm_slave_northeast_req_ready[t]   ),
      .tcdm_slave_northeast_resp_o       (tcdm_slave_northeast_resp[t]        ),
      .tcdm_slave_northeast_resp_valid_o (tcdm_slave_northeast_resp_valid[t]  ),
      .tcdm_slave_northeast_resp_ready_i (tcdm_slave_northeast_resp_ready[t]  ),
      .tcdm_slave_center_req_i           (tcdm_slave_center_req[t]            ),
      .tcdm_slave_center_req_valid_i     (tcdm_slave_center_req_valid[t]      ),
      .tcdm_slave_center_req_ready_o     (tcdm_slave_center_req_ready[t]      ),
      .tcdm_slave_center_resp_o          (tcdm_slave_center_resp[t]           ),
      .tcdm_slave_center_resp_valid_o    (tcdm_slave_center_resp_valid[t]     ),
      .tcdm_slave_center_resp_ready_i    (tcdm_slave_center_resp_ready[t]     ),
      // AXI interface
      .axi_mst_req_o                     (axi_mst_req_o[t]                    ),
      .axi_mst_resp_i                    (axi_mst_resp_i[t]                   ),
      // Instruction refill interface
      .refill_qaddr_o                    (/* Not yet implemented */           ),
      .refill_qlen_o                     (/* Not yet implemented */           ), // AXI signal
      .refill_qvalid_o                   (/* Not yet implemented */           ),
      .refill_qready_i                   (/* Not yet implemented */ 1'b0      ),
      .refill_pdata_i                    (/* Not yet implemented */ '0        ),
      .refill_perror_i                   (/* Not yet implemented */ '0        ),
      .refill_pvalid_i                   (/* Not yet implemented */ 1'b0      ),
      .refill_plast_i                    (/* Not yet implemented */ 1'b0      ),
      .refill_pready_o                   (/* Not yet implemented */           )
    );
  end : gen_tiles

  /*******************
   *  Interconnects  *
   *******************/

  // Center
  for (genvar ini = 0; ini < NumHives; ini++) begin: gen_center_intercos
    localparam int unsigned tgt = ini ^ 2'b00;

    logic [NumTilesPerHive-1:0] master_center_req_valid             ;
    logic [NumTilesPerHive-1:0] master_center_req_ready             ;
    tcdm_addr_t [NumTilesPerHive-1:0] master_center_req_tgt_addr    ;
    logic [NumTilesPerHive-1:0] master_center_req_wen               ;
    tcdm_payload_t [NumTilesPerHive-1:0] master_center_req_wdata    ;
    strb_t [NumTilesPerHive-1:0] master_center_req_be               ;
    logic [NumTilesPerHive-1:0] master_center_resp_valid            ;
    logic [NumTilesPerHive-1:0] master_center_resp_ready            ;
    tcdm_payload_t [NumTilesPerHive-1:0] master_center_resp_rdata   ;
    logic [NumTilesPerHive-1:0] slave_center_req_valid              ;
    logic [NumTilesPerHive-1:0] slave_center_req_ready              ;
    tile_addr_t [NumTilesPerHive-1:0] slave_center_req_tgt_addr     ;
    hive_tile_id_t [NumTilesPerHive-1:0] slave_center_req_ini_addr  ;
    logic [NumTilesPerHive-1:0] slave_center_req_wen                ;
    tcdm_payload_t [NumTilesPerHive-1:0] slave_center_req_wdata     ;
    strb_t [NumTilesPerHive-1:0] slave_center_req_be                ;
    logic [NumTilesPerHive-1:0] slave_center_resp_valid             ;
    logic [NumTilesPerHive-1:0] slave_center_resp_ready             ;
    hive_tile_id_t [NumTilesPerHive-1:0] slave_center_resp_ini_addr ;
    tcdm_payload_t [NumTilesPerHive-1:0] slave_center_resp_rdata    ;

    for (genvar t = 0; t < NumTilesPerHive; t++) begin: gen_connections
      assign master_center_req_valid[t]                              = tcdm_master_center_req_valid[NumTilesPerHive*ini + t]   ;
      assign master_center_req_tgt_addr[t]                           = tcdm_master_center_req[NumTilesPerHive*ini + t].tgt_addr;
      assign master_center_req_wen[t]                                = tcdm_master_center_req[NumTilesPerHive*ini + t].wen     ;
      assign master_center_req_wdata[t]                              = tcdm_master_center_req[NumTilesPerHive*ini + t].wdata   ;
      assign master_center_req_be[t]                                 = tcdm_master_center_req[NumTilesPerHive*ini + t].be      ;
      assign tcdm_master_center_req_ready[NumTilesPerHive*ini + t]   = master_center_req_ready[t]                              ;
      assign slave_center_resp_valid[t]                              = tcdm_slave_center_resp_valid[NumTilesPerHive*ini + t]   ;
      assign slave_center_resp_ini_addr[t]                           = tcdm_slave_center_resp[NumTilesPerHive*ini + t].ini_addr;
      assign slave_center_resp_rdata[t]                              = tcdm_slave_center_resp[NumTilesPerHive*ini + t].rdata   ;
      assign tcdm_slave_center_resp_ready[NumTilesPerHive*ini + t]   = slave_center_resp_ready[t]                              ;
      assign tcdm_master_center_resp_valid[NumTilesPerHive*tgt + t]  = master_center_resp_valid[t]                             ;
      assign tcdm_master_center_resp[NumTilesPerHive*tgt + t].rdata  = master_center_resp_rdata[t]                             ;
      assign master_center_resp_ready[t]                             = tcdm_master_center_resp_ready[NumTilesPerHive*tgt + t]  ;
      assign tcdm_slave_center_req_valid[NumTilesPerHive*tgt + t]    = slave_center_req_valid[t]                               ;
      assign tcdm_slave_center_req[NumTilesPerHive*tgt + t].tgt_addr = slave_center_req_tgt_addr[t]                            ;
      assign tcdm_slave_center_req[NumTilesPerHive*tgt + t].ini_addr = slave_center_req_ini_addr[t]                            ;
      assign tcdm_slave_center_req[NumTilesPerHive*tgt + t].wen      = slave_center_req_wen[t]                                 ;
      assign tcdm_slave_center_req[NumTilesPerHive*tgt + t].wdata    = slave_center_req_wdata[t]                               ;
      assign tcdm_slave_center_req[NumTilesPerHive*tgt + t].be       = slave_center_req_be[t]                                  ;
      assign slave_center_req_ready[t]                               = tcdm_slave_center_req_ready[NumTilesPerHive*tgt + t]    ;
    end

    variable_latency_interconnect #(
      .NumIn       (NumTilesPerHive                           ),
      .NumOut      (NumTilesPerHive                           ),
      .AddrWidth   (TCDMAddrWidth                             ),
      .DataWidth   ($bits(tcdm_payload_t)                     ),
      .BeWidth     (DataWidth/8                               ),
      .ByteOffWidth(0                                         ),
      .AddrMemWidth(TCDMAddrMemWidth + $clog2(NumBanksPerTile)),
      .Topology    (tcdm_interconnect_pkg::BFLY4              ),
      .AxiVldRdy   (1'b1                                      )
    ) i_interco (
      .clk_i          (clk_i                     ),
      .rst_ni         (rst_n                     ),
      .req_valid_i    (master_center_req_valid   ),
      .req_ready_o    (master_center_req_ready   ),
      .req_tgt_addr_i (master_center_req_tgt_addr),
      .req_wen_i      (master_center_req_wen     ),
      .req_wdata_i    (master_center_req_wdata   ),
      .req_be_i       (master_center_req_be      ),
      .resp_valid_o   (master_center_resp_valid  ),
      .resp_ready_i   (master_center_resp_ready  ),
      .resp_rdata_o   (master_center_resp_rdata  ),
      .resp_ini_addr_i(slave_center_resp_ini_addr),
      .resp_rdata_i   (slave_center_resp_rdata   ),
      .resp_valid_i   (slave_center_resp_valid   ),
      .resp_ready_o   (slave_center_resp_ready   ),
      .req_valid_o    (slave_center_req_valid    ),
      .req_ready_i    (slave_center_req_ready    ),
      .req_be_o       (slave_center_req_be       ),
      .req_wdata_o    (slave_center_req_wdata    ),
      .req_wen_o      (slave_center_req_wen      ),
      .req_ini_addr_o (slave_center_req_ini_addr ),
      .req_tgt_addr_o (slave_center_req_tgt_addr )
    );
  end

  // East
  for (genvar ini = 0; ini < NumHives; ini++) begin: gen_east_intercos
    localparam int unsigned tgt = ini ^ 2'b01;
    localparam int unsigned idx[NumTilesPerHive] = {0,2,8,10,1,3,9,11,4,6,12,14,5,7,13,15};

    logic [NumTilesPerHive-1:0] master_east_req_valid             ;
    logic [NumTilesPerHive-1:0] master_east_req_ready             ;
    tcdm_addr_t [NumTilesPerHive-1:0] master_east_req_tgt_addr    ;
    logic [NumTilesPerHive-1:0] master_east_req_wen               ;
    tcdm_payload_t [NumTilesPerHive-1:0] master_east_req_wdata    ;
    strb_t [NumTilesPerHive-1:0] master_east_req_be               ;
    logic [NumTilesPerHive-1:0] master_east_resp_valid            ;
    logic [NumTilesPerHive-1:0] master_east_resp_ready            ;
    tcdm_payload_t [NumTilesPerHive-1:0] master_east_resp_rdata   ;
    logic [NumTilesPerHive-1:0] slave_east_req_valid              ;
    logic [NumTilesPerHive-1:0] slave_east_req_ready              ;
    tile_addr_t [NumTilesPerHive-1:0] slave_east_req_tgt_addr     ;
    hive_tile_id_t [NumTilesPerHive-1:0] slave_east_req_ini_addr  ;
    logic [NumTilesPerHive-1:0] slave_east_req_wen                ;
    tcdm_payload_t [NumTilesPerHive-1:0] slave_east_req_wdata     ;
    strb_t [NumTilesPerHive-1:0] slave_east_req_be                ;
    logic [NumTilesPerHive-1:0] slave_east_resp_valid             ;
    logic [NumTilesPerHive-1:0] slave_east_resp_ready             ;
    hive_tile_id_t [NumTilesPerHive-1:0] slave_east_resp_ini_addr ;
    tcdm_payload_t [NumTilesPerHive-1:0] slave_east_resp_rdata    ;

    for (genvar t = 0; t < NumTilesPerHive; t++) begin: gen_connections
      assign master_east_req_valid[t]                              = tcdm_master_east_req_valid[NumTilesPerHive*ini + idx[t]]   ;
      assign master_east_req_tgt_addr[t]                           = tcdm_master_east_req[NumTilesPerHive*ini + idx[t]].tgt_addr;
      assign master_east_req_wen[t]                                = tcdm_master_east_req[NumTilesPerHive*ini + idx[t]].wen     ;
      assign master_east_req_wdata[t]                              = tcdm_master_east_req[NumTilesPerHive*ini + idx[t]].wdata   ;
      assign master_east_req_be[t]                                 = tcdm_master_east_req[NumTilesPerHive*ini + idx[t]].be      ;
      assign tcdm_master_east_req_ready[NumTilesPerHive*ini + idx[t]]   = master_east_req_ready[t]                              ;
      assign slave_east_resp_valid[t]                              = tcdm_slave_east_resp_valid[NumTilesPerHive*ini + idx[t]]   ;
      assign slave_east_resp_ini_addr[t]                           = tcdm_slave_east_resp[NumTilesPerHive*ini + idx[t]].ini_addr;
      assign slave_east_resp_rdata[t]                              = tcdm_slave_east_resp[NumTilesPerHive*ini + idx[t]].rdata   ;
      assign tcdm_slave_east_resp_ready[NumTilesPerHive*ini + idx[t]]   = slave_east_resp_ready[t]                              ;
      assign tcdm_master_east_resp_valid[NumTilesPerHive*tgt + idx[t]]  = master_east_resp_valid[t]                             ;
      assign tcdm_master_east_resp[NumTilesPerHive*tgt + idx[t]].rdata  = master_east_resp_rdata[t]                             ;
      assign master_east_resp_ready[t]                             = tcdm_master_east_resp_ready[NumTilesPerHive*tgt + idx[t]]  ;
      assign tcdm_slave_east_req_valid[NumTilesPerHive*tgt + t]    = slave_east_req_valid[t]                               ;
      assign tcdm_slave_east_req[NumTilesPerHive*tgt + t].tgt_addr = slave_east_req_tgt_addr[t]                            ;
      assign tcdm_slave_east_req[NumTilesPerHive*tgt + t].ini_addr = slave_east_req_ini_addr[t]                            ;
      assign tcdm_slave_east_req[NumTilesPerHive*tgt + t].wen      = slave_east_req_wen[t]                                 ;
      assign tcdm_slave_east_req[NumTilesPerHive*tgt + t].wdata    = slave_east_req_wdata[t]                               ;
      assign tcdm_slave_east_req[NumTilesPerHive*tgt + t].be       = slave_east_req_be[t]                                  ;
      assign slave_east_req_ready[t]                               = tcdm_slave_east_req_ready[NumTilesPerHive*tgt + t]    ;
    end

    variable_latency_interconnect #(
      .NumIn            (NumTilesPerHive                           ),
      .NumOut           (NumTilesPerHive                           ),
      .AddrWidth        (TCDMAddrWidth                             ),
      .DataWidth        ($bits(tcdm_payload_t)                     ),
      .BeWidth          (DataWidth/8                               ),
      .ByteOffWidth     (0                                         ),
      .AddrMemWidth     (TCDMAddrMemWidth + $clog2(NumBanksPerTile)),
      .Topology         (tcdm_interconnect_pkg::BFLY4              ),
      .AxiVldRdy        (1'b1                                      ),
      .SpillRegisterReq (64'b10                                    ),
      .SpillRegisterResp(64'b10                                    )
    ) i_interco (
      .clk_i          (clk_i                   ),
      .rst_ni         (rst_n                   ),
      .req_valid_i    (master_east_req_valid   ),
      .req_ready_o    (master_east_req_ready   ),
      .req_tgt_addr_i (master_east_req_tgt_addr),
      .req_wen_i      (master_east_req_wen     ),
      .req_wdata_i    (master_east_req_wdata   ),
      .req_be_i       (master_east_req_be      ),
      .resp_valid_o   (master_east_resp_valid  ),
      .resp_ready_i   (master_east_resp_ready  ),
      .resp_rdata_o   (master_east_resp_rdata  ),
      .resp_ini_addr_i(slave_east_resp_ini_addr),
      .resp_rdata_i   (slave_east_resp_rdata   ),
      .resp_valid_i   (slave_east_resp_valid   ),
      .resp_ready_o   (slave_east_resp_ready   ),
      .req_valid_o    (slave_east_req_valid    ),
      .req_ready_i    (slave_east_req_ready    ),
      .req_be_o       (slave_east_req_be       ),
      .req_wdata_o    (slave_east_req_wdata    ),
      .req_wen_o      (slave_east_req_wen      ),
      .req_ini_addr_o (slave_east_req_ini_addr ),
      .req_tgt_addr_o (slave_east_req_tgt_addr )
    );
  end

  // North
  for (genvar ini = 0; ini < NumHives; ini++) begin: gen_north_intercos
    localparam int unsigned tgt = ini ^ 2'b10;
    localparam int unsigned idx[NumTilesPerHive] = {0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15};

    logic [NumTilesPerHive-1:0] master_north_req_valid             ;
    logic [NumTilesPerHive-1:0] master_north_req_ready             ;
    tcdm_addr_t [NumTilesPerHive-1:0] master_north_req_tgt_addr    ;
    logic [NumTilesPerHive-1:0] master_north_req_wen               ;
    tcdm_payload_t [NumTilesPerHive-1:0] master_north_req_wdata    ;
    strb_t [NumTilesPerHive-1:0] master_north_req_be               ;
    logic [NumTilesPerHive-1:0] master_north_resp_valid            ;
    logic [NumTilesPerHive-1:0] master_north_resp_ready            ;
    tcdm_payload_t [NumTilesPerHive-1:0] master_north_resp_rdata   ;
    logic [NumTilesPerHive-1:0] slave_north_req_valid              ;
    logic [NumTilesPerHive-1:0] slave_north_req_ready              ;
    tile_addr_t [NumTilesPerHive-1:0] slave_north_req_tgt_addr     ;
    hive_tile_id_t [NumTilesPerHive-1:0] slave_north_req_ini_addr  ;
    logic [NumTilesPerHive-1:0] slave_north_req_wen                ;
    tcdm_payload_t [NumTilesPerHive-1:0] slave_north_req_wdata     ;
    strb_t [NumTilesPerHive-1:0] slave_north_req_be                ;
    logic [NumTilesPerHive-1:0] slave_north_resp_valid             ;
    logic [NumTilesPerHive-1:0] slave_north_resp_ready             ;
    hive_tile_id_t [NumTilesPerHive-1:0] slave_north_resp_ini_addr ;
    tcdm_payload_t [NumTilesPerHive-1:0] slave_north_resp_rdata    ;

    for (genvar t = 0; t < NumTilesPerHive; t++) begin: gen_connections
      assign master_north_req_valid[t]                              = tcdm_master_north_req_valid[NumTilesPerHive*ini + idx[t]]   ;
      assign master_north_req_tgt_addr[t]                           = tcdm_master_north_req[NumTilesPerHive*ini + idx[t]].tgt_addr;
      assign master_north_req_wen[t]                                = tcdm_master_north_req[NumTilesPerHive*ini + idx[t]].wen     ;
      assign master_north_req_wdata[t]                              = tcdm_master_north_req[NumTilesPerHive*ini + idx[t]].wdata   ;
      assign master_north_req_be[t]                                 = tcdm_master_north_req[NumTilesPerHive*ini + idx[t]].be      ;
      assign tcdm_master_north_req_ready[NumTilesPerHive*ini + idx[t]]   = master_north_req_ready[t]                              ;
      assign slave_north_resp_valid[t]                              = tcdm_slave_north_resp_valid[NumTilesPerHive*ini + idx[t]]   ;
      assign slave_north_resp_ini_addr[t]                           = tcdm_slave_north_resp[NumTilesPerHive*ini + idx[t]].ini_addr;
      assign slave_north_resp_rdata[t]                              = tcdm_slave_north_resp[NumTilesPerHive*ini + idx[t]].rdata   ;
      assign tcdm_slave_north_resp_ready[NumTilesPerHive*ini + idx[t]]   = slave_north_resp_ready[t]                              ;
      assign tcdm_master_north_resp_valid[NumTilesPerHive*tgt + idx[t]]  = master_north_resp_valid[t]                             ;
      assign tcdm_master_north_resp[NumTilesPerHive*tgt + idx[t]].rdata  = master_north_resp_rdata[t]                             ;
      assign master_north_resp_ready[t]                             = tcdm_master_north_resp_ready[NumTilesPerHive*tgt + idx[t]]  ;
      assign tcdm_slave_north_req_valid[NumTilesPerHive*tgt + t]    = slave_north_req_valid[t]                               ;
      assign tcdm_slave_north_req[NumTilesPerHive*tgt + t].tgt_addr = slave_north_req_tgt_addr[t]                            ;
      assign tcdm_slave_north_req[NumTilesPerHive*tgt + t].ini_addr = slave_north_req_ini_addr[t]                            ;
      assign tcdm_slave_north_req[NumTilesPerHive*tgt + t].wen      = slave_north_req_wen[t]                                 ;
      assign tcdm_slave_north_req[NumTilesPerHive*tgt + t].wdata    = slave_north_req_wdata[t]                               ;
      assign tcdm_slave_north_req[NumTilesPerHive*tgt + t].be       = slave_north_req_be[t]                                  ;
      assign slave_north_req_ready[t]                               = tcdm_slave_north_req_ready[NumTilesPerHive*tgt + t]    ;
    end

    variable_latency_interconnect #(
      .NumIn            (NumTilesPerHive                           ),
      .NumOut           (NumTilesPerHive                           ),
      .AddrWidth        (TCDMAddrWidth                             ),
      .DataWidth        ($bits(tcdm_payload_t)                     ),
      .BeWidth          (DataWidth/8                               ),
      .ByteOffWidth     (0                                         ),
      .AddrMemWidth     (TCDMAddrMemWidth + $clog2(NumBanksPerTile)),
      .Topology         (tcdm_interconnect_pkg::BFLY4              ),
      .AxiVldRdy        (1'b1                                      ),
      .SpillRegisterReq (64'b10                                    ),
      .SpillRegisterResp(64'b10                                    )
    ) i_interco (
      .clk_i          (clk_i                    ),
      .rst_ni         (rst_n                    ),
      .req_valid_i    (master_north_req_valid   ),
      .req_ready_o    (master_north_req_ready   ),
      .req_tgt_addr_i (master_north_req_tgt_addr),
      .req_wen_i      (master_north_req_wen     ),
      .req_wdata_i    (master_north_req_wdata   ),
      .req_be_i       (master_north_req_be      ),
      .resp_valid_o   (master_north_resp_valid  ),
      .resp_ready_i   (master_north_resp_ready  ),
      .resp_rdata_o   (master_north_resp_rdata  ),
      .resp_ini_addr_i(slave_north_resp_ini_addr),
      .resp_rdata_i   (slave_north_resp_rdata   ),
      .resp_valid_i   (slave_north_resp_valid   ),
      .resp_ready_o   (slave_north_resp_ready   ),
      .req_valid_o    (slave_north_req_valid    ),
      .req_ready_i    (slave_north_req_ready    ),
      .req_be_o       (slave_north_req_be       ),
      .req_wdata_o    (slave_north_req_wdata    ),
      .req_wen_o      (slave_north_req_wen      ),
      .req_ini_addr_o (slave_north_req_ini_addr ),
      .req_tgt_addr_o (slave_north_req_tgt_addr )
    );
  end

  // Northeast
  for (genvar ini = 0; ini < NumHives; ini++) begin: gen_northeast_intercos
    localparam int unsigned tgt = ini ^ 2'b11;

    logic [NumTilesPerHive-1:0] master_northeast_req_valid             ;
    logic [NumTilesPerHive-1:0] master_northeast_req_ready             ;
    tcdm_addr_t [NumTilesPerHive-1:0] master_northeast_req_tgt_addr    ;
    logic [NumTilesPerHive-1:0] master_northeast_req_wen               ;
    tcdm_payload_t [NumTilesPerHive-1:0] master_northeast_req_wdata    ;
    strb_t [NumTilesPerHive-1:0] master_northeast_req_be               ;
    logic [NumTilesPerHive-1:0] master_northeast_resp_valid            ;
    logic [NumTilesPerHive-1:0] master_northeast_resp_ready            ;
    tcdm_payload_t [NumTilesPerHive-1:0] master_northeast_resp_rdata   ;
    logic [NumTilesPerHive-1:0] slave_northeast_req_valid              ;
    logic [NumTilesPerHive-1:0] slave_northeast_req_ready              ;
    tile_addr_t [NumTilesPerHive-1:0] slave_northeast_req_tgt_addr     ;
    hive_tile_id_t [NumTilesPerHive-1:0] slave_northeast_req_ini_addr  ;
    logic [NumTilesPerHive-1:0] slave_northeast_req_wen                ;
    tcdm_payload_t [NumTilesPerHive-1:0] slave_northeast_req_wdata     ;
    strb_t [NumTilesPerHive-1:0] slave_northeast_req_be                ;
    logic [NumTilesPerHive-1:0] slave_northeast_resp_valid             ;
    logic [NumTilesPerHive-1:0] slave_northeast_resp_ready             ;
    hive_tile_id_t [NumTilesPerHive-1:0] slave_northeast_resp_ini_addr ;
    tcdm_payload_t [NumTilesPerHive-1:0] slave_northeast_resp_rdata    ;

    for (genvar t = 0; t < NumTilesPerHive; t++) begin: gen_connections
      assign master_northeast_req_valid[t]                              = tcdm_master_northeast_req_valid[NumTilesPerHive*ini + t]   ;
      assign master_northeast_req_tgt_addr[t]                           = tcdm_master_northeast_req[NumTilesPerHive*ini + t].tgt_addr;
      assign master_northeast_req_wen[t]                                = tcdm_master_northeast_req[NumTilesPerHive*ini + t].wen     ;
      assign master_northeast_req_wdata[t]                              = tcdm_master_northeast_req[NumTilesPerHive*ini + t].wdata   ;
      assign master_northeast_req_be[t]                                 = tcdm_master_northeast_req[NumTilesPerHive*ini + t].be      ;
      assign tcdm_master_northeast_req_ready[NumTilesPerHive*ini + t]   = master_northeast_req_ready[t]                              ;
      assign slave_northeast_resp_valid[t]                              = tcdm_slave_northeast_resp_valid[NumTilesPerHive*ini + t]   ;
      assign slave_northeast_resp_ini_addr[t]                           = tcdm_slave_northeast_resp[NumTilesPerHive*ini + t].ini_addr;
      assign slave_northeast_resp_rdata[t]                              = tcdm_slave_northeast_resp[NumTilesPerHive*ini + t].rdata   ;
      assign tcdm_slave_northeast_resp_ready[NumTilesPerHive*ini + t]   = slave_northeast_resp_ready[t]                              ;
      assign tcdm_master_northeast_resp_valid[NumTilesPerHive*tgt + t]  = master_northeast_resp_valid[t]                             ;
      assign tcdm_master_northeast_resp[NumTilesPerHive*tgt + t].rdata  = master_northeast_resp_rdata[t]                             ;
      assign master_northeast_resp_ready[t]                             = tcdm_master_northeast_resp_ready[NumTilesPerHive*tgt + t]  ;
      assign tcdm_slave_northeast_req_valid[NumTilesPerHive*tgt + t]    = slave_northeast_req_valid[t]                               ;
      assign tcdm_slave_northeast_req[NumTilesPerHive*tgt + t].tgt_addr = slave_northeast_req_tgt_addr[t]                            ;
      assign tcdm_slave_northeast_req[NumTilesPerHive*tgt + t].ini_addr = slave_northeast_req_ini_addr[t]                            ;
      assign tcdm_slave_northeast_req[NumTilesPerHive*tgt + t].wen      = slave_northeast_req_wen[t]                                 ;
      assign tcdm_slave_northeast_req[NumTilesPerHive*tgt + t].wdata    = slave_northeast_req_wdata[t]                               ;
      assign tcdm_slave_northeast_req[NumTilesPerHive*tgt + t].be       = slave_northeast_req_be[t]                                  ;
      assign slave_northeast_req_ready[t]                               = tcdm_slave_northeast_req_ready[NumTilesPerHive*tgt + t]    ;
    end

    variable_latency_interconnect #(
      .NumIn            (NumTilesPerHive                           ),
      .NumOut           (NumTilesPerHive                           ),
      .AddrWidth        (TCDMAddrWidth                             ),
      .DataWidth        ($bits(tcdm_payload_t)                     ),
      .BeWidth          (DataWidth/8                               ),
      .ByteOffWidth     (0                                         ),
      .AddrMemWidth     (TCDMAddrMemWidth + $clog2(NumBanksPerTile)),
      .Topology         (tcdm_interconnect_pkg::BFLY4              ),
      .AxiVldRdy        (1'b1                                      ),
      .SpillRegisterReq (64'b10                                    ),
      .SpillRegisterResp(64'b10                                    )
    ) i_interco (
      .clk_i          (clk_i                        ),
      .rst_ni         (rst_n                        ),
      .req_valid_i    (master_northeast_req_valid   ),
      .req_ready_o    (master_northeast_req_ready   ),
      .req_tgt_addr_i (master_northeast_req_tgt_addr),
      .req_wen_i      (master_northeast_req_wen     ),
      .req_wdata_i    (master_northeast_req_wdata   ),
      .req_be_i       (master_northeast_req_be      ),
      .resp_valid_o   (master_northeast_resp_valid  ),
      .resp_ready_i   (master_northeast_resp_ready  ),
      .resp_rdata_o   (master_northeast_resp_rdata  ),
      .resp_ini_addr_i(slave_northeast_resp_ini_addr),
      .resp_rdata_i   (slave_northeast_resp_rdata   ),
      .resp_valid_i   (slave_northeast_resp_valid   ),
      .resp_ready_o   (slave_northeast_resp_ready   ),
      .req_valid_o    (slave_northeast_req_valid    ),
      .req_ready_i    (slave_northeast_req_ready    ),
      .req_be_o       (slave_northeast_req_be       ),
      .req_wdata_o    (slave_northeast_req_wdata    ),
      .req_wen_o      (slave_northeast_req_wen      ),
      .req_ini_addr_o (slave_northeast_req_ini_addr ),
      .req_tgt_addr_o (slave_northeast_req_tgt_addr )
    );
  end

  /****************
   *  Assertions  *
   ****************/

  if (NumCores > 1024)
    $fatal(1, "[mempool] MemPool is currently limited to 1024 cores.");

  if (NumTiles <= 1)
    $fatal(1, "[mempool] MemPool requires at least two tiles.");

  if (NumCores != NumTiles * NumCoresPerTile)
    $fatal(1, "[mempool] The number of cores is not divisible by the number of cores per tile.");

  if (BankingFactor < 1)
    $fatal(1, "[mempool] The banking factor must be a positive integer.");

  if (BankingFactor != 2**$clog2(BankingFactor))
    $fatal(1, "[mempool] The banking factor must be a power of two.");

  if (NumHives != 4)
    $fatal(1, "[mempool] This version of the MemPool cluster only works with four hives.");

endmodule : mempool
