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
    input  logic clk_i,
    input  logic rst_ni,
    input  logic testmode_i,
    // Scan chain
    input  logic scan_enable_i,
    input  logic scan_data_i,
    output logic scan_data_o
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
   *  Hives  *
   ***********/

  // TCDM interfaces
  // North
  tcdm_slave_req_t   [NumHives-1:0][NumTilesPerHive-1:0] tcdm_master_north_req;
  logic              [NumHives-1:0][NumTilesPerHive-1:0] tcdm_master_north_req_valid;
  logic              [NumHives-1:0][NumTilesPerHive-1:0] tcdm_master_north_req_ready;
  tcdm_master_resp_t [NumHives-1:0][NumTilesPerHive-1:0] tcdm_master_north_resp;
  logic              [NumHives-1:0][NumTilesPerHive-1:0] tcdm_master_north_resp_valid;
  logic              [NumHives-1:0][NumTilesPerHive-1:0] tcdm_master_north_resp_ready;
  tcdm_slave_req_t   [NumHives-1:0][NumTilesPerHive-1:0] tcdm_slave_north_req;
  logic              [NumHives-1:0][NumTilesPerHive-1:0] tcdm_slave_north_req_valid;
  logic              [NumHives-1:0][NumTilesPerHive-1:0] tcdm_slave_north_req_ready;
  tcdm_master_resp_t [NumHives-1:0][NumTilesPerHive-1:0] tcdm_slave_north_resp;
  logic              [NumHives-1:0][NumTilesPerHive-1:0] tcdm_slave_north_resp_valid;
  logic              [NumHives-1:0][NumTilesPerHive-1:0] tcdm_slave_north_resp_ready;
  // East
  tcdm_slave_req_t   [NumHives-1:0][NumTilesPerHive-1:0] tcdm_master_east_req;
  logic              [NumHives-1:0][NumTilesPerHive-1:0] tcdm_master_east_req_valid;
  logic              [NumHives-1:0][NumTilesPerHive-1:0] tcdm_master_east_req_ready;
  tcdm_master_resp_t [NumHives-1:0][NumTilesPerHive-1:0] tcdm_master_east_resp;
  logic              [NumHives-1:0][NumTilesPerHive-1:0] tcdm_master_east_resp_valid;
  logic              [NumHives-1:0][NumTilesPerHive-1:0] tcdm_master_east_resp_ready;
  tcdm_slave_req_t   [NumHives-1:0][NumTilesPerHive-1:0] tcdm_slave_east_req;
  logic              [NumHives-1:0][NumTilesPerHive-1:0] tcdm_slave_east_req_valid;
  logic              [NumHives-1:0][NumTilesPerHive-1:0] tcdm_slave_east_req_ready;
  tcdm_master_resp_t [NumHives-1:0][NumTilesPerHive-1:0] tcdm_slave_east_resp;
  logic              [NumHives-1:0][NumTilesPerHive-1:0] tcdm_slave_east_resp_valid;
  logic              [NumHives-1:0][NumTilesPerHive-1:0] tcdm_slave_east_resp_ready;
  // Northeast
  tcdm_slave_req_t   [NumHives-1:0][NumTilesPerHive-1:0] tcdm_master_northeast_req;
  logic              [NumHives-1:0][NumTilesPerHive-1:0] tcdm_master_northeast_req_valid;
  logic              [NumHives-1:0][NumTilesPerHive-1:0] tcdm_master_northeast_req_ready;
  tcdm_master_resp_t [NumHives-1:0][NumTilesPerHive-1:0] tcdm_master_northeast_resp;
  logic              [NumHives-1:0][NumTilesPerHive-1:0] tcdm_master_northeast_resp_valid;
  logic              [NumHives-1:0][NumTilesPerHive-1:0] tcdm_master_northeast_resp_ready;
  tcdm_slave_req_t   [NumHives-1:0][NumTilesPerHive-1:0] tcdm_slave_northeast_req;
  logic              [NumHives-1:0][NumTilesPerHive-1:0] tcdm_slave_northeast_req_valid;
  logic              [NumHives-1:0][NumTilesPerHive-1:0] tcdm_slave_northeast_req_ready;
  tcdm_master_resp_t [NumHives-1:0][NumTilesPerHive-1:0] tcdm_slave_northeast_resp;
  logic              [NumHives-1:0][NumTilesPerHive-1:0] tcdm_slave_northeast_resp_valid;
  logic              [NumHives-1:0][NumTilesPerHive-1:0] tcdm_slave_northeast_resp_ready;

  for (genvar h = 0; unsigned'(h) < NumHives; h++) begin: gen_hives
    mempool_hive #(
      .NumBanksPerTile   (NumBanksPerTile   ),
      .NumTiles          (NumTiles          ),
      .NumHives          (NumHives          ),
      .NumBanks          (NumBanks          ),
      .TCDMBaseAddr      (TCDMBaseAddr      ),
      .BootAddr          (BootAddr          ),
      .tcdm_master_req_t (tcdm_master_req_t ),
      .tcdm_master_resp_t(tcdm_master_resp_t),
      .tcdm_slave_req_t  (tcdm_slave_req_t  ),
      .tcdm_slave_resp_t (tcdm_slave_resp_t )
    ) i_hive (
      .clk_i                             (clk_i                               ),
      .rst_ni                            (rst_n                               ),
      .scan_enable_i                     (scan_enable_i                       ),
      .scan_data_i                       (/* Unconnected */                   ),
      .scan_data_o                       (/* Unconnected */                   ),
      .hive_id_i                         (h[$clog2(NumHives)-1:0]             ),
      // TCDM Master interfaces
      .tcdm_master_north_req_o           (tcdm_master_north_req[h]            ),
      .tcdm_master_north_req_valid_o     (tcdm_master_north_req_valid[h]      ),
      .tcdm_master_north_req_ready_i     (tcdm_master_north_req_ready[h]      ),
      .tcdm_master_north_resp_i          (tcdm_master_north_resp[h]           ),
      .tcdm_master_north_resp_valid_i    (tcdm_master_north_resp_valid[h]     ),
      .tcdm_master_north_resp_ready_o    (tcdm_master_north_resp_ready[h]     ),
      .tcdm_master_east_req_o            (tcdm_master_east_req[h]             ),
      .tcdm_master_east_req_valid_o      (tcdm_master_east_req_valid[h]       ),
      .tcdm_master_east_req_ready_i      (tcdm_master_east_req_ready[h]       ),
      .tcdm_master_east_resp_i           (tcdm_master_east_resp[h]            ),
      .tcdm_master_east_resp_valid_i     (tcdm_master_east_resp_valid[h]      ),
      .tcdm_master_east_resp_ready_o     (tcdm_master_east_resp_ready[h]      ),
      .tcdm_master_northeast_req_o       (tcdm_master_northeast_req[h]        ),
      .tcdm_master_northeast_req_valid_o (tcdm_master_northeast_req_valid[h]  ),
      .tcdm_master_northeast_req_ready_i (tcdm_master_northeast_req_ready[h]  ),
      .tcdm_master_northeast_resp_i      (tcdm_master_northeast_resp[h]       ),
      .tcdm_master_northeast_resp_valid_i(tcdm_master_northeast_resp_valid[h] ),
      .tcdm_master_northeast_resp_ready_o(tcdm_master_northeast_resp_ready[h] ),
      // TCDM banks interface
      .tcdm_slave_north_req_i            (tcdm_slave_north_req[h]             ),
      .tcdm_slave_north_req_valid_i      (tcdm_slave_north_req_valid[h]       ),
      .tcdm_slave_north_req_ready_o      (tcdm_slave_north_req_ready[h]       ),
      .tcdm_slave_north_resp_o           (tcdm_slave_north_resp[h]            ),
      .tcdm_slave_north_resp_valid_o     (tcdm_slave_north_resp_valid[h]      ),
      .tcdm_slave_north_resp_ready_i     (tcdm_slave_north_resp_ready[h]      ),
      .tcdm_slave_east_req_i             (tcdm_slave_east_req[h]              ),
      .tcdm_slave_east_req_valid_i       (tcdm_slave_east_req_valid[h]        ),
      .tcdm_slave_east_req_ready_o       (tcdm_slave_east_req_ready[h]        ),
      .tcdm_slave_east_resp_o            (tcdm_slave_east_resp[h]             ),
      .tcdm_slave_east_resp_valid_o      (tcdm_slave_east_resp_valid[h]       ),
      .tcdm_slave_east_resp_ready_i      (tcdm_slave_east_resp_ready[h]       ),
      .tcdm_slave_northeast_req_i        (tcdm_slave_northeast_req[h]         ),
      .tcdm_slave_northeast_req_valid_i  (tcdm_slave_northeast_req_valid[h]   ),
      .tcdm_slave_northeast_req_ready_o  (tcdm_slave_northeast_req_ready[h]   ),
      .tcdm_slave_northeast_resp_o       (tcdm_slave_northeast_resp[h]        ),
      .tcdm_slave_northeast_resp_valid_o (tcdm_slave_northeast_resp_valid[h]  ),
      .tcdm_slave_northeast_resp_ready_i (tcdm_slave_northeast_resp_ready[h]  )
    );
  end : gen_hives

  /*******************
   *  Interconnects  *
   *******************/

  for (genvar ini = 0; ini < NumHives; ini++) begin: gen_interconnections
    // East
    assign tcdm_slave_east_req[ini ^ 2'b01]       = tcdm_master_east_req[ini]              ;
    assign tcdm_slave_east_req_valid[ini ^ 2'b01] = tcdm_master_east_req_valid[ini]        ;
    assign tcdm_master_east_req_ready[ini]        = tcdm_slave_east_req_ready[ini ^ 2'b01] ;

    assign tcdm_master_east_resp[ini ^ 2'b01]       = tcdm_slave_east_resp[ini]               ;
    assign tcdm_master_east_resp_valid[ini ^ 2'b01] = tcdm_slave_east_resp_valid[ini]         ;
    assign tcdm_slave_east_resp_ready[ini]          = tcdm_master_east_resp_ready[ini ^ 2'b01];

    // Northeast
    assign tcdm_slave_northeast_req[ini ^ 2'b11]       = tcdm_master_northeast_req[ini]             ;
    assign tcdm_slave_northeast_req_valid[ini ^ 2'b11] = tcdm_master_northeast_req_valid[ini]       ;
    assign tcdm_master_northeast_req_ready[ini]        = tcdm_slave_northeast_req_ready[ini ^ 2'b11];

    assign tcdm_master_northeast_resp[ini ^ 2'b11]       = tcdm_slave_northeast_resp[ini]               ;
    assign tcdm_master_northeast_resp_valid[ini ^ 2'b11] = tcdm_slave_northeast_resp_valid[ini]         ;
    assign tcdm_slave_northeast_resp_ready[ini]          = tcdm_master_northeast_resp_ready[ini ^ 2'b11];

    // North
    assign tcdm_slave_north_req[ini ^ 2'b10]       = tcdm_master_north_req[ini]             ;
    assign tcdm_slave_north_req_valid[ini ^ 2'b10] = tcdm_master_north_req_valid[ini]       ;
    assign tcdm_master_north_req_ready[ini]        = tcdm_slave_north_req_ready[ini ^ 2'b10];

    assign tcdm_master_north_resp[ini ^ 2'b10]       = tcdm_slave_north_resp[ini]               ;
    assign tcdm_master_north_resp_valid[ini ^ 2'b10] = tcdm_slave_north_resp_valid[ini]         ;
    assign tcdm_slave_north_resp_ready[ini]          = tcdm_master_north_resp_ready[ini ^ 2'b10];
  end: gen_interconnections

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
