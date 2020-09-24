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
    parameter int unsigned NumCores      = 1,
    parameter int unsigned BankingFactor = 1,
    // TCDM
    parameter addr_t TCDMBaseAddr        = 32'b0,
    // Boot address
    parameter logic [31:0] BootAddr      = 32'h0000_0000
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

  localparam int unsigned NumTiles         = NumCores / NumCoresPerTile;
  localparam int unsigned NumBanks         = NumCores * BankingFactor;
  localparam int unsigned NumBanksPerTile  = NumBanks / NumTiles;
  localparam int unsigned NumBanksPerGroup = NumBanks / NumGroups;
  localparam int unsigned TCDMAddrWidth    = TCDMAddrMemWidth + $clog2(NumBanksPerGroup);
  localparam int unsigned NumTilesPerGroup = NumTiles / NumGroups;

  typedef logic [$clog2(NumTiles)-1:0] tile_id_t;
  typedef logic [$clog2(NumTilesPerGroup)-1:0] tile_group_id_t;
  typedef logic [TCDMAddrMemWidth + $clog2(NumBanksPerTile)-1:0] tile_addr_t;
  typedef logic [TCDMAddrWidth-1:0] tcdm_addr_t;

  typedef struct packed {
    tcdm_payload_t wdata;
    logic wen;
    strb_t be;
    tcdm_addr_t tgt_addr;
  } tcdm_master_req_t;

  typedef struct packed {
    tcdm_payload_t rdata;
  } tcdm_master_resp_t;

  typedef struct packed {
    tcdm_payload_t wdata;
    logic wen;
    strb_t be;
    tile_addr_t tgt_addr;
    tile_group_id_t ini_addr;
  } tcdm_slave_req_t;

  typedef struct packed {
    tcdm_payload_t rdata;
    tile_group_id_t ini_addr;
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

  /************
   *  Groups  *
   ************/

  // TCDM interfaces
  // North
  tcdm_slave_req_t   [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_master_north_req;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_master_north_req_valid;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_master_north_req_ready;
  tcdm_master_resp_t [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_master_north_resp;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_master_north_resp_valid;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_master_north_resp_ready;
  tcdm_slave_req_t   [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_slave_north_req;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_slave_north_req_valid;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_slave_north_req_ready;
  tcdm_master_resp_t [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_slave_north_resp;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_slave_north_resp_valid;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_slave_north_resp_ready;
  // East
  tcdm_slave_req_t   [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_master_east_req;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_master_east_req_valid;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_master_east_req_ready;
  tcdm_master_resp_t [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_master_east_resp;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_master_east_resp_valid;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_master_east_resp_ready;
  tcdm_slave_req_t   [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_slave_east_req;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_slave_east_req_valid;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_slave_east_req_ready;
  tcdm_master_resp_t [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_slave_east_resp;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_slave_east_resp_valid;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_slave_east_resp_ready;
  // Northeast
  tcdm_slave_req_t   [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_master_northeast_req;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_master_northeast_req_valid;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_master_northeast_req_ready;
  tcdm_master_resp_t [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_master_northeast_resp;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_master_northeast_resp_valid;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_master_northeast_resp_ready;
  tcdm_slave_req_t   [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_slave_northeast_req;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_slave_northeast_req_valid;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_slave_northeast_req_ready;
  tcdm_master_resp_t [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_slave_northeast_resp;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_slave_northeast_resp_valid;
  logic              [NumGroups-1:0][NumTilesPerGroup-1:0] tcdm_slave_northeast_resp_ready;

  for (genvar g = 0; unsigned'(g) < NumGroups; g++) begin: gen_groups
    mempool_group #(
      .NumBanksPerTile   (NumBanksPerTile   ),
      .NumTiles          (NumTiles          ),
      .NumBanks          (NumBanks          ),
      .TCDMBaseAddr      (TCDMBaseAddr      ),
      .BootAddr          (BootAddr          ),
      .tcdm_master_req_t (tcdm_master_req_t ),
      .tcdm_master_resp_t(tcdm_master_resp_t),
      .tcdm_slave_req_t  (tcdm_slave_req_t  ),
      .tcdm_slave_resp_t (tcdm_slave_resp_t )
    ) i_group (
      .clk_i                             (clk_i                               ),
      .rst_ni                            (rst_n                               ),
      .scan_enable_i                     (scan_enable_i                       ),
      .scan_data_i                       (/* Unconnected */                   ),
      .scan_data_o                       (/* Unconnected */                   ),
      .group_id_i                        (g[$clog2(NumGroups)-1:0]            ),
      // TCDM Master interfaces
      .tcdm_master_north_req_o           (tcdm_master_north_req[g]            ),
      .tcdm_master_north_req_valid_o     (tcdm_master_north_req_valid[g]      ),
      .tcdm_master_north_req_ready_i     (tcdm_master_north_req_ready[g]      ),
      .tcdm_master_north_resp_i          (tcdm_master_north_resp[g]           ),
      .tcdm_master_north_resp_valid_i    (tcdm_master_north_resp_valid[g]     ),
      .tcdm_master_north_resp_ready_o    (tcdm_master_north_resp_ready[g]     ),
      .tcdm_master_east_req_o            (tcdm_master_east_req[g]             ),
      .tcdm_master_east_req_valid_o      (tcdm_master_east_req_valid[g]       ),
      .tcdm_master_east_req_ready_i      (tcdm_master_east_req_ready[g]       ),
      .tcdm_master_east_resp_i           (tcdm_master_east_resp[g]            ),
      .tcdm_master_east_resp_valid_i     (tcdm_master_east_resp_valid[g]      ),
      .tcdm_master_east_resp_ready_o     (tcdm_master_east_resp_ready[g]      ),
      .tcdm_master_northeast_req_o       (tcdm_master_northeast_req[g]        ),
      .tcdm_master_northeast_req_valid_o (tcdm_master_northeast_req_valid[g]  ),
      .tcdm_master_northeast_req_ready_i (tcdm_master_northeast_req_ready[g]  ),
      .tcdm_master_northeast_resp_i      (tcdm_master_northeast_resp[g]       ),
      .tcdm_master_northeast_resp_valid_i(tcdm_master_northeast_resp_valid[g] ),
      .tcdm_master_northeast_resp_ready_o(tcdm_master_northeast_resp_ready[g] ),
      // TCDM banks interface
      .tcdm_slave_north_req_i            (tcdm_slave_north_req[g]             ),
      .tcdm_slave_north_req_valid_i      (tcdm_slave_north_req_valid[g]       ),
      .tcdm_slave_north_req_ready_o      (tcdm_slave_north_req_ready[g]       ),
      .tcdm_slave_north_resp_o           (tcdm_slave_north_resp[g]            ),
      .tcdm_slave_north_resp_valid_o     (tcdm_slave_north_resp_valid[g]      ),
      .tcdm_slave_north_resp_ready_i     (tcdm_slave_north_resp_ready[g]      ),
      .tcdm_slave_east_req_i             (tcdm_slave_east_req[g]              ),
      .tcdm_slave_east_req_valid_i       (tcdm_slave_east_req_valid[g]        ),
      .tcdm_slave_east_req_ready_o       (tcdm_slave_east_req_ready[g]        ),
      .tcdm_slave_east_resp_o            (tcdm_slave_east_resp[g]             ),
      .tcdm_slave_east_resp_valid_o      (tcdm_slave_east_resp_valid[g]       ),
      .tcdm_slave_east_resp_ready_i      (tcdm_slave_east_resp_ready[g]       ),
      .tcdm_slave_northeast_req_i        (tcdm_slave_northeast_req[g]         ),
      .tcdm_slave_northeast_req_valid_i  (tcdm_slave_northeast_req_valid[g]   ),
      .tcdm_slave_northeast_req_ready_o  (tcdm_slave_northeast_req_ready[g]   ),
      .tcdm_slave_northeast_resp_o       (tcdm_slave_northeast_resp[g]        ),
      .tcdm_slave_northeast_resp_valid_o (tcdm_slave_northeast_resp_valid[g]  ),
      .tcdm_slave_northeast_resp_ready_i (tcdm_slave_northeast_resp_ready[g]  )
    );
  end : gen_groups

  /*******************
   *  Interconnects  *
   *******************/

  for (genvar ini = 0; ini < NumGroups; ini++) begin: gen_interconnections
    // East
    assign tcdm_slave_east_req[ini ^ 2'b01]       = tcdm_master_east_req[ini];
    assign tcdm_slave_east_req_valid[ini ^ 2'b01] = tcdm_master_east_req_valid[ini];
    assign tcdm_master_east_req_ready[ini]        = tcdm_slave_east_req_ready[ini ^ 2'b01];

    assign tcdm_master_east_resp[ini ^ 2'b01]       = tcdm_slave_east_resp[ini];
    assign tcdm_master_east_resp_valid[ini ^ 2'b01] = tcdm_slave_east_resp_valid[ini];
    assign tcdm_slave_east_resp_ready[ini]          = tcdm_master_east_resp_ready[ini ^ 2'b01];

    // Northeast
    assign tcdm_slave_northeast_req[ini ^ 2'b11]       = tcdm_master_northeast_req[ini];
    assign tcdm_slave_northeast_req_valid[ini ^ 2'b11] = tcdm_master_northeast_req_valid[ini];
    assign tcdm_master_northeast_req_ready[ini]        = tcdm_slave_northeast_req_ready[ini ^ 2'b11];

    assign tcdm_master_northeast_resp[ini ^ 2'b11]       = tcdm_slave_northeast_resp[ini];
    assign tcdm_master_northeast_resp_valid[ini ^ 2'b11] = tcdm_slave_northeast_resp_valid[ini];
    assign tcdm_slave_northeast_resp_ready[ini]          = tcdm_master_northeast_resp_ready[ini ^ 2'b11];

    // North
    assign tcdm_slave_north_req[ini ^ 2'b10]       = tcdm_master_north_req[ini];
    assign tcdm_slave_north_req_valid[ini ^ 2'b10] = tcdm_master_north_req_valid[ini];
    assign tcdm_master_north_req_ready[ini]        = tcdm_slave_north_req_ready[ini ^ 2'b10];

    assign tcdm_master_north_resp[ini ^ 2'b10]       = tcdm_slave_north_resp[ini];
    assign tcdm_master_north_resp_valid[ini ^ 2'b10] = tcdm_slave_north_resp_valid[ini];
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

  if (NumGroups != 4)
    $fatal(1, "[mempool] This version of the MemPool cluster only works with four groups.");

endmodule : mempool
