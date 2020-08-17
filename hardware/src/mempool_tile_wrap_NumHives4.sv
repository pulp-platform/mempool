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

module mempool_tile_wrap_NumHives4 #(
    parameter int unsigned NumBanksPerTile = 1     ,
    parameter int unsigned NumTiles        = 1     ,
    parameter int unsigned NumBanks        = 1     ,
    // TCDM
    parameter addr_t TCDMBaseAddr          = 32'b0 ,
    parameter type tcdm_master_req_t       = logic ,
    parameter type tcdm_master_resp_t      = logic ,
    parameter type tcdm_slave_req_t        = logic ,
    parameter type tcdm_slave_resp_t       = logic ,
    // Boot address
    parameter logic [31:0] BootAddr = 32'h0000_1000 ,
    // Instruction cache
    parameter int unsigned ICacheSizeByte  = 512 * NumCoresPerTile, // Total Size of instruction cache in bytes
    parameter int unsigned ICacheSets      = NumCoresPerTile      , // Number of sets
    parameter int unsigned ICacheLineWidth = 32 * NumCoresPerTile   // Size of each cache line in bits
  ) (
    // Clock and reset
    input  logic                                     clk_i,
    input  logic                                     rst_ni,
    // Scan chain
    input  logic                                     scan_enable_i,
    input  logic                                     scan_data_i,
    output logic                                     scan_data_o,
    // Tile ID
    input  logic              [$clog2(NumTiles)-1:0] tile_id_i,
    // TCDM Master interfaces
    output tcdm_master_req_t                         tcdm_master_north_req_o,
    output logic                                     tcdm_master_north_req_valid_o,
    input  logic                                     tcdm_master_north_req_ready_i,
    input  tcdm_master_resp_t                        tcdm_master_north_resp_i,
    input  logic                                     tcdm_master_north_resp_valid_i,
    output logic                                     tcdm_master_north_resp_ready_o,
    output tcdm_master_req_t                         tcdm_master_northeast_req_o,
    output logic                                     tcdm_master_northeast_req_valid_o,
    input  logic                                     tcdm_master_northeast_req_ready_i,
    input  tcdm_master_resp_t                        tcdm_master_northeast_resp_i,
    input  logic                                     tcdm_master_northeast_resp_valid_i,
    output logic                                     tcdm_master_northeast_resp_ready_o,
    output tcdm_master_req_t                         tcdm_master_east_req_o,
    output logic                                     tcdm_master_east_req_valid_o,
    input  logic                                     tcdm_master_east_req_ready_i,
    input  tcdm_master_resp_t                        tcdm_master_east_resp_i,
    input  logic                                     tcdm_master_east_resp_valid_i,
    output logic                                     tcdm_master_east_resp_ready_o,
    output tcdm_master_req_t                         tcdm_master_center_req_o,
    output logic                                     tcdm_master_center_req_valid_o,
    input  logic                                     tcdm_master_center_req_ready_i,
    input  tcdm_master_resp_t                        tcdm_master_center_resp_i,
    input  logic                                     tcdm_master_center_resp_valid_i,
    output logic                                     tcdm_master_center_resp_ready_o,
    // TCDM Slave interfaces
    input  tcdm_slave_req_t                          tcdm_slave_north_req_i,
    input  logic                                     tcdm_slave_north_req_valid_i,
    output logic                                     tcdm_slave_north_req_ready_o,
    output tcdm_slave_resp_t                         tcdm_slave_north_resp_o,
    output logic                                     tcdm_slave_north_resp_valid_o,
    input  logic                                     tcdm_slave_north_resp_ready_i,
    input  tcdm_slave_req_t                          tcdm_slave_northeast_req_i,
    input  logic                                     tcdm_slave_northeast_req_valid_i,
    output logic                                     tcdm_slave_northeast_req_ready_o,
    output tcdm_slave_resp_t                         tcdm_slave_northeast_resp_o,
    output logic                                     tcdm_slave_northeast_resp_valid_o,
    input  logic                                     tcdm_slave_northeast_resp_ready_i,
    input  tcdm_slave_req_t                          tcdm_slave_east_req_i,
    input  logic                                     tcdm_slave_east_req_valid_i,
    output logic                                     tcdm_slave_east_req_ready_o,
    output tcdm_slave_resp_t                         tcdm_slave_east_resp_o,
    output logic                                     tcdm_slave_east_resp_valid_o,
    input  logic                                     tcdm_slave_east_resp_ready_i,
    input  tcdm_slave_req_t                          tcdm_slave_center_req_i,
    input  logic                                     tcdm_slave_center_req_valid_i,
    output logic                                     tcdm_slave_center_req_ready_o,
    output tcdm_slave_resp_t                         tcdm_slave_center_resp_o,
    output logic                                     tcdm_slave_center_resp_valid_o,
    input  logic                                     tcdm_slave_center_resp_ready_i,
    // AXI Interface
    output axi_req_t                                 axi_mst_req_o ,
    input  axi_resp_t                                axi_mst_resp_i ,
    // Instruction interface
    output addr_t                                    refill_qaddr_o ,
    output logic              [7:0]                  refill_qlen_o ,                    // AXI signal
    output logic                                     refill_qvalid_o ,
    input  logic                                     refill_qready_i ,
    input  logic              [ICacheLineWidth-1:0]  refill_pdata_i ,
    input  logic                                     refill_perror_i ,
    input  logic                                     refill_pvalid_i ,
    input  logic                                     refill_plast_i ,
    output logic                                     refill_pready_o
  );

  /*****************
   *  Definitions  *
   *****************/

  localparam NumHives = 4;

  /**********
   *  Tile  *
   **********/

  mempool_tile #(
    .NumBanksPerTile   (NumBanksPerTile   ),
    .NumTiles          (NumTiles          ),
    .NumHives          (NumHives          ),
    .NumBanks          (NumBanks          ),
    .TCDMBaseAddr      (TCDMBaseAddr      ),
    .BootAddr          (BootAddr          ),
    .ICacheSizeByte    (ICacheSizeByte    ),
    .ICacheSets        (ICacheSets        ),
    .ICacheLineWidth   (ICacheLineWidth   ),
    .tcdm_master_req_t (tcdm_master_req_t ),
    .tcdm_master_resp_t(tcdm_master_resp_t),
    .tcdm_slave_req_t  (tcdm_slave_req_t  ),
    .tcdm_slave_resp_t (tcdm_slave_resp_t )
  ) i_tile (
    .clk_i                   (clk_i                                                                                                                               ),
    .rst_ni                  (rst_ni                                                                                                                              ),
    .tile_id_i               (tile_id_i                                                                                                                           ),
    // Scan chain
    .scan_enable_i           (scan_enable_i                                                                                                                       ),
    .scan_data_i             (scan_data_i                                                                                                                         ),
    .scan_data_o             (scan_data_o                                                                                                                         ),
    // TCDM Master
    .tcdm_master_req_o       ({tcdm_master_northeast_req_o, tcdm_master_north_req_o, tcdm_master_east_req_o, tcdm_master_center_req_o}                            ),
    .tcdm_master_req_ready_i ({tcdm_master_northeast_req_ready_i, tcdm_master_north_req_ready_i, tcdm_master_east_req_ready_i, tcdm_master_center_req_ready_i}    ),
    .tcdm_master_req_valid_o ({tcdm_master_northeast_req_valid_o, tcdm_master_north_req_valid_o, tcdm_master_east_req_valid_o, tcdm_master_center_req_valid_o}    ),
    .tcdm_master_resp_i      ({tcdm_master_northeast_resp_i, tcdm_master_north_resp_i, tcdm_master_east_resp_i, tcdm_master_center_resp_i}                        ),
    .tcdm_master_resp_ready_o({tcdm_master_northeast_resp_ready_o, tcdm_master_north_resp_ready_o, tcdm_master_east_resp_ready_o, tcdm_master_center_resp_ready_o}),
    .tcdm_master_resp_valid_i({tcdm_master_northeast_resp_valid_i, tcdm_master_north_resp_valid_i, tcdm_master_east_resp_valid_i, tcdm_master_center_resp_valid_i}),
    // TCDM Slave
    .tcdm_slave_req_i        ({tcdm_slave_northeast_req_i, tcdm_slave_north_req_i, tcdm_slave_east_req_i, tcdm_slave_center_req_i}                                ),
    .tcdm_slave_req_ready_o  ({tcdm_slave_northeast_req_ready_o, tcdm_slave_north_req_ready_o, tcdm_slave_east_req_ready_o, tcdm_slave_center_req_ready_o}        ),
    .tcdm_slave_req_valid_i  ({tcdm_slave_northeast_req_valid_i, tcdm_slave_north_req_valid_i, tcdm_slave_east_req_valid_i, tcdm_slave_center_req_valid_i}        ),
    .tcdm_slave_resp_o       ({tcdm_slave_northeast_resp_o, tcdm_slave_north_resp_o, tcdm_slave_east_resp_o, tcdm_slave_center_resp_o}                            ),
    .tcdm_slave_resp_ready_i ({tcdm_slave_northeast_resp_ready_i, tcdm_slave_north_resp_ready_i, tcdm_slave_east_resp_ready_i, tcdm_slave_center_resp_ready_i}    ),
    .tcdm_slave_resp_valid_o ({tcdm_slave_northeast_resp_valid_o, tcdm_slave_north_resp_valid_o, tcdm_slave_east_resp_valid_o, tcdm_slave_center_resp_valid_o}    ),
    // AXI interface
    .axi_mst_req_o           (axi_mst_req_o                                                                                                                       ),
    .axi_mst_resp_i          (axi_mst_resp_i                                                                                                                      ),
    // Instruction interface
    .refill_qaddr_o          (refill_qaddr_o                                                                                                                      ),
    .refill_qlen_o           (refill_qlen_o                                                                                                                       ),
    .refill_qvalid_o         (refill_qvalid_o                                                                                                                     ),
    .refill_qready_i         (refill_qready_i                                                                                                                     ),
    .refill_pdata_i          (refill_pdata_i                                                                                                                      ),
    .refill_perror_i         (refill_perror_i                                                                                                                     ),
    .refill_pvalid_i         (refill_pvalid_i                                                                                                                     ),
    .refill_plast_i          (refill_plast_i                                                                                                                      ),
    .refill_pready_o         (refill_pready_o                                                                                                                     )
  );

endmodule: mempool_tile_wrap_NumHives4
