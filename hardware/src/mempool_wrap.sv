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

module mempool_wrap #(
    parameter int unsigned NumCores        = 1             ,
    parameter int unsigned NumCoresPerTile = 1             ,
    parameter int unsigned BankingFactor   = 1             ,
    // TCDM
    parameter addr_t TCDMBaseAddr          = 32'b0         ,
    parameter int unsigned TCDMSizePerBank = 1024 /* [B] */,
    // Boot address
    parameter logic [31:0] BootAddr        = 32'h0000_0000 ,
    // Dependent parameters. DO NOT CHANGE!
    parameter int unsigned NumTiles        = NumCores / NumCoresPerTile
  ) (
    // Clock and reset
    input  logic clk_i,
    input  logic rst_ni,
    // Scan chain
    input  logic scan_enable_i,
    input  logic scan_data_i,
    output logic scan_data_o
  );

  /*********
   *  AXI  *
   *********/

  `include "axi/assign.svh"
  `include "axi/typedef.svh"

  localparam AxiMstIdWidth = $clog2(NumCoresPerTile);

  typedef logic [AxiMstIdWidth-1:0] axi_mst_id_t;

  `AXI_TYPEDEF_AW_CHAN_T(axi_aw_t, addr_t, axi_mst_id_t, logic);
  `AXI_TYPEDEF_W_CHAN_T(axi_w_t, data_t, strb_t, logic)        ;
  `AXI_TYPEDEF_B_CHAN_T(axi_b_t, axi_mst_id_t, logic)          ;
  `AXI_TYPEDEF_AR_CHAN_T(axi_ar_t, addr_t, axi_mst_id_t, logic);
  `AXI_TYPEDEF_R_CHAN_T(axi_r_t, data_t, axi_mst_id_t, logic)  ;
  `AXI_TYPEDEF_REQ_T(axi_req_t, axi_aw_t, axi_w_t, axi_ar_t)   ;
  `AXI_TYPEDEF_RESP_T(axi_resp_t, axi_b_t, axi_r_t )           ;

  axi_req_t  [NumTiles-1:0] axi_mst_req;
  axi_resp_t [NumTiles-1:0] axi_mst_resp;

  /*********************
   *  MemPool Cluster  *
   *********************/

  mempool #(
    .NumCores       (NumCores       ),
    .NumCoresPerTile(NumCoresPerTile),
    .BankingFactor  (BankingFactor  ),
    .TCDMBaseAddr   (TCDMBaseAddr   ),
    .TCDMSizePerBank(TCDMSizePerBank),
    .BootAddr       (BootAddr       ),
    // AXI
    .axi_aw_t       (axi_aw_t       ),
    .axi_w_t        (axi_w_t        ),
    .axi_b_t        (axi_b_t        ),
    .axi_ar_t       (axi_ar_t       ),
    .axi_r_t        (axi_r_t        ),
    .axi_req_t      (axi_req_t      ),
    .axi_resp_t     (axi_resp_t     )
  ) i_mempool (
    .clk_i         (clk_i        ),
    .rst_ni        (rst_ni       ),
    .scan_enable_i (scan_enable_i),
    .scan_data_i   (scan_data_i  ),
    .scan_data_o   (scan_data_o  ),
    .axi_mst_req_o (axi_mst_req  ),
    .axi_mst_resp_i(axi_mst_resp )
  );

endmodule : mempool_wrap

