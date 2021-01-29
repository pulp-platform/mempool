// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.


module mempool_wrap
  import mempool_pkg::*;
#(
  parameter int unsigned NumCores      = 1,
  parameter int unsigned BankingFactor = 1,
  // TCDM
  parameter addr_t       TCDMBaseAddr  = 32'b0000_0000,
  // Boot address
  parameter logic [31:0] BootAddr      = 32'h0000_0000,
  // Dependant parameters. DO NOT CHANGE!
  parameter int unsigned NumTiles      = NumCores / NumCoresPerTile,
  parameter int unsigned NumAXIMasters = NumTiles
) (
  // Clock and reset
  input  logic                               clk_i,
  input  logic                               rst_ni,
  input  logic                               testmode_i,
  // Scan chain
  input  logic                               scan_enable_i,
  input  logic                               scan_data_i,
  output logic                               scan_data_o,
  // Wake up signal
  input  logic           [NumCores-1:0]      wake_up_i,
  // AXI Interface
  output axi_tile_req_t  [NumAXIMasters-1:0] axi_mst_req_o,
  input  axi_tile_resp_t [NumAXIMasters-1:0] axi_mst_resp_i
);

  /*********************
   *  MemPool Cluster  *
   *********************/

  mempool #(
    .NumCores      (NumCores      ),
    .BankingFactor (BankingFactor ),
    .TCDMBaseAddr  (TCDMBaseAddr  ),
    .BootAddr      (BootAddr      )
  ) i_mempool (
    .clk_i         (clk_i         ),
    .rst_ni        (rst_ni        ),
    .testmode_i    (testmode_i    ),
    .scan_enable_i (scan_enable_i ),
    .scan_data_i   (scan_data_i   ),
    .scan_data_o   (scan_data_o   ),
    .wake_up_i     ('0            ),
    .axi_mst_req_o (axi_mst_req_o ),
    .axi_mst_resp_i(axi_mst_resp_i)
  );

endmodule : mempool_wrap
