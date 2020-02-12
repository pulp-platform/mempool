// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
//         Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich

// Date: 16.01.2020

// Description: Full-duplex crossbar, capable of handling a variable
// memory access latency.

module full_duplex_xbar #(
    parameter int unsigned NumIn         = 4  , // Number of Initiators
    parameter int unsigned NumOut        = 4  , // Number of Targets
    parameter int unsigned ReqDataWidth  = 32 , // Request Data Width
    parameter int unsigned RespDataWidth = 32 , // Response Data Width
    parameter bit ExtPrio                = 1'b0 // Use external arbiter priority flags
  ) (
    input  logic                                 clk_i,
    input  logic                                 rst_ni,
    // External priority signals
    input  logic [NumOut-1:0][$clog2(NumIn)-1:0] req_rr_i,
    input  logic [NumIn-1:0][$clog2(NumOut)-1:0] resp_rr_i,
    // Initiator side
    input  logic [NumIn-1:0]                     req_i,     // Request signal
    output logic [NumIn-1:0]                     gnt_o,     // Grant signal
    input  logic [NumIn-1:0][$clog2(NumOut)-1:0] add_i,     // Target address
    input  logic [NumIn-1:0][ReqDataWidth-1:0]   wdata_i,   // Write data
    output logic [NumIn-1:0]                     vld_o,     // Response valid
    input  logic [NumIn-1:0]                     rdy_i,     // Response ready
    output logic [NumIn-1:0][RespDataWidth-1:0]  rdata_o,   // Data response (for load commands)
    // Target side
    output logic [NumOut-1:0]                    req_o,     // Request signal
    output logic [NumOut-1:0][$clog2(NumIn)-1:0] ini_add_o, // Initiador address
    input  logic [NumOut-1:0]                    gnt_i,     // Grant signal
    output logic [NumOut-1:0][ReqDataWidth-1:0]  wdata_o,   // Write data
    input  logic [NumOut-1:0]                    vld_i,     // Response valid
    output logic [NumOut-1:0]                    rdy_o,     // Response ready
    input  logic [NumOut-1:0][$clog2(NumIn)-1:0] ini_add_i, // Initiator address (response path)
    input  logic [NumOut-1:0][RespDataWidth-1:0] rdata_i    // Data response (for load commands)
  );

  /****************
   *   Crossbars  *
   ****************/

  // Instantiate two simplex crossbars, one for the requests and one for the responses.

  simplex_xbar #(
    .NumIn    (NumIn       ),
    .NumOut   (NumOut      ),
    .DataWidth(ReqDataWidth),
    .ExtPrio  (ExtPrio     )
  ) req_xbar (
    .clk_i    (clk_i    ),
    .rst_ni   (rst_ni   ),
    .rr_i     (req_rr_i ),
    .req_i    (req_i    ),
    .gnt_o    (gnt_o    ),
    .add_i    (add_i    ),
    .wdata_i  (wdata_i  ),
    .req_o    (req_o    ),
    .ini_add_o(ini_add_o),
    .gnt_i    (gnt_i    ),
    .wdata_o  (wdata_o  )
  );

  simplex_xbar #(
    .NumIn    (NumOut       ),
    .NumOut   (NumIn        ),
    .DataWidth(RespDataWidth),
    .ExtPrio  (ExtPrio      )
  ) resp_xbar (
    .clk_i    (clk_i       ),
    .rst_ni   (rst_ni      ),
    .rr_i     (resp_rr_i   ),
    .req_i    (vld_i       ),
    .gnt_o    (rdy_o       ),
    .add_i    (ini_add_i   ),
    .wdata_i  (rdata_i     ),
    .req_o    (vld_o       ),
    .ini_add_o(/* Unused */),
    .gnt_i    (rdy_i       ),
    .wdata_o  (rdata_o     )
  );

  /******************
   *   Assertions   *
   ******************/

  if (NumIn <= 0)
    $fatal(1, "[full_duplex_xbar] NumIn needs to be larger than 0.");

  if (NumOut <= 0)
    $fatal(1, "[full_duplex_xbar] NumOut needs to be larger than 0.");

endmodule : full_duplex_xbar
