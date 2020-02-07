// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
//         Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
// Date: 16.01.2020
// Description: Full crossbar with variable memory access latency.

module numa_xbar #(
    parameter int unsigned NumIn         = 4   , // number of requestors
    parameter int unsigned NumOut        = 4   , // number of targets
    parameter int unsigned ReqDataWidth  = 32  , // word width of data
    parameter int unsigned RespDataWidth = 32  , // word width of data
    parameter bit BroadCastOn            = 1'b0, // perform broadcast
    parameter bit ExtPrio                = 1'b0  // use external arbiter priority flags
  ) (
    input  logic                                 clk_i,
    input  logic                                 rst_ni,
    input  logic [NumOut-1:0][$clog2(NumIn)-1:0] rr_i,     // External priority signal
    input  logic [NumIn-1:0][$clog2(NumOut)-1:0] rr_ret_i, // External priority signal (return path)
    // Master side
    input  logic [NumIn-1:0]                     req_i,    // Request signal
    output logic [NumIn-1:0]                     gnt_o,    // Grant signal
    input  logic [NumIn-1:0][$clog2(NumOut)-1:0] add_i,    // Bank address
    input  logic [NumIn-1:0][ReqDataWidth-1:0]   wdata_i,  // Write data
    output logic [NumIn-1:0]                     vld_o,    // Response valid
    input  logic [NumIn-1:0]                     rdy_i,    // Response ready
    output logic [NumIn-1:0][RespDataWidth-1:0]  rdata_o,  // Data response (for load commands)
    // slave side
    output logic [NumOut-1:0]                    req_o,    // Request signal
    output logic [NumOut-1:0][$clog2(NumIn)-1:0] idx_o,    // Master address
    input  logic [NumOut-1:0]                    gnt_i,    // Grant signal
    output logic [NumOut-1:0][ReqDataWidth-1:0]  wdata_o,  // Write data
    input  logic [NumOut-1:0]                    vld_i,    // Response valid
    output logic [NumOut-1:0]                    rdy_o,    // Response ready
    input  logic [NumOut-1:0][$clog2(NumIn)-1:0] idx_i,    // Master address
    input  logic [NumOut-1:0][RespDataWidth-1:0] rdata_i   // Data response (for load commands)
  );

  /***********
   *   XBAR  *
   ***********/

  // Instantiate a unidirectional crossbar for the requests and one for the responses.

  unidirectional_xbar #(
    .NumIn      ( NumIn        ),
    .NumOut     ( NumOut       ),
    .DataWidth  ( ReqDataWidth ),
    .ExtPrio    ( ExtPrio      ),
    .BroadCastOn( BroadCastOn  )
  ) req_xbar (
    .clk_i  ( clk_i   ),
    .rst_ni ( rst_ni  ),
    .rr_i   ( rr_i    ),
    .req_i  ( req_i   ),
    .gnt_o  ( gnt_o   ),
    .add_i  ( add_i   ),
    .wdata_i( wdata_i ),
    .req_o  ( req_o   ),
    .idx_o  ( idx_o   ),
    .gnt_i  ( gnt_i   ),
    .wdata_o( wdata_o )
  );

  unidirectional_xbar #(
    .NumIn      ( NumOut        ),
    .NumOut     ( NumIn         ),
    .DataWidth  ( RespDataWidth ),
    .ExtPrio    ( ExtPrio       ),
    .BroadCastOn( 1'b0          )
  ) resp_xbar (
    .clk_i  ( clk_i    ),
    .rst_ni ( rst_ni   ),
    .rr_i   ( rr_ret_i ),
    .req_i  ( vld_i    ),
    .gnt_o  ( rdy_o    ),
    .add_i  ( idx_i    ),
    .wdata_i( rdata_i  ),
    .req_o  ( vld_o    ),
    .idx_o  (          ), // Unused
    .gnt_i  ( rdy_i    ),
    .wdata_o( rdata_o  )
  );

  /******************
   *   ASSERTIONS   *
   ******************/

  `ifndef SYNTHESIS
  initial begin
    assert (NumIn > 0) else
      $fatal(1, "NumIn needs to be larger than 0.");
    assert (NumOut > 0) else
      $fatal(1, "NumOut needs to be larger than 0.");
  end
  `endif

endmodule : numa_xbar
