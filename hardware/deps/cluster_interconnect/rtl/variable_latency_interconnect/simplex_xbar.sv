// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Authors: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>, ETH Zurich
//          Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich

// Date: 16.01.2020
// Description: Simplex (uni-directional) crossbar.

module simplex_xbar #(
    parameter int unsigned NumIn     = 4  , // Number of Initiators
    parameter int unsigned NumOut    = 4  , // Number of Targets
    parameter int unsigned DataWidth = 32 , // Data Width
    parameter bit ExtPrio            = 1'b0 // Use external arbiter priority flags
  ) (
    input  logic                                 clk_i,
    input  logic                                 rst_ni,
    // External priority signal
    input  logic [NumOut-1:0][$clog2(NumIn)-1:0] rr_i,
    // Initiator side
    input  logic [NumIn-1:0]                     req_i,     // Request signal
    output logic [NumIn-1:0]                     gnt_o,     // Grant signal
    input  logic [NumIn-1:0][$clog2(NumOut)-1:0] add_i,     // Target address
    input  logic [NumIn-1:0][DataWidth-1:0]      wdata_i,   // Write data
    // Target side
    output logic [NumOut-1:0]                    req_o,     // Request signal
    input  logic [NumOut-1:0]                    gnt_i,     // Grant signal
    output logic [NumOut-1:0][$clog2(NumIn)-1:0] ini_add_o, // Initiator address
    output logic [NumOut-1:0][DataWidth-1:0]     wdata_o    // Write data
  );

  /*************
   *   Wires   *
   *************/

  logic [NumOut-1:0][ NumIn-1:0][DataWidth-1:0] tgt_data;
  logic [ NumIn-1:0][NumOut-1:0][DataWidth-1:0] ini_data;
  logic [NumOut-1:0][ NumIn-1:0]                tgt_gnt, tgt_req;
  logic [ NumIn-1:0][NumOut-1:0]                ini_gnt, ini_req;

  /***********************
   *   Address decoder   *
   ***********************/

  for (genvar j = 0; j < NumIn; j++) begin: gen_inputs

    // Instantiate a bank address decoder for each initiator
    addr_decoder #(
      .NumOut   (NumOut   ),
      .DataWidth(DataWidth)
    ) i_addr_decoder (
      // Initiator side
      .req_i  (req_i[j]   ),
      .add_i  (add_i[j]   ),
      .data_i (wdata_i[j] ),
      .gnt_o  (gnt_o[j]   ),
      // Target side
      .req_o  (ini_req[j] ),
      .gnt_i  (ini_gnt[j] ),
      .data_o (ini_data[j])
    );

    // Reshape connections between initiator and target
    for (genvar k = 0; unsigned'(k) < NumOut; k++) begin : gen_reshape
      assign tgt_req[k][j]  = ini_req[j][k] ;
      assign ini_gnt[j][k]  = tgt_gnt[k][j] ;
      assign tgt_data[k][j] = ini_data[j][k];
    end

  end

  /****************
   *   Arbiters   *
   ****************/

  for (genvar k = 0; k < NumOut; k++) begin: gen_rr_outputs
    if (NumIn == 1) begin

      assign req_o[k]      = tgt_req[k][0] ;
      assign tgt_gnt[k][0] = gnt_i[k]      ;
      assign wdata_o[k]    = tgt_data[k][0];

    end else begin : gen_rr_arb_tree

      // Instantiate an RR arbiter for each target
      rr_arb_tree #(
        .NumIn    (NumIn    ),
        .DataWidth(DataWidth),
        .ExtPrio  (ExtPrio  )
      ) i_rr_arb_tree (
        .clk_i  (clk_i        ),
        .rst_ni (rst_ni       ),
        .flush_i(1'b0         ),
        .rr_i   (rr_i[k]      ),
        .req_i  (tgt_req[k]   ),
        .gnt_o  (tgt_gnt[k]   ),
        .data_i (tgt_data[k]  ),
        .gnt_i  (gnt_i[k]     ),
        .req_o  (req_o[k]     ),
        .data_o (wdata_o[k]   ),
        .idx_o  (ini_add_o[k] )
      );

    end
  end

  /******************
   *   Assertions   *
   ******************/

  if (NumIn <= 0)
    $fatal(1, "[simplex_xbar] NumIn needs to be larger than 0.");

  if (NumOut <= 0)
    $fatal(1, "[simplex_xbar] NumOut needs to be larger than 0.");

endmodule : simplex_xbar
