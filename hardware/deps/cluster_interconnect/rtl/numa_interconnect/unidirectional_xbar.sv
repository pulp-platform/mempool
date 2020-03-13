// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Authors: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>, ETH Zurich
//          Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
// Date: 16.01.2020
// Description: Unidirectional full crossbar.

module unidirectional_xbar #(
    parameter int unsigned NumIn     = 4   , // number of requestors
    parameter int unsigned NumOut    = 4   , // number of targets
    parameter int unsigned DataWidth = 32  , // word width of data
    parameter bit BroadCastOn        = 1'b0, // perform broadcast
    parameter bit ExtPrio            = 1'b0  // use external arbiter priority flags
  ) (
    input  logic                                 clk_i,
    input  logic                                 rst_ni,
    input  logic [NumOut-1:0][$clog2(NumIn)-1:0] rr_i,    // External priority signal
    // Master side
    input  logic [NumIn-1:0]                     req_i,   // Request signal
    output logic [NumIn-1:0]                     gnt_o,   // Grant signal
    input  logic [NumIn-1:0][$clog2(NumOut)-1:0] add_i,   // Bank address
    input  logic [NumIn-1:0][DataWidth-1:0]      wdata_i, // Write data
    // Slave side
    output logic [NumOut-1:0]                    req_o,   // Request signal
    output logic [NumOut-1:0][$clog2(NumIn)-1:0] idx_o,   // Master index
    input  logic [NumOut-1:0]                    gnt_i,   // Grant signal
    output logic [NumOut-1:0][DataWidth-1:0]     wdata_o  // Write data
  );

  /*************
   *   WIRES   *
   *************/

  logic [NumOut-1:0][ NumIn-1:0][DataWidth-1:0] sl_data;
  logic [ NumIn-1:0][NumOut-1:0][DataWidth-1:0] ma_data;
  logic [NumOut-1:0][ NumIn-1:0]                sl_gnt, sl_req;
  logic [ NumIn-1:0][NumOut-1:0]                ma_gnt, ma_req;

  /***********************
   *   ADDRESS DECODER   *
   ***********************/

  // Instantiate a bank address decoder for each master

  for (genvar j = 0; j < NumIn; j++) begin : gen_inputs
    addr_dec_resp_mux #(
      .NumOut       ( NumOut      ),
      .ReqDataWidth ( DataWidth   ),
      .BroadCastOn  ( BroadCastOn )
    ) i_addr_dec_resp_mux (
      .clk_i  ( clk_i      ),
      .rst_ni ( rst_ni     ),
      .req_i  ( req_i[j]   ),
      .add_i  ( add_i[j]   ),
      .wen_i  ( '0         ), // unused
      .data_i ( wdata_i[j] ),
      .gnt_o  ( gnt_o[j]   ),
      .vld_o  (            ), // unused
      .rdata_o(            ), // unused
      .req_o  ( ma_req[j]  ),
      .gnt_i  ( ma_gnt[j]  ),
      .data_o ( ma_data[j] ),
      .rdata_i( 'X         )  // unused
    );

    // Reshape connections between master and slave

    for (genvar k = 0; unsigned'(k) < NumOut; k++) begin : gen_reshape
      assign sl_req[k][j]  = ma_req[j][k] ;
      assign ma_gnt[j][k]  = sl_gnt[k][j] ;
      assign sl_data[k][j] = ma_data[j][k];
    end
  end

  /*******************
   *   RR ARBITERS   *
   *******************/

  // Instantiate an RR arbiter for each endpoint

  for (genvar k = 0; k < NumOut; k++) begin: gen_rr_outputs
    if (NumIn == 1) begin
      assign req_o[k]     = sl_req[k][0] ;
      assign sl_gnt[k][0] = gnt_i[k]     ;
      assign wdata_o[k]   = sl_data[k][0];
    end else begin : gen_rr_arb_tree
      rr_arb_tree #(
        .NumIn    ( NumIn     ),
        .DataWidth( DataWidth ),
        .ExtPrio  ( ExtPrio   )
      ) i_rr_arb_tree (
        .clk_i  ( clk_i      ),
        .rst_ni ( rst_ni     ),
        .flush_i( 1'b0       ),
        .rr_i   ( rr_i[k]    ),
        .req_i  ( sl_req[k]  ),
        .gnt_o  ( sl_gnt[k]  ),
        .data_i ( sl_data[k] ),
        .gnt_i  ( gnt_i[k]   ),
        .req_o  ( req_o[k]   ),
        .data_o ( wdata_o[k] ),
        .idx_o  ( idx_o[k]   ) 
      );
    end
  end

  /******************
   *   ASSERTIONS   *
   ******************/

  `ifndef SYNTHESIS
  initial begin
    assert (NumIn > 0 ) else
      $fatal(1, "NumIn needs to be larger than 0." );
    assert (NumOut > 0 ) else
      $fatal(1, "NumOut needs to be larger than 0.");
  end
  `endif

endmodule : unidirectional_xbar
