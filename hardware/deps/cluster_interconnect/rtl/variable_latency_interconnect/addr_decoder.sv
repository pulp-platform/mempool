// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
//         Matheus Cavalcante <matheusd@iis.ee.ethz.ch>, ETH Zurich

// Date: 12.02.2020

// Description: Address decoder for the simplex crossbar.

module addr_decoder #(
    parameter int unsigned NumOut    = 32,
    parameter int unsigned DataWidth = 32
  ) (
    // Initiator side
    input  logic                             req_i,  // Request from this initiator
    input  logic [$clog2(NumOut)-1:0]        add_i,  // Bank selection index to be decoded
    input  logic [DataWidth-1:0]             data_i, // Data to be transported to the targets
    output logic                             gnt_o,  // Grant to the initiator
    // slave side
    output logic [NumOut-1:0]                req_o,  // Request signals after decoding
    input  logic [NumOut-1:0]                gnt_i,  // Grants from targets
    output logic [NumOut-1:0][DataWidth-1:0] data_o
  );

  /**********************
   *  Degenerated case  *
   **********************/

  if (NumOut == 1) begin: gen_one_output
    assign req_o[0]  = req_i   ;
    assign gnt_o     = gnt_i[0];
    assign data_o[0] = data_i  ;
  end

  /*****************
   *  Normal case  *
   *****************/

  else begin: gen_several_outputs
    // Address decoder
    always_comb begin : p_addr_dec
      req_o        = '0   ;
      req_o[add_i] = req_i;
    end

    // Connect data outputs
    assign data_o = {NumOut{data_i}};

    // Aggregate grant signals
    assign gnt_o = |gnt_i ;
  end

  /****************
   *  Assertions  *
   ****************/

  if (NumOut <= 0)
    $fatal(1, "[addr_decoder] NumOut must be greater than 0.");

endmodule : addr_decoder

