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
    parameter int unsigned NumIn       = 4   , // Number of Initiators
    parameter int unsigned NumOut      = 4   , // Number of Targets
    parameter int unsigned DataWidth   = 32  , // Data Width
    parameter bit ExtPrio              = 1'b0, // Use external arbiter priority flags
    parameter bit SpillRegister        = 1'b0, // Insert a spill register per target after the arbitration step.
    parameter bit AxiVldRdy            = 1'b0, // Valid/ready signaling.
    // Credit-based handshake. ready_o is a "credit grant" signal.
    // Initiators can only send requests if they have a credit.
    // Each request consumes a credit. A credit cannot be used on the same cycle it is issued.
    parameter bit CreditBasedHandshake = 1'b0,
    parameter int unsigned NumCredits  = 2   , // Number of credits at each initiator port.
    parameter int unsigned MaxCredits  = 15    // Maximum number of credits that can be issued.
  ) (
    input  logic                                 clk_i,
    input  logic                                 rst_ni,
    // External priority signal
    input  logic [NumOut-1:0][$clog2(NumIn)-1:0] rr_i,
    // Initiator side
    input  logic [NumIn-1:0]                     valid_i,    // Valid signal
    output logic [NumIn-1:0]                     ready_o,    // Ready signal
    input  logic [NumIn-1:0][$clog2(NumOut)-1:0] tgt_addr_i, // Target address
    input  logic [NumIn-1:0][DataWidth-1:0]      data_i,     // Data
    // Target side
    output logic [NumOut-1:0]                    valid_o,    // Valid signal
    input  logic [NumOut-1:0]                    ready_i,    // Ready signal
    output logic [NumOut-1:0][$clog2(NumIn)-1:0] ini_addr_o, // Initiator address
    output logic [NumOut-1:0][DataWidth-1:0]     data_o      // Data
  );

  /****************
   *   Includes   *
   ****************/

  `include "common_cells/registers.svh"

  typedef logic [$clog2(MaxCredits):0] credit_t;

  /*************
   *   Wires   *
   *************/

  logic [NumOut-1:0][ NumIn-1:0][DataWidth-1:0] tgt_data;
  logic [NumOut-1:0][ NumIn-1:0]                tgt_ready, tgt_valid;

  logic [ NumIn-1:0][NumOut-1:0][DataWidth-1:0] ini_data;
  logic [ NumIn-1:0][NumOut-1:0]                ini_ready, ini_valid;

  logic [NumOut-1:0]                    arb_valid, arb_ready;
  logic [NumOut-1:0][DataWidth-1:0]     arb_data;
  logic [NumOut-1:0][$clog2(NumIn)-1:0] arb_ini_add;

  /***********************
   *   Address decoder   *
   ***********************/

  for (genvar j = 0; j < NumIn; j++) begin: gen_inputs
    logic ini_queue_valid                        ;
    logic ini_queue_ready                        ;
    logic ini_queue_full                         ;
    logic ini_queue_empty                        ;
    logic [$clog2(NumOut)-1:0] ini_queue_tgt_addr;
    logic [DataWidth-1:0] ini_queue_wdata        ;

    // Credit emission
    if (CreditBasedHandshake) begin: gen_credits
      logic ini_queue_pop;
      credit_t credits_d, credits_q;

      always_comb begin
        credits_d = credits_q;
        if (ini_queue_pop) credits_d++;
        if (ready_o[j]) credits_d--   ;
      end

      fifo_v3 #(
        .FALL_THROUGH(1'b1                      ),
        .DEPTH       (NumCredits                ),
        .DATA_WIDTH  (DataWidth + $clog2(NumOut))
      ) i_ini_queue (
        .clk_i     (clk_i                                ),
        .rst_ni    (rst_ni                               ),
        .flush_i   (1'b0                                 ),
        .testmode_i(1'b0                                 ),
        .data_i    ({data_i[j], tgt_addr_i[j]}           ),
        .push_i    (valid_i[j]                           ),
        .full_o    (ini_queue_full                       ),
        .data_o    ({ini_queue_wdata, ini_queue_tgt_addr}),
        .empty_o   (ini_queue_empty                      ),
        .pop_i     (ini_queue_pop                        ),
        .usage_o   (/* Unused */                         )
      );

      assign ini_queue_pop   = ini_queue_ready & ~ini_queue_empty;
      assign ini_queue_valid = !ini_queue_empty                  ;
      `FF(credits_q, credits_d, NumCredits)
      `FF(ready_o[j], (credits_d != '0), 1'b0)
    end: gen_credits else begin: gen_no_credits
      assign ini_queue_valid    = valid_i[j]      ;
      assign ini_queue_tgt_addr = tgt_addr_i[j]   ;
      assign ini_queue_wdata    = data_i[j]       ;
      assign ready_o[j]         = ini_queue_ready ;
    end: gen_no_credits

    // Instantiate a bank address decoder for each initiator
    addr_decoder #(
      .NumOut   (NumOut   ),
      .DataWidth(DataWidth),
      .AxiVldRdy(AxiVldRdy)
    ) i_addr_decoder (
      // Initiator side
      .valid_i(ini_queue_valid   ),
      .addr_i (ini_queue_tgt_addr),
      .data_i (ini_queue_wdata   ),
      .ready_o(ini_queue_ready   ),
      // Target side
      .valid_o(ini_valid[j]      ),
      .ready_i(ini_ready[j]      ),
      .data_o (ini_data[j]       )
    );

    // Reshape connections between initiator and target
    for (genvar k = 0; unsigned'(k) < NumOut; k++) begin : gen_reshape
      assign tgt_valid[k][j] = ini_valid[j][k];
      assign ini_ready[j][k] = tgt_ready[k][j];
      assign tgt_data[k][j]  = ini_data[j][k] ;
    end

  end: gen_inputs

  /****************
   *   Arbiters   *
   ****************/

  for (genvar k = 0; k < NumOut; k++) begin: gen_rr_outputs
    logic tgt_register_valid;
    logic tgt_register_ready;
    if (CreditBasedHandshake) begin: gen_credits
      credit_t credits_d, credits_q;

      always_comb begin
        credits_d = credits_q;
        if (valid_o[k]) credits_d--;
        if (ready_i[k]) credits_d++;
      end

      // Ready if we got any credits
      assign tgt_register_ready = (credits_q != '0);
      `FF(credits_q, credits_d, 0)
    end: gen_credits else begin: gen_no_credits
      assign tgt_register_ready = ready_i[k];
    end: gen_no_credits

    if (NumIn == 1) begin

      assign arb_valid[k]    = tgt_valid[k][0];
      assign tgt_ready[k][0] = arb_ready[k]   ;
      assign arb_data[k]     = tgt_data[k][0] ;

    end else begin : gen_rr_arb_tree
      // Instantiate an RR arbiter for each target
      rr_arb_tree #(
        .NumIn    (NumIn    ),
        .DataWidth(DataWidth),
        .ExtPrio  (ExtPrio  ),
        .AxiVldRdy(AxiVldRdy)
      ) i_rr_arb_tree (
        .clk_i  (clk_i         ),
        .rst_ni (rst_ni        ),
        .flush_i(1'b0          ),
        .rr_i   (rr_i[k]       ),
        .req_i  (tgt_valid[k]  ),
        .gnt_o  (tgt_ready[k]  ),
        .data_i (tgt_data[k]   ),
        .gnt_i  (arb_ready[k]  ),
        .req_o  (arb_valid[k]  ),
        .data_o (arb_data[k]   ),
        .idx_o  (arb_ini_add[k])
      );

      // Register the arbitrated result
      spill_register #(
        .Bypass(!SpillRegister                    ),
        .T     (logic[DataWidth+$clog2(NumIn)-1:0])
      ) i_register (
        .clk_i  (clk_i                        ),
        .rst_ni (rst_ni                       ),
        .data_i ({arb_data[k], arb_ini_add[k]}),
        .valid_i(arb_valid[k]                 ),
        .ready_o(arb_ready[k]                 ),
        .data_o ({data_o[k], ini_addr_o[k]}   ),
        .valid_o(tgt_register_valid           ),
        .ready_i(tgt_register_ready           )
        );

      // Filter the outbound requests if we have no credits
      assign valid_o[k] = tgt_register_valid & (!CreditBasedHandshake | tgt_register_ready);
    end
  end : gen_rr_outputs

  /******************
   *   Assertions   *
   ******************/

  if (NumIn <= 0)
    $fatal(1, "[simplex_xbar] NumIn needs to be larger than 0.");

  if (NumOut <= 0)
    $fatal(1, "[simplex_xbar] NumOut needs to be larger than 0.");

endmodule : simplex_xbar
