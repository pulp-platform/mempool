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
    parameter int unsigned NumIn         = 4   , // Number of Initiators
    parameter int unsigned NumOut        = 4   , // Number of Targets
    parameter int unsigned ReqDataWidth  = 32  , // Request Data Width
    parameter int unsigned RespDataWidth = 32  , // Response Data Width
    parameter bit ExtPrio                = 1'b0, // Use external arbiter priority flags
    parameter bit SpillRegisterReq       = 1'b0, // Insert a spill register on the request path (after arbitration)
    parameter bit SpillRegisterResp      = 1'b0, // Insert a spill register on the response path (after arbitration)
    parameter bit AxiVldRdy              = 1'b0, // Valid/ready signaling.
    // Credit-based handshake. ready_o is a "credit grant" signal.
    // Initiators can only send requests if they have a credit.
    // Each request consumes a credit. A credit cannot be used on the same cycle it is issued.
    parameter bit CreditBasedHandshake   = 1'b0,
    parameter int unsigned NumCredits    = 2 // Number of credits at each initiator port.
  ) (
    input  logic                                 clk_i,
    input  logic                                 rst_ni,
    // External priority signals
    input  logic [NumOut-1:0][$clog2(NumIn)-1:0] req_rr_i,
    input  logic [NumIn-1:0][$clog2(NumOut)-1:0] resp_rr_i,
    // Initiator side
    input  logic [NumIn-1:0]                     req_valid_i,     // Request valid
    output logic [NumIn-1:0]                     req_ready_o,     // Request ready
    input  logic [NumIn-1:0][$clog2(NumOut)-1:0] req_tgt_addr_i,  // Target address
    input  logic [NumIn-1:0][ReqDataWidth-1:0]   req_wdata_i,     // Write data
    output logic [NumIn-1:0]                     resp_valid_o,    // Response valid
    input  logic [NumIn-1:0]                     resp_ready_i,    // Response ready
    output logic [NumIn-1:0][RespDataWidth-1:0]  resp_rdata_o,    // Data response (for load commands)
    // Target side
    output logic [NumOut-1:0]                    req_valid_o,     // Request valid
    input  logic [NumOut-1:0]                    req_ready_i,     // Request ready
    output logic [NumOut-1:0][$clog2(NumIn)-1:0] req_ini_addr_o,  // Initiator address
    output logic [NumOut-1:0][ReqDataWidth-1:0]  req_wdata_o,     // Write data
    input  logic [NumOut-1:0]                    resp_valid_i,    // Response valid
    output logic [NumOut-1:0]                    resp_ready_o,    // Response ready
    input  logic [NumOut-1:0][$clog2(NumIn)-1:0] resp_ini_addr_i, // Initiator address
    input  logic [NumOut-1:0][RespDataWidth-1:0] resp_rdata_i     // Data response (for load commands)
  );

  /****************
   *   Crossbars  *
   ****************/

  // Instantiate two simplex crossbars, one for the requests and one for the responses.

  simplex_xbar #(
    .NumIn               (NumIn                ),
    .NumOut              (NumOut               ),
    .DataWidth           (ReqDataWidth         ),
    .ExtPrio             (ExtPrio              ),
    .SpillRegister       (SpillRegisterReq     ),
    .AxiVldRdy           (AxiVldRdy            ),
    .CreditBasedHandshake(CreditBasedHandshake ),
    .NumCredits          (NumCredits           )
  ) req_xbar (
    .clk_i     (clk_i         ),
    .rst_ni    (rst_ni        ),
    .rr_i      (req_rr_i      ),
    .valid_i   (req_valid_i   ),
    .ready_o   (req_ready_o   ),
    .tgt_addr_i(req_tgt_addr_i),
    .data_i    (req_wdata_i   ),
    .valid_o   (req_valid_o   ),
    .ini_addr_o(req_ini_addr_o),
    .ready_i   (req_ready_i   ),
    .data_o    (req_wdata_o   )
  );

  simplex_xbar #(
    .NumIn               (NumOut               ),
    .NumOut              (NumIn                ),
    .DataWidth           (RespDataWidth        ),
    .ExtPrio             (ExtPrio              ),
    .SpillRegister       (SpillRegisterResp    ),
    .AxiVldRdy           (AxiVldRdy            ),
    .CreditBasedHandshake(CreditBasedHandshake ),
    .NumCredits          (NumCredits           )
  ) resp_xbar (
    .clk_i     (clk_i          ),
    .rst_ni    (rst_ni         ),
    .rr_i      (resp_rr_i      ),
    .valid_i   (resp_valid_i   ),
    .ready_o   (resp_ready_o   ),
    .tgt_addr_i(resp_ini_addr_i),
    .data_i    (resp_rdata_i   ),
    .valid_o   (resp_valid_o   ),
    .ini_addr_o(/* Unused */   ),
    .ready_i   (resp_ready_i   ),
    .data_o    (resp_rdata_o   )
  );

  /******************
   *   Assertions   *
   ******************/

  if (NumIn <= 0)
    $fatal(1, "[full_duplex_xbar] NumIn needs to be larger than 0.");

  if (NumOut <= 0)
    $fatal(1, "[full_duplex_xbar] NumOut needs to be larger than 0.");

endmodule : full_duplex_xbar
