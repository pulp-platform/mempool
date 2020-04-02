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

// Date: 16.01.2020

// Description: Interconnect with support to variable target latencies with different
// network topologies. Currently supported are: full crossbar and radix-2/4 butterflies.
// Note that only the full crossbar allows NumIn/NumOut configurations that are not
// aligned to a power of 2.

import tcdm_interconnect_pkg::topo_e;

module variable_latency_interconnect #(
    // Global parameters
    parameter int unsigned NumIn             = 32                   , // Number of Initiators. Must be aligned with a power of 2 for butterflies.
    parameter int unsigned NumOut            = 64                   , // Number of Targets. Must be aligned with a power of 2 for butterflies.
    parameter int unsigned AddrWidth         = 32                   , // Address Width on the Initiator Side
    parameter int unsigned DataWidth         = 32                   , // Data Word Width
    parameter int unsigned BeWidth           = DataWidth/8          , // Byte Strobe Width
    parameter int unsigned AddrMemWidth      = 12                   , // Number of Address bits per Target
    parameter bit AxiVldRdy                  = 1'b1                 , // Valid/ready signaling
    // Spill registers
    // A bit set at position i indicates a spill register at the i-th crossbar layer.
    // The layers are counted starting at 0 from the initiator, for the requests, and from the target, for the responses.
    parameter logic [63:0] SpillRegisterReq  = 64'h0                ,
    parameter logic [63:0] SpillRegisterResp = 64'h0                ,
    // Determines the width of the byte offset in a memory word. Normally this can be left at the default value,
    // but sometimes it needs to be overridden (e.g., when metadata is supplied to the memory via the wdata signal).
    parameter int unsigned ByteOffWidth      = $clog2(DataWidth-1)-3,
    // Topology can be: LIC, BFLY2, BFLY4, CLOS
    parameter topo_e Topology                = tcdm_interconnect_pkg::LIC
  ) (
    input  logic                                 clk_i,
    input  logic                                 rst_ni,
    // Initiator side
    input  logic [NumIn-1:0]                     req_valid_i,     // Request valid
    output logic [NumIn-1:0]                     req_ready_o,     // Request ready
    input  logic [NumIn-1:0][AddrWidth-1:0]      req_tgt_addr_i,  // Target address
    input  logic [NumIn-1:0]                     req_wen_i,       // Write enable
    input  logic [NumIn-1:0][DataWidth-1:0]      req_wdata_i,     // Write data
    input  logic [NumIn-1:0][BeWidth-1:0]        req_be_i,        // Byte enable
    output logic [NumIn-1:0]                     resp_valid_o,    // Response valid
    input  logic [NumIn-1:0]                     resp_ready_i,    // Response ready
    output logic [NumIn-1:0][DataWidth-1:0]      resp_rdata_o,    // Data response
    // Target side
    output logic [NumOut-1:0]                    req_valid_o,     // Request valid
    input  logic [NumOut-1:0]                    req_ready_i,     // Request ready
    output logic [NumOut-1:0][$clog2(NumIn)-1:0] req_ini_addr_o,  // Initiator address
    output logic [NumOut-1:0][AddrMemWidth-1:0]  req_tgt_addr_o,  // Target address
    output logic [NumOut-1:0]                    req_wen_o,       // Write enable
    output logic [NumOut-1:0][DataWidth-1:0]     req_wdata_o,     // Write data
    output logic [NumOut-1:0][BeWidth-1:0]       req_be_o,        // Byte enable
    input  logic [NumOut-1:0]                    resp_valid_i,    // Response valid
    output logic [NumOut-1:0]                    resp_ready_o,    // Response ready
    input  logic [NumOut-1:0][$clog2(NumIn)-1:0] resp_ini_addr_i, // Initiator address
    input  logic [NumOut-1:0][DataWidth-1:0]     resp_rdata_i     // Data response
  );

  /******************
   *   Parameters   *
   ******************/

  // localparams and aggregation of address, wen and payload data

  localparam int unsigned NumOutLog2      = $clog2(NumOut);
  localparam int unsigned NumInLog2       = $clog2(NumIn);
  localparam int unsigned IniAggDataWidth = 1 + BeWidth + AddrMemWidth + DataWidth;

  /*********************
   *  Spill registers  *
   *********************/

  // Request
  logic [NumIn-1:0]                ini_req_valid;
  logic [NumIn-1:0]                ini_req_ready;
  logic [NumIn-1:0][AddrWidth-1:0] ini_req_tgt_addr;
  logic [NumIn-1:0]                ini_req_wen;
  logic [NumIn-1:0][DataWidth-1:0] ini_req_wdata;
  logic [NumIn-1:0][BeWidth-1:0]   ini_req_be;

  for (genvar i = 0; i < NumIn; i++) begin: gen_req_spill_registers
    spill_register #(
      .Bypass(!SpillRegisterReq[0]                    ),
      .T     (logic[AddrWidth+1+DataWidth+BeWidth-1:0])
    ) i_req_spill_reg (
      .clk_i  (clk_i                                                                 ),
      .rst_ni (rst_ni                                                                ),
      .data_i ({req_tgt_addr_i[i], req_wen_i[i], req_wdata_i[i], req_be_i[i]}        ),
      .valid_i(req_valid_i[i]                                                        ),
      .ready_o(req_ready_o[i]                                                        ),
      .data_o ({ini_req_tgt_addr[i], ini_req_wen[i], ini_req_wdata[i], ini_req_be[i]}),
      .valid_o(ini_req_valid[i]                                                      ),
      .ready_i(ini_req_ready[i]                                                      )
    );
  end: gen_req_spill_registers

  // Response
  logic [NumOut-1:0]                tgt_resp_valid;
  logic [NumOut-1:0]                tgt_resp_ready;
  logic [NumOut-1:0][NumInLog2-1:0] tgt_resp_ini_addr;
  logic [NumOut-1:0][DataWidth-1:0] tgt_resp_rdata;

  for (genvar t = 0; t < NumOut; t++) begin: gen_resp_spill_registers
    spill_register #(
      .Bypass(!SpillRegisterResp[0]         ),
      .T     (logic[NumInLog2+DataWidth-1:0])
    ) i_resp_spill_reg (
      .clk_i  (clk_i                                    ),
      .rst_ni (rst_ni                                   ),
      .data_i ({resp_ini_addr_i[t], resp_rdata_i[t]}    ),
      .valid_i(resp_valid_i[t]                          ),
      .ready_o(resp_ready_o[t]                          ),
      .data_o ({tgt_resp_ini_addr[t], tgt_resp_rdata[t]}),
      .valid_o(tgt_resp_valid[t]                        ),
      .ready_i(tgt_resp_ready[t]                        )
    );
  end: gen_resp_spill_registers

  /*************
   *  Signals  *
   *************/

  logic [NumIn-1:0][IniAggDataWidth-1:0]  data_agg_in;
  logic [NumOut-1:0][IniAggDataWidth-1:0] data_agg_out;
  logic [NumIn-1:0][NumOutLog2-1:0]       tgt_sel;

  for (genvar j = 0; unsigned'(j) < NumIn; j++) begin : gen_inputs
    // Extract target index
    assign tgt_sel[j] = ini_req_tgt_addr[j][ByteOffWidth +: NumOutLog2];

    // Aggregate data to be routed to targets
    assign data_agg_in[j] = {ini_req_wen[j], ini_req_be[j], ini_req_tgt_addr[j][ByteOffWidth + NumOutLog2 +: AddrMemWidth], ini_req_wdata[j]};
  end

  // Disaggregate data
  for (genvar k = 0; unsigned'(k) < NumOut; k++) begin : gen_outputs
    assign {req_wen_o[k], req_be_o[k], req_tgt_addr_o[k], req_wdata_o[k]} = data_agg_out[k];
  end

  /****************
   *   Networks   *
   ****************/

  // Tuned logarithmic interconnect architecture, based on rr_arb_tree primitives
  if (Topology == tcdm_interconnect_pkg::LIC) begin : gen_lic
    full_duplex_xbar #(
      .NumIn            (NumIn               ),
      .NumOut           (NumOut              ),
      .ReqDataWidth     (IniAggDataWidth     ),
      .RespDataWidth    (DataWidth           ),
      .SpillRegisterReq (SpillRegisterReq[1] ),
      .SpillRegisterResp(SpillRegisterResp[1]),
      .AxiVldRdy        (AxiVldRdy           )
    ) i_xbar (
      .clk_i          (clk_i            ),
      .rst_ni         (rst_ni           ),
      // Extern priority flags
      .req_rr_i       ('0               ),
      .resp_rr_i      ('0               ),
      // Initiator side
      .req_valid_i    (ini_req_valid    ),
      .req_ready_o    (ini_req_ready    ),
      .req_tgt_addr_i (tgt_sel          ),
      .req_wdata_i    (data_agg_in      ),
      .resp_valid_o   (resp_valid_o     ),
      .resp_rdata_o   (resp_rdata_o     ),
      .resp_ready_i   (resp_ready_i     ),
      // Target side
      .req_valid_o    (req_valid_o      ),
      .req_ini_addr_o (req_ini_addr_o   ),
      .req_ready_i    (req_ready_i      ),
      .req_wdata_o    (data_agg_out     ),
      .resp_valid_i   (tgt_resp_valid   ),
      .resp_ready_o   (tgt_resp_ready   ),
      .resp_ini_addr_i(tgt_resp_ini_addr),
      .resp_rdata_i   (tgt_resp_rdata   )
    );
  end

  // Butterfly network (radix 2 or 4)
  else if (Topology == tcdm_interconnect_pkg::BFLY2 || Topology == tcdm_interconnect_pkg::BFLY4) begin: gen_bfly
    localparam int unsigned Radix = 2**Topology;

    variable_latency_bfly_net #(
      .NumIn            (NumIn                 ),
      .NumOut           (NumOut                ),
      .ReqDataWidth     (IniAggDataWidth       ),
      .RespDataWidth    (DataWidth             ),
      .Radix            (Radix                 ),
      .ExtPrio          (1'b0                  ),
      .SpillRegisterReq (SpillRegisterReq >> 1 ),
      .SpillRegisterResp(SpillRegisterResp >> 1),
      .AxiVldRdy        (AxiVldRdy             )
    ) i_bfly_net (
      .clk_i          (clk_i            ),
      .rst_ni         (rst_ni           ),
      // Extern priority flags
      .req_rr_i       ('0               ),
      .resp_rr_i      ('0               ),
      // Initiator side
      .req_valid_i    (ini_req_valid    ),
      .req_ready_o    (ini_req_ready    ),
      .req_tgt_addr_i (tgt_sel          ),
      .req_wdata_i    (data_agg_in      ),
      .resp_valid_o   (resp_valid_o     ),
      .resp_ready_i   (resp_ready_i     ),
      .resp_rdata_o   (resp_rdata_o     ),
      // Target side
      .req_valid_o    (req_valid_o      ),
      .req_ini_addr_o (req_ini_addr_o   ),
      .req_ready_i    (req_ready_i      ),
      .req_wdata_o    (data_agg_out     ),
      .resp_valid_i   (tgt_resp_valid   ),
      .resp_ready_o   (tgt_resp_ready   ),
      .resp_ini_addr_i(tgt_resp_ini_addr),
      .resp_rdata_i   (tgt_resp_rdata   )
    );
  end

  // Unknown network
  else begin: gen_unknown
    $fatal(1, "[variable_latency_interconnect] Unknown TCDM configuration %d.", Topology);
  end

  /******************
   *   Assertions   *
   ******************/

  if (AddrMemWidth + NumOutLog2 > AddrWidth)
    $fatal(1, "[variable_latency_interconnect] Address is not wide enough to accomodate the requested TCDM configuration.");

  if (Topology != tcdm_interconnect_pkg::LIC && NumOut < NumIn)
    $fatal(1, "[variable_latency_interconnect] NumOut < NumIn is not supported with the chosen TCDM configuration.");

endmodule : variable_latency_interconnect
