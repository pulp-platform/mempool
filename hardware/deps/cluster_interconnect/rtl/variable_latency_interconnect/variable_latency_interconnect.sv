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
    parameter int unsigned NumIn              = 32                   , // Number of Initiators. Must be aligned with a power of 2 for butterflies.
    parameter int unsigned NumOut             = 64                   , // Number of Targets. Must be aligned with a power of 2 for butterflies.
    parameter int unsigned AddrWidth          = 32                   , // Address Width on the Initiator Side
    parameter int unsigned DataWidth          = 32                   , // Data Word Width
    parameter int unsigned BeWidth            = DataWidth/8          , // Byte Strobe Width
    parameter int unsigned AddrMemWidth       = 12                   , // Number of Address bits per Target
    // Registers
    parameter bit unsigned SpillInitiatorReq  = 1'b1                 ,
    parameter bit unsigned SpillInitiatorResp = 1'b0                 ,
    parameter bit unsigned SpillTargetReq     = 1'b0                 ,
    parameter bit unsigned SpillTargetResp    = 1'b1                 ,
    // Determines the width of the byte offset in a memory word. Normally this can be left at the default value,
    // but sometimes it needs to be overridden (e.g., when metadata is supplied to the memory via the wdata signal).
    parameter int unsigned ByteOffWidth       = $clog2(DataWidth-1)-3,
    // Topology can be: LIC, BFLY2, BFLY4, CLOS
    parameter topo_e Topology                 = tcdm_interconnect_pkg::LIC
  ) (
    input  logic                                 clk_i,
    input  logic                                 rst_ni,
    // Initiator side
    input  logic [NumIn-1:0]                     req_i,     // Request signal
    output logic [NumIn-1:0]                     gnt_o,     // Grant signal
    input  logic [NumIn-1:0][AddrWidth-1:0]      add_i,     // Target address
    input  logic [NumIn-1:0]                     wen_i,     // Write enable
    input  logic [NumIn-1:0][DataWidth-1:0]      wdata_i,   // Write data
    input  logic [NumIn-1:0][BeWidth-1:0]        be_i,      // Byte enable
    output logic [NumIn-1:0]                     vld_o,     // Response valid
    input  logic [NumIn-1:0]                     rdy_i,     // Response ready
    output logic [NumIn-1:0][DataWidth-1:0]      rdata_o,   // Data response (for load commands)
    // Target side
    output logic [NumOut-1:0]                    req_o,     // Request signal
    output logic [NumOut-1:0][$clog2(NumIn)-1:0] ini_add_o, // Initiator address
    input  logic [NumOut-1:0]                    gnt_i,     // Grant signal
    output logic [NumOut-1:0][AddrMemWidth-1:0]  add_o,     // Target address
    output logic [NumOut-1:0]                    wen_o,     // Write enable
    output logic [NumOut-1:0][DataWidth-1:0]     wdata_o,   // Write data
    output logic [NumOut-1:0][BeWidth-1:0]       be_o,      // Byte enable
    input  logic [NumOut-1:0]                    vld_i,     // Response valid
    output logic [NumOut-1:0]                    rdy_o,     // Response ready
    input  logic [NumOut-1:0][$clog2(NumIn)-1:0] ini_add_i, // Initiator address (response)
    input  logic [NumOut-1:0][DataWidth-1:0]     rdata_i    // Data response (for load commands)
  );

  /******************
   *   Parameters   *
   ******************/

  // localparams and aggregation of address, wen and payload data

  localparam int unsigned NumOutLog2      = $clog2(NumOut);
  localparam int unsigned NumInLog2       = $clog2(NumIn);
  localparam int unsigned IniAggDataWidth = 1 + BeWidth + AddrMemWidth + DataWidth;

  /************************************
   *  Initiator side spill registers  *
   ************************************/

  // Request
  logic [NumIn-1:0]                ini_req;
  logic [NumIn-1:0]                ini_gnt;
  logic [NumIn-1:0][AddrWidth-1:0] ini_add;
  logic [NumIn-1:0]                ini_wen;
  logic [NumIn-1:0][DataWidth-1:0] ini_wdata;
  logic [NumIn-1:0][BeWidth-1:0]   ini_be;

  for (genvar i = 0; i < NumIn; i++) begin: gen_initiator_req_spill_registers
    spill_register #(
      .Bypass(!SpillInitiatorReq                      ),
      .T     (logic[AddrWidth+1+DataWidth+BeWidth-1:0])
    ) i_initiator_req_spill_reg (
      .clk_i  (clk_i                                            ),
      .rst_ni (rst_ni                                           ),
      .data_i ({add_i[i], wen_i[i], wdata_i[i], be_i[i]}        ),
      .valid_i(req_i[i]                                         ),
      .ready_o(gnt_o[i]                                         ),
      .data_o ({ini_add[i], ini_wen[i], ini_wdata[i], ini_be[i]}),
      .valid_o(ini_req[i]                                       ),
      .ready_i(ini_gnt[i]                                       )
    );
  end: gen_initiator_req_spill_registers

  // Response
  logic [NumIn-1:0]                ini_vld;
  logic [NumIn-1:0]                ini_rdy;
  logic [NumIn-1:0][DataWidth-1:0] ini_rdata;

  for (genvar i = 0; i < NumIn; i++) begin: gen_initiator_resp_spill_registers
    spill_register #(
      .Bypass(!SpillInitiatorResp ),
      .T     (logic[DataWidth-1:0])
    ) i_initiator_resp_spill_reg (
      .clk_i  (clk_i       ),
      .rst_ni (rst_ni      ),
      .data_o (rdata_o[i]  ),
      .valid_o(vld_o[i]    ),
      .ready_i(rdy_i[i]    ),
      .data_i (ini_rdata[i]),
      .valid_i(ini_vld[i]  ),
      .ready_o(ini_rdy[i]  )
    );
  end: gen_initiator_resp_spill_registers

  /*********************************
   *  Target side spill registers  *
   *********************************/

  // Request
  logic [NumOut-1:0]                   tgt_req;
  logic [NumOut-1:0][NumInLog2-1:0]    tgt_ini_add_o;
  logic [NumOut-1:0]                   tgt_gnt;
  logic [NumOut-1:0][AddrMemWidth-1:0] tgt_add;
  logic [NumOut-1:0]                   tgt_wen;
  logic [NumOut-1:0][DataWidth-1:0]    tgt_wdata;
  logic [NumOut-1:0][BeWidth-1:0]      tgt_be;

  for (genvar t = 0; t < NumOut; t++) begin: gen_target_req_spill_registers
    spill_register #(
      .Bypass(!SpillTargetReq                                      ),
      .T     (logic[NumInLog2+AddrMemWidth+1+DataWidth+BeWidth-1:0])
    ) i_target_req_spill_reg (
      .clk_i  (clk_i                                                              ),
      .rst_ni (rst_ni                                                             ),
      .data_o ({ini_add_o[t], add_o[t], wen_o[t], wdata_o[t], be_o[t]}            ),
      .valid_o(req_o[t]                                                           ),
      .ready_i(gnt_i[t]                                                           ),
      .data_i ({tgt_ini_add_o[t], tgt_add[t], tgt_wen[t], tgt_wdata[t], tgt_be[t]}),
      .valid_i(tgt_req[t]                                                         ),
      .ready_o(tgt_gnt[t]                                                         )
    );
  end: gen_target_req_spill_registers

  // Response
  logic [NumOut-1:0]                tgt_vld;
  logic [NumOut-1:0]                tgt_rdy;
  logic [NumOut-1:0][NumInLog2-1:0] tgt_ini_add_i;
  logic [NumOut-1:0][DataWidth-1:0] tgt_rdata;

  for (genvar t = 0; t < NumOut; t++) begin: gen_target_resp_spill_registers
    spill_register #(
      .Bypass(!SpillTargetResp              ),
      .T     (logic[NumInLog2+DataWidth-1:0])
    ) i_target_resp_spill_reg (
      .clk_i  (clk_i                           ),
      .rst_ni (rst_ni                          ),
      .data_i ({ini_add_i[t], rdata_i[t]}      ),
      .valid_i(vld_i[t]                        ),
      .ready_o(rdy_o[t]                        ),
      .data_o ({tgt_ini_add_i[t], tgt_rdata[t]}),
      .valid_o(tgt_vld[t]                      ),
      .ready_i(tgt_rdy[t]                      )
    );
  end: gen_target_resp_spill_registers

  /*************
   *  Signals  *
   *************/

  logic [NumIn-1:0][IniAggDataWidth-1:0]  data_agg_in;
  logic [NumOut-1:0][IniAggDataWidth-1:0] data_agg_out;
  logic [NumIn-1:0][NumOutLog2-1:0]       bank_sel;

  for (genvar j = 0; unsigned'(j) < NumIn; j++) begin : gen_inputs
    // Extract bank index
    assign bank_sel[j] = ini_add[j][ByteOffWidth +: NumOutLog2];

    // Aggregate data to be routed to slaves
    assign data_agg_in[j] = {ini_wen[j], ini_be[j], ini_add[j][ByteOffWidth + NumOutLog2 +: AddrMemWidth], ini_wdata[j]};
  end

  // Disaggregate data
  for (genvar k = 0; unsigned'(k) < NumOut; k++) begin : gen_outputs
    assign {tgt_wen[k], tgt_be[k], tgt_add[k], tgt_wdata[k]} = data_agg_out[k];
  end

  /****************
   *   Networks   *
   ****************/

  // Tuned logarithmic interconnect architecture, based on rr_arb_tree primitives
  if (Topology == tcdm_interconnect_pkg::LIC) begin : gen_lic
    full_duplex_xbar #(
      .NumIn        (NumIn          ),
      .NumOut       (NumOut         ),
      .ReqDataWidth (IniAggDataWidth),
      .RespDataWidth(DataWidth      )
    ) i_xbar (
      .clk_i    (clk_i        ),
      .rst_ni   (rst_ni       ),
      // Extern priority flags
      .req_rr_i ('0           ),
      .resp_rr_i('0           ),
      // Initiator side
      .req_i    (ini_req      ),
      .gnt_o    (ini_gnt      ),
      .add_i    (bank_sel     ),
      .wdata_i  (data_agg_in  ),
      .vld_o    (ini_vld      ),
      .rdata_o  (ini_rdata    ),
      .rdy_i    (ini_rdy      ),
      // Target side
      .req_o    (tgt_req      ),
      .ini_add_o(tgt_ini_add_o),
      .gnt_i    (tgt_gnt      ),
      .wdata_o  (data_agg_out ),
      .vld_i    (tgt_vld      ),
      .rdy_o    (tgt_rdy      ),
      .ini_add_i(tgt_ini_add_i),
      .rdata_i  (tgt_rdata    )
    );
  end

  // Butterfly network (radix 2 or 4)
  else if (Topology == tcdm_interconnect_pkg::BFLY2 || Topology == tcdm_interconnect_pkg::BFLY4) begin: gen_bfly
    localparam int unsigned Radix = 2**Topology;

    logic [$clog2(NumOut)-1:0] req_rr ;
    logic [$clog2(NumOut)-1:0] resp_rr;

    // Although round robin arbitration works in some cases, it
    // it is quite likely that it interferes with linear access patterns
    // hence we use a relatively long LFSR + block cipher here to create a
    // pseudo random sequence with good randomness. the block cipher layers
    // are used to break shift register linearity.
    lfsr #(
      .LfsrWidth   (64            ),
      .OutWidth    ($clog2(NumOut)),
      .CipherLayers(3             ),
      .CipherReg   (1'b1          )
    ) lfsr_req_i (
      .clk_i (clk_i               ),
      .rst_ni(rst_ni              ),
      .en_i  (|(tgt_gnt & tgt_req)),
      .out_o (req_rr              )
    );

    lfsr #(
      .LfsrWidth   (64            ),
      .OutWidth    ($clog2(NumOut)),
      .CipherLayers(3             ),
      .CipherReg   (1'b1          )
    ) lfsr_resp_i (
      .clk_i (clk_i               ),
      .rst_ni(rst_ni              ),
      .en_i  (|(tgt_vld & tgt_rdy)),
      .out_o (resp_rr             )
    );

    variable_latency_bfly_net #(
      .NumIn        (NumIn          ),
      .NumOut       (NumOut         ),
      .ReqDataWidth (IniAggDataWidth),
      .RespDataWidth(DataWidth      ),
      .Radix        (Radix          ),
      .ExtPrio      (1'b1           )
    ) i_bfly_net (
      .clk_i    (clk_i        ),
      .rst_ni   (rst_ni       ),
      // Extern priority flags
      .req_rr_i (req_rr       ),
      .resp_rr_i(resp_rr      ),
      // Initiator side
      .req_i    (ini_req      ),
      .gnt_o    (ini_gnt      ),
      .add_i    (bank_sel     ),
      .wdata_i  (data_agg_in  ),
      .vld_o    (ini_vld      ),
      .rdy_i    (ini_rdy      ),
      .rdata_o  (ini_rdata    ),
      // Target side
      .req_o    (tgt_req      ),
      .ini_add_o(tgt_ini_add_o),
      .gnt_i    (tgt_gnt      ),
      .wdata_o  (data_agg_out ),
      .vld_i    (tgt_vld      ),
      .rdy_o    (tgt_rdy      ),
      .ini_add_i(tgt_ini_add_i),
      .rdata_i  (tgt_rdata    )
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
