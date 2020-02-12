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
    parameter int unsigned NumIn                  = 32                   , // Number of Initiators. Must be aligned with a power of 2 for butterflies.
    parameter int unsigned NumOut                 = 64                   , // Number of Targets. Must be aligned with a power of 2 for butterflies.
    parameter int unsigned AddrWidth              = 32                   , // Address Width on the Initiator Side
    parameter int unsigned DataWidth              = 32                   , // Data Word Width
    parameter int unsigned BeWidth                = DataWidth/8          , // Byte Strobe Width
    parameter int unsigned AddrMemWidth           = 12                   , // Number of Address bits per Target
    parameter bit unsigned WriteRespOn            = 1'b1                 , // Do writes return a response?
    parameter int unsigned NumOutstanding         = 4                    , // Number of Outstanding Transactions per Target
    parameter bit unsigned TargetQueueFallThrough = 1'b0                 , // Are the target queues are fall-through?
    // Determines the width of the byte offset in a memory word. Normally this can be left at the default value,
    // but sometimes it needs to be overridden (e.g., when metadata is supplied to the memory via the wdata signal).
    parameter int unsigned ByteOffWidth           = $clog2(DataWidth-1)-3,
    // Topology can be: LIC, BFLY2, BFLY4, CLOS
    parameter topo_e Topology                     = tcdm_interconnect_pkg::LIC
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
    input  logic [NumOut-1:0][$clog2(NumIn)-1:0] ini_add_i, // Initiator address (response)
    input  logic [NumOut-1:0][DataWidth-1:0]     rdata_i    // Data response (for load commands)
  );

  /******************
   *   Parameters   *
   ******************/

  // localparams and aggregation of address, wen and payload data

  localparam int unsigned NumOutLog2     = $clog2(NumOut);
  localparam int unsigned AggDataWidth   = 1 + BeWidth + AddrMemWidth + DataWidth;
  localparam int unsigned TransactionIdx = NumOutstanding > 1 ? $clog2(NumOutstanding) : 1;

  logic [NumIn-1:0][AggDataWidth-1:0]  data_agg_in;
  logic [NumOut-1:0][AggDataWidth-1:0] data_agg_out;
  logic [NumIn-1:0][NumOutLog2-1:0]    bank_sel;

  logic [NumOut-1:0][DataWidth-1:0]     tgt_fifo_rdata;
  logic [NumOut-1:0][$clog2(NumIn)-1:0] tgt_fifo_ini_add;
  logic [NumOut-1:0]                    tgt_fifo_full;
  logic [NumOut-1:0]                    tgt_fifo_empty;
  logic [NumOut-1:0]                    tgt_fifo_pop;

  logic [NumOut-1:0] tgt_xbar_req;

  for (genvar j = 0; unsigned'(j) < NumIn; j++) begin : gen_inputs
    // Extract bank index
    assign bank_sel[j] = add_i[j][ByteOffWidth + NumOutLog2 - 1 : ByteOffWidth];

    // Aggregate data to be routed to slaves
    assign data_agg_in[j] = {wen_i[j], be_i[j], add_i[j][ByteOffWidth + NumOutLog2 + AddrMemWidth - 1 : ByteOffWidth + NumOutLog2], wdata_i[j]};
  end

  // Disaggregate data
  for (genvar k = 0; unsigned'(k) < NumOut; k++) begin : gen_outputs
    assign {wen_o[k], be_o[k], add_o[k], wdata_o[k]} = data_agg_out[k];
  end

  /****************
   *   Networks   *
   ****************/

  // Tuned logarithmic interconnect architecture, based on rr_arb_tree primitives
  if (Topology == tcdm_interconnect_pkg::LIC) begin : gen_lic
    full_duplex_xbar #(
      .NumIn        (NumIn       ),
      .NumOut       (NumOut      ),
      .ReqDataWidth (AggDataWidth),
      .RespDataWidth(DataWidth   )
    ) i_xbar (
      .clk_i    (clk_i           ),
      .rst_ni   (rst_ni          ),
      // Extern priority flags
      .req_rr_i ('0              ),
      .resp_rr_i('0              ),
      // Initiator side
      .req_i    (req_i           ),
      .gnt_o    (gnt_o           ),
      .add_i    (bank_sel        ),
      .wdata_i  (data_agg_in     ),
      .vld_o    (vld_o           ),
      .rdata_o  (rdata_o         ),
      .rdy_i    (rdy_i           ),
      // Target side
      .req_o    (tgt_xbar_req    ),
      .ini_add_o(ini_add_o       ),
      .gnt_i    (gnt_i           ),
      .wdata_o  (data_agg_out    ),
      .vld_i    (~tgt_fifo_empty ),
      .rdy_o    (tgt_fifo_pop    ),
      .ini_add_i(tgt_fifo_ini_add),
      .rdata_i  (tgt_fifo_rdata  )
    );
  end

  // Butterfly network (radix 2 or 4)
  else if (Topology == tcdm_interconnect_pkg::BFLY2 || Topology == tcdm_interconnect_pkg::BFLY4) begin: gen_bfly
    localparam int unsigned Radix = 2**Topology;

    logic [NumOut-1:0][AggDataWidth-1:0] data1;
    logic [NumOut-1:0][DataWidth-1:0] rdata1  ;
    logic [NumOut-1:0] gnt1, req1;

    logic [NumOut-1:0][AggDataWidth-1:0] data1_trsp;
    logic [NumOut-1:0][DataWidth-1:0] rdata1_trsp  ;
    logic [NumOut-1:0] gnt1_trsp                   ;
    logic [NumOut-1:0] req1_trsp                   ;

    logic [$clog2(NumOut)-1:0] req_rr ;
    logic [$clog2(NumOut)-1:0] resp_rr;

    // Although round robin arbitration works in some cases, it
    // it is quite likely that it interferes with linear access patterns
    // hence we use a relatively long LFSR + block cipher here to create a
    // pseudo random sequence with good randomness. the block cipher layers
    // are used to break shift register linearity.
    lfsr #(
      .LfsrWidth   (64              ),
      .OutWidth    (2*$clog2(NumOut)),
      .CipherLayers(3               ),
      .CipherReg   (1'b1            )
    ) lfsr_i (
      .clk_i (clk_i            ),
      .rst_ni(rst_ni           ),
      .en_i  (|(gnt_i & req_o) ),
      .out_o ({resp_rr, req_rr})
    );

    variable_latency_bfly_net #(
      .NumIn        (NumIn       ),
      .NumOut       (NumOut      ),
      .ReqDataWidth (AggDataWidth),
      .RespDataWidth(DataWidth   ),
      .Radix        (Radix       ),
      .ExtPrio      (1'b1        )
    ) i_bfly_net (
      .clk_i    (clk_i           ),
      .rst_ni   (rst_ni          ),
      // Extern priority flags
      .req_rr_i (req_rr          ),
      .resp_rr_i(resp_rr         ),
      // Initiator side
      .req_i    (req_i           ),
      .gnt_o    (gnt_o           ),
      .add_i    (bank_sel        ),
      .wdata_i  (data_agg_in     ),
      .vld_o    (vld_o           ),
      .rdy_i    (rdy_i           ),
      .rdata_o  (rdata_o         ),
      // Target side
      .req_o    (tgt_xbar_req    ),
      .ini_add_o(ini_add_o       ),
      .gnt_i    (gnt_i           ),
      .wdata_o  (data_agg_out    ),
      .vld_i    (~tgt_fifo_empty ),
      .rdy_o    (tgt_fifo_pop    ),
      .ini_add_i(tgt_fifo_ini_add),
      .rdata_i  (tgt_fifo_rdata  )
    );
  end

  // Unknown network
  else begin: gen_unknown
    $fatal(1, "[variable_latency_interconnect] Unknown TCDM configuration %d.", Topology);
  end

  /******************************
   *   Target response queues   *
   ******************************/

  logic [NumOut-1:0][TransactionIdx:0] usage_d, usage_q;
  logic [NumOut-1:0]                   tgt_fifo_pop_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      tgt_fifo_pop_q <= '0;
      usage_q        <= '0;
    end else begin
      tgt_fifo_pop_q <= tgt_fifo_pop;
      usage_q        <= usage_d     ;
    end
  end

  for (genvar k = 0; k < NumOut; k++) begin: gen_target_queues

    // Generate request signal

    // Only request if the corresponding queue is not full
    assign req_o[k]         = tgt_xbar_req[k] & ~tgt_fifo_full[k];
    assign tgt_fifo_full[k] = (usage_q[k] == NumOutstanding)     ;

    // Target response queue
    fifo_v3 #(
      .DATA_WIDTH  (DataWidth + $clog2(NumIn)),
      .DEPTH       (NumOutstanding           ),
      .FALL_THROUGH(TargetQueueFallThrough   )
    ) i_target_queue (
      .clk_i     (clk_i                                   ),
      .rst_ni    (rst_ni                                  ),
      .flush_i   (1'b0                                    ),
      .testmode_i(1'b0                                    ),
      .data_i    ({rdata_i[k], ini_add_i[k]}              ),
      .push_i    (vld_i[k]                                ),
      .full_o    (/* Unused */                            ),
      .data_o    ({tgt_fifo_rdata[k], tgt_fifo_ini_add[k]}),
      .pop_i     (tgt_fifo_pop[k]                         ),
      .empty_o   (tgt_fifo_empty[k]                       ),
      .usage_o   (/* Unused */                            )
    );

    // Count inflight transactions
    always_comb begin
      usage_d[k] = usage_q[k];

      if (gnt_i[k] & (~wen_o[k] | WriteRespOn))
        usage_d[k] = usage_d[k] + 1'b1;

      if (TargetQueueFallThrough) begin
        // The position in the FIFO is freed at the same cycle
        if (tgt_fifo_pop[k])
          usage_d[k] = usage_d[k] - 1'b1;
      end else begin
        // Must wait a cycle before freeing the position
        if (tgt_fifo_pop_q[k])
          usage_d[k] = usage_d[k] - 1'b1;
      end
    end

    `ifndef SYNTHESIS
    `ifndef VERILATOR
    assert property (@(posedge clk_i) disable iff (!rst_ni) (usage_q[k] <= NumOutstanding)) else
      $fatal(1, "Accepted more outstanding requests than actually supported.");
    `endif
    `endif
  end

  /******************
   *   Assertions   *
   ******************/

  if (AddrMemWidth + NumOutLog2 > AddrWidth)
    $fatal(1, "[variable_latency_interconnect] Address is not wide enough to accomodate the requested TCDM configuration.");

  if (Topology != tcdm_interconnect_pkg::LIC && NumOut < NumIn)
    $fatal(1, "[variable_latency_interconnect] NumOut < NumIn is not supported with the chosen TCDM configuration.");

endmodule : variable_latency_interconnect
