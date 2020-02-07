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
// Author: Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
//         Matheus Cavalcante <matheusd@iis.ee.ethz.ch>, ETH Zurich
// Date: 16.01.2020
// Description: TCDM interconnect with different network topologies. Currently
// supported are: full crossbar, radix-2/4 butterflies and clos networks.
// Note that only the full crossbar allows NumIn/NumOut configurations that are not
// aligned to a power of 2.

module numa_interconnect #(
    // Global parameters
    parameter int unsigned NumIn          = 32                   , // number of initiator ports (must be aligned with power of 2 for bfly and clos)
    parameter int unsigned NumOut         = 64                   , // number of target ports (must be aligned with power of 2 for bfly and clos)
    parameter int unsigned AddrWidth      = 32                   , // address width on initiator side
    parameter int unsigned DataWidth      = 32                   , // word width of data
    parameter int unsigned BeWidth        = DataWidth/8          , // width of corresponding byte enables
    parameter int unsigned AddrMemWidth   = 12                   , // number of address bits per TCDM bank
    parameter int unsigned NumOutstanding = 2                    , // number of outstanding transactions per target
    parameter bit unsigned WriteRespOn    = 1'b1                 , // defines whether the interconnect returns a write response
    // Determines the width of the byte offset in a memory word. normally this can be left at the default vaule,
    // but sometimes it needs to be overridden (e.g. when meta-data is supplied to the memory via the wdata signal).
    parameter int unsigned ByteOffWidth   = $clog2(DataWidth-1)-3,

    // Topology can be: LIC, BFLY2, BFLY4, CLOS
    parameter tcdm_interconnect_pkg::topo_e Topology = tcdm_interconnect_pkg::LIC,
    // This detemines which Clos config to use, only relevant for CLOS topologies
    // 1: m=0.50*n, 2: m=1.00*n, 3: m=2.00*n
    parameter int unsigned ClosConfig                = 2
  ///////////////////////////
  ) (
    input  logic                                 clk_i,
    input  logic                                 rst_ni,
    // master side
    input  logic [NumIn-1:0]                     req_i,   // request signal
    input  logic [NumIn-1:0][AddrWidth-1:0]      add_i,   // tcdm address
    input  logic [NumIn-1:0]                     wen_i,   // 1: store, 0: load
    input  logic [NumIn-1:0][DataWidth-1:0]      wdata_i, // write data
    input  logic [NumIn-1:0][BeWidth-1:0]        be_i,    // byte enable
    output logic [NumIn-1:0]                     gnt_o,   // grant (combinationally dependent on req_i and add_i
    output logic [NumIn-1:0]                     vld_o,   // response valid, also asserted if write responses are enabled
    input  logic [NumIn-1:0]                     rdy_i,   // response ready
    output logic [NumIn-1:0][DataWidth-1:0]      rdata_o, // data response (for load commands)
    // slave side
    output logic [NumOut-1:0]                    req_o,   // request out
    output logic [NumOut-1:0][$clog2(NumIn)-1:0] idx_o,   // initiator port index
    input  logic [NumOut-1:0]                    gnt_i,   // grant input
    output logic [NumOut-1:0][AddrMemWidth-1:0]  add_o,   // address within bank
    output logic [NumOut-1:0]                    wen_o,   // write enable
    output logic [NumOut-1:0][DataWidth-1:0]     wdata_o, // write data
    output logic [NumOut-1:0][BeWidth-1:0]       be_o,    // byte enable
    input  logic [NumOut-1:0]                    vld_i,   // response valid
    input  logic [NumOut-1:0][$clog2(NumIn)-1:0] idx_i,   // initiator port index
    input  logic [NumOut-1:0][DataWidth-1:0]     rdata_i  // data response (for load commands)
  );

  /*******************
   *   LOCALPARAMS   *
   *******************/

  // localparams and aggregation of address, wen and payload data

  localparam int unsigned NumOutLog2     = $clog2(NumOut);
  localparam int unsigned AggDataWidth   = 1 + BeWidth + AddrMemWidth + DataWidth;
  localparam int unsigned TransactionIdx = NumOutstanding > 1 ? $clog2(NumOutstanding) : 1;

  logic [NumIn-1:0][AggDataWidth-1:0]  data_agg_in;
  logic [NumOut-1:0][AggDataWidth-1:0] data_agg_out;
  logic [NumIn-1:0][NumOutLog2-1:0]    bank_sel;

  logic [NumOut-1:0] network_req;

  logic [NumOut-1:0][DataWidth-1:0]     sl_fifo_rdata;
  logic [NumOut-1:0][$clog2(NumIn)-1:0] sl_fifo_idx;
  logic [NumOut-1:0]                    sl_fifo_full;
  logic [NumOut-1:0]                    sl_fifo_empty;
  logic [NumOut-1:0]                    sl_fifo_pop;

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
   *   NETWORKS   *
   ****************/

  // Only request if the corresponding queue is not full
  assign req_o = network_req & ~sl_fifo_full;

  // Tuned logarithmic interconnect architecture, based on rr_arb_tree primitives
  if (Topology == tcdm_interconnect_pkg::LIC) begin : gen_lic
    numa_xbar #(
      .NumIn        (NumIn       ),
      .NumOut       (NumOut      ),
      .ReqDataWidth (AggDataWidth),
      .RespDataWidth(DataWidth   )
    ) i_xbar (
      .clk_i   (clk_i         ),
      .rst_ni  (rst_ni        ),
      .rr_i    ('0            ),
      .rr_ret_i('0            ),
      .req_i   (req_i         ),
      .gnt_o   (gnt_o         ),
      .add_i   (bank_sel      ),
      .wdata_i (data_agg_in   ),
      .vld_o   (vld_o         ),
      .rdata_o (rdata_o       ),
      .rdy_i   (rdy_i         ),
      .req_o   (network_req   ),
      .idx_o   (idx_o         ),
      .gnt_i   (gnt_i         ),
      .wdata_o (data_agg_out  ),
      .vld_i   (~sl_fifo_empty),
      .rdy_o   (sl_fifo_pop   ),
      .idx_i   (sl_fifo_idx   ),
      .rdata_i (sl_fifo_rdata )
    );
  end
  // Butterfly network (radix 2 or 4)
  else if (Topology == tcdm_interconnect_pkg::BFLY2 || Topology == tcdm_interconnect_pkg::BFLY4) begin : gen_bfly
    localparam int unsigned Radix = 2**Topology ;

    logic [NumOut-1:0][AggDataWidth-1:0] data1;
    logic [NumOut-1:0][DataWidth-1:0] rdata1  ;
    logic [NumOut-1:0] gnt1, req1;

    logic [NumOut-1:0][AggDataWidth-1:0] data1_trsp ;
    logic [NumOut-1:0][DataWidth-1:0] rdata1_trsp   ;
    logic [NumOut-1:0] gnt1_trsp                    ;
    logic [NumOut-1:0] req1_trsp                    ;

    logic [$clog2(NumOut)-1:0] rr    ;
    logic [$clog2(NumOut)-1:0] rr_ret;

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
      .clk_i  ,
      .rst_ni ,
      .en_i  (|(gnt_i & req_o)),
      .out_o ({rr_ret, rr}    )
    );

    numa_bfly_net #(
      .NumIn        (NumIn       ),
      .NumOut       (NumOut      ),
      .ReqDataWidth (AggDataWidth),
      .RespDataWidth(DataWidth   ),
      .Radix        (Radix       ),
      .ExtPrio      (1'b1        )
    ) i_bfly_net (
      .clk_i   (clk_i         ),
      .rst_ni  (rst_ni        ),
      .rr_i    (rr            ),
      .rr_ret_i(rr_ret        ),
      .req_i   (req_i         ),
      .gnt_o   (gnt_o         ),
      .add_i   (bank_sel      ),
      .wdata_i (data_agg_in   ),
      .vld_o   (vld_o         ),
      .rdy_i   (rdy_i         ),
      .rdata_o (rdata_o       ),
      .req_o   (network_req   ),
      .idx_o   (idx_o         ),
      .gnt_i   (gnt_i         ),
      .wdata_o (data_agg_out  ),
      .vld_i   (~sl_fifo_empty),
      .rdy_o   (sl_fifo_pop   ),
      .idx_i   (sl_fifo_idx   ),
      .rdata_i (sl_fifo_rdata )
    );
  // Clos network
  end else if (Topology == tcdm_interconnect_pkg::CLOS) begin : gen_clos
    numa_clos_net #(
      .NumIn        (NumIn       ),
      .NumOut       (NumOut      ),
      .ReqDataWidth (AggDataWidth),
      .RespDataWidth(DataWidth   ),
      .ClosConfig   (ClosConfig  )
    ) i_clos_net (
      .clk_i  (clk_i         ),
      .rst_ni (rst_ni        ),
      .req_i  (req_i         ),
      .gnt_o  (gnt_o         ),
      .add_i  (bank_sel      ),
      .wdata_i(data_agg_in   ),
      .vld_o  (vld_o         ),
      .rdy_i  (rdy_i         ),
      .rdata_o(rdata_o       ),
      .req_o  (network_req   ),
      .idx_o  (idx_o         ),
      .gnt_i  (gnt_i         ),
      .wdata_o(data_agg_out  ),
      .vld_i  (~sl_fifo_empty),
      .rdy_o  (sl_fifo_pop   ),
      .idx_i  (sl_fifo_idx   ),
      .rdata_i(sl_fifo_rdata )
    );
  // Unknown topology
  end else begin : gen_unknown
    `ifndef SYNTHESIS
    initial begin
      $fatal(1, "Unknown TCDM configuration %d.", Topology);
    end
    `endif
  end


  /*********************
   *   TARGET QUEUES   *
   *********************/

  logic [NumOut-1:0][TransactionIdx:0] usage_q;

  for (genvar k = 0; k < NumOut; k++) begin: gen_target_queues

    fifo_v3 #(
      .DATA_WIDTH (DataWidth + $clog2(NumIn)),
      .DEPTH      (NumOutstanding           )
    ) i_target_queue (
      .clk_i     (clk_i                             ),
      .rst_ni    (rst_ni                            ),
      .flush_i   (1'b0                              ),
      .testmode_i(1'b0                              ),
      .data_i    ({rdata_i[k], idx_i[k]}            ),
      .push_i    (vld_i[k]                          ),
      .full_o    (/* Unused */                      ),
      .data_o    ({sl_fifo_rdata[k], sl_fifo_idx[k]}),
      .pop_i     (sl_fifo_pop[k]                    ),
      .empty_o   (sl_fifo_empty[k]                  ),
      .usage_o   (/* Unused */                      )
    );

    // Count in-flight transactions
    logic sl_fifo_pop_q;

    assign sl_fifo_full[k] = (usage_q[k] == NumOutstanding);

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        usage_q[k]    <= '0;
        sl_fifo_pop_q <= '0;
      end else begin
        usage_q[k]    <= usage_q[k] + (gnt_i[k] & (~wen_o[k] | WriteRespOn)) - sl_fifo_pop_q;
        sl_fifo_pop_q <= sl_fifo_pop[k]                                                     ;
      end
    end

    `ifndef SYNTHESIS
    assert property (@(posedge clk_i) disable iff (!rst_ni) (usage_q[k] <= NumOutstanding))
    else $fatal(1, "Accepted more outstanding requests than actually supported.");
    `endif
  end

  /******************
   *   ASSERTIONS   *
   ******************/

  `ifndef SYNTHESIS
  initial begin
    assert (AddrMemWidth + NumOutLog2 <= AddrWidth) else
      $fatal(1, "Address not wide enough to accomodate the requested TCDM configuration.");

    assert (Topology == tcdm_interconnect_pkg::LIC || NumOut >= NumIn) else
      $fatal(1, "NumOut < NumIn is not supported.");
  end
  `endif

endmodule : numa_interconnect
