// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"

module traffic_generator
  import mempool_pkg::*;
#(
  parameter int unsigned AddrWidth           = 32,
  parameter int unsigned DataWidth           = 32,
  parameter int unsigned NumCores            = 32,
  parameter int unsigned MaxOutStandingReads = 1024,
  parameter int unsigned NumBanks            = 1,
  parameter int unsigned NumCycles           = 10000,
  parameter int unsigned ReqProbability      = 500,
  parameter int unsigned SeqProbability      = 0,
  parameter int unsigned NrTCDM              = 2,
  parameter int unsigned NumRules            = 1, // Routing rules
  localparam int unsigned StrbWidth          = DataWidth/8,
  parameter addr_t TCDMBaseAddr              = 32'b0,
  parameter int unsigned NumBanksPerTile     = 0,
  localparam int unsigned ReorderIdWidth     = $clog2(MaxOutStandingReads)
) (
  input  logic                                          clk_i,
  input  logic                                          rst_ni,
  input  logic         [$clog2(NumCores)-1:0]           core_id_i,
  // to TCDM
  output logic         [NrTCDM-1:0]                     tcdm_req_valid_o,
  output logic         [NrTCDM-1:0][AddrWidth-1:0]      tcdm_req_tgt_addr_o,
  output logic         [NrTCDM-1:0]                     tcdm_req_wen_o,
  output logic         [NrTCDM-1:0][DataWidth-1:0]      tcdm_req_wdata_o,
  output logic         [NrTCDM-1:0][3:0]                tcdm_req_amo_o,
  output logic         [NrTCDM-1:0][ReorderIdWidth-1:0] tcdm_req_id_o,
  output logic         [NrTCDM-1:0][StrbWidth-1:0]      tcdm_req_be_o,
  input  logic         [NrTCDM-1:0]                     tcdm_req_ready_i,
  input  logic         [NrTCDM-1:0]                     tcdm_resp_valid_i,
  output logic         [NrTCDM-1:0]                     tcdm_resp_ready_o,
  input  logic         [NrTCDM-1:0][DataWidth-1:0]      tcdm_resp_rdata_i,
  input  logic         [NrTCDM-1:0][ReorderIdWidth-1:0] tcdm_resp_id_i,
  // Address map
  input  address_map_t [NumRules-1:0]                   address_map_i
);

  /*************
   *  IMPORTS  *
   *************/

  import snitch_pkg::dreq_t;
  import snitch_pkg::dresp_t;

  // TCDM Memory Region
  localparam addr_t TCDMSize = NumBanks * TCDMSizePerBank;
  localparam addr_t TCDMMask = ~(TCDMSize - 1);
  localparam int unsigned BankOffsetBits = $clog2(NumBanksPerTile);
  localparam int unsigned NumTilesBits   = $clog2(NumBanks/NumBanksPerTile);

  // Track the instructions
  typedef logic [ReorderIdWidth-1:0] id_t;
  int unsigned starting_cycle[id_t];

  // Cycle count
  int unsigned cycle;
  `FF(cycle, cycle+1, 0)

  /**************************
   *  PENDING INSTRUCTIONS  *
   **************************/

  id_t                            next_id;
  logic                           full;
  logic [MaxOutStandingReads-1:0] pending_instructions_d, pending_instructions_q;

  `FF(pending_instructions_q, pending_instructions_d, '0)
  lzc #(
    .WIDTH(MaxOutStandingReads)
  ) i_next_id_lzc (
    .in_i   (~pending_instructions_q),
    .cnt_o  (next_id                ),
    .empty_o(/* Unused */           )
  );

  assign full = &pending_instructions_q;
  full_traffic_generator : assert property (
      @(posedge clk_i) disable iff (!rst_ni) (!full))
  else $warning("The traffic generator exhausted all the ROB IDs.");

  /*************
   *  PAYLOAD  *
   *************/

  dreq_t               data_qpayload;
  dresp_t              data_ppayload;
  dreq_t  [NrTCDM-1:0] tcdm_qpayload;
  dresp_t [NrTCDM-1:0] tcdm_ppayload;

  for (genvar i = 0; i < NrTCDM; i++) begin : gen_tcdm_ppayload
    assign tcdm_ppayload[i].id    = tcdm_resp_id_i[i];
    assign tcdm_ppayload[i].data  = tcdm_resp_rdata_i[i];
    assign tcdm_ppayload[i].error = 1'b0;
  end

  for (genvar i = 0; i < NrTCDM; i++) begin : gen_tcdm_qpayload
    assign tcdm_req_tgt_addr_o[i] = tcdm_qpayload[i].addr;
    assign tcdm_req_wdata_o[i]    = tcdm_qpayload[i].data;
    assign tcdm_req_amo_o[i]      = tcdm_qpayload[i].amo;
    assign tcdm_req_id_o[i]       = tcdm_qpayload[i].id;
    assign tcdm_req_wen_o[i]      = tcdm_qpayload[i].write;
    assign tcdm_req_be_o[i]       = tcdm_qpayload[i].strb;
  end

  // Generate requests
  logic                 req_valid;
  logic                 req_ready;
  logic [AddrWidth-1:0] req_tgt_addr;
  logic                 resp_valid;
  logic                 resp_ready;

  // Demux according to address
  snitch_addr_demux #(
    .NrOutput     (NrTCDM   ),
    .AddressWidth (AddrWidth),
    .NumRules     (NumRules ), // TODO
    .req_t        (dreq_t   ),
    .resp_t       (dresp_t  )
  ) i_snitch_addr_demux (
    .clk_i         (clk_i            ),
    .rst_ni        (rst_ni           ),
    .req_addr_i    (req_tgt_addr     ),
    .req_payload_i (data_qpayload    ),
    .req_valid_i   (req_valid        ),
    .req_ready_o   (req_ready        ),
    .resp_payload_o(data_ppayload    ),
    .resp_valid_o  (resp_valid       ),
    .resp_ready_i  (resp_ready       ),
    .req_payload_o (tcdm_qpayload    ),
    .req_valid_o   (tcdm_req_valid_o ),
    .req_ready_i   (tcdm_req_ready_i ),
    .resp_payload_i(tcdm_ppayload    ),
    .resp_valid_i  (tcdm_resp_valid_i),
    .resp_ready_o  (tcdm_resp_ready_o),
    .address_map_i (address_map_i    )
  );

  /***********************
   *  GENERATE REQUESTS  *
   ***********************/

  logic resp_valid_q;
  id_t  resp_id_q;
  `FF(resp_valid_q, resp_valid, 0)
  `FF(resp_id_q, data_ppayload.id, 0)
  logic [NumTilesBits-1:0] tile_id;
  assign tile_id = core_id_i[$clog2(NumCores)-1 -: NumTilesBits];


  // Latency histogram
  int  unsigned latency_histogram[int];
  id_t          requests[$];


  task automatic randomUniformRequest(int numCycles, int unsigned reqProbability, int unsigned seqProbability);
    // Seed the randomizer
    process::self().srandom(core_id_i);

    repeat (numCycles) begin
      @(negedge clk_i);

      // Receive response
      if (resp_valid) begin
        automatic int unsigned latency = cycle - starting_cycle[data_ppayload.id];
        if (latency_histogram.exists(latency))
          latency_histogram[latency] = latency_histogram[latency] + 1;
        else
          latency_histogram[latency] = 1;
      end

      if (!full) begin
        automatic int unsigned val;

        // decide whether to request
        void'(randomize(val) with {val>0; val<=1000;});
        if (val <= int'(reqProbability)) begin
          // Mark the request as pending
          starting_cycle[next_id]         = cycle;
          pending_instructions_d[next_id] = 1'b1;
          requests.push_back(next_id);
        end
      end

      // Send a request if the queue is not empty
      if (requests.size() == 0) begin
        req_valid     = 1'b0;
        req_tgt_addr  = '0;
        data_qpayload = '0;
      end else begin
        automatic int unsigned val;
        void'(randomize(req_tgt_addr) with {(req_tgt_addr & TCDMMask) == TCDMBaseAddr;});
        // Make it fall into the sequential region
        void'(randomize(val) with {val>=0; val<1000;});
        if (val <= int'(seqProbability)) begin
          req_tgt_addr[BankOffsetBits + ByteOffset +: NumTilesBits] = tile_id;
        end
        req_valid         = 1'b1;
        req_tgt_addr[1:0] = '0;

        data_qpayload      = '0;
        data_qpayload.addr = req_tgt_addr;
        data_qpayload.id   = requests[0];
      end

      @(posedge clk_i);
      if (req_valid && req_ready) begin
        void'(requests.pop_front());
      end

      // Unmark the pending requests
      if (resp_valid_q) begin
        pending_instructions_d[resp_id_q] = 1'b0;
      end
    end
  endtask: randomUniformRequest

  /*************
   *  RESULTS  *
   *************/

  initial begin
    // Idle
    pending_instructions_d = '0;
    req_valid              = 1'b0;
    req_tgt_addr           = '0;
    data_qpayload          = '0;

    // We are always ready
    resp_ready = 1'b1;

    @(posedge rst_ni);
    repeat(3)
      @(posedge clk_i);

    // Start the requests
    randomUniformRequest(NumCycles, ReqProbability, SeqProbability);
  end

endmodule: traffic_generator
