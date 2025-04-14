// Copyright 2023 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Author: Diyou Shen ETH Zurich


module tcdm_burst_manager #(
  parameter int unsigned      NrInOut           = 1,
  parameter int unsigned      ByteOffset        = 2,

  parameter int unsigned      MetaIdWidth       = 1,
  parameter int unsigned      TCDMAddrWidth     = 1,

  // Group Response Extension Grouping Factor for TCDM
  parameter int unsigned      RspGF             = 1,

  parameter type              req_payload_t     = logic,
  parameter type              rsp_payload_t     = logic,
  parameter type              addr_t            = logic,
  parameter type              tile_addr_t       = logic
) (
  input  logic                clk_i,
  input  logic                rst_ni,

  /// Xbar side
  input  req_payload_t  [NrInOut-1:0] req_payload_i,
  input  addr_t         [NrInOut-1:0] req_addr_i,
  input  logic          [NrInOut-1:0] req_wide_i,
  input  logic          [NrInOut-1:0] req_valid_i,
  output logic          [NrInOut-1:0] req_ready_o,

  output rsp_payload_t  [NrInOut-1:0] rsp_payload_o,
  output addr_t         [NrInOut-1:0] rsp_addr_o,
  output logic          [NrInOut-1:0] rsp_wide_o,
  output logic          [NrInOut-1:0] rsp_valid_o,
  input  logic          [NrInOut-1:0] rsp_ready_i,

  /// Bank side
  output req_payload_t  [NrInOut-1:0] req_payload_o,
  output addr_t         [NrInOut-1:0] req_addr_o,
  output logic          [NrInOut-1:0] req_wide_o,
  output logic          [NrInOut-1:0] req_valid_o,
  input  logic          [NrInOut-1:0] req_ready_i,

  input  rsp_payload_t  [NrInOut-1:0] rsp_payload_i,
  input  addr_t         [NrInOut-1:0] rsp_addr_i,
  input  logic          [NrInOut-1:0] rsp_wide_i,
  input  logic          [NrInOut-1:0] rsp_valid_i,
  output logic          [NrInOut-1:0] rsp_ready_o
);
  /*************************************************************
   * req_i --+--> arbiter --> fifo --> req generator --> req_o *
   *         \--------------- bypass ------------------> req_o *
   * rsp_o <----- data_grouper <----- rsp_i                    *
   *************************************************************/

  // Include FF module
  `include "common_cells/registers.svh"

  localparam int unsigned BankOffsetBits  = $clog2(NrInOut);
  localparam int unsigned IdWidth = (NrInOut > 32'd1) ? unsigned'($clog2(NrInOut)) : 32'd1;
  // Number of groups we will check for grouping rsp
  localparam int unsigned NumGroup = (RspGF <= 1) ? 0 : NrInOut/RspGF;
  // rr_arb_tree related parameters, do not override
  localparam bit          ExtPrio   = 1'b0;
  localparam bit          AxiVldRdy = 1'b1;
  localparam bit          LockIn    = 1'b1;

  typedef logic [MetaIdWidth-1:0] meta_id_t;

  /******************
   * Burst Identify *
   ******************/
  typedef struct packed {
    req_payload_t   payload;
    addr_t          ini_addr;
    logic           wide;
  } arb_data_t;

  arb_data_t [NrInOut-1:0]  prearb_data;
  logic      [NrInOut-1:0]  prearb_valid, prearb_ready;

  arb_data_t postarb_data;
  logic      postarb_valid, postarb_ready;
  logic      [IdWidth-1:0]  postarb_idx;

  logic      [NrInOut-1:0]  valid_mask;
  logic      [NrInOut-1:0]  ready_mask;
  logic      [NrInOut-1:0]  not_ready_mask;

  always_comb begin
    prearb_data    = '0;
    prearb_valid   = '0;
    // If bypass, forward the valid and ready
    valid_mask     = req_valid_i;
    // To indicate which bank need to be ready for ack the burst request
    ready_mask     = '0;
    not_ready_mask = '1;

    for (int unsigned i = 0; i < NrInOut; i++) begin
      if (req_valid_i[i] && req_payload_i[i].burst.isburst) begin
        prearb_data[i] = '{
          payload:  req_payload_i[i],
          ini_addr: req_addr_i[i],
          wide:     req_wide_i[i]
        };
        prearb_valid[i]   = 1'b1;
        // If burst, invalid this request to bank
        valid_mask[i]     = 1'b0;

        if (prearb_ready[i]) begin
          // request is picked by arbiter and fifo, mark as accepted
          ready_mask[i]   = 1'b1;
        end else begin
          // This means this burst request is not picked yet, do not ack it
          not_ready_mask[i]   = 1'b0;
        end
      end
    end
  end

  rr_arb_tree #(
    .NumIn     ( NrInOut       ),
    .DataType  ( arb_data_t    ),
    .ExtPrio   ( ExtPrio       ),
    .AxiVldRdy ( AxiVldRdy     ),
    .LockIn    ( LockIn        )
  ) i_rr_arb_tree (
    .clk_i   ( clk_i           ),
    .rst_ni  ( rst_ni          ),
    .flush_i ( 1'b0            ),
    .rr_i    ( '0              ),
    .req_i   ( prearb_valid    ),
    .gnt_o   ( prearb_ready    ),
    .data_i  ( prearb_data     ),
    .req_o   ( postarb_valid   ),
    .gnt_i   ( postarb_ready   ),
    .data_o  ( postarb_data    ),
    .idx_o   ( postarb_idx     )
  );

  typedef struct packed {
    req_payload_t       payload;
    addr_t              ini_addr;
    logic               wide;
    logic [IdWidth-1:0] idx;
  } fifo_data_t;

  fifo_data_t   fifo_data, pre_fifo_data;
  logic         fifo_pop, fifo_empty, fifo_full, fifo_push;

  assign postarb_ready = fifo_full ? 1'b0 : 1'b1;
  assign pre_fifo_data = '{
    payload:  postarb_data.payload,
    ini_addr: postarb_data.ini_addr,
    wide:     postarb_data.wide,
    idx:      postarb_idx
  };
  // Push when FIFO is not full and data is valid
  assign fifo_push = postarb_valid & (~fifo_full);

  // Fall though FIFO to store bursts
  fifo_v3 #(
    .FALL_THROUGH ( 1'b1            ),
    .DEPTH        ( NrInOut         ),
    .dtype        ( fifo_data_t     )
  ) i_fall_though_fifo (
    .clk_i        ( clk_i           ),
    .rst_ni       ( rst_ni          ),
    .flush_i      ( 1'b0            ),
    .testmode_i   ( 1'b0            ),
    .full_o       ( fifo_full       ),
    .empty_o      ( fifo_empty      ),
    .usage_o      ( /*not used */   ),
    .data_i       ( pre_fifo_data   ),
    .push_i       ( fifo_push       ),
    .data_o       ( fifo_data       ),
    .pop_i        ( fifo_pop        )
  );

  /*********************
   * Request Generator *
   *********************/

  typedef enum logic {
    // idle until burst request comes
    Idle,
    // generate parallel requests when ready
    DoBurst
  } req_gen_fsm_e;

  // generated ID and Addr
  meta_id_t   [NrInOut-1:0] gen_id;
  tile_addr_t [NrInOut-1:0] gen_addr;

  // FSM state
  req_gen_fsm_e  state_d, state_q;
  // FSM stored signals
  fifo_data_t     breq_d, breq_q;
  logic [NrInOut-1:0] burst_mask_d, burst_mask_q;
  logic [NrInOut-1:0] burst_valid_mask, burst_ready_mask;

  // group mask used for response grouping
  logic [NrInOut-1:0] group_mask;

  // indicate if there is pending response to be picked
  logic pending_rsp;


  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(~rst_ni) begin
      state_q      <= Idle;
      breq_q       <= '0;
      burst_mask_q <= '0;
    end else begin
      state_q      <= state_d;
      breq_q       <= breq_d;
      burst_mask_q <= burst_mask_d;
    end
  end

  always_comb begin : request_generator
    // FSM defaults
    state_d       = state_q;
    breq_d        = breq_q;
    burst_mask_d  = burst_mask_q;

    // comb logic defaults
    gen_id        = '0;
    gen_addr      = '0;
    pending_rsp   = '0;
    group_mask    = '0;

    // Do not take in next burst for now
    fifo_pop      = 1'b0;

    // By defauly, bypass input ready and valid signals
    burst_valid_mask = req_valid_i;
    burst_ready_mask = req_ready_i;
    // Bypass all requests by default
    req_payload_o = req_payload_i;
    req_wide_o    = req_wide_i;
    req_addr_o    = req_addr_i;
    // Bypass not-masked ready, stall all other ready
    req_valid_o   = valid_mask & burst_valid_mask;
    // By default, pass the ready signals
    req_ready_o   = (ready_mask | burst_ready_mask) & not_ready_mask;

    case (state_q)
      Idle: begin
        // Idle state, ready to take in burst request

        // Clear mask (unlock banks)
        burst_mask_d  = '0;

        if (~fifo_empty) begin
          // there is pending burst request
          // start to handling the burst, mark as not ready
          // pop next element
          fifo_pop = 1'b1;
          // store request
          breq_d = fifo_data;
          // a mask with burst length ones
          burst_mask_d = (1'b1 << breq_d.payload.burst.blen) - 1'b1;
          // then left shift by id of port
          burst_mask_d = burst_mask_d << breq_d.idx;
          // the mask should now have ones from the starting port, with length blen

          state_d   = DoBurst;
        end

        req_ready_o   = (ready_mask | burst_ready_mask) & not_ready_mask;
      end

      DoBurst: begin
        // all masked ready bits need to be 1 -> all banks ready
        // for influenced banks, marked as not ready
        burst_ready_mask = req_ready_i & ~burst_mask_q;

        // Check if there is pending responses among the affected banks
        // If the valid is high, but ready is low, we need to wait
        pending_rsp = |((rsp_valid_o & ~rsp_ready_i) & burst_mask_q);
        // only send out requests when
        // 1. required banks are all ready
        // 2. no pending responses among them
        if (&(req_ready_i | (~burst_mask_q)) & !pending_rsp) begin
          // calculate the id and tgt_addr for parallel requests
          for (int unsigned i = 0; i < NrInOut; i ++) begin
            // an array of values equal id, plus the input id
            gen_id[i]   = i + breq_q.payload.wdata.meta_id;
            gen_addr[i] = i + breq_q.payload.tgt_addr;
          end
          // offset the array to correct location
          gen_id   = gen_id   << (breq_q.idx * MetaIdWidth);
          gen_addr = gen_addr << (breq_q.idx * TCDMAddrWidth);

          req_valid_o   = valid_mask;

          for (int unsigned i = 0; i < NrInOut; i ++) begin
            if (burst_mask_q[i]) begin
              // Most info are the same, except id and tgt_addr
              req_payload_o[i]               = breq_q.payload;
              // overwrite meta_id and tgt_addr
              req_payload_o[i].wdata.meta_id = gen_id[i];
              req_payload_o[i].tgt_addr      = gen_addr[i];

              req_wide_o[i]          = breq_q.wide;
              req_addr_o[i]          = breq_q.ini_addr;

              // request valid, tie sent requests to 1
              req_valid_o[i] = 1'b1;
            end
          end
          // Request sent
          // Put the mask into FF, rsp should be avaiblable in next cycle
          group_mask = (RspGF > 1) ? burst_mask_q : '0;
          // Switch stae
          state_d = Idle;
        end else begin
          // We are waiting for banks to become ready, block the incoming requests
          burst_valid_mask = ~burst_mask_q;
          req_valid_o   = valid_mask & burst_valid_mask;
        end
        req_ready_o   = (ready_mask | burst_ready_mask) & not_ready_mask;
      end

      default: state_d = Idle;
    endcase
  end

  /******************
   *   Rsp Handling *
   ******************/

  if (RspGF == 1) begin : gen_grouper_bypass
    // Bypass all responses if no grouping
    assign rsp_valid_o   = rsp_valid_i;
    assign rsp_ready_o   = rsp_ready_i;
    assign rsp_addr_o    = rsp_addr_i;
    assign rsp_wide_o    = rsp_wide_i;
    assign rsp_payload_o = rsp_payload_i;

  end else begin : gen_grouper
    for (genvar i = 0; i < NumGroup; i ++) begin : gen_data_grouper
      data_grouper #(
        .RspGF          ( RspGF         ),
        .addr_t         ( addr_t        ),
        .rsp_payload_t  ( rsp_payload_t )
      ) i_data_grouper (
        .clk_i          ( clk_i                          ),
        .rst_ni         ( rst_ni                         ),
        // Only group the response if all response can be grouped
        .group_i        ( &group_mask   [i*RspGF+:RspGF] ),

        .rsp_payload_o  ( rsp_payload_o [i*RspGF+:RspGF] ),
        .rsp_addr_o     ( rsp_addr_o    [i*RspGF+:RspGF] ),
        .rsp_wide_o     ( rsp_wide_o    [i*RspGF+:RspGF] ),
        .rsp_valid_o    ( rsp_valid_o   [i*RspGF+:RspGF] ),
        .rsp_ready_i    ( rsp_ready_i   [i*RspGF+:RspGF] ),

        .rsp_payload_i  ( rsp_payload_i [i*RspGF+:RspGF] ),
        .rsp_addr_i     ( rsp_addr_i    [i*RspGF+:RspGF] ),
        .rsp_wide_i     ( rsp_wide_i    [i*RspGF+:RspGF] ),
        .rsp_valid_i    ( rsp_valid_i   [i*RspGF+:RspGF] ),
        .rsp_ready_o    ( rsp_ready_o   [i*RspGF+:RspGF] )
      );
    end
  end

  /******************
   *   Assertions   *
   ******************/
  if (NrInOut == 0)
    $error("[burst_manager] NrInOut needs to be greater or equal to 1");

  if (NrInOut < RspGF)
    $error("[burst_manager] NrInOut needs to be larger or equal to RspGF");

endmodule : tcdm_burst_manager
