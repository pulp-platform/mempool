// Copyright 2023 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Author: Diyou Shen ETH Zurich
// Author: Marco Bertuletti ETH Zurich

/// Burst Req Manager:
/// Receives a burst request from NumIn initiators and produces a parallel request
/// to NumIn target banks in a target multi-banked memory with NumOut banks.
/// Collects a parallel response from NumOut banks in a target multi-banked memory
/// and groups them according to the RspGF.

module tcdm_burst_manager
  import tcdm_burst_pkg::*;
#(
  parameter int unsigned NumIn  = 32, // number of initiator ports
  parameter int unsigned NumOut = 64, // number of destination ports
  parameter int unsigned AddrWidth  = 32,
  parameter int unsigned DataWidth  = 32,
  parameter int unsigned BeWidth    = DataWidth/8,
  // determines the width of the byte offset in a memory word. normally this can be left at the default vaule,
  // but sometimes it needs to be overridden (e.g. when meta-data is supplied to the memory via the wdata signal).
  parameter int unsigned  ByteOffWidth = $clog2(DataWidth-1)-3,
  // Group Response Extension Grouping Factor for TCDM
  parameter int unsigned  RspGF = 1,
  // Dependant parameters. DO NOT CHANGE!
  parameter int unsigned NumInLog2 = (NumIn == 1) ? 1 : $clog2(NumIn),
  // Burst response type can be overwritten for DataWidth > 32b
  // This can happen when the DataWidth includes transaction metadata
  parameter type burst_resp_t = tcdm_burst_pkg::burst_gresp_t
) (
  input  logic clk_i,
  input  logic rst_ni,
  /// Xbar side
  input  logic   [NumOut-1:0][NumInLog2-1:0] req_ini_addr_i,
  input  logic   [NumOut-1:0][AddrWidth-1:0] req_tgt_addr_i,
  input  logic   [NumOut-1:0][DataWidth-1:0] req_wdata_i,
  input  logic   [NumOut-1:0]                req_wen_i,
  input  logic   [NumOut-1:0][BeWidth-1:0]   req_ben_i,
  input  burst_t [NumOut-1:0]                req_burst_i,
  input  logic   [NumOut-1:0]                req_valid_i,
  output logic   [NumOut-1:0]                req_ready_o,
  //
  output logic         [NumOut-1:0][NumInLog2-1:0] resp_ini_addr_o,
  output logic         [NumOut-1:0][DataWidth-1:0] resp_rdata_o,
  output burst_resp_t  [NumOut-1:0]                resp_burst_o,
  output logic         [NumOut-1:0]                resp_valid_o,
  input  logic         [NumOut-1:0]                resp_ready_i,
  /// Bank side
  output logic [NumOut-1:0][NumInLog2-1:0] req_ini_addr_o,
  output logic [NumOut-1:0][AddrWidth-1:0] req_tgt_addr_o,
  output logic [NumOut-1:0][DataWidth-1:0] req_wdata_o,
  output logic [NumOut-1:0]                req_wen_o,
  output logic [NumOut-1:0][BeWidth-1:0]   req_ben_o,
  output logic [NumOut-1:0]                req_valid_o,
  input  logic [NumOut-1:0]                req_ready_i,
  //
  input  logic [NumOut-1:0][NumInLog2-1:0] resp_ini_addr_i,
  input  logic [NumOut-1:0][DataWidth-1:0] resp_rdata_i,
  input  logic [NumOut-1:0]                resp_valid_i,
  output logic [NumOut-1:0]                resp_ready_o
);
  /*************************************************************
   * req_i --+--> arbiter --> fifo --> req generator --> req_o *
   *         \--------------- bypass ------------------> req_o *
   * rsp_o <----- data_grouper <----- rsp_i                    *
   *************************************************************/

  // Include FF module
  `include "common_cells/registers.svh"

  localparam int unsigned NumOutLog2 = (NumOut > 32'd1) ? unsigned'($clog2(NumOut)) : 32'd1;

  /******************
   * Burst Identify *
   ******************/

  typedef struct packed {
    logic   [NumInLog2-1:0] ini_addr;
    logic   [AddrWidth-1:0] tgt_addr;
    logic   [DataWidth-1:0] wdata;
    logic                   wen;
    logic   [BeWidth]       ben;
    burst_t                 burst;
  } arb_data_t;

  arb_data_t [NumOut-1:0]      prearb_data;
  logic      [NumOut-1:0]      prearb_valid, prearb_ready;
  arb_data_t                   postarb_data;
  logic                        postarb_valid, postarb_ready;
  logic      [NumOutLog2-1:0]  postarb_idx;
  logic      [NumOut-1:0]  ready_mask;
  logic      [NumOut-1:0]  valid_mask;

  always_comb begin
    prearb_data    = '0;
    prearb_valid   = '0;
    ready_mask     = '0;
    valid_mask     = req_valid_i;

    for (int unsigned i = 0; i < NumOut; i++) begin
      if (req_valid_i[i] && req_burst_i[i].isburst) begin
        prearb_data[i].ini_addr = req_ini_addr_i[i];
        prearb_data[i].tgt_addr = req_tgt_addr_i[i];
        prearb_data[i].wdata = req_wdata_i[i];
        prearb_data[i].wen = req_wen_i[i];
        prearb_data[i].ben = req_ben_i[i];
        prearb_data[i].burst = req_burst_i[i];
        prearb_valid[i] = 1'b1;
        valid_mask = 1'b0;
        // Mark retired burst requests
        if (prearb_ready[i]) begin
          ready_mask[i]   = 1'b1;
        end
      end
    end
  end

  rr_arb_tree #(
    .NumIn     ( NumOut       ),
    .DataType  ( arb_data_t    ),
    .ExtPrio   ( 1'b0),
    .AxiVldRdy ( 1'b1),
    .LockIn    ( 1'b1)
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
    logic   [NumInLog2-1:0]  ini_addr;
    logic   [AddrWidth-1:0]  tgt_addr;
    logic   [DataWidth-1:0]  wdata;
    logic                    wen;
    logic   [BeWidth]        ben;
    burst_t                  burst;
    logic   [NumOutLog2-1:0] idx;
  } fifo_data_t;

  fifo_data_t   fifo_data, pre_fifo_data;
  logic         fifo_pop, fifo_empty, fifo_full, fifo_push;

  assign postarb_ready = fifo_full ? 1'b0 : 1'b1;
  assign pre_fifo_data.ini_addr = postarb_data.ini_addr;
  assign pre_fifo_data.tgt_addr = postarb_data.tgt_addr;
  assign pre_fifo_data.wdata = postarb_data.wdata;
  assign pre_fifo_data.wen = postarb_data.wen;
  assign pre_fifo_data.ben = postarb_data.ben;
  assign pre_fifo_data.burst = postarb_data.burst;
  assign pre_fifo_data.idx = postarb_idx;

  // Push when FIFO is not full and data is valid
  assign fifo_push = postarb_valid & (~fifo_full);

  // Fall though FIFO to store bursts
  fifo_v3 #(
    .FALL_THROUGH ( 1'b1            ),
    .DEPTH        ( NumOut         ),
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
    Idle, // idle until burst request comes
    DoBurst // generate parallel requests when ready
  } req_gen_fsm_e;

  // FSM state
  req_gen_fsm_e state_d, state_q;
  // FSM stored signals
  fifo_data_t breq_d, breq_q;

  logic [NumOut-1:0] burst_mask_d, burst_mask_q;
  // group mask used for response grouping
  logic [NumOut-1:0] group_mask_d, group_mask_q;

  // indicate if there is pending response to be picked
  logic pending_rsp;

  `FF(state_q, state_d, Idle, clk_i, rst_ni);
  `FF(breq_q, breq_d, '0, clk_i, rst_ni);
  `FF(burst_mask_q, burst_mask_d, '0, clk_i, rst_ni);
  `FF(group_mask_q, group_mask_d, '0, clk_i, rst_ni);

  // Each element of a burst request must be retired to start request
  assign req_ready_o = ready_mask | (req_ready_i & ~burst_mask_q);

  always_comb begin : request_generator

    // FSM defaults
    state_d = state_q;
    breq_d = breq_q;
    burst_mask_d  = burst_mask_q;

    // comb logic defaults
    pending_rsp = '0;
    // Do not take in next burst for now
    fifo_pop = 1'b0;

    // Bypass all requests by default
    req_wdata_o = req_wdata_i;
    req_tgt_addr_o = req_tgt_addr_i;
    req_ini_addr_o = req_ini_addr_i;
    req_wen_o = req_wen_i;
    req_ben_o = req_ben_i;

    // Let valid requests not in burst pass
    req_valid_o = valid_mask;

    case (state_q)

      // Idle state, ready to take in burst request
      Idle: begin

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
          burst_mask_d = (1'b1 << breq_d.burst.blen) - 1'b1;
          // shift the mask to the first bank index addressed by the burst
          burst_mask_d = burst_mask_d << breq_d.idx;
          state_d   = DoBurst;
        end

      end

      DoBurst: begin

        // If there is pending responses among the affected banks we wait
        pending_rsp = |((resp_valid_o & ~resp_ready_i) & burst_mask_q);
        // Send out requests when 1. required banks are all ready 2. no pending responses
        if (&(req_ready_i | (~burst_mask_q)) & !pending_rsp) begin
          for (int unsigned i = 0; i < NumOut; i++) begin
            if (burst_mask_q[i]) begin
              req_wdata_o[i] = breq_q.wdata;
              req_wen_o[i] = breq_q.wen;
              req_ben_o[i] = breq_q.ben;
              // overwrite tgt_addr
              req_tgt_addr_o[i] = i + breq_q.tgt_addr - breq_q.idx;
              req_ini_addr_o[i] = i + breq_q.ini_addr - breq_q.idx;
              // Set the valid for burst requests
              req_valid_o[i] = 1'b1;
            end
          end
          // Switch state
          state_d = Idle;
        end

      end

      default: state_d = Idle;
    endcase
  end

  /******************
   *   Rsp Handling *
   ******************/

  if (RspGF == 1) begin : gen_grouper_bypass
    // Bypass all responses if no grouping
    assign resp_valid_o = resp_valid_i;
    assign resp_ready_o = resp_ready_i;
    assign resp_rdata_o = resp_rdata_i;
    assign resp_ini_addr_o = resp_ini_addr_i;
    assign resp_burst_o = '0;

  end else begin : gen_grouper

    // Number of groups we will check for grouping rsp
    localparam int unsigned NumGroup = RspGF > 0 ? NumOut >> $clog2(RspGF) : NumOut;

    logic         [NumOut-1:0][NumInLog2-1:0] grouped_resp_ini_addr;
    logic         [NumOut-1:0][DataWidth-1:0] grouped_resp_rdata;
    burst_resp_t  [NumOut-1:0]                grouped_resp_burst;
    logic         [NumOut-1:0]                grouped_resp_valid;
    logic         [NumOut-1:0]                grouped_resp_ready;

    for (genvar i = 0; i < NumGroup; i ++) begin : gen_data_grouper
      tcdm_burst_rsp_grouper #(
        .NumIn        ( NumIn        ),
        .NumOut       ( NumOut       ),
        .DataWidth    ( DataWidth    ),
        .RspGF        ( RspGF        ),
        .burst_resp_t ( burst_resp_t )
      ) i_tcdm_burst_rsp_grouper (
        .clk_i  (clk_i  ),
        .rst_ni (rst_ni ),
        /// Bank side
        .resp_ini_addr_i (resp_ini_addr_i[i*RspGF+:RspGF]       ),
        .resp_rdata_i    (resp_rdata_i[i*RspGF+:RspGF]          ),
        .resp_valid_i    (resp_valid_i[i*RspGF+:RspGF]          ),
        .resp_ready_o    (grouped_resp_ready[i*RspGF+:RspGF]    ),
        /// Xbar side
        .resp_ini_addr_o (grouped_resp_ini_addr[i*RspGF+:RspGF] ),
        .resp_rdata_o    (grouped_resp_rdata[i*RspGF+:RspGF]    ),
        .resp_burst_o    (grouped_resp_burst[i*RspGF+:RspGF]    ),
        .resp_valid_o    (grouped_resp_valid[i*RspGF+:RspGF]    ),
        .resp_ready_i    (resp_ready_i[i*RspGF+:RspGF]          )
      );
    end

    always_comb begin
      for (int i = 0; i < NumGroup; i ++) begin
        if (state_q == DoBurst) begin
          group_mask_d[i*RspGF+:RspGF] = {RspGF{&burst_mask_q[i*RspGF+:RspGF]}};
        end else if (resp_ready_i[i*RspGF]) begin
          group_mask_d[i*RspGF+:RspGF] = '0;
        end else begin
          group_mask_d[i*RspGF+:RspGF] = group_mask_q[i*RspGF+:RspGF];
        end
      end
    end

    for (genvar i = 0; i < NumOut; i++) begin
      assign resp_ini_addr_o[i] = group_mask_q[i] ? (i % RspGF == 0 ? grouped_resp_ini_addr[i] : '0) : resp_ini_addr_i[i];
      assign resp_rdata_o[i] = group_mask_q[i] ? (i % RspGF == 0 ? grouped_resp_rdata[i] : '0) : resp_rdata_i[i];
      assign resp_burst_o[i] = group_mask_q[i] ? (i % RspGF == 0 ? grouped_resp_burst[i] : '0) : '0;
      assign resp_valid_o[i] = group_mask_q[i] ? (i % RspGF == 0 ? grouped_resp_valid[i] : '0) : resp_valid_i[i];
      assign resp_ready_o[i] = group_mask_q[i] ? grouped_resp_ready[RspGF*(i/RspGF)] : resp_ready_i[i];
    end
  end

  /******************
   *   Assertions   *
   ******************/
  if (NumOut == 0)
    $error("[burst_manager] NumBanks needs to be greater or equal to 1");

  if (NumOut < RspGF)
    $error("[burst_manager] NumBanks needs to be larger or equal to RspGF");

endmodule : tcdm_burst_manager
