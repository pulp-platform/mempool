// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Description: Handles the protocol conversion from valid/ready to req/gnt and correctly returns
// the metadata. Additionally, it handles atomics. Hence, it needs to be instantiated in front of
// an SRAM over which it has exclusive access.
//
// Author: Samuel Riedel <sriedel@iis.ee.ethz.ch>

`include "common_cells/registers.svh"

import cf_math_pkg::idx_width;

module tcdm_adapter_xqueue #(
  parameter int unsigned AddrWidth    = 32,
  parameter int unsigned DataWidth    = 32,
  parameter int unsigned XQueueSize   = 4,
  parameter type         metadata_t   = logic,
  parameter bit          RegisterAmo  = 1'b0, // Cut path between request and response at the cost of increased AMO latency
  // Dependent parameters. DO NOT CHANGE.
  localparam int unsigned BeWidth     = DataWidth/8,
  localparam int unsigned QCntWidth   = idx_width(XQueueSize)
) (
  input  logic                 clk_i,
  input  logic                 rst_ni,
  // master side
  input  logic                 in_valid_i,   // Bank request
  output logic                 in_ready_o,   // Bank grant
  input  logic [AddrWidth-1:0] in_address_i, // Address
  input  logic [3:0]           in_amo_i,     // Atomic Memory Operation
  input  logic                 in_write_i,   // 1: Store, 0: Load
  input  logic [DataWidth-1:0] in_wdata_i,   // Write data
  input  metadata_t            in_meta_i,    // Meta data
  input  logic [BeWidth-1:0]   in_be_i,      // Byte enable
  output logic                 in_valid_o,   // Response valid
  input  logic                 in_ready_i,   // Response ready
  output logic [DataWidth-1:0] in_rdata_o,   // Read data
  output metadata_t            in_meta_o,    // Meta data
  // slave side
  output logic                 out_req_o,   // Bank request
  output logic [AddrWidth-1:0] out_add_o,   // Address
  output logic                 out_write_o, // 1: Store, 0: Load
  output logic [DataWidth-1:0] out_wdata_o, // Write data
  output logic [BeWidth-1:0]   out_be_o,    // Bit enable
  input  logic [DataWidth-1:0] out_rdata_i  // Read data
);

  typedef enum logic [3:0] {
      AMONone = 4'h0,
      AMOSwap = 4'h1,
      AMOAdd  = 4'h2,
      AMOAnd  = 4'h3,
      AMOOr   = 4'h4,
      AMOXor  = 4'h5,
      AMOMax  = 4'h6,
      AMOMaxu = 4'h7,
      AMOMin  = 4'h8,
      AMOMinu = 4'h9,
      AMOLR   = 4'hA,
      AMOSC   = 4'hB,
      QPush   = 4'hC,
      QPop    = 4'hD
  } amo_op_t;

  typedef enum logic [2:0] {
    Idle, DoAMO, WriteBackAMO, ResolveQPushStall, ResolveQPopStall
  } state_e;

  // Stored data in spill registers and fall through register
  metadata_t           stored_meta_data;
  metadata_t           stored_smeta_data;
  logic[DataWidth-1:0] resp_in_data;

  // Handshake signals for spill registers and fall through register
  logic meta_in_vld, meta_in_rdy, meta_out_vld, meta_out_rdy;
  logic smeta_in_vld, smeta_in_rdy, smeta_out_vld, smeta_out_rdy;
  logic rdata_in_vld_d, rdata_in_vld_q;
  logic rdata_in_rdy, rdata_out_vld, rdata_out_rdy;

  // Response meta data selection and valid signals
  logic sresp_select_d, sresp_select_q;
  logic resp_vld;
  logic sresp_vld;

  // Helper signals to determine response data acquisition
  logic mem_read_req;
  logic force_rdata_acq;
  logic prevent_rdata_acq;

  // FSM related signals
  state_e state_q, state_d;
  logic   vld_amo_op;
  logic   req_accepted, resp_accepted;
  logic   queue_stalled_d, queue_stalled_q;

  // Temporary storage for AMO operations
  amo_op_t              amo_op_d, amo_op_q;
  logic [AddrWidth-1:0] addr_d, addr_q;

  // AMO ALU signals
  logic [31:0] amo_operand_a;
  logic [31:0] amo_operand_b_d, amo_operand_b_q;
  logic [31:0] amo_result, amo_result_q;

  // Queue counters
  logic unsigned [QCntWidth-1:0] curr_tail_d, curr_tail_q;
  logic unsigned [QCntWidth-1:0] next_tail_d, next_tail_q;
  logic unsigned [QCntWidth-1:0] curr_head_d, curr_head_q;

  // Queue counter increment
  logic unsigned [QCntWidth-1:0] increment_operand, increment_result;

  // Queue management signals
  logic queue_empty;
  logic queue_full;
  logic increment_tail, increment_head;
  logic stalled_queue_op;

  // Stores the metadata at handshake (except stalled queue operations)
  spill_register #(
    .T     (metadata_t),
    .Bypass(1'b0      )
  ) i_meta_register (
    .clk_i  (clk_i           ),
    .rst_ni (rst_ni          ),
    .valid_i(meta_in_vld     ),
    .ready_o(meta_in_rdy     ),
    .data_i (in_meta_i       ),
    .valid_o(meta_out_vld    ),
    .ready_i(meta_out_rdy    ),
    .data_o (stored_meta_data)
  );
  assign meta_in_vld  = req_accepted & !in_write_i & !stalled_queue_op;
  assign meta_out_rdy = sresp_select_q ? 1'b0 : resp_accepted;

  // Stores the metadata at handshake of stalled queue operations
  spill_register #(
    .T     (metadata_t),
    .Bypass(1'b0      )
  ) i_stallmeta_register (
    .clk_i  (clk_i            ),
    .rst_ni (rst_ni           ),
    .valid_i(smeta_in_vld     ),
    .ready_o(smeta_in_rdy     ),
    .data_i (in_meta_i        ),
    .valid_o(smeta_out_vld    ),
    .ready_i(smeta_out_rdy    ),
    .data_o (stored_smeta_data)
  );
  assign smeta_in_vld  = req_accepted & stalled_queue_op;
  assign smeta_out_rdy = sresp_select_q ? resp_accepted : 1'b0;

  // Store response data if it's not accepted immediately
  fall_through_register #(
    .T(logic[DataWidth-1:0])
  ) i_rdata_register (
    .clk_i     (clk_i         ),
    .rst_ni    (rst_ni        ),
    .clr_i     (1'b0          ),
    .testmode_i(1'b0          ),
    .data_i    (resp_in_data  ),
    .valid_i   (rdata_in_vld_q),
    .ready_o   (rdata_in_rdy  ),
    .data_o    (in_rdata_o    ),
    .valid_o   (rdata_out_vld ),
    .ready_i   (rdata_out_rdy )
  );
  assign resp_in_data  = out_rdata_i;
  assign rdata_out_rdy = resp_accepted;

  // Set if memory read request occurs this cycle
  assign mem_read_req = out_req_o & !out_write_o;
  // Acquire response data a cycle after a memory read request (can be forced or prevented)
  assign rdata_in_vld_d = force_rdata_acq | (mem_read_req & !prevent_rdata_acq);

  // Output response valid if both meta and read data are available (the read data will always be last)
  assign resp_vld   = meta_out_vld  & rdata_out_vld;
  assign sresp_vld  = smeta_out_vld & rdata_out_vld;
  // Select output valid depending on response selection
  assign in_valid_o = sresp_select_q ? sresp_vld         : resp_vld;
  // Select output meta data depending on response selection
  assign in_meta_o  = sresp_select_q ? stored_smeta_data : stored_meta_data;

  // Exclude queue operations as valid amo operations
  assign vld_amo_op    = !(amo_op_t'(in_amo_i) inside {AMONone, QPush, QPop});
  // Request is accepted on successful input handshake
  assign req_accepted  = in_valid_i & in_ready_o;
  // Response is accepted on successful output handshake
  assign resp_accepted = in_ready_i & in_valid_o;

  always_comb begin
    // Default
    amo_op_d        = AMONone;
    addr_d          = addr_q;
    amo_operand_b_d = amo_operand_b_q;
    state_d         = state_q;
    sresp_select_d  = sresp_select_q;
    queue_stalled_d = queue_stalled_q;

    // While response is pending no requests are accepted
    in_ready_o = in_valid_o & ~in_ready_i ? 1'b0 : 1'b1;

    // Feed-through of request
    out_req_o   = req_accepted;
    out_add_o   = in_address_i;
    out_write_o = in_write_i;
    out_wdata_o = in_wdata_i;
    out_be_o    = in_be_i;

    // Response data as feed-through of read data
    // resp_in_data   = out_rdata_i;

    // Flags to force or prevent response acquisition
    force_rdata_acq   = 1'b0;
    prevent_rdata_acq = 1'b0;

    // Flags to increment queue counters
    increment_tail = 1'b0;
    increment_head = 1'b0;

    // FSM
    unique case (state_q)
      // Idle State handles normal load/stores, non-stalled queue operations
      // and the initial read of AMO operations (single cycle operations)
      // In case of pending queue stall or AMO operations transition away
      Idle: begin
        // Prepare queue push
        if (amo_op_t'(in_amo_i) == QPush) begin
          // Write data at tail of queue
          out_add_o   = curr_tail_q;
          out_write_o = 1'b1;
        end

        // Prepare queue pop
        if (amo_op_t'(in_amo_i) == QPop) begin
          // Read data at head of queue
          out_add_o = curr_head_q;
        end

        // Request accepted (triggers memory access)
        if (req_accepted) begin
          // Reset meta data selection to default meta data
          sresp_select_d = 1'b0;

          // AMO operation
          if (vld_amo_op) begin
            amo_op_d        = amo_op_t'(in_amo_i);
            addr_d          = in_address_i;
            amo_operand_b_d = in_wdata_i;
            state_d         = DoAMO;
          end

          // Queue push
          if (amo_op_t'(in_amo_i) == QPush) begin
            if (queue_full) begin
              // Note: Memory write is still executed but the tail is not incremented
              // Set stalled flag
              queue_stalled_d   = 1'b1;
              // Prevent acquisition of response data
              prevent_rdata_acq = 1'b1;
            end else begin
              // Set increment flag
              increment_tail  = 1'b1;
              // Force acquisition of response data despite a write access
              // Response data will match the write data of the write access
              force_rdata_acq = 1'b1;
              // Previous queue pop failed due to empty queue
              if (queue_stalled_q) begin
                queue_stalled_d = 1'b0;
                state_d         = ResolveQPopStall;
              end
            end
          end

          // Queue pop
          if (amo_op_t'(in_amo_i) == QPop) begin
            if (queue_empty) begin
              // Set stalled flag
              queue_stalled_d   = 1'b1;
              // Prevent acquisition of response data despite read access
              prevent_rdata_acq = 1'b1;
            end else begin
              // Set increment flag
              increment_head = 1'b1;
              // Previous queue push failed due to full queue
              if (queue_stalled_q) begin
                queue_stalled_d = 1'b0;
                state_d         = ResolveQPushStall;
              end
            end
          end
        end
      end

      // DoAMO & WriteBackAMO State claims the memory interface for AMO write
      DoAMO, WriteBackAMO: begin
        in_ready_o  = 1'b0;
        // Return to Idle one cycle later if we cut the path
        state_d     = (RegisterAmo && state_q != WriteBackAMO) ?  WriteBackAMO : Idle;
        // Commit AMO
        out_req_o   = 1'b1;
        out_write_o = 1'b1;
        out_add_o   = addr_q;
        out_be_o    = 4'b1111;
        // serve from register if we cut the path
        if (RegisterAmo) begin
          out_wdata_o = amo_result_q;
        end else begin
          out_wdata_o = amo_result;
        end
      end

      // ResolveQPushStall State blocks any requests until queue pop response
      // has been accepted and then prepares the queue push response
      // (queue push stores data even in full queue but does not update tail)
      ResolveQPushStall: begin
        // Do not accept any requests during resolve
        in_ready_o  = 1'b0;
        // Retrieve queue push data as dummy response (read data at tail of queue)
        out_add_o   = curr_tail_q;
        out_write_o = 1'b0;
        out_be_o    = 4'b1111;
        // Wait until pop response accepted
        if (resp_accepted) begin
          // Set increment flag
          increment_tail  = 1'b1;
          // Trigger memory access
          out_req_o       = 1'b1;
          // Force acquisition of response data despite a write access
          // Response data will match the write data of the write access
          force_rdata_acq = 1'b1;
          // Set meta data selection to stalled meta data
          sresp_select_d  = 1'b1;
          // Return to Idle
          state_d         = Idle;
        end
      end

      // ResolveQPushStall State blocks any requests until queue push response
      // has been accepted and then executes the queue pop
      ResolveQPopStall: begin
        // Do not accept any requests during resolve
        in_ready_o  = 1'b0;
        // Prepare queue pop (read data at head of queue)
        out_add_o   = curr_head_q;
        out_write_o = 1'b0;
        out_be_o    = 4'b1111;
        // Wait until push response accepted
        if (resp_accepted) begin
          // Set increment flag
          increment_head = 1'b1;
          // Trigger memory access
          out_req_o      = 1'b1;
          // Set meta data selection to stalled meta data
          sresp_select_d = 1'b1;
          // Return to Idle
          state_d        = Idle;
        end
      end
      default:;
    endcase
  end

  // ----------------
  // AMO ALU
  // ----------------
  logic [33:0] adder_sum;
  logic [32:0] adder_operand_a, adder_operand_b;

  assign amo_operand_a = out_rdata_i;
  assign adder_sum     = adder_operand_a + adder_operand_b;
  /* verilator lint_off WIDTH */
  always_comb begin : amo_alu

    adder_operand_a = $signed(amo_operand_a);
    adder_operand_b = $signed(amo_operand_b_q);

    amo_result = amo_operand_b_q;

    unique case (amo_op_q)
      // the default is to output operand_b
      AMOSwap:;
      AMOAdd: amo_result = adder_sum[31:0];
      AMOAnd: amo_result = amo_operand_a & amo_operand_b_q;
      AMOOr:  amo_result = amo_operand_a | amo_operand_b_q;
      AMOXor: amo_result = amo_operand_a ^ amo_operand_b_q;
      AMOMax: begin
        adder_operand_b = -$signed(amo_operand_b_q);
        amo_result = adder_sum[32] ? amo_operand_b_q : amo_operand_a;
      end
      AMOMin: begin
        adder_operand_b = -$signed(amo_operand_b_q);
        amo_result = adder_sum[32] ? amo_operand_a : amo_operand_b_q;
      end
      AMOMaxu: begin
        adder_operand_a = $unsigned(amo_operand_a);
        adder_operand_b = -$unsigned(amo_operand_b_q);
        amo_result = adder_sum[32] ? amo_operand_b_q : amo_operand_a;
      end
      AMOMinu: begin
        adder_operand_a = $unsigned(amo_operand_a);
        adder_operand_b = -$unsigned(amo_operand_b_q);
        amo_result = adder_sum[32] ? amo_operand_a : amo_operand_b_q;
      end
      default: amo_result = '0;
    endcase
  end

  if (RegisterAmo) begin : gen_amo_slice
    `FFLNR(amo_result_q, amo_result, (state_q == DoAMO), clk_i)
  end else begin : gen_amo_slice
    assign amo_result_q = '0;
  end

  // ----------------
  // QUEUE MANAGEMENT
  // ----------------
  assign queue_empty = (curr_head_q == curr_tail_q);
  assign queue_full  = (curr_head_q == next_tail_q);

  assign increment_result = increment_operand + 1;

  always_comb begin : queue_management
    // Default
    curr_tail_d = curr_tail_q;
    next_tail_d = next_tail_q;
    curr_head_d = curr_head_q;

    // Increment queue counters
    increment_operand = curr_head_q;
    if (increment_tail) begin
      increment_operand = next_tail_q;
      curr_tail_d       = next_tail_q;
      next_tail_d       = increment_result;
    end
    if (increment_head) begin
      increment_operand = curr_head_q;
      curr_head_d       = increment_result;
    end

    // Select spill register for meta data
    unique case (amo_op_t'(in_amo_i))
      QPush:   stalled_queue_op = queue_full;
      QPop:    stalled_queue_op = queue_empty;
      default: stalled_queue_op = 1'b0;
    endcase
  end

  // ----------------
  // SEQUENTIAL PROCESS
  // ----------------
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q         <= Idle;
      amo_op_q        <= amo_op_t'('0);
      addr_q          <= '0;
      amo_operand_b_q <= '0;
      rdata_in_vld_q  <= 1'b0;
      sresp_select_q  <= 1'b0;
      curr_tail_q     <= 0;
      next_tail_q     <= 1;
      curr_head_q     <= 0;
      queue_stalled_q <= 1'b0;
    end else begin
      state_q         <= state_d;
      amo_op_q        <= amo_op_d;
      addr_q          <= addr_d;
      amo_operand_b_q <= amo_operand_b_d;
      rdata_in_vld_q  <= rdata_in_vld_d;
      sresp_select_q  <= sresp_select_d;
      curr_tail_q     <= curr_tail_d;
      next_tail_q     <= next_tail_d;
      curr_head_q     <= curr_head_d;
      queue_stalled_q <= queue_stalled_d;
    end
  end

  // ----------------
  // ASSERTIONS
  // ----------------
  // pragma translate_off
  // Check for unsupported parameters
  if (DataWidth != 32) begin
    $error($sformatf("Module currently only supports DataWidth = 32. DataWidth is currently set to: %0d", DataWidth));
  end

  `ifndef VERILATOR
    meta_full : assert property(
      @(posedge clk_i) disable iff (~rst_ni) (meta_in_vld |-> meta_in_rdy))
      else $fatal (1, "Trying to push new data although the i_meta_register is not ready.");
  `endif

  `ifndef VERILATOR
    smeta_full : assert property(
      @(posedge clk_i) disable iff (~rst_ni) (smeta_in_vld |-> smeta_in_rdy))
      else $fatal (1, "Trying to push new data although the i_stallmeta_register is not ready.");
  `endif

  `ifndef VERILATOR
    rdata_full : assert property(
      @(posedge clk_i) disable iff (~rst_ni) (rdata_in_vld_q |-> rdata_in_rdy))
      else $fatal (1, "Trying to push new data although the i_rdata_register is not ready.");
  `endif
  // pragma translate_on

endmodule
