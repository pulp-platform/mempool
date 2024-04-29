// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"
`include "common_cells/assertions.svh"

// Floating Point Subsystem
module snitch_fp_divsqrt
  import snitch_pkg::*;
#(
  parameter fpnew_pkg::fpu_implementation_t FPUImplementation = '0
) (
  input  logic             clk_i,
  input  logic             rst_i,
  // pragma translate_off
  output fpu_trace_port_t  trace_port_o,
  // pragma translate_on
  // Accelerator Interface - Slave
  input  sh_acc_req_t      acc_req_i,
  input  logic             acc_req_valid_i,
  output logic             acc_req_ready_o,
  output sh_acc_resp_t     acc_resp_o,
  output logic             acc_resp_valid_o,
  input  logic             acc_resp_ready_i,
  // Register Interface
  // FPU **un-timed** Side-channel
  input  fpnew_pkg::roundmode_e divsqrt_rnd_mode_i,
  output fpnew_pkg::status_t    divsqrt_status_o,
  // Core event strobes
  output fp_ss_core_events_t    core_events_o
);

  fpnew_pkg::operation_e  fpu_op;
  fpnew_pkg::roundmode_e  fpu_rnd_mode;
  fpnew_pkg::fp_format_e  src_fmt, dst_fmt;
  fpnew_pkg::int_format_e int_fmt;
  logic                   vectorial_op;
  logic                   set_dyn_rm;

  typedef struct packed {
    logic         acc; // write-back to result bus
    logic [4:0]   rd;  // write-back to floating point regfile
    logic [5:0]  hart_id;
  } tag_t;
  tag_t fpu_tag_in, fpu_tag_out;

  logic [2:0][FLEN-1:0] op;
  logic [2:0] op_ready; // operand is ready

  // FPU Controller
  logic fpu_out_valid, fpu_out_ready;
  logic fpu_in_valid, fpu_in_ready;

  typedef enum logic [2:0] {
    None,
    AccBus_A,
    AccBus_B,
    AccBus_C
  } op_select_e;
  op_select_e [2:0] op_select;

  logic op_mode;
  logic [4:0] rs1, rs2, rs3, rd;

  snitch_pkg::acc_req_t   acc_req;
  logic                   acc_req_valid;
  logic                   acc_req_ready;
  // Accelerator interface
  assign acc_req_ready_o = acc_req_ready;
  assign acc_req_valid = acc_req_valid_i;
  assign acc_req = acc_req_i;

  // check that the FPU and all operands are ready
  assign fpu_in_valid = acc_req_valid & (&op_ready);
  assign acc_req_ready = fpu_in_ready; // FPU got data

  // the FPU produced a result
  assign acc_resp_valid_o = fpu_out_valid;
  // stall FPU if the accelerator bus is stalled
  assign fpu_out_ready = acc_resp_ready_i;

  assign rd = acc_req.data_op[11:7];
  assign rs1 = acc_req.data_op[19:15];
  assign rs2 = acc_req.data_op[24:20];
  assign rs3 = acc_req.data_op[31:27];

  // FPU Result
  logic [FLEN-1:0] fpu_result;
  // accelerator bus write-port
  assign acc_resp_o.data = fpu_result;

  // FPU Tag
  assign acc_resp_o.id = fpu_tag_out.rd;
  assign fpu_tag_in.acc = 1'b1;
  assign fpu_tag_in.rd = rd;
  assign fpu_tag_in.hart_id = acc_req_i.hart_id;
  assign acc_resp_o.hart_id = fpu_tag_out.hart_id;

  always_comb begin
    acc_resp_o.error = 1'b0;
    fpu_op = fpnew_pkg::ADD;
    fpu_rnd_mode = (fpnew_pkg::roundmode_e'(acc_req.data_op[14:12]) == fpnew_pkg::DYN)
                   ? divsqrt_rnd_mode_i
                   : fpnew_pkg::roundmode_e'(acc_req.data_op[14:12]);

    set_dyn_rm = 1'b0;
    src_fmt = fpnew_pkg::FP32;
    dst_fmt = fpnew_pkg::FP32;
    int_fmt = fpnew_pkg::INT32;

    op_select[0] = None;
    op_select[1] = None;
    op_select[2] = None;

    vectorial_op = 1'b0;
    op_mode = 1'b0;

    // Destination register is in FPR
    unique casez (acc_req.data_op)
      // FP - FP Operations
      // Single Precision
      riscv_instr::FDIV_S: begin  // currently illegal
        fpu_op = fpnew_pkg::DIV;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
      end
      riscv_instr::FSQRT_S: begin  // currently illegal
        fpu_op = fpnew_pkg::SQRT;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
      end
      // Half Precision
      riscv_instr::FDIV_H: begin
        fpu_op = fpnew_pkg::DIV;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
      end
      riscv_instr::FSQRT_H: begin
        fpu_op = fpnew_pkg::SQRT;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
      end
      riscv_instr::VFDIV_H,
      riscv_instr::VFDIV_R_H: begin
        fpu_op = fpnew_pkg::DIV;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFSQRT_H: begin
        fpu_op = fpnew_pkg::SQRT;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      // Quarter Precision
      riscv_instr::FDIV_B: begin
        fpu_op = fpnew_pkg::DIV;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
      end
      riscv_instr::FSQRT_B: begin
        fpu_op = fpnew_pkg::SQRT;
        op_select[0] = AccBus_A;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
      end
      default: ;
    endcase
    // fix round mode for vectors and fp16alt
    if (set_dyn_rm) fpu_rnd_mode = divsqrt_rnd_mode_i;
  end

  // ----------------------
  // Operand Select
  // ----------------------
  logic [2:0][FLEN-1:0] acc_qdata;
  assign acc_qdata = {acc_req.data_argc, acc_req.data_argb, acc_req.data_arga};

  for (genvar i = 0; i < 3; i++) begin: gen_operand_select
    always_comb begin
      unique case (op_select[i])
        None: begin
          op[i] = '1;
          op_ready[i] = 1'b1;
        end
        AccBus_A: begin
          op[i] = acc_qdata[0];
          op_ready[i] = acc_req_valid;
        end
        AccBus_B: begin
          op[i] = acc_qdata[1];
          op_ready[i] = acc_req_valid;
        end
        AccBus_C: begin
          op[i] = acc_qdata[2];
          op_ready[i] = acc_req_valid;
        end
        default: begin
          op[i] = '0;
          op_ready[i] = 1'b1;
        end
      endcase
    end
  end

  // ----------------------
  // Floating Point Unit
  // ----------------------
  snitch_fpu #(
    .TagType           ( logic[11:0]       ),
    .FPUImplementation ( FPUImplementation )
  ) i_fpu (
    .clk_i                           ,
    .rst_ni         ( ~rst_i        ),
    .hart_id_i      ( '0            ),
    .operands_i     ( op            ),
    .rnd_mode_i     ( fpu_rnd_mode  ),
    .op_i           ( fpu_op        ),
    .op_mod_i       ( op_mode       ), // Sign of operand?
    .src_fmt_i      ( src_fmt       ),
    .dst_fmt_i      ( dst_fmt       ),
    .int_fmt_i      ( int_fmt       ),
    .vectorial_op_i ( vectorial_op  ),
    .tag_i          ( fpu_tag_in    ),
    .in_valid_i     ( fpu_in_valid  ),
    .in_ready_o     ( fpu_in_ready  ),
    .result_o       ( fpu_result    ),
    .status_o       ( divsqrt_status_o  ),
    .tag_o          ( fpu_tag_out   ),
    .out_valid_o    ( fpu_out_valid ),
    .out_ready_i    ( fpu_out_ready )
  );

  logic [63:0] nan_boxed_arga;
  assign nan_boxed_arga = {{32{1'b1}}, acc_req.data_arga[31:0]};

  // Counter pipeline.
  logic issue_fpu, issue_core_to_fpu;
  `FFAR(issue_fpu, fpu_in_valid & fpu_in_ready, 1'b0, clk_i, rst_i)
  `FFAR(issue_core_to_fpu, acc_req_valid_i & acc_req_ready_o, 1'b0, clk_i, rst_i)

  always_comb begin
    core_events_o = '0;
    core_events_o.issue_fpu = issue_fpu;
    core_events_o.issue_core_to_fpu = issue_core_to_fpu;
  end

  // Tracer
  // pragma translate_off
  assign trace_port_o.acc_q_hs     = (acc_req_valid  && acc_req_ready );
  assign trace_port_o.fpu_out_hs   = (fpu_out_valid && fpu_out_ready );
  assign trace_port_o.op_in        = acc_req.data_op;
  assign trace_port_o.op_sel_0     = op_select[0];
  assign trace_port_o.op_sel_1     = op_select[1];
  assign trace_port_o.op_sel_2     = op_select[2];
  assign trace_port_o.src_fmt      = src_fmt;
  assign trace_port_o.dst_fmt      = dst_fmt;
  assign trace_port_o.int_fmt      = int_fmt;
  assign trace_port_o.acc_qdata_0  = acc_qdata[0];
  assign trace_port_o.acc_qdata_1  = acc_qdata[1];
  assign trace_port_o.acc_qdata_2  = acc_qdata[2];
  assign trace_port_o.op_0         = op[0];
  assign trace_port_o.op_1         = op[1];
  assign trace_port_o.op_2         = op[2];
  assign trace_port_o.use_fpu      = 1'b1;
  // pragma translate_on

endmodule
