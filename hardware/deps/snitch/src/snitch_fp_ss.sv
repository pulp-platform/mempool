// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"
`include "common_cells/assertions.svh"

// Floating Point Subsystem
module snitch_fp_ss
  import snitch_pkg::*;
#(
  parameter bit RegisterSequencer = 1,
  parameter bit FPUSequencer = 0,
  parameter fpnew_pkg::fpu_implementation_t FPUImplementation = '0
) (
  input  logic             clk_i,
  input  logic             rst_i,
  // pragma translate_off
  output fpu_trace_port_t  trace_port_o,
  output fpu_sequencer_trace_port_t sequencer_tracer_port_o,
  // pragma translate_on
  // Accelerator Interface - Slave
  input  acc_req_t         acc_req_i,
  input  logic             acc_req_valid_i,
  output logic             acc_req_ready_o,
  output acc_resp_t        acc_resp_o,
  output logic             acc_resp_valid_o,
  input  logic             acc_resp_ready_i,
  // Register Interface
  // FPU **un-timed** Side-channel
  input  fpnew_pkg::roundmode_e fpu_rnd_mode_i,
  output fpnew_pkg::status_t    fpu_status_o,
  // Core event strobes
  output core_events_t core_events_o
);

  fpnew_pkg::operation_e  fpu_op;
  fpnew_pkg::roundmode_e  fpu_rnd_mode;
  fpnew_pkg::fp_format_e  src_fmt, dst_fmt;
  fpnew_pkg::int_format_e int_fmt;
  logic                   vectorial_op;
  logic                   set_dyn_rm;

  typedef struct packed {
    logic       acc; // write-back to result bus
    logic [4:0] rd;  // write-back to floating point regfile
  } tag_t;
  tag_t fpu_tag_in, fpu_tag_out;

  logic use_fpu;
  logic [2:0][FLEN-1:0] op;
  logic [2:0] op_ready; // operand is ready

  logic csr_instr;

  // FPU Controller
  logic fpu_out_valid, fpu_out_ready;
  logic fpu_in_valid, fpu_in_ready;

  typedef enum logic [2:0] {
    None,
    AccBus
  } op_select_e;
  op_select_e [2:0] op_select;

  typedef enum logic [1:0] {
    ResNone, ResAccBus
  } result_select_e;
  result_select_e result_select;

  logic op_mode;
  logic [4:0] rs1, rs2, rs3, rd;

  // -------------
  // FPU Sequencer
  // -------------
  snitch_pkg::acc_req_t   acc_req, acc_req_q;
  logic                   acc_req_valid, acc_req_valid_q;
  logic                   acc_req_ready, acc_req_ready_q;
  if (FPUSequencer) begin : gen_fpu_sequencer
    snitch_sequencer #(
      .Depth    ( snitch_pkg::FPUSequencerInstr )
    ) i_snitch_fpu_sequencer (
      .clk_i,
      .rst_i,
      // pragma translate_off
      .trace_port_o     ( sequencer_tracer_port_o ),
      // pragma translate_on
      .inp_qaddr_i      ( acc_req_i.addr      ),
      .inp_qid_i        ( acc_req_i.id        ),
      .inp_qdata_op_i   ( acc_req_i.data_op   ),
      .inp_qdata_arga_i ( acc_req_i.data_arga ),
      .inp_qdata_argb_i ( acc_req_i.data_argb ),
      .inp_qdata_argc_i ( acc_req_i.data_argc ),
      .inp_qvalid_i     ( acc_req_valid_i     ),
      .inp_qready_o     ( acc_req_ready_o     ),
      .oup_qaddr_o      ( acc_req.addr        ),
      .oup_qid_o        ( acc_req.id          ),
      .oup_qdata_op_o   ( acc_req.data_op     ),
      .oup_qdata_arga_o ( acc_req.data_arga   ),
      .oup_qdata_argb_o ( acc_req.data_argb   ),
      .oup_qdata_argc_o ( acc_req.data_argc   ),
      .oup_qvalid_o     ( acc_req_valid       ),
      .oup_qready_i     ( acc_req_ready       )
    );
  end else begin : gen_no_fpu_sequencer
    assign sequencer_tracer_port_o = 0;
    assign acc_req_ready_o = acc_req_ready;
    assign acc_req_valid = acc_req_valid_i;
    assign acc_req = acc_req_i;
  end

  // Optional spill-register
  spill_register  #(
    .T      ( snitch_pkg::acc_req_t               ),
    .Bypass ( !RegisterSequencer || !FPUSequencer )
  ) i_spill_register_acc (
    .clk_i   ,
    .rst_ni  ( ~rst_i          ),
    .valid_i ( acc_req_valid   ),
    .ready_o ( acc_req_ready   ),
    .data_i  ( acc_req         ),
    .valid_o ( acc_req_valid_q ),
    .ready_i ( acc_req_ready_q ),
    .data_o  ( acc_req_q       )
  );

  // check that the FPU and all operands are ready
  assign fpu_in_valid = use_fpu & acc_req_valid_q & (&op_ready);
  assign acc_req_ready_q = ((fpu_in_ready & fpu_in_valid) // FPU ready
                                      | csr_instr
                                      | (acc_req_valid_q && result_select == ResAccBus)); // Direct Reg Write

  // either the FPU or the regfile produced a result
  assign acc_resp_valid_o = (fpu_tag_out.acc & fpu_out_valid);
  // stall FPU if we forward from reg
  assign fpu_out_ready = (fpu_tag_out.acc & acc_resp_ready_i);

  // FPU Result
  logic [FLEN-1:0] fpu_result;

  // FPU Tag
  assign acc_resp_o.id = fpu_tag_out.rd;
  // accelerator bus write-port
  assign acc_resp_o.data = fpu_result;

  assign rd = acc_req_q.data_op[11:7];
  assign rs1 = acc_req_q.data_op[19:15];
  assign rs2 = acc_req_q.data_op[24:20];
  assign rs3 = acc_req_q.data_op[31:27];

  always_comb begin
    acc_resp_o.error = 1'b0;
    fpu_op = fpnew_pkg::ADD;
    use_fpu = 1'b1;
    fpu_rnd_mode = (fpnew_pkg::roundmode_e'(acc_req_q.data_op[14:12]) == fpnew_pkg::DYN)
                   ? fpu_rnd_mode_i
                   : fpnew_pkg::roundmode_e'(acc_req_q.data_op[14:12]);

    set_dyn_rm = 1'b0;

    src_fmt = fpnew_pkg::FP32;
    dst_fmt = fpnew_pkg::FP32;
    int_fmt = fpnew_pkg::INT32;

    result_select = ResNone;

    op_select[0] = None;
    op_select[1] = None;
    op_select[2] = None;

    vectorial_op = 1'b0;
    op_mode = 1'b0;

    fpu_tag_in.rd = rd;
    fpu_tag_in.acc = 1'b1;

    // Destination register is in FPR
    csr_instr = 1'b0; // is a csr instruction
    unique casez (acc_req_q.data_op)
      // FP - FP Operations
      // Single Precision
      riscv_instr::FADD_S: begin
        fpu_op = fpnew_pkg::ADD;
        op_select[1] = AccBus;
        op_select[2] = AccBus;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
      end
      riscv_instr::FSUB_S: begin
        fpu_op = fpnew_pkg::ADD;
        op_select[1] = AccBus;
        op_select[2] = AccBus;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
        op_mode = 1'b1;
      end
      riscv_instr::FMUL_S: begin
        fpu_op = fpnew_pkg::MUL;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
      end
      riscv_instr::FDIV_S: begin  // currently illegal
        fpu_op = fpnew_pkg::DIV;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
      end
      riscv_instr::FSGNJ_S,
      riscv_instr::FSGNJN_S,
      riscv_instr::FSGNJX_S: begin
        fpu_op = fpnew_pkg::SGNJ;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
      end
      riscv_instr::FMIN_S,
      riscv_instr::FMAX_S: begin
        fpu_op = fpnew_pkg::MINMAX;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
      end
      riscv_instr::FSQRT_S: begin  // currently illegal
        fpu_op = fpnew_pkg::SQRT;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
      end
      riscv_instr::FMADD_S: begin
        fpu_op = fpnew_pkg::FMADD;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        op_select[2] = AccBus;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
      end
      riscv_instr::FMSUB_S: begin
        fpu_op = fpnew_pkg::FMADD;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        op_select[2] = AccBus;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
        op_mode      = 1'b1;
      end
      riscv_instr::FNMSUB_S: begin
        fpu_op = fpnew_pkg::FNMSUB;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        op_select[2] = AccBus;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
      end
      riscv_instr::FNMADD_S: begin
        fpu_op = fpnew_pkg::FNMSUB;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        op_select[2] = AccBus;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
        op_mode      = 1'b1;
      end
      // Half Precision
      riscv_instr::FADD_H: begin
        fpu_op = fpnew_pkg::ADD;
        op_select[1] = AccBus;
        op_select[2] = AccBus;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
      end
      riscv_instr::FSUB_H: begin
        fpu_op = fpnew_pkg::ADD;
        op_select[1] = AccBus;
        op_select[2] = AccBus;
        op_mode = 1'b1;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
      end
      riscv_instr::FMUL_H: begin
        fpu_op = fpnew_pkg::MUL;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
      end
      riscv_instr::FDIV_H: begin
        fpu_op = fpnew_pkg::DIV;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
      end
      riscv_instr::FSGNJ_H,
      riscv_instr::FSGNJN_H,
      riscv_instr::FSGNJX_H: begin
        fpu_op = fpnew_pkg::SGNJ;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
      end
      riscv_instr::FMIN_H,
      riscv_instr::FMAX_H: begin
        fpu_op = fpnew_pkg::MINMAX;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
      end
      riscv_instr::FSQRT_H: begin
        fpu_op = fpnew_pkg::SQRT;
        op_select[0] = AccBus;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
      end
      riscv_instr::FMADD_H: begin
        fpu_op = fpnew_pkg::FMADD;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        op_select[2] = AccBus;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
      end
      riscv_instr::FMSUB_H: begin
        fpu_op = fpnew_pkg::FMADD;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        op_select[2] = AccBus;
        op_mode      = 1'b1;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
      end
      riscv_instr::FNMSUB_H: begin
        fpu_op = fpnew_pkg::FNMSUB;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        op_select[2] = AccBus;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
      end
      riscv_instr::FNMADD_H: begin
        fpu_op = fpnew_pkg::FNMSUB;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        op_select[2] = AccBus;
        op_mode      = 1'b1;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
      end
      riscv_instr::FCVT_S_H: begin
        fpu_op = fpnew_pkg::F2F;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        src_fmt      = fpnew_pkg::FP32;
        dst_fmt      = fpnew_pkg::FP16;
      end
      riscv_instr::FCVT_H_S: begin
        fpu_op = fpnew_pkg::F2F;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP32;
      end



      // Vectorized Half Precision Floating-Point
      riscv_instr::VFADD_H,
      riscv_instr::VFADD_R_H: begin
        fpu_op = fpnew_pkg::ADD;
        op_select[1] = AccBus;
        op_select[2] = AccBus;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFSUB_H,
      riscv_instr::VFSUB_R_H: begin
        fpu_op = fpnew_pkg::ADD;
        op_select[1] = AccBus;
        op_select[2] = AccBus;
        op_mode      = 1'b1;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFMUL_H,
      riscv_instr::VFMUL_R_H: begin
        fpu_op = fpnew_pkg::MUL;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFDIV_H,
      riscv_instr::VFDIV_R_H: begin
        fpu_op = fpnew_pkg::DIV;
        op_select[1] = AccBus;
        op_select[2] = AccBus;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFMIN_H,
      riscv_instr::VFMIN_R_H: begin
        fpu_op = fpnew_pkg::MINMAX;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        fpu_rnd_mode = fpnew_pkg::RNE;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
      end
      riscv_instr::VFMAX_H,
      riscv_instr::VFMAX_R_H: begin
        fpu_op = fpnew_pkg::MINMAX;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        fpu_rnd_mode = fpnew_pkg::RTZ;
        vectorial_op = 1'b1;
      end
      riscv_instr::VFSQRT_H: begin
        fpu_op = fpnew_pkg::SQRT;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFMAC_H,
      riscv_instr::VFMAC_R_H: begin
        fpu_op = fpnew_pkg::FMADD;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        op_select[2] = AccBus;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFMRE_H,
      riscv_instr::VFMRE_R_H: begin
        fpu_op = fpnew_pkg::FNMSUB;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        op_select[2] = AccBus;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFSGNJ_H,
      riscv_instr::VFSGNJ_R_H: begin
        fpu_op = fpnew_pkg::SGNJ;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        fpu_rnd_mode = fpnew_pkg::RNE;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
      end
      riscv_instr::VFSGNJN_H,
      riscv_instr::VFSGNJN_R_H: begin
        fpu_op = fpnew_pkg::SGNJ;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        fpu_rnd_mode = fpnew_pkg::RTZ;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
      end
      riscv_instr::VFSGNJX_H,
      riscv_instr::VFSGNJX_R_H: begin
        fpu_op = fpnew_pkg::SGNJ;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        fpu_rnd_mode = fpnew_pkg::RDN;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
      end
      riscv_instr::VFCPKA_H_S: begin
        fpu_op = fpnew_pkg::CPKAB;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        op_select[2] = AccBus;
        src_fmt      = fpnew_pkg::FP32;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFCPKB_H_S: begin
        fpu_op = fpnew_pkg::CPKAB;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        op_select[2] = AccBus;
        op_mode      = 1'b1;
        src_fmt      = fpnew_pkg::FP32;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFCVT_S_H,
      riscv_instr::VFCVTU_S_H: begin
        fpu_op = fpnew_pkg::F2F;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP32;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFCVT_H_S,
      riscv_instr::VFCVTU_H_S: begin
        fpu_op = fpnew_pkg::F2F;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        src_fmt      = fpnew_pkg::FP32;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      // Quarter Precision
      riscv_instr::FADD_B: begin
        fpu_op = fpnew_pkg::ADD;
        op_select[1] = AccBus;
        op_select[2] = AccBus;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
      end
      riscv_instr::FSUB_B: begin
        fpu_op = fpnew_pkg::ADD;
        op_select[1] = AccBus;
        op_select[2] = AccBus;
        op_mode = 1'b1;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
      end
      riscv_instr::FMUL_B: begin
        fpu_op = fpnew_pkg::MUL;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
      end
      riscv_instr::FDIV_B: begin
        fpu_op = fpnew_pkg::DIV;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
      end
      riscv_instr::FSGNJ_B,
      riscv_instr::FSGNJN_B,
      riscv_instr::FSGNJX_B: begin
        fpu_op = fpnew_pkg::SGNJ;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
      end
      riscv_instr::FMIN_B,
      riscv_instr::FMAX_B: begin
        fpu_op = fpnew_pkg::MINMAX;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
      end
      riscv_instr::FSQRT_B: begin
        fpu_op = fpnew_pkg::SQRT;
        op_select[0] = AccBus;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
      end
      riscv_instr::FMADD_B: begin
        fpu_op = fpnew_pkg::FMADD;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        op_select[2] = AccBus;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
      end
      riscv_instr::FMSUB_B: begin
        fpu_op = fpnew_pkg::FMADD;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        op_select[2] = AccBus;
        op_mode      = 1'b1;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
      end
      riscv_instr::FNMSUB_B: begin
        fpu_op = fpnew_pkg::FNMSUB;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        op_select[2] = AccBus;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
      end
      riscv_instr::FNMADD_B: begin
        fpu_op = fpnew_pkg::FNMSUB;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        op_select[2] = AccBus;
        op_mode      = 1'b1;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
      end
      riscv_instr::FCVT_S_B: begin
        fpu_op = fpnew_pkg::F2F;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        src_fmt      = fpnew_pkg::FP32;
        dst_fmt      = fpnew_pkg::FP8;
      end
      riscv_instr::FCVT_B_S: begin
        fpu_op = fpnew_pkg::F2F;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP32;
      end
      riscv_instr::FCVT_B_H: begin
        fpu_op = fpnew_pkg::F2F;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP16;
      end
      riscv_instr::FCVT_H_B: begin
        fpu_op = fpnew_pkg::F2F;
        op_select[0] = AccBus;
        op_select[1] = AccBus;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP8;
      end
      // FP - Int Operations
      // Single Precision Floating-Point
      riscv_instr::FLE_S,
      riscv_instr::FLT_S,
      riscv_instr::FEQ_S: begin
        fpu_op = fpnew_pkg::CMP;
        op_select[0]   = AccBus;
        op_select[1]   = AccBus;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
        fpu_tag_in.acc = 1'b1;
      end
      riscv_instr::FCLASS_S: begin
        fpu_op = fpnew_pkg::CLASSIFY;
        op_select[0]   = AccBus;
        fpu_rnd_mode   = fpnew_pkg::RNE;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
        fpu_tag_in.acc = 1'b1;
      end
      riscv_instr::FCVT_W_S,
      riscv_instr::FCVT_WU_S: begin
        fpu_op = fpnew_pkg::F2I;
        op_select[0]   = AccBus;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
        fpu_tag_in.acc = 1'b1;
        if (acc_req_q.data_op inside {riscv_instr::FCVT_WU_S}) op_mode = 1'b1; // unsigned
      end
      riscv_instr::FMV_X_W: begin
        fpu_op = fpnew_pkg::SGNJ;
        fpu_rnd_mode   = fpnew_pkg::RUP; // passthrough without checking nan-box
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
        op_mode        = 1'b1; // sign-extend result
        op_select[0]   = AccBus;
        fpu_tag_in.acc = 1'b1;
      end
      // FP - Int Operations
      // Half Precision Floating-Point
      riscv_instr::FLE_H,
      riscv_instr::FLT_H,
      riscv_instr::FEQ_H: begin
        fpu_op = fpnew_pkg::CMP;
        op_select[0]   = AccBus;
        op_select[1]   = AccBus;
        src_fmt        = fpnew_pkg::FP16;
        dst_fmt        = fpnew_pkg::FP16;
        fpu_tag_in.acc = 1'b1;
      end
      riscv_instr::FCLASS_H: begin
        fpu_op = fpnew_pkg::CLASSIFY;
        op_select[0]   = AccBus;
        fpu_rnd_mode   = fpnew_pkg::RNE;
        src_fmt        = fpnew_pkg::FP16;
        dst_fmt        = fpnew_pkg::FP16;
        fpu_tag_in.acc = 1'b1;
      end
      riscv_instr::FCVT_W_H,
      riscv_instr::FCVT_WU_H: begin
        fpu_op = fpnew_pkg::F2I;
        op_select[0]   = AccBus;
        src_fmt        = fpnew_pkg::FP16;
        dst_fmt        = fpnew_pkg::FP16;
        fpu_tag_in.acc = 1'b1;
        if (acc_req_q.data_op inside {riscv_instr::FCVT_WU_H}) op_mode = 1'b1; // unsigned
      end
      riscv_instr::FMV_X_H: begin
        fpu_op = fpnew_pkg::SGNJ;
        fpu_rnd_mode   = fpnew_pkg::RUP; // passthrough without checking nan-box
        src_fmt        = fpnew_pkg::FP16;
        dst_fmt        = fpnew_pkg::FP16;
        op_mode        = 1'b1; // sign-extend result
        op_select[0]   = AccBus;
        fpu_tag_in.acc = 1'b1;
      end
      // FP - Int Operations
      // Quarter Precision Floating-Point
      riscv_instr::FLE_B,
      riscv_instr::FLT_B,
      riscv_instr::FEQ_B: begin
        fpu_op = fpnew_pkg::CMP;
        op_select[0]   = AccBus;
        op_select[1]   = AccBus;
        src_fmt        = fpnew_pkg::FP8;
        dst_fmt        = fpnew_pkg::FP8;
        fpu_tag_in.acc = 1'b1;
      end
      riscv_instr::FCLASS_B: begin
        fpu_op = fpnew_pkg::CLASSIFY;
        op_select[0]   = AccBus;
        fpu_rnd_mode   = fpnew_pkg::RNE;
        src_fmt        = fpnew_pkg::FP8;
        dst_fmt        = fpnew_pkg::FP8;
        fpu_tag_in.acc = 1'b1;
      end
      riscv_instr::FCVT_W_B,
      riscv_instr::FCVT_WU_B: begin
        fpu_op = fpnew_pkg::F2I;
        op_select[0]   = AccBus;
        src_fmt        = fpnew_pkg::FP8;
        dst_fmt        = fpnew_pkg::FP8;
        fpu_tag_in.acc = 1'b1;
        if (acc_req_q.data_op inside {riscv_instr::FCVT_WU_B}) op_mode = 1'b1; // unsigned
      end
      riscv_instr::FMV_X_B: begin
        fpu_op = fpnew_pkg::SGNJ;
        fpu_rnd_mode   = fpnew_pkg::RUP; // passthrough without checking nan-box
        src_fmt        = fpnew_pkg::FP8;
        dst_fmt        = fpnew_pkg::FP8;
        op_mode        = 1'b1; // sign-extend result
        op_select[0]   = AccBus;
        fpu_tag_in.acc = 1'b1;
      end
      default: ;
    endcase
    // fix round mode for vectors and fp16alt
    if (set_dyn_rm) fpu_rnd_mode = fpu_rnd_mode_i;
  end

  // ----------------------
  // Operand Select
  // ----------------------
  logic [2:0][FLEN-1:0] acc_qdata;
  assign acc_qdata = {acc_req_q.data_argc, acc_req_q.data_argb, acc_req_q.data_arga};

  for (genvar i = 0; i < 3; i++) begin: gen_operand_select
    always_comb begin
      unique case (op_select[i])
        None: begin
          op[i] = '1;
          op_ready[i] = 1'b1;
        end
        AccBus: begin
          if ((i > 0) && (op_select[0] == None)) begin
            op[i] = acc_qdata[i-1];
          end else begin
            op[i] = acc_qdata[i];
          end
          op_ready[i] = acc_req_valid_q;
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
  snitch_fpu i_fpu (
    .clk_i                           ,
    .rst_ni         ( ~rst_i        ),
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
    .status_o       ( fpu_status_o  ),
    .tag_o          ( fpu_tag_out   ),
    .out_valid_o    ( fpu_out_valid ),
    .out_ready_i    ( fpu_out_ready )
  );

  logic [63:0] nan_boxed_arga;
  assign nan_boxed_arga = {{32{1'b1}}, acc_req_q.data_arga[31:0]};

  // Counter pipeline.
  logic issue_fpu, issue_core_to_fpu, issue_fpu_seq;
  `FFAR(issue_fpu, fpu_in_valid & fpu_in_ready, 1'b0, clk_i, rst_i)
  `FFAR(issue_core_to_fpu, acc_req_valid_i & acc_req_ready_o, 1'b0, clk_i, rst_i)
  `FFAR(issue_fpu_seq, acc_req_valid & acc_req_ready, 1'b0, clk_i, rst_i)

  always_comb begin
    core_events_o = '0;
    core_events_o.issue_fpu = issue_fpu;
    core_events_o.issue_core_to_fpu = issue_core_to_fpu;
    core_events_o.issue_fpu_seq = issue_fpu_seq;
  end

  // Tracer
  // pragma translate_off
  assign trace_port_o.acc_q_hs     = (acc_req_valid_q  && acc_req_ready_q );
  assign trace_port_o.fpu_out_hs   = (fpu_out_valid && fpu_out_ready );
  assign trace_port_o.op_in        = acc_req_q.data_op;
  assign trace_port_o.rs1          = rs1;
  assign trace_port_o.rs2          = rs2;
  assign trace_port_o.rs3          = rs3;
  assign trace_port_o.rd           = rd;
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
  assign trace_port_o.use_fpu      = use_fpu;
  assign trace_port_o.fpu_in_rd    = fpu_tag_in.rd;
  assign trace_port_o.fpu_in_acc   = fpu_tag_in.acc;
  // pragma translate_on

endmodule
