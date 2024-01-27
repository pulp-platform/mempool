// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"
`include "common_cells/assertions.svh"

// Floating Point Subsystem
module snitch_fp_ss
  import snitch_pkg::*;
#(
  parameter fpnew_pkg::fpu_implementation_t FPUImplementation = '0
) (
  input  logic             clk_i,
  input  logic             rst_i,
  // pragma translate_off
  output fpu_trace_port_t  trace_port_o,
  // pragma translate_on
  input  logic [31:0]      hart_id_i,
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
  output fp_ss_core_events_t    core_events_o
);

  fpnew_pkg::operation_e  fpu_op;
  fpnew_pkg::roundmode_e  fpu_rnd_mode;
  fpnew_pkg::fp_format_e  src_fmt, dst_fmt;
  fpnew_pkg::int_format_e int_fmt;
  logic                   vectorial_op;
  logic                   set_dyn_rm;
  logic                   select_upper_half;

  typedef struct packed {
    logic       acc; // write-back to result bus
    logic [4:0] rd;  // write-back to floating point regfile
  } tag_t;
  tag_t fpu_tag_in, fpu_tag_out;

  logic [2:0][FLEN-1:0] op;
  logic [2:0] op_ready; // operand is ready

  logic csr_instr;

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

  typedef enum logic [1:0] {
    ResNone, ResAccBus
  } result_select_e;
  result_select_e result_select;

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
  assign acc_req_ready = ((fpu_in_ready & fpu_in_valid) // FPU ready
                                      | csr_instr
                                      | (acc_req_valid && result_select == ResAccBus)); // Direct Reg Write

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

  assign rd = acc_req.data_op[11:7];
  assign rs1 = acc_req.data_op[19:15];
  assign rs2 = acc_req.data_op[24:20];
  assign rs3 = acc_req.data_op[31:27];

  always_comb begin
    acc_resp_o.error = 1'b0;
    fpu_op = fpnew_pkg::ADD;
    fpu_rnd_mode = (fpnew_pkg::roundmode_e'(acc_req.data_op[14:12]) == fpnew_pkg::DYN)
                   ? fpu_rnd_mode_i
                   : fpnew_pkg::roundmode_e'(acc_req.data_op[14:12]);

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
    select_upper_half = 1'b0;

    fpu_tag_in.rd = rd;
    fpu_tag_in.acc = 1'b1;

    // Destination register is in FPR
    csr_instr = 1'b0; // is a csr instruction
    unique casez (acc_req.data_op)

      //////////////////////
      // Single Precision //
      //////////////////////

      riscv_instr::FADD_S: begin
        fpu_op = fpnew_pkg::ADD;
        op_select[1] = AccBus_A;
        op_select[2] = AccBus_B;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
      end
      riscv_instr::FSUB_S: begin
        fpu_op = fpnew_pkg::ADD;
        op_select[1] = AccBus_A;
        op_select[2] = AccBus_B;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
        op_mode = 1'b1;
      end
      riscv_instr::FMUL_S: begin
        fpu_op = fpnew_pkg::MUL;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
      end
      riscv_instr::FSGNJ_S,
      riscv_instr::FSGNJN_S,
      riscv_instr::FSGNJX_S: begin
        fpu_op = fpnew_pkg::SGNJ;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
      end
      riscv_instr::FMIN_S,
      riscv_instr::FMAX_S: begin
        fpu_op = fpnew_pkg::MINMAX;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
      end
      riscv_instr::FLE_S,
      riscv_instr::FLT_S,
      riscv_instr::FEQ_S: begin
        fpu_op = fpnew_pkg::CMP;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
      end
      riscv_instr::FCVT_W_S,
      riscv_instr::FCVT_WU_S: begin
        fpu_op = fpnew_pkg::F2I;
        op_select[0]   = AccBus_A;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
        if (acc_req.data_op inside {riscv_instr::FCVT_WU_S}) op_mode = 1'b1; // unsigned
      end
      riscv_instr::FMV_X_W: begin
        fpu_op = fpnew_pkg::SGNJ;
        fpu_rnd_mode   = fpnew_pkg::RUP; // passthrough without checking nan-box
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
        op_mode        = 1'b1; // sign-extend result
        op_select[0]   = AccBus_A;
      end
      riscv_instr::FCLASS_S: begin
        fpu_op = fpnew_pkg::CLASSIFY;
        op_select[0]   = AccBus_A;
        fpu_rnd_mode   = fpnew_pkg::RNE;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
      end
      riscv_instr::FCVT_S_W,
      riscv_instr::FCVT_S_WU: begin
        fpu_op = fpnew_pkg::I2F;
        op_select[0]   = AccBus_A;
        dst_fmt        = fpnew_pkg::FP32;
        if (acc_req.data_op inside {riscv_instr::FCVT_S_WU}) op_mode = 1'b1; // unsigned
      end
      riscv_instr::FMV_W_X: begin
        fpu_op = fpnew_pkg::SGNJ;
        fpu_rnd_mode   = fpnew_pkg::RUP; // passthrough without checking nan-box
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
        op_select[0]   = AccBus_A;
      end
      riscv_instr::FMADD_S: begin
        fpu_op = fpnew_pkg::FMADD;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
      end
      riscv_instr::FMSUB_S: begin
        fpu_op = fpnew_pkg::FMADD;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
        op_mode      = 1'b1;
      end
      riscv_instr::FNMSUB_S: begin
        fpu_op = fpnew_pkg::FNMSUB;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
      end
      riscv_instr::FNMADD_S: begin
        fpu_op = fpnew_pkg::FNMSUB;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        src_fmt        = fpnew_pkg::FP32;
        dst_fmt        = fpnew_pkg::FP32;
        op_mode      = 1'b1;
      end

      ////////////////////
      // Half Precision //
      ////////////////////

      riscv_instr::FADD_H: begin
        fpu_op = fpnew_pkg::ADD;
        op_select[1] = AccBus_A;
        op_select[2] = AccBus_B;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
      end
      riscv_instr::FSUB_H: begin
        fpu_op = fpnew_pkg::ADD;
        op_select[1] = AccBus_A;
        op_select[2] = AccBus_B;
        op_mode = 1'b1;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
      end
      riscv_instr::FMUL_H: begin
        fpu_op = fpnew_pkg::MUL;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
      end
      riscv_instr::FSGNJ_H,
      riscv_instr::FSGNJN_H,
      riscv_instr::FSGNJX_H: begin
        fpu_op = fpnew_pkg::SGNJ;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
      end
      riscv_instr::FMIN_H,
      riscv_instr::FMAX_H: begin
        fpu_op = fpnew_pkg::MINMAX;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
      end
      riscv_instr::FCVT_S_H: begin
        fpu_op = fpnew_pkg::F2F;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt      = fpnew_pkg::FP32;
        dst_fmt      = fpnew_pkg::FP16;
      end
      riscv_instr::FCVT_H_S: begin
        fpu_op = fpnew_pkg::F2F;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP32;
      end
      riscv_instr::FLE_H,
      riscv_instr::FLT_H,
      riscv_instr::FEQ_H: begin
        fpu_op = fpnew_pkg::CMP;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt        = fpnew_pkg::FP16;
        dst_fmt        = fpnew_pkg::FP16;
      end
      riscv_instr::FCVT_W_H,
      riscv_instr::FCVT_WU_H: begin
        fpu_op = fpnew_pkg::F2I;
        op_select[0]   = AccBus_A;
        src_fmt        = fpnew_pkg::FP16;
        dst_fmt        = fpnew_pkg::FP16;
        if (acc_req.data_op inside {riscv_instr::FCVT_WU_H}) op_mode = 1'b1; // unsigned
      end
      riscv_instr::FMV_X_H: begin
        fpu_op = fpnew_pkg::SGNJ;
        fpu_rnd_mode   = fpnew_pkg::RUP; // passthrough without checking nan-box
        src_fmt        = fpnew_pkg::FP16;
        dst_fmt        = fpnew_pkg::FP16;
        op_mode        = 1'b1; // sign-extend result
        op_select[0]   = AccBus_A;
      end
      riscv_instr::FCLASS_H: begin
        fpu_op = fpnew_pkg::CLASSIFY;
        op_select[0]   = AccBus_A;
        fpu_rnd_mode   = fpnew_pkg::RNE;
        src_fmt        = fpnew_pkg::FP16;
        dst_fmt        = fpnew_pkg::FP16;
      end
      riscv_instr::FCVT_H_W,
      riscv_instr::FCVT_H_WU: begin
        fpu_op = fpnew_pkg::I2F;
        op_select[0]   = AccBus_A;
        src_fmt        = fpnew_pkg::FP16;
        dst_fmt        = fpnew_pkg::FP16;
        if (acc_req.data_op inside {riscv_instr::FCVT_H_WU}) op_mode = 1'b1; // unsigned
      end
      riscv_instr::FMV_H_X: begin
        fpu_op = fpnew_pkg::SGNJ;
        fpu_rnd_mode   = fpnew_pkg::RUP; // passthrough without checking nan-box
        src_fmt        = fpnew_pkg::FP16;
        dst_fmt        = fpnew_pkg::FP16;
        op_select[0]   = AccBus_A;
      end
      riscv_instr::FMADD_H: begin
        fpu_op = fpnew_pkg::FMADD;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
      end
      riscv_instr::FMSUB_H: begin
        fpu_op = fpnew_pkg::FMADD;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        op_mode      = 1'b1;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
      end
      riscv_instr::FNMSUB_H: begin
        fpu_op = fpnew_pkg::FNMSUB;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
      end
      riscv_instr::FNMADD_H: begin
        fpu_op = fpnew_pkg::FNMSUB;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        op_mode      = 1'b1;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
      end

      ////////////////////////////////////////
      // SIMD Half Precision Floating-Point //
      ////////////////////////////////////////

      riscv_instr::VFADD_H,
      riscv_instr::VFADD_R_H: begin
        fpu_op = fpnew_pkg::ADD;
        op_select[1] = AccBus_A;
        op_select[2] = AccBus_B;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFSUB_H,
      riscv_instr::VFSUB_R_H: begin
        fpu_op = fpnew_pkg::ADD;
        op_select[1] = AccBus_A;
        op_select[2] = AccBus_B;
        op_mode      = 1'b1;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFMUL_H,
      riscv_instr::VFMUL_R_H: begin
        fpu_op = fpnew_pkg::MUL;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFMIN_H,
      riscv_instr::VFMIN_R_H: begin
        fpu_op = fpnew_pkg::MINMAX;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        fpu_rnd_mode = fpnew_pkg::RNE;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
      end
      riscv_instr::VFMAX_H,
      riscv_instr::VFMAX_R_H: begin
        fpu_op = fpnew_pkg::MINMAX;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        fpu_rnd_mode = fpnew_pkg::RTZ;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
      end
      riscv_instr::VFSGNJ_H,
      riscv_instr::VFSGNJ_R_H: begin
        fpu_op = fpnew_pkg::SGNJ;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        fpu_rnd_mode = fpnew_pkg::RNE;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
      end
      riscv_instr::VFCLASS_H: begin
        fpu_op = fpnew_pkg::CLASSIFY;
        op_select[0]   = AccBus_A;
        fpu_rnd_mode   = fpnew_pkg::RNE;
        src_fmt        = fpnew_pkg::FP16;
        dst_fmt        = fpnew_pkg::FP16;
        vectorial_op   = 1'b1;
        fpu_tag_in.acc = 1'b1;
      end
      riscv_instr::VFSGNJN_H,
      riscv_instr::VFSGNJN_R_H: begin
        fpu_op = fpnew_pkg::SGNJ;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        fpu_rnd_mode = fpnew_pkg::RTZ;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
      end
      riscv_instr::VFSGNJX_H,
      riscv_instr::VFSGNJX_R_H: begin
        fpu_op = fpnew_pkg::SGNJ;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        fpu_rnd_mode = fpnew_pkg::RDN;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
      end
      riscv_instr::VFCVT_H_S,
      riscv_instr::VFCVTU_H_S: begin
        fpu_op = fpnew_pkg::F2F;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt      = fpnew_pkg::FP32;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFCVT_S_H,
      riscv_instr::VFCVTU_S_H: begin
        fpu_op = fpnew_pkg::F2F;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP32;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFEQ_H,
      riscv_instr::VFEQ_R_H: begin
        fpu_op = fpnew_pkg::CMP;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        fpu_rnd_mode   = fpnew_pkg::RDN;
        src_fmt        = fpnew_pkg::FP16;
        dst_fmt        = fpnew_pkg::FP16;
        vectorial_op   = 1'b1;
        fpu_tag_in.acc = 1'b1;
      end
      riscv_instr::VFNE_H,
      riscv_instr::VFNE_R_H: begin
        fpu_op = fpnew_pkg::CMP;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        fpu_rnd_mode   = fpnew_pkg::RDN;
        src_fmt        = fpnew_pkg::FP16;
        dst_fmt        = fpnew_pkg::FP16;
        op_mode        = 1'b1;
        vectorial_op   = 1'b1;
        fpu_tag_in.acc = 1'b1;
      end
      riscv_instr::VFLT_H,
      riscv_instr::VFLT_R_H: begin
        fpu_op = fpnew_pkg::CMP;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        fpu_rnd_mode   = fpnew_pkg::RTZ;
        src_fmt        = fpnew_pkg::FP16;
        dst_fmt        = fpnew_pkg::FP16;
        vectorial_op   = 1'b1;
        fpu_tag_in.acc = 1'b1;
      end
      riscv_instr::VFGE_H,
      riscv_instr::VFGE_R_H: begin
        fpu_op = fpnew_pkg::CMP;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        fpu_rnd_mode   = fpnew_pkg::RTZ;
        src_fmt        = fpnew_pkg::FP16;
        dst_fmt        = fpnew_pkg::FP16;
        op_mode        = 1'b1;
        vectorial_op   = 1'b1;
        fpu_tag_in.acc = 1'b1;
      end
      riscv_instr::VFLE_H,
      riscv_instr::VFLE_R_H: begin
        fpu_op = fpnew_pkg::CMP;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        fpu_rnd_mode   = fpnew_pkg::RNE;
        src_fmt        = fpnew_pkg::FP16;
        dst_fmt        = fpnew_pkg::FP16;
        vectorial_op   = 1'b1;
        fpu_tag_in.acc = 1'b1;
      end
      riscv_instr::VFGT_H,
      riscv_instr::VFGT_R_H: begin
        fpu_op = fpnew_pkg::CMP;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        fpu_rnd_mode   = fpnew_pkg::RNE;
        src_fmt        = fpnew_pkg::FP16;
        dst_fmt        = fpnew_pkg::FP16;
        op_mode        = 1'b1;
        vectorial_op   = 1'b1;
        fpu_tag_in.acc = 1'b1;
      end
      riscv_instr::VFMV_H_X: begin
        fpu_op = fpnew_pkg::SGNJ;
        fpu_rnd_mode   = fpnew_pkg::RUP; // passthrough without checking nan-box
        src_fmt        = fpnew_pkg::FP16;
        dst_fmt        = fpnew_pkg::FP16;
        vectorial_op   = 1'b1;
      end
      riscv_instr::VFMV_X_H: begin
        fpu_op = fpnew_pkg::SGNJ;
        fpu_rnd_mode   = fpnew_pkg::RUP; // passthrough without checking nan-box
        src_fmt        = fpnew_pkg::FP16;
        dst_fmt        = fpnew_pkg::FP16;
        op_mode        = 1'b1; // sign-extend result
        op_select[0] = AccBus_A;
        vectorial_op   = 1'b1;
        fpu_tag_in.acc = 1'b1;
      end
      riscv_instr::VFCVT_X_H,
      riscv_instr::VFCVT_XU_H: begin
        fpu_op = fpnew_pkg::F2I;
        op_select[0]   = AccBus_A;
        src_fmt        = fpnew_pkg::FP16;
        dst_fmt        = fpnew_pkg::FP16;
        int_fmt        = fpnew_pkg::INT16;
        vectorial_op   = 1'b1;
        fpu_tag_in.acc = 1'b1;
        set_dyn_rm     = 1'b1;
        if (acc_req.data_op inside {riscv_instr::VFCVT_XU_H}) op_mode = 1'b1; // upper
      end
      riscv_instr::VFCVT_H_X,
      riscv_instr::VFCVT_H_XU: begin
        fpu_op = fpnew_pkg::I2F;
        op_select[0] = AccBus_A;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        int_fmt      = fpnew_pkg::INT16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
        if (acc_req.data_op inside {riscv_instr::VFCVT_H_XU}) op_mode = 1'b1; // upper
      end
      riscv_instr::VFMAC_H,
      riscv_instr::VFMAC_R_H: begin
        fpu_op = fpnew_pkg::FMADD;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFMRE_H,
      riscv_instr::VFMRE_R_H: begin
        fpu_op = fpnew_pkg::FNMSUB;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFCPKA_H_S: begin
        fpu_op = fpnew_pkg::CPKAB;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        src_fmt      = fpnew_pkg::FP32;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFCPKB_H_S: begin
        fpu_op = fpnew_pkg::CPKAB;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        op_mode      = 1'b1;
        src_fmt      = fpnew_pkg::FP32;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFDOTPEX_S_H,
      riscv_instr::VFDOTPEX_S_R_H: begin
        fpu_op = fpnew_pkg::SDOTP;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP32;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFNDOTPEX_S_H,
      riscv_instr::VFNDOTPEX_S_R_H: begin
        fpu_op = fpnew_pkg::SDOTP;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        op_mode      = 1'b1;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP32;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFSUMEX_S_H,
      riscv_instr::VFNSUMEX_S_H: begin
        fpu_op = fpnew_pkg::EXVSUM;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP32;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::FCDOTPEX_S_H: begin
        fpu_op = fpnew_pkg::CSDOTP;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::FCNDOTPEX_S_H: begin
        fpu_op = fpnew_pkg::CSDOTP;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        op_mode      = 1'b1;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::FCCDOTPEX_S_H: begin
        fpu_op = fpnew_pkg::CCSDOTP;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::FCCNDOTPEX_S_H: begin
        fpu_op = fpnew_pkg::CCSDOTP;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        op_mode      = 1'b1;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end

      ///////////////////////
      // Quarter Precision //
      ///////////////////////

      riscv_instr::FADD_B: begin
        fpu_op = fpnew_pkg::ADD;
        op_select[1] = AccBus_A;
        op_select[2] = AccBus_B;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
      end
      riscv_instr::FSUB_B: begin
        fpu_op = fpnew_pkg::ADD;
        op_select[1] = AccBus_A;
        op_select[2] = AccBus_B;
        op_mode = 1'b1;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
      end
      riscv_instr::FMUL_B: begin
        fpu_op = fpnew_pkg::MUL;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
      end
      riscv_instr::FSGNJ_B,
      riscv_instr::FSGNJN_B,
      riscv_instr::FSGNJX_B: begin
        fpu_op = fpnew_pkg::SGNJ;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
      end
      riscv_instr::FMIN_B,
      riscv_instr::FMAX_B: begin
        fpu_op = fpnew_pkg::MINMAX;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
      end
      riscv_instr::FCVT_S_B: begin
        fpu_op = fpnew_pkg::F2F;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt      = fpnew_pkg::FP32;
        dst_fmt      = fpnew_pkg::FP8;
      end
      riscv_instr::FCVT_B_S: begin
        fpu_op = fpnew_pkg::F2F;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP32;
      end
      riscv_instr::FCVT_H_B: begin
        fpu_op = fpnew_pkg::F2F;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP8;
      end
      riscv_instr::FCVT_B_H: begin
        fpu_op = fpnew_pkg::F2F;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP16;
      end
      riscv_instr::FLE_B,
      riscv_instr::FLT_B,
      riscv_instr::FEQ_B: begin
        fpu_op = fpnew_pkg::CMP;
        op_select[0]   = AccBus_A;
        op_select[1]   = AccBus_B;
        src_fmt        = fpnew_pkg::FP8;
        dst_fmt        = fpnew_pkg::FP8;
      end
      riscv_instr::FCVT_W_B,
      riscv_instr::FCVT_WU_B: begin
        fpu_op = fpnew_pkg::F2I;
        op_select[0]   = AccBus_A;
        src_fmt        = fpnew_pkg::FP8;
        dst_fmt        = fpnew_pkg::FP8;
        if (acc_req.data_op inside {riscv_instr::FCVT_WU_B}) op_mode = 1'b1; // unsigned
      end
      riscv_instr::FMV_X_B: begin
        fpu_op = fpnew_pkg::SGNJ;
        op_select[0]   = AccBus_A;
        fpu_rnd_mode   = fpnew_pkg::RUP; // passthrough without checking nan-box
        src_fmt        = fpnew_pkg::FP8;
        dst_fmt        = fpnew_pkg::FP8;
        op_mode        = 1'b1; // sign-extend result
      end
      riscv_instr::FCLASS_B: begin
        fpu_op = fpnew_pkg::CLASSIFY;
        op_select[0]   = AccBus_A;
        fpu_rnd_mode   = fpnew_pkg::RNE;
        src_fmt        = fpnew_pkg::FP8;
        dst_fmt        = fpnew_pkg::FP8;
      end
      riscv_instr::FCVT_B_W,
      riscv_instr::FCVT_B_WU: begin
        fpu_op = fpnew_pkg::I2F;
        op_select[0] = AccBus_A;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
        if (acc_req.data_op inside {riscv_instr::FCVT_B_WU}) op_mode = 1'b1; // unsigned
      end
      riscv_instr::FMADD_B: begin
        fpu_op = fpnew_pkg::FMADD;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
      end
      riscv_instr::FMSUB_B: begin
        fpu_op = fpnew_pkg::FMADD;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        op_mode      = 1'b1;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
      end
      riscv_instr::FNMSUB_B: begin
        fpu_op = fpnew_pkg::FNMSUB;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
      end
      riscv_instr::FNMADD_B: begin
        fpu_op = fpnew_pkg::FNMSUB;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        op_mode      = 1'b1;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
      end

      ///////////////////////////////////////////
      // SIMD Quarter Precision Floating-Point //
      ///////////////////////////////////////////

      riscv_instr::VFADD_B,
      riscv_instr::VFADD_R_B: begin
        fpu_op = fpnew_pkg::ADD;
        op_select[1] = AccBus_A;
        op_select[2] = AccBus_B;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFSUB_B,
      riscv_instr::VFSUB_R_B: begin
        fpu_op = fpnew_pkg::ADD;
        op_select[1] = AccBus_A;
        op_select[2] = AccBus_B;
        op_mode      = 1'b1;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFMUL_B,
      riscv_instr::VFMUL_R_B: begin
        fpu_op = fpnew_pkg::MUL;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFMIN_B,
      riscv_instr::VFMIN_R_B: begin
        fpu_op = fpnew_pkg::MINMAX;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        fpu_rnd_mode = fpnew_pkg::RNE;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
        vectorial_op = 1'b1;
      end
      riscv_instr::VFMAX_B,
      riscv_instr::VFMAX_R_B: begin
        fpu_op = fpnew_pkg::MINMAX;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        fpu_rnd_mode = fpnew_pkg::RTZ;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
        vectorial_op = 1'b1;
      end
      riscv_instr::VFSGNJ_B,
      riscv_instr::VFSGNJ_R_B: begin
        fpu_op = fpnew_pkg::SGNJ;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        fpu_rnd_mode = fpnew_pkg::RNE;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
        vectorial_op = 1'b1;
      end
      riscv_instr::VFCLASS_H: begin
        fpu_op = fpnew_pkg::CLASSIFY;
        op_select[0]   = AccBus_A;
        fpu_rnd_mode   = fpnew_pkg::RNE;
        src_fmt        = fpnew_pkg::FP8;
        dst_fmt        = fpnew_pkg::FP8;
        vectorial_op   = 1'b1;
        fpu_tag_in.acc = 1'b1;
      end
      riscv_instr::VFSGNJN_B,
      riscv_instr::VFSGNJN_R_B: begin
        fpu_op = fpnew_pkg::SGNJ;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        fpu_rnd_mode = fpnew_pkg::RTZ;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
        vectorial_op = 1'b1;
      end
      riscv_instr::VFSGNJX_B,
      riscv_instr::VFSGNJX_R_B: begin
        fpu_op = fpnew_pkg::SGNJ;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        fpu_rnd_mode = fpnew_pkg::RDN;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
        vectorial_op = 1'b1;
      end
      riscv_instr::VFCVT_B_S,
      riscv_instr::VFCVTU_B_S: begin
        fpu_op = fpnew_pkg::F2F;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt      = fpnew_pkg::FP32;
        dst_fmt      = fpnew_pkg::FP8;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFCVT_H_B,
      riscv_instr::VFCVTU_H_B: begin
        fpu_op = fpnew_pkg::F2F;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFCVT_B_H,
      riscv_instr::VFCVTU_B_H: begin
        fpu_op = fpnew_pkg::F2F;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt      = fpnew_pkg::FP16;
        dst_fmt      = fpnew_pkg::FP8;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFEQ_B,
      riscv_instr::VFEQ_R_B: begin
        fpu_op = fpnew_pkg::CMP;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        fpu_rnd_mode   = fpnew_pkg::RDN;
        src_fmt        = fpnew_pkg::FP8;
        dst_fmt        = fpnew_pkg::FP8;
        vectorial_op   = 1'b1;
        fpu_tag_in.acc = 1'b1;
      end
      riscv_instr::VFNE_B,
      riscv_instr::VFNE_R_B: begin
        fpu_op = fpnew_pkg::CMP;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        fpu_rnd_mode   = fpnew_pkg::RDN;
        src_fmt        = fpnew_pkg::FP8;
        dst_fmt        = fpnew_pkg::FP8;
        op_mode        = 1'b1;
        vectorial_op   = 1'b1;
        fpu_tag_in.acc = 1'b1;
      end
      riscv_instr::VFLT_B,
      riscv_instr::VFLT_R_B: begin
        fpu_op = fpnew_pkg::CMP;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        fpu_rnd_mode   = fpnew_pkg::RTZ;
        src_fmt        = fpnew_pkg::FP8;
        dst_fmt        = fpnew_pkg::FP8;
        vectorial_op   = 1'b1;
        fpu_tag_in.acc = 1'b1;
      end
      riscv_instr::VFGE_B,
      riscv_instr::VFGE_R_B: begin
        fpu_op = fpnew_pkg::CMP;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        fpu_rnd_mode   = fpnew_pkg::RTZ;
        src_fmt        = fpnew_pkg::FP8;
        dst_fmt        = fpnew_pkg::FP8;
        op_mode        = 1'b1;
        vectorial_op   = 1'b1;
        fpu_tag_in.acc = 1'b1;
      end
      riscv_instr::VFLE_B,
      riscv_instr::VFLE_R_B: begin
        fpu_op = fpnew_pkg::CMP;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        fpu_rnd_mode   = fpnew_pkg::RNE;
        src_fmt        = fpnew_pkg::FP8;
        dst_fmt        = fpnew_pkg::FP8;
        vectorial_op   = 1'b1;
        fpu_tag_in.acc = 1'b1;
      end
      riscv_instr::VFGT_B,
      riscv_instr::VFGT_R_B: begin
        fpu_op = fpnew_pkg::CMP;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        fpu_rnd_mode   = fpnew_pkg::RNE;
        src_fmt        = fpnew_pkg::FP8;
        dst_fmt        = fpnew_pkg::FP8;
        op_mode        = 1'b1;
        vectorial_op   = 1'b1;
        fpu_tag_in.acc = 1'b1;
      end
      riscv_instr::VFMV_B_X: begin
        fpu_op = fpnew_pkg::SGNJ;
        fpu_rnd_mode   = fpnew_pkg::RUP; // passthrough without checking nan-box
        src_fmt        = fpnew_pkg::FP8;
        dst_fmt        = fpnew_pkg::FP8;
        vectorial_op   = 1'b1;
      end
      riscv_instr::VFMV_X_B: begin
        fpu_op = fpnew_pkg::SGNJ;
        fpu_rnd_mode   = fpnew_pkg::RUP; // passthrough without checking nan-box
        src_fmt        = fpnew_pkg::FP8;
        dst_fmt        = fpnew_pkg::FP8;
        op_mode        = 1'b1; // sign-extend result
        op_select[0] = AccBus_A;
        vectorial_op   = 1'b1;
        fpu_tag_in.acc = 1'b1;
      end
      riscv_instr::VFCVT_X_B,
      riscv_instr::VFCVT_XU_B: begin
        fpu_op = fpnew_pkg::F2I;
        op_select[0]   = AccBus_A;
        src_fmt        = fpnew_pkg::FP8;
        dst_fmt        = fpnew_pkg::FP8;
        int_fmt        = fpnew_pkg::INT8;
        vectorial_op   = 1'b1;
        fpu_tag_in.acc = 1'b1;
        set_dyn_rm     = 1'b1;
        if (acc_req.data_op inside {riscv_instr::VFCVT_XU_B}) op_mode = 1'b1; // upper
      end
      riscv_instr::VFCVT_B_X,
      riscv_instr::VFCVT_B_XU: begin
        fpu_op = fpnew_pkg::I2F;
        op_select[0] = AccBus_A;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
        int_fmt      = fpnew_pkg::INT8;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
        if (acc_req.data_op inside {riscv_instr::VFCVT_B_XU}) op_mode = 1'b1; // upper
      end
      riscv_instr::VFMAC_B,
      riscv_instr::VFMAC_R_B: begin
        fpu_op = fpnew_pkg::FMADD;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFMRE_B,
      riscv_instr::VFMRE_R_B: begin
        fpu_op = fpnew_pkg::FNMSUB;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP8;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFCPKA_B_S: begin
        fpu_op = fpnew_pkg::CPKAB;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        src_fmt      = fpnew_pkg::FP32;
        dst_fmt      = fpnew_pkg::FP8;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFCPKB_B_S: begin
        fpu_op = fpnew_pkg::CPKAB;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        op_mode      = 1'b1;
        src_fmt      = fpnew_pkg::FP32;
        dst_fmt      = fpnew_pkg::FP8;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFDOTPEX_H_B,
      riscv_instr::VFDOTPEX_H_R_B: begin
        fpu_op = fpnew_pkg::SDOTP;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFNDOTPEX_H_B,
      riscv_instr::VFNDOTPEX_H_R_B: begin
        fpu_op = fpnew_pkg::SDOTP;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        op_mode      = 1'b1;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFSUMEX_H_B,
      riscv_instr::VFNSUMEX_H_B: begin
        fpu_op = fpnew_pkg::EXVSUM;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP16;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFDOTPEXA_S_B,
      riscv_instr::VFDOTPEXA_S_R_B: begin
        fpu_op = fpnew_pkg::SDOTP;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP32;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
      end
      riscv_instr::VFDOTPEXB_S_B,
      riscv_instr::VFDOTPEXB_S_R_B: begin
        select_upper_half = 1'b1;
        fpu_op = fpnew_pkg::SDOTP;
        op_select[0] = AccBus_A;
        op_select[1] = AccBus_B;
        op_select[2] = AccBus_C;
        src_fmt      = fpnew_pkg::FP8;
        dst_fmt      = fpnew_pkg::FP32;
        vectorial_op = 1'b1;
        set_dyn_rm   = 1'b1;
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
      // Select upper half if needed - only required by VFDOTPEXB_S_B, VFDOTPEXB_S_R_B
      if (i != 2) begin
        if (select_upper_half) begin
          op[i] = {{(FLEN/2){1'b1}}, op[i][FLEN-1:FLEN/2]};
        end
      end
    end
  end

  // ----------------------
  // Floating Point Unit
  // ----------------------
  snitch_fpu #(
    .TagType            ( logic[5:0]        ),
    .FPUImplementation  ( FPUImplementation )
  ) i_fpu (
    .clk_i                           ,
    .rst_ni         ( ~rst_i        ),
    .hart_id_i      ( hart_id_i     ),
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
