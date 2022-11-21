`include "common_cells/registers.svh"

/// Description: Filters FPU repetition instructions
module snitch_sequencer import snitch_pkg::*; #(
    parameter int unsigned Depth = 16,
    parameter acc_addr_e DstAddr = snitch_pkg::FP_SS,
    localparam int unsigned DepthBits = $clog2(Depth)
) (
  input  logic          clk_i,
  input  logic          rst_i,
  // pragma translate_off
  output fpu_sequencer_trace_port_t trace_port_o,
  // pragma translate_on
  input  acc_addr_e     inp_qaddr_i,
  input  logic [4:0]    inp_qid_i,
  input  logic [31:0]   inp_qdata_op_i, // RISC-V instruction
  input  data_t         inp_qdata_arga_i,
  input  data_t         inp_qdata_argb_i,
  input  addr_t         inp_qdata_argc_i,
  input  logic          inp_qvalid_i,
  output logic          inp_qready_o,
  output acc_addr_e     oup_qaddr_o,
  output logic [4:0]    oup_qid_o,
  output logic [31:0]   oup_qdata_op_o, // RISC-V instruction
  output data_t         oup_qdata_arga_o,
  output data_t         oup_qdata_argb_o,
  output addr_t         oup_qdata_argc_o,
  output logic          oup_qvalid_o,
  input  logic          oup_qready_i
);
  localparam int RptBits = 16;

  typedef struct packed {
    logic                 is_outer;
    logic [DepthBits-1:0] max_inst;
    logic [RptBits-1:0]   max_rpt;
    logic [2:0]           stagger_max;
    logic [3:0]           stagger_mask; // one-hot stagger mask
    logic [DepthBits:0]   base_pointer; // loop base pointer where the config starts
  } seq_cfg_t;

  logic seq_cfg_buffer_empty, seq_cfg_buffer_full, seq_cfg_buffer_push, seq_cfg_buffer_pop, seq_cfg_buffer_valid;
  seq_cfg_t seq_cfg_buffer_in, seq_cfg_buffer_out;
  seq_cfg_t curr_cfg;

  logic inst_last, rpt_last, seq_last, seq_next;

  logic seq_out_ready, seq_out_valid;
  logic [31:0] seq_qdata_op;
  logic [33:0] seq_qdata_argc;

  logic core_rb_valid, core_rb_ready;
  logic core_rpt_valid, core_rpt_ready;
  logic core_direct_valid, core_direct_ready;

  // Ringbuffer.
  // TODO(fschuiki, zarubaf) ICEBOX: This is a hack to allow fld/fsd to be added
  // into the main sequence buffer. It would actually be better to have a
  // separate buffer only for fld/fsd. But this would require more precise
  // tracking of instruction IDs to ensure ordering at the output.
  typedef struct packed {
    logic [31:0] qdata_op;
    addr_t qdata_argc;
  } seq_entry_t;
  seq_entry_t [Depth-1:0] mem_d, mem_q;
  logic [DepthBits:0] rb_rd_pointer;
  logic [DepthBits:0] rb_wr_pointer;
  logic [DepthBits:0] rb_base_pointer;
  seq_entry_t rb_rd_data;
  seq_entry_t rb_wr_data;
  logic rb_wr_en;
  logic rb_full;
  logic rb_empty;
  logic rb_contains_instructions, rb_contains_no_instructions;

  always_comb begin : ringbuffer
    mem_d = mem_q;
    if (rb_wr_en) mem_d[rb_wr_pointer[DepthBits-1:0]] = rb_wr_data;
    rb_rd_data = mem_q[rb_rd_pointer[DepthBits-1:0]];
    rb_full = (rb_base_pointer ^ rb_wr_pointer) == 1 << DepthBits;
    rb_contains_no_instructions = (rb_base_pointer ^ rb_wr_pointer) == '0;
    rb_contains_instructions = ~rb_contains_no_instructions;
    rb_empty = (rb_rd_pointer ^ rb_wr_pointer) == '0;
  end

  `FFNR(mem_q, mem_d, clk_i)

  /// Compute ringbuffer addresses.
  logic [DepthBits:0] rd_pointer_d, rd_pointer_q;
  logic [DepthBits:0] wr_pointer_d, wr_pointer_q;

  logic [RptBits-1:0]   rpt_cnt_d, rpt_cnt_q;
  logic [DepthBits-1:0] inst_cnt_d, inst_cnt_q;
  logic [2:0] stagger_cnt_q, stagger_cnt_d;

  `FFSR(rd_pointer_q, rd_pointer_d, '0, clk_i, rst_i)
  `FFSR(wr_pointer_q, wr_pointer_d, '0, clk_i, rst_i)
  `FFSR(rpt_cnt_q, rpt_cnt_d,'0, clk_i, rst_i)
  `FFSR(inst_cnt_q, inst_cnt_d,'0, clk_i, rst_i)
  `FFSR(stagger_cnt_q, stagger_cnt_d,'0, clk_i, rst_i)

  // set by sequencer when done with the entire sequence

  always_comb begin
    rd_pointer_d = rd_pointer_q;
    wr_pointer_d = wr_pointer_q;

    rb_wr_en = 0;
    core_rb_ready = ~rb_full;

    // write logic
    if (core_rb_valid && core_rb_ready) begin
      wr_pointer_d = wr_pointer_q + 1;
      rb_wr_en = 1;
    end
    // read logic
    if (seq_last && seq_next) begin
      /* verilator lint_off WIDTH */
      rd_pointer_d = rd_pointer_q + curr_cfg.max_inst + 1;
      /* verilator lint_on WIDTH */
    end
  end


  assign rb_wr_data.qdata_op = inp_qdata_op_i;
  assign rb_wr_data.qdata_argc = inp_qdata_argc_i;
  assign rb_wr_pointer = wr_pointer_q;
  assign rb_base_pointer = rd_pointer_q;
  assign rb_rd_pointer = rb_base_pointer + inst_cnt_q;

  assign inst_last = inst_cnt_q == curr_cfg.max_inst;
  assign rpt_last = rpt_cnt_q == curr_cfg.max_rpt;
  assign seq_last = inst_last & rpt_last;
  assign seq_cfg_buffer_pop = seq_last & seq_next & seq_cfg_buffer_valid;

  always_comb begin : sequence_logic
    inst_cnt_d = inst_cnt_q;
    rpt_cnt_d = rpt_cnt_q;
    stagger_cnt_d = stagger_cnt_q;
    if (seq_next) begin
      if (curr_cfg.is_outer) begin
        if (inst_last) begin
          inst_cnt_d = 0;
          rpt_cnt_d = rpt_last ? 0 : rpt_cnt_q + 1;
          stagger_cnt_d = rpt_last ? 0 : ((stagger_cnt_q == curr_cfg.stagger_max) ? 0 : stagger_cnt_q + 1);
        end else begin
          inst_cnt_d = inst_cnt_q + 1;
        end
      end else begin
        if (rpt_last) begin
          rpt_cnt_d = 0;
          inst_cnt_d = inst_last ? 0 : inst_cnt_q + 1;
          stagger_cnt_d = inst_last ? 0 : ((stagger_cnt_q == curr_cfg.stagger_max) ? 0 : stagger_cnt_q + 1);
        end else begin
          rpt_cnt_d = rpt_cnt_q + 1;
          stagger_cnt_d = (stagger_cnt_q == curr_cfg.stagger_max) ? 0 : stagger_cnt_q + 1;
        end
      end
    end
  end

  assign seq_next = seq_out_valid & seq_out_ready;
  assign seq_out_valid = ~rb_empty;

  // Compose offloading instruction e.g. staggering.
  /* verilator lint_off WIDTH */
  always_comb begin
    seq_qdata_op = rb_rd_data.qdata_op;
    seq_qdata_argc = rb_rd_data.qdata_argc;
    if (curr_cfg.stagger_mask[0]) seq_qdata_op[11:7] += stagger_cnt_q;
    if (curr_cfg.stagger_mask[1]) seq_qdata_op[19:15] += stagger_cnt_q;
    if (curr_cfg.stagger_mask[2]) seq_qdata_op[24:20] += stagger_cnt_q;
    if (curr_cfg.stagger_mask[3]) seq_qdata_op[31:27] += stagger_cnt_q;
  end
  /* verilator lint_on WIDTH */

  // Sequence configuration buffer input.
  assign core_rpt_ready = ~seq_cfg_buffer_full;
  assign seq_cfg_buffer_push = core_rpt_valid & core_rpt_ready;

  fifo_v3 #(
    .dtype ( seq_cfg_t )
  ) seq_cfg_buffer (
    .clk_i                              ,
    .rst_ni     ( ~rst_i               ),
    .flush_i    ( 1'b0                 ),
    .testmode_i ( 1'b0                 ),
    .full_o     ( seq_cfg_buffer_full  ),
    .empty_o    ( seq_cfg_buffer_empty ),
    .usage_o    (                      ),
    .data_i     ( seq_cfg_buffer_in    ),
    .push_i     ( seq_cfg_buffer_push  ),
    .data_o     ( seq_cfg_buffer_out   ),
    .pop_i      ( seq_cfg_buffer_pop   )
  );

  assign seq_cfg_buffer_in.is_outer = inp_qdata_op_i[7];
  assign seq_cfg_buffer_in.max_inst = inp_qdata_op_i[20 +: DepthBits];
  assign seq_cfg_buffer_in.stagger_mask = inp_qdata_op_i[11:8];
  assign seq_cfg_buffer_in.stagger_max = inp_qdata_op_i[14:12];
  assign seq_cfg_buffer_in.max_rpt =  inp_qdata_arga_i[RptBits-1:0];
  assign seq_cfg_buffer_in.base_pointer = rb_wr_pointer;

  always_comb begin
    curr_cfg = seq_cfg_buffer_out;
    seq_cfg_buffer_valid = 1;
    if (seq_cfg_buffer_empty || seq_cfg_buffer_out.base_pointer != rb_base_pointer) begin
      curr_cfg.max_inst = '0;
      curr_cfg.max_rpt = '0;
      seq_cfg_buffer_valid = 0;
    end
  end

  /// Generate core handshakes.
  always_comb begin
    core_rb_valid = '0;
    core_rpt_valid = '0;
    core_direct_valid = '0;

    inp_qready_o = '0;

    unique casez (inp_qdata_op_i)
      // // frep instructions are pushed into the sequencer control branch
      // riscv_instr::FREP,
      // riscv_instr::IREP: begin
      //   inp_qready_o = core_rpt_ready;
      //   core_rpt_valid = inp_qvalid_i;
      // end

      // instructions which explicitly sync between int and float pipeline are
      // pushed into the direct branch where they block

      // flo// at to int
      // riscv_instr::FLE_S,
      // riscv_instr::FLT_S,
      // riscv_instr::FEQ_S,
      // riscv_instr::FCLASS_S,
      // riscv_instr::FCVT_W_S,
      // riscv_instr::FCVT_WU_S,
      // riscv_instr::FMV_X_W,
      // riscv_instr::VFEQ_S,
      // riscv_instr::VFEQ_R_S,
      // riscv_instr::VFNE_S,
      // riscv_instr::VFNE_R_S,
      // riscv_instr::VFLT_S,
      // riscv_instr::VFLT_R_S,
      // riscv_instr::VFGE_S,
      // riscv_instr::VFGE_R_S,
      // riscv_instr::VFLE_S,
      // riscv_instr::VFLE_R_S,
      // riscv_instr::VFGT_S,
      // riscv_instr::VFGT_R_S,
      // riscv_instr::VFCLASS_S,
      // riscv_instr::FLE_D,
      // riscv_instr::FLT_D,
      // riscv_instr::FEQ_D,
      // riscv_instr::FCLASS_D,
      // riscv_instr::FCVT_W_D,
      // riscv_instr::FCVT_WU_D,
      // riscv_instr::FMV_X_D,
      // riscv_instr::FLE_H,
      // riscv_instr::FLT_H,
      // riscv_instr::FEQ_H,
      // riscv_instr::FCLASS_H,
      // riscv_instr::FCVT_W_H,
      // riscv_instr::FCVT_WU_H,
      // riscv_instr::FMV_X_H,
      // riscv_instr::VFEQ_H,
      // riscv_instr::VFEQ_R_H,
      // riscv_instr::VFNE_H,
      // riscv_instr::VFNE_R_H,
      // riscv_instr::VFLT_H,
      // riscv_instr::VFLT_R_H,
      // riscv_instr::VFGE_H,
      // riscv_instr::VFGE_R_H,
      // riscv_instr::VFLE_H,
      // riscv_instr::VFLE_R_H,
      // riscv_instr::VFGT_H,
      // riscv_instr::VFGT_R_H,
      // riscv_instr::VFCLASS_H,
      // riscv_instr::VFMV_X_H,
      // riscv_instr::VFCVT_X_H,
      // riscv_instr::VFCVT_XU_H,
      // riscv_instr::FLE_AH,
      // riscv_instr::FLT_AH,
      // riscv_instr::FEQ_AH,
      // riscv_instr::FCLASS_AH,
      // riscv_instr::FMV_X_AH,
      // riscv_instr::VFEQ_AH,
      // riscv_instr::VFEQ_R_AH,
      // riscv_instr::VFNE_AH,
      // riscv_instr::VFNE_R_AH,
      // riscv_instr::VFLT_AH,
      // riscv_instr::VFLT_R_AH,
      // riscv_instr::VFGE_AH,
      // riscv_instr::VFGE_R_AH,
      // riscv_instr::VFLE_AH,
      // riscv_instr::VFLE_R_AH,
      // riscv_instr::VFGT_AH,
      // riscv_instr::VFGT_R_AH,
      // riscv_instr::VFCLASS_AH,
      // riscv_instr::VFMV_X_AH,
      // riscv_instr::VFCVT_X_AH,
      // riscv_instr::VFCVT_XU_AH,
      // riscv_instr::FLE_B,
      // riscv_instr::FLT_B,
      // riscv_instr::FEQ_B,
      // riscv_instr::FCLASS_B,
      // riscv_instr::FCVT_W_B,
      // riscv_instr::FCVT_WU_B,
      // riscv_instr::FMV_X_B,
      // riscv_instr::VFEQ_B,
      // riscv_instr::VFEQ_R_B,
      // riscv_instr::VFNE_B,
      // riscv_instr::VFNE_R_B,
      // riscv_instr::VFLT_B,
      // riscv_instr::VFLT_R_B,
      // riscv_instr::VFGE_B,
      // riscv_instr::VFGE_R_B,
      // riscv_instr::VFLE_B,
      // riscv_instr::VFLE_R_B,
      // riscv_instr::VFGT_B,
      // riscv_instr::VFGT_R_B,
      // riscv_instr::VFCLASS_B,
      // riscv_instr::VFMV_X_B,
      // riscv_instr::VFCVT_X_B,
      // riscv_instr::VFCVT_XU_B,

      // // int to float
      // riscv_instr::FMV_W_X,
      // riscv_instr::FCVT_S_W,
      // riscv_instr::FCVT_S_WU,
      // riscv_instr::FCVT_D_W,
      // riscv_instr::FCVT_D_WU,
      // riscv_instr::FMV_H_X,
      // riscv_instr::FCVT_H_W,
      // riscv_instr::FCVT_H_WU,
      // riscv_instr::VFMV_H_X,
      // riscv_instr::VFCVT_H_X,
      // riscv_instr::VFCVT_H_XU,
      // riscv_instr::FMV_AH_X,
      // riscv_instr::VFMV_AH_X,
      // riscv_instr::VFCVT_AH_X,
      // riscv_instr::VFCVT_AH_XU,
      // riscv_instr::FMV_B_X,
      // riscv_instr::FCVT_B_W,
      // riscv_instr::FCVT_B_WU,
      // riscv_instr::VFMV_B_X,
      // riscv_instr::VFCVT_B_X,
      // riscv_instr::VFCVT_B_XU,

      // riscv_instr::IMV_X_W,
      // riscv_instr::IMV_W_X,
      // // CSR accesses
      // riscv_instr::CSRRW,
      // riscv_instr::CSRRS,
      // riscv_instr::CSRRC,
      // riscv_instr::CSRRWI,
      // riscv_instr::CSRRSI,
      // riscv_instr::CSRRCI: begin
      //   inp_qready_o = core_direct_ready;
      //   core_direct_valid = inp_qvalid_i;
      // end

      // all other instructions are pushed into the sequence buffer
      default: begin
        inp_qready_o = core_rb_ready;
        core_rb_valid = inp_qvalid_i;
      end
    endcase
  end

  /// Priority encoder to core.
  always_comb begin
    oup_qvalid_o     = core_direct_valid;
    oup_qaddr_o      = inp_qaddr_i;
    oup_qid_o        = inp_qid_i;
    oup_qdata_op_o   = inp_qdata_op_i;
    oup_qdata_arga_o = inp_qdata_arga_i;
    oup_qdata_argb_o = inp_qdata_argb_i;
    oup_qdata_argc_o = inp_qdata_argc_i;

    core_direct_ready = 1'b0;
    seq_out_ready = 1'b0;

    if (rb_contains_instructions) begin
      oup_qvalid_o     = seq_out_valid;
      oup_qid_o        = '0;
      oup_qaddr_o      = DstAddr;
      oup_qdata_op_o   = seq_qdata_op;
      oup_qdata_arga_o = '0;
      oup_qdata_argb_o = '0;
      oup_qdata_argc_o = $unsigned(seq_qdata_argc);
      seq_out_ready    = oup_qready_i;
    end else begin
      core_direct_ready = oup_qready_i;
    end
  end

  // Trace Port
  // pragma translate_off
  assign trace_port_o.cbuf_push = seq_cfg_buffer_push;
  assign trace_port_o.is_outer = seq_cfg_buffer_in.is_outer;
  assign trace_port_o.max_inst = seq_cfg_buffer_in.max_inst;
  assign trace_port_o.max_rpt = seq_cfg_buffer_in.max_rpt;
  assign trace_port_o.stg_max = seq_cfg_buffer_in.stagger_max;
  assign trace_port_o.stg_mask = seq_cfg_buffer_in.stagger_mask;
  // pragma translate_on
endmodule
