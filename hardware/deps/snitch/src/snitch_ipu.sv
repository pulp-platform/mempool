/// Integer Processing Unit
`include "common_cells/registers.svh"
/// Based on Snitch Shared Muliplier/Divider
/// Author: Sergio Mazzola, <smazzola@student.ethz.ch>

module snitch_ipu #(
  parameter int unsigned IdWidth = 5
) (
  input  logic                     clk_i,
  input  logic                     rst_i,
  // Accelerator Interface - Slave
  input  logic [31:0]              acc_qaddr_i,      // unused
  input  logic [IdWidth-1:0]       acc_qid_i,
  input  logic [31:0]              acc_qdata_op_i,   // RISC-V instruction
  input  logic [31:0]              acc_qdata_arga_i,
  input  logic [31:0]              acc_qdata_argb_i,
  input  logic [31:0]              acc_qdata_argc_i,
  input  logic                     acc_qvalid_i,
  output logic                     acc_qready_o,
  output logic [31:0]              acc_pdata_o,
  output logic [IdWidth-1:0]       acc_pid_o,
  output logic                     acc_perror_o,
  output logic                     acc_pvalid_o,
  input  logic                     acc_pready_i
);
  typedef struct packed {
    logic [31:0]        result;
    logic [IdWidth-1:0] id;
  } result_t;
  // input handshake
  logic div_valid_op, div_ready_op;
  logic mul_valid_op, mul_ready_op;
  logic dsp_valid_op, dsp_ready_op;
  // output handshake
  logic mul_valid, mul_ready;
  logic div_valid, div_ready;
  logic dsp_valid, dsp_ready;
  result_t div, mul, dsp, oup;
  logic illegal_instruction;

  always_comb begin
    mul_valid_op = 1'b0;
    div_valid_op = 1'b0;
    dsp_valid_op = 1'b0;
    acc_qready_o = 1'b0;
    acc_perror_o = 1'b0;
    illegal_instruction = 1'b0;
    unique casez (acc_qdata_op_i)
      riscv_instr::MUL,
      riscv_instr::MULH,
      riscv_instr::MULHSU,
      riscv_instr::MULHU: begin
        mul_valid_op = acc_qvalid_i;
        acc_qready_o = mul_ready_op;
      end
      riscv_instr::DIV,
      riscv_instr::DIVU,
      riscv_instr::REM,
      riscv_instr::REMU: begin
        div_valid_op = acc_qvalid_i;
        acc_qready_o = div_ready_op;
      end
      riscv_instr::P_ABS,          // Xpulpimg: p.abs
      riscv_instr::P_SLET,         // Xpulpimg: p.slet
      riscv_instr::P_SLETU,        // Xpulpimg: p.sletu
      riscv_instr::P_MIN,          // Xpulpimg: p.min
      riscv_instr::P_MINU,         // Xpulpimg: p.minu
      riscv_instr::P_MAX,          // Xpulpimg: p.max
      riscv_instr::P_MAXU,         // Xpulpimg: p.maxu
      riscv_instr::P_EXTHS,        // Xpulpimg: p.exths
      riscv_instr::P_EXTHZ,        // Xpulpimg: p.exthz
      riscv_instr::P_EXTBS,        // Xpulpimg: p.extbs
      riscv_instr::P_EXTBZ,        // Xpulpimg: p.extbz
      riscv_instr::P_CLIP,         // Xpulpimg: p.clip
      riscv_instr::P_CLIPU,        // Xpulpimg: p.clipu
      riscv_instr::P_CLIPR,        // Xpulpimg: p.clipr
      riscv_instr::P_CLIPUR: begin // Xpulpimg: p.clipur
        dsp_valid_op = acc_qvalid_i;
        acc_qready_o = dsp_ready_op;
      end
      default: illegal_instruction = 1'b1;
    endcase
  end

  // Multiplication
  multiplier #(
    .Width    ( 32      ),
    .IdWidth  ( IdWidth )
  ) i_multiplier (
    .clk_i,
    .rst_i,
    .id_i        ( acc_qid_i              ),
    .operator_i  ( acc_qdata_op_i         ),
    .operand_a_i ( acc_qdata_arga_i       ),
    .operand_b_i ( acc_qdata_argb_i       ),
    .valid_i     ( mul_valid_op           ),
    .ready_o     ( mul_ready_op           ),
    .result_o    ( mul.result             ),
    .valid_o     ( mul_valid              ),
    .ready_i     ( mul_ready              ),
    .id_o        ( mul.id                 )
  );
  // Serial Divider
  serdiv #(
      .WIDTH       ( 32      ),
      .IdWidth     ( IdWidth )
  ) i_div (
      .clk_i       ( clk_i                ),
      .rst_ni      ( ~rst_i               ),
      .id_i        ( acc_qid_i              ),
      .operator_i  ( acc_qdata_op_i         ),
      .op_a_i      ( acc_qdata_arga_i       ),
      .op_b_i      ( acc_qdata_argb_i       ),
      .in_vld_i    ( div_valid_op           ),
      .in_rdy_o    ( div_ready_op           ),
      .out_vld_o   ( div_valid              ),
      .out_rdy_i   ( div_ready              ),
      .id_o        ( div.id                 ),
      .res_o       ( div.result             )
  );
  // DSP Unit
  dspu #(
      .Width    ( 32      ),
      .IdWidth  ( IdWidth )
  ) i_dspu (
      .clk_i       ( clk_i                  ),
      .rst_i       ( rst_i                  ),
      .id_i        ( acc_qid_i              ),
      .operator_i  ( acc_qdata_op_i         ),
      .op_a_i      ( acc_qdata_arga_i       ),
      .op_b_i      ( acc_qdata_argb_i       ),
      .in_valid_i  ( dsp_valid_op           ),
      .in_ready_o  ( dsp_ready_op           ),
      .out_valid_o ( dsp_valid              ),
      .out_ready_i ( dsp_ready              ),
      .id_o        ( dsp.id                 ),
      .result_o    ( dsp.result             )
  );
  // Output Arbitration
  stream_arbiter #(
    .DATA_T ( result_t ),
    .N_INP  ( 3        )
  ) i_stream_arbiter (
    .clk_i,
    .rst_ni      ( ~rst_i                            ),
    .inp_data_i  ( {div, mul, dsp}                   ),
    .inp_valid_i ( {div_valid, mul_valid, dsp_valid} ),
    .inp_ready_o ( {div_ready, mul_ready, dsp_ready} ),
    .oup_data_o  ( oup                               ),
    .oup_valid_o ( acc_pvalid_o                      ),
    .oup_ready_i ( acc_pready_i                      )
  );
  assign acc_pdata_o = oup.result;
  assign acc_pid_o = oup.id;
endmodule


module dspu #(
  parameter int unsigned Width = 32,
  parameter int unsigned IdWidth = 5
) (
    input  logic               clk_i,      // unused
    input  logic               rst_i,      // unused
    input  logic [IdWidth-1:0] id_i,
    input  logic [31:0]        operator_i,
    input  logic [Width-1:0]   op_a_i,
    input  logic [Width-1:0]   op_b_i,
    input  logic               in_valid_i,
    output logic               in_ready_o,
    output logic               out_valid_o,
    input  logic               out_ready_i,
    output logic [IdWidth-1:0] id_o,
    output logic [Width-1:0]   result_o
);

  // Control signals
  assign out_valid_o = in_valid_i;
  assign in_ready_o = out_ready_i;
  assign id_o = id_i;

  // Decode fields
  logic [4:0] ximm;
  assign ximm = operator_i[24:20];

  //  ___    _  _____  _    ___   _  _____  _  _
  // |   \  /_\|_   _|/_\  | _ \ /_\|_   _|| || |
  // | |) |/ _ \ | | / _ \ |  _// _ \ | |  | __ |
  // |___//_/ \_\|_|/_/ \_\|_| /_/ \_\|_|  |_||_|
  //

  // --------------------
  // Clips
  // --------------------
  logic [Width-1:0] clip_op_b, clip_op_b_n;
  logic [Width-1:0] clip_lower;
  logic clip_instr_unsigned;
  logic clip_instr_immediate;

  assign clip_instr_unsigned = (operator_i ==? riscv_instr::P_CLIPU) || (operator_i ==? riscv_instr::P_CLIPUR);
  assign clip_instr_immediate = (operator_i ==? riscv_instr::P_CLIP) || (operator_i ==? riscv_instr::P_CLIPU);

  // Generate -2^(ximm-1), 2^(ximm-1)-1 for clip/clipu and -rs2-1, rs2 for clipr, clipur
  assign clip_lower = ({(Width+1){1'b1}} << $unsigned(ximm)) >> 1;
  assign clip_op_b_n = clip_instr_unsigned ? 'b0 : ((operator_i ==? riscv_instr::P_CLIP) ? clip_lower : ~op_b_i);
  assign clip_op_b = clip_instr_immediate ? ~clip_lower : op_b_i;

  // --------------------
  // Shared comparator
  // --------------------
  logic [Width-1:0] cmp_op_a, cmp_op_b;
  logic cmp_signed;
  logic cmp_result;

  // Sign of the comparison
  always_comb begin
    cmp_signed = 1'b1;
    unique casez (operator_i)
      riscv_instr::P_SLETU,
      riscv_instr::P_MINU,
      riscv_instr::P_MAXU:
        cmp_signed = 1'b0;
      default: ;
    endcase
  end

  // Comparison operands
  always_comb begin
    cmp_op_a = op_a_i;
    cmp_op_b = op_b_i;
    unique casez (operator_i)
      riscv_instr::P_ABS: cmp_op_b = 'b0;
      riscv_instr::P_CLIP,
      riscv_instr::P_CLIPU,
      riscv_instr::P_CLIPR,
      riscv_instr::P_CLIPUR: cmp_op_b = (op_a_i[Width-1] | clip_op_b[Width-1]) ? clip_op_b_n : clip_op_b;
      default: ;
    endcase
  end

  // Instantiate comparator
  assign cmp_result = $signed({cmp_op_a[Width-1] & cmp_signed, cmp_op_a}) <= $signed({cmp_op_b[Width-1] & cmp_signed, cmp_op_b});

  // --------------------
  // Result generation
  // --------------------
  always_comb begin
    unique casez (operator_i)
      riscv_instr::P_ABS: result_o = cmp_result ? -$signed(op_a_i) : op_a_i;
      riscv_instr::P_SLET,
      riscv_instr::P_SLETU: result_o = $unsigned(cmp_result);
      riscv_instr::P_MIN,
      riscv_instr::P_MINU: result_o = cmp_result ? op_a_i : op_b_i;
      riscv_instr::P_MAX,
      riscv_instr::P_MAXU:
        result_o = ~cmp_result ? op_a_i : op_b_i;
      riscv_instr::P_EXTHS: result_o = $signed(op_a_i[Width/2-1:0]);
      riscv_instr::P_EXTHZ: result_o = $unsigned(op_a_i[Width/2-1:0]);
      riscv_instr::P_EXTBS: result_o = $signed(op_a_i[7:0]);
      riscv_instr::P_EXTBZ: result_o = $unsigned(op_a_i[7:0]);
      riscv_instr::P_CLIP,
      riscv_instr::P_CLIPU,
      riscv_instr::P_CLIPR,
      riscv_instr::P_CLIPUR: result_o = cmp_result ? ((op_a_i[Width-1] | clip_op_b[Width-1]) ? clip_op_b_n : op_a_i) : (op_a_i[Width-1] ? op_a_i : clip_op_b);
      default: result_o = '0;
    endcase
  end

endmodule
