/// FPU Synthesis Wrapper
module snitch_fpu import snitch_pkg::*; (
  input logic                               clk_i,
  input logic                               rst_ni,
  // Input signals
  input logic [31:0]                        hart_id_i,
  input logic [2:0][FLEN-1:0]               operands_i,
  input fpnew_pkg::roundmode_e              rnd_mode_i,
  input fpnew_pkg::operation_e              op_i,
  input logic                               op_mod_i,
  input fpnew_pkg::fp_format_e              src_fmt_i,
  input fpnew_pkg::fp_format_e              dst_fmt_i,
  input fpnew_pkg::int_format_e             int_fmt_i,
  input logic                               vectorial_op_i,
  input logic [5:0]                         tag_i,
  // Input Handshake
  input  logic                              in_valid_i,
  output logic                              in_ready_o,
  // Output signals
  output logic [FLEN-1:0]                   result_o,
  output logic [4:0]                        status_o,
  output logic [5:0]                        tag_o,
  // Output handshake
  output logic                              out_valid_o,
  input  logic                              out_ready_i
);

  typedef struct packed {
    logic [2:0][FLEN-1:0]    operands;
    fpnew_pkg::roundmode_e   rnd_mode;
    fpnew_pkg::operation_e   op;
    logic                    op_mod;
    fpnew_pkg::fp_format_e   src_fmt;
    fpnew_pkg::fp_format_e   dst_fmt;
    fpnew_pkg::int_format_e  int_fmt;
    logic                    vectorial_op;
    logic [5:0]              tag;
  } fpu_in_t;

  typedef struct packed {
    logic [FLEN-1:0] result;
    logic [4:0]      status;
    logic [5:0]      tag;
  } fpu_out_t;

  fpu_in_t fpu_in;
  fpu_out_t fpu_out;

  assign fpu_in = '{
    operands: operands_i,
    rnd_mode: rnd_mode_i,
    op: op_i,
    op_mod: op_mod_i,
    src_fmt: src_fmt_i,
    dst_fmt: dst_fmt_i,
    int_fmt: int_fmt_i,
    vectorial_op: vectorial_op_i,
    tag: tag_i
  };

// If you want to use Stochastic Rounding, propagate the hart_id to the FPU (each FPU needs a different hart_id) and set EnableRSR to 1'b1s
  fpnew_top #(
    // FPU configuration
    .Features                   ( snitch_pkg::FPU_FEATURES       ),
    .Implementation             ( snitch_pkg::FPU_IMPLEMENTATION ),
    .TagType                    ( logic[5:0]                     ),
    .StochasticRndImplementation( snitch_pkg::FPU_RSR            ),
    .PulpDivsqrt                ( 1'b1                           ),
    .ComplexDotp                ( 1'b1                           )
  ) i_fpu (
    .clk_i                                    ,
    .rst_ni                                   ,
    .hart_id_i       ( hart_id_i             ),
    .operands_i      ( fpu_in.operands       ),
    .rnd_mode_i      ( fpu_in.rnd_mode       ),
    .op_i            ( fpu_in.op             ),
    .op_mod_i        ( fpu_in.op_mod         ),
    .src_fmt_i       ( fpu_in.src_fmt        ),
    .dst_fmt_i       ( fpu_in.dst_fmt        ),
    .int_fmt_i       ( fpu_in.int_fmt        ),
    .vectorial_op_i  ( fpu_in.vectorial_op   ),
    .tag_i           ( fpu_in.tag            ),
    .simd_mask_i     ( '1                    ),
    .in_valid_i      ( in_valid_i            ),
    .in_ready_o      ( in_ready_o            ),
    .flush_i         ( 1'b0                  ),
    .result_o        ( fpu_out.result        ),
    .status_o        ( fpu_out.status        ),
    .tag_o           ( fpu_out.tag           ),
    .out_valid_o     ( out_valid_o           ),
    .out_ready_i     ( out_ready_i           ),
    .busy_o          (                       )
  );

  assign result_o = fpu_out.result;
  assign status_o = fpu_out.status;
  assign tag_o = fpu_out.tag;

endmodule
