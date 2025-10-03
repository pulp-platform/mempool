// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Danilo Cammarata <dcammarata@iis.ee.ethz.ch>
// Francesco Conti <f.conti@unibo.it>

module opope_tiler
  import opope_pkg::*;
  import hwpe_ctrl_package::*;
(
  input  logic              clk_i      ,
  input  logic              rst_ni     ,
  input  logic              clear_i    ,
  input  logic              setback_i  ,
  input  logic              start_cfg_i,
  input  ctrl_regfile_t     reg_file_i ,
  output logic              valid_o    ,
  output ctrl_regfile_t     reg_file_o
);

logic clk_en;
logic clk_int;
logic shift;
assign shift = (BITW==32 & reg_file_i.hwpe_params[MACFG][ 9: 7]==Float16) |
               (BITW==16 & reg_file_i.hwpe_params[MACFG][ 9: 7]==Float8 );

opope_config_t config_d, config_q;

always_ff @(posedge clk_i, negedge rst_ni) begin: clock_gate_enabler
  if (~rst_ni) begin
    clk_en <= 1'b0;
  end else begin
    if (clear_i || setback_i) begin
      clk_en <= 1'b0;
    end else if (start_cfg_i) begin
      clk_en <= 1'b1;
    end
  end
end

tc_clk_gating i_tiler_clockg (
  .clk_i      ( clk_i   ),
  .en_i       ( clk_en  ),
  .test_en_i  ( '0      ),
  .clk_o      ( clk_int )
);
  // typedef enum logic [2:0] { Float8=3'h0, Float16=3'h1, Float8Alt=3'h2, Float16Alt=3'h3, Float32=3'h4 } gemm_fmt_e;

assign config_d.x_addr          = reg_file_i.hwpe_params[X_ADDR];
assign config_d.w_addr          = reg_file_i.hwpe_params[W_ADDR];
assign config_d.z_addr          = reg_file_i.hwpe_params[Z_ADDR];
assign config_d.m_size          = reg_file_i.hwpe_params[MCFIG0][15: 0];
assign config_d.k_size          = reg_file_i.hwpe_params[MCFIG0][31:16];
assign config_d.n_size          = reg_file_i.hwpe_params[MCFIG1][15: 0] >> shift;
// assign config_d.gemm_ops        = gemm_op_e' (reg_file_i.hwpe_params[MACFG][12:10]);
assign config_d.gemm_ops        = gemm_op_e' (reg_file_i.hwpe_params[MACFG][12:10]);
assign config_d.gemm_memory_fmt     = gemm_fmt_e'(reg_file_i.hwpe_params[MACFG][ 9: 7]);    // Memory Format
assign config_d.gemm_computing_fmt  = gemm_fmt_e'(reg_file_i.hwpe_params[MACFG][ 19: 17]);  // Computing Format

logic k_m_valid_d, k_m_valid, k_m_ready, k_m_valid_q;
logic [31:0] k_m;


hwpe_ctrl_seq_mult #(
  .AW ( 16 ),
  .BW ( 16 )
) i_k_m (
  .clk_i    ( clk_i                         ),
  .rst_ni   ( rst_ni                        ),
  .clear_i  ( clear_i | setback_i           ),
  .start_i  ( start_cfg_i                   ),
  .a_i      ( config_d.m_size          ),
  .b_i      ( config_d.k_size          ),
  .invert_i ( 1'b0                          ),
  .valid_o  ( k_m_valid_d ),
  .ready_o  ( k_m_ready ),
  .prod_o   ( k_m         )
);

always_ff @(posedge clk_int or negedge rst_ni) begin
  if(~rst_ni)
    k_m_valid_q <= '0;
  else if(clear_i | setback_i)
    k_m_valid_q <= '0;
  else
    k_m_valid_q <= k_m_valid_d;
end
assign k_m_valid = ~k_m_valid_q & k_m_valid_d;


logic n_k_m_valid, n_k_m_ready;
logic [47:0] n_k_m;
hwpe_ctrl_seq_mult #(
  .AW ( 16 ),
  .BW ( 32 )
) i_n_m_k (
  .clk_i    ( clk_int                        ),
  .rst_ni   ( rst_ni                        ),
  .clear_i  ( clear_i | setback_i           ),
  .start_i  ( k_m_valid                   ),
  .a_i      ( config_d.n_size          ),
  .b_i      ( k_m),
  .invert_i ( 1'b0                          ),
  .valid_o  ( n_k_m_valid ),
  .ready_o  ( n_k_m_ready   ),
  .prod_o   ( n_k_m         )
);

assign config_d.stage_1_rnd_mode = config_d.gemm_ops == MATMUL ? RNE :
                                   config_d.gemm_ops == GEMM   ? RNE :
                                   config_d.gemm_ops == ADDMAX ? RNE :
                                   config_d.gemm_ops == ADDMIN ? RNE :
                                   config_d.gemm_ops == MULMAX ? RNE :
                                   config_d.gemm_ops == MULMIN ? RNE :
                                   config_d.gemm_ops == MAXMIN ? RTZ :
                                                                 RNE ;
assign config_d.stage_2_rnd_mode = config_d.gemm_ops == MATMUL ? RNE :
                                   config_d.gemm_ops == GEMM   ? RNE :
                                   config_d.gemm_ops == ADDMAX ? RTZ :
                                   config_d.gemm_ops == ADDMIN ? RNE :
                                   config_d.gemm_ops == MULMAX ? RTZ :
                                   config_d.gemm_ops == MULMIN ? RNE :
                                   config_d.gemm_ops == MAXMIN ? RNE :
                                                                 RTZ;
assign config_d.stage_1_op       = config_d.gemm_ops == MATMUL ? FPU_FMADD :
                                   config_d.gemm_ops == GEMM   ? FPU_FMADD :
                                   config_d.gemm_ops == ADDMAX ? FPU_ADD :
                                   config_d.gemm_ops == ADDMIN ? FPU_ADD :
                                   config_d.gemm_ops == MULMAX ? FPU_MUL :
                                   config_d.gemm_ops == MULMIN ? FPU_MUL :
                                   config_d.gemm_ops == MAXMIN ? FPU_MINMAX :
                                                                 FPU_MINMAX;
assign config_d.stage_2_op       = FPU_MINMAX;
assign config_d.memory_format     = config_d.gemm_memory_fmt == Float16    ? FPU_FP16 :
                                   config_d.gemm_memory_fmt == Float8     ? FPU_FP8 :
                                   config_d.gemm_memory_fmt == Float16Alt ? FPU_FP16ALT :
                                   config_d.gemm_memory_fmt == Float32    ? FPU_FP32 :
                                                                           FPU_FP8ALT;
assign config_d.computing_format = config_d.gemm_computing_fmt == Float16    ? FPU_FP16 :
                                   config_d.gemm_computing_fmt == Float8     ? FPU_FP8 :
                                   config_d.gemm_computing_fmt == Float16Alt ? FPU_FP16ALT :
                                   config_d.gemm_computing_fmt == Float32    ? FPU_FP32 :
                                                                            FPU_FP8ALT;

assign config_d.gemm_selection   = 1'b1;

assign config_d.k_m = k_m[31:0];
assign config_d.n_k_m = n_k_m[31:0];

// register configuration to avoid critical paths (maybe removable!)
always_ff @(posedge clk_int or negedge rst_ni) begin
  if(~rst_ni)
    config_q <= '0;
  else if (clear_i)
    config_q <= '0;
  else if(n_k_m_valid & n_k_m_ready)
    config_q <= config_d;
end

// generate output valid
always_ff @(posedge clk_int or negedge rst_ni) begin
  if(~rst_ni)
    valid_o <= '0;
  else if (clear_i | setback_i)
    valid_o <= '0;
  else if(n_k_m_ready)
    valid_o <= n_k_m_valid;
end

// re-encode in older O-POPE regfile map
assign reg_file_o.generic_params = '0;
assign reg_file_o.ext_data = '0;
assign reg_file_o.hwpe_params[REGFILE_N_MAX_IO_REGS-1:OPOPE_REGS] = '0;
assign reg_file_o.hwpe_params[      X_ADDR]        = config_d.x_addr; // do not register (these are straight from regfile)
assign reg_file_o.hwpe_params[      W_ADDR]        = config_d.w_addr; // do not register (these are straight from regfile)
assign reg_file_o.hwpe_params[      Z_ADDR]        = config_d.z_addr; // do not register (these are straight from regfile)
assign reg_file_o.hwpe_params[OP_SELECTION][31:29] = config_q.stage_1_rnd_mode;
assign reg_file_o.hwpe_params[OP_SELECTION][28:26] = config_q.stage_2_rnd_mode;
assign reg_file_o.hwpe_params[OP_SELECTION][25:21] = (config_q.memory_format != config_q.computing_format)? fpnew_pkg::operation_e'(fpnew_pkg::SDOTP) : FPU_FMADD;
// assign reg_file_o.hwpe_params[OP_SELECTION][25:21] = config_q.stage_1_op;
assign reg_file_o.hwpe_params[OP_SELECTION][20:16] = config_q.stage_2_op;
assign reg_file_o.hwpe_params[OP_SELECTION][15:13] = config_q.memory_format;
assign reg_file_o.hwpe_params[OP_SELECTION][12:10] = config_q.computing_format;
assign reg_file_o.hwpe_params[OP_SELECTION][ 9: 1] = '0;
assign reg_file_o.hwpe_params[OP_SELECTION][0]     = config_q.gemm_selection;

assign reg_file_o.hwpe_params[M_SIZE][15:0]        = config_q.m_size;
assign reg_file_o.hwpe_params[N_SIZE][15:0]        = config_q.n_size;
assign reg_file_o.hwpe_params[K_SIZE][15:0]        = config_q.k_size;
assign reg_file_o.hwpe_params[N_K_M][31:0]         = config_q.n_k_m;
assign reg_file_o.hwpe_params[K_M][31:0]           = config_q.k_m;
assign reg_file_o.hwpe_params[M_SIZE][31:16]       = 'b0;
assign reg_file_o.hwpe_params[N_SIZE][31:16]       = 'b0;
assign reg_file_o.hwpe_params[K_SIZE][31:16]       = 'b0;

endmodule: opope_tiler
