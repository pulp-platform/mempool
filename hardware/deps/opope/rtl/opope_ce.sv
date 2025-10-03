// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Danilo Cammarata <dcammarata@iis.ee.ethz.ch>

module opope_ce
  import fpnew_pkg::*;
  import opope_pkg::*;
#(
  parameter fpnew_pkg::fp_format_e   FpFormat    = fpnew_pkg::FP32              ,
  parameter int unsigned             NumPipeRegs = 4                            ,
  parameter fpnew_pkg::pipe_config_t PipeConfig  = fpnew_pkg::DISTRIBUTED       ,
  parameter type                     TagType     = logic                        ,
  parameter type                     AuxType     = logic                        ,
  parameter logic                    Stallable   = 1'b0                         ,
  localparam int unsigned            BITW        = fpnew_pkg::fp_width(FpFormat)
)(
  input  logic                               clk_i             ,
  input  logic                               rst_ni            ,
  input  logic                    [BITW-1:0] x_input_i         ,
  input  logic                    [BITW-1:0] w_input_i         ,
  input  logic                    [BITW-1:0] y_bias_i          ,
  input  logic                    [2:0]      fma_is_boxed_i    ,
  input  logic                    [1:0]      noncomp_is_boxed_i,
  input  fpnew_pkg::roundmode_e              stage1_rnd_i      ,
  input  fpnew_pkg::roundmode_e              stage2_rnd_i      ,
  input  fpnew_pkg::operation_e              op1_i             ,
  input  fpnew_pkg::operation_e              op2_i             ,
  input  fpu_fmt_e                           memory_fmt_i      ,
  input  fpu_fmt_e                           computing_fmt_i   ,
  input  logic                               same_fmt_i        , 
  input  logic                               op_mod_i          ,
  input  TagType                             tag_i             ,
  input  AuxType                             aux_i             ,
  input  logic                               in_valid_i        ,
  output logic                               in_ready_o        ,
  input  logic                               reg_enable_i      ,
  input  logic                               flush_i           ,
  output logic                    [BITW-1:0] z_output_o        ,
  output fpnew_pkg::status_t                 status_o          ,
  output logic                               extension_bit_o   ,
  output fpnew_pkg::classmask_e              class_mask_o      ,
  output logic                               is_class_o        ,
  output TagType                             tag_o             ,
  output AuxType                             aux_o             ,
  output logic                               out_valid_o       ,
  input  logic                               out_ready_i       ,
  output logic                               busy_o
);

  logic                       fma_clk_en;
  logic                       fma_clk;
  logic [2:0][BITW-1:0]       fma_operands;
  logic [2:0]                 fma_is_boxed_int;
  fpnew_pkg::roundmode_e      fma_rnd_int;
  logic                       fma_op_mod;
  TagType                     fma_input_tag;
  AuxType                     fma_input_aux;
  logic                       fma_in_valid;
  logic                       fma_in_ready;
  logic                       fma_reg_enable;
  logic                       fma_flush;
  logic [BITW-1:0]            fma_res;
  fpnew_pkg::status_t         fma_status;
  logic                       fma_extension_bit;
  TagType                     fma_output_tag;
  AuxType                     fma_output_aux;
  logic                       fma_out_valid;
  logic                       fma_out_ready;
  logic                       fma_busy;

  logic                                       sdotp_clk_en;
  logic                                       sdotp_clk;
  logic [2:0][BITW-1:0]                       sdotp_operands;
  logic [fpnew_pkg::NUM_FP_FORMATS-1:0][2:0]  sdotq_is_boxed_int;
  fpnew_pkg::roundmode_e                      sdotp_rnd_int;
  logic                                       sdotp_op_mod;
  TagType                                     sdotp_input_tag;
  AuxType                                     sdotp_input_aux;
  logic                                       sdotp_in_valid;
  logic                                       sdotp_in_ready;
  logic                                       sdotp_reg_enable;
  logic                                       sdotp_flush;
  logic [BITW-1:0]                            sdotp_res;
  fpnew_pkg::status_t                         sdotp_status;
  logic                                       sdotp_extension_bit;
  TagType                                     sdotp_output_tag;
  AuxType                                     sdotp_output_aux;
  logic                                       sdotp_out_valid;
  logic                                       sdotp_out_ready;
  logic                                       sdotp_busy;


  fpnew_pkg::fp_format_e  memory_fmt_fpnew; 
  fpnew_pkg::fp_format_e  computing_fmt_fpnew; 
  assign memory_fmt_fpnew = fpnew_pkg::fp_format_e'(memory_fmt_i);
  assign computing_fmt_fpnew = fpnew_pkg::fp_format_e'(computing_fmt_i);
/*******************************************************************************/
/* Assigning input signals to the FMA and to the SDOTP module                  */
/*******************************************************************************/
  assign fma_operands[0] = x_input_i;
  assign fma_operands[1] = w_input_i;
  assign fma_operands[2] = y_bias_i;

  assign fma_is_boxed_int = fma_is_boxed_i;
  assign fma_rnd_int      = stage1_rnd_i  ;
  assign fma_op_mod       = op_mod_i      ;
  assign fma_input_tag    = tag_i         ;
  assign fma_input_aux    = aux_i         ;
  assign fma_in_valid     = in_valid_i    ;
  assign fma_reg_enable   = reg_enable_i  ;
  assign fma_flush        = flush_i       ;
  assign fma_out_ready    = out_ready_i   ;

  assign sdotp_operands[0] = x_input_i;
  assign sdotp_operands[1] = w_input_i;
  assign sdotp_operands[2] = y_bias_i;
      
  assign sdotq_is_boxed_int = { {fpnew_pkg::NUM_FP_FORMATS{fma_is_boxed_i}} };
  assign sdotp_rnd_int      = roundmode_e'(fpnew_pkg::RNE);
  assign sdotp_op_mod       = op_mod_i      ;
  assign sdotp_input_tag    = tag_i         ;
  assign sdotp_input_aux    = aux_i         ;
  assign sdotp_in_valid     = in_valid_i    ;
  assign sdotp_reg_enable   = reg_enable_i  ;
  assign sdotp_flush        = flush_i       ;
  assign sdotp_out_ready    = out_ready_i   ;
/*******************************************************************************/
/* Depending on input format, we clock gate either FMA or SDOTP module.        */
/*******************************************************************************/
  always_comb begin : clock_gating_selector
    fma_clk_en            = 1'b0;
    sdotp_clk_en          = 1'b0;
      if (same_fmt_i) fma_clk_en = 1'b1;
      else sdotp_clk_en     = 1'b1;
  end : clock_gating_selector

  tc_clk_gating fma_clk_gating (
    .clk_i      ( clk_i      ),
    .en_i       ( fma_clk_en ),
    .test_en_i  ( '0         ),
    .clk_o      ( fma_clk    )    
  );

  tc_clk_gating sdotq_clk_gating (
    .clk_i      ( clk_i         ),
    .en_i       ( sdotp_clk_en  ),
    .test_en_i  ( '0            ),
    .clk_o      ( sdotp_clk     )   
  );

/*******************************************************************************/
/* Instantiation of FMA and SDOTP                                              */
/*******************************************************************************/


  logic [2:0][BITW-1:0]                       sdotp_operands_d, sdotp_operands_q;
  logic [fpnew_pkg::NUM_FP_FORMATS-1:0][2:0]  sdotp_is_boxed_int_d, sdotp_is_boxed_int_q;



  fpnew_pkg::roundmode_e                      sdotp_rnd_int_d, sdotp_rnd_int_q;
  fpnew_pkg::operation_e                      sdotp_op1_d, sdotp_op1_q;
  logic                                       sdotp_op_mod_d, sdotp_op_mod_q;
  fpnew_pkg::fp_format_e                      sdotp_computing_fmt_d, sdotp_computing_fmt_q;
  fpnew_pkg::fp_format_e                      sdotp_memory_fmt_d, sdotp_memory_fmt_q;

  TagType                                     sdotp_input_tag_d, sdotp_input_tag_q;
  AuxType                                     sdotp_input_aux_d, sdotp_input_aux_q;
  logic                                       sdotp_in_valid_d, sdotp_in_valid_q;

  always_comb begin
    sdotp_operands_d        = sdotp_operands;
    sdotp_is_boxed_int_d    = sdotq_is_boxed_int;
    sdotp_rnd_int_d         = sdotp_rnd_int;
    sdotp_op1_d             = op1_i;
    sdotp_op_mod_d          = sdotp_op_mod;
    sdotp_computing_fmt_d   = computing_fmt_fpnew;
    sdotp_memory_fmt_d      = memory_fmt_fpnew;
    sdotp_input_tag_d       = sdotp_input_tag;
    sdotp_input_aux_d       = sdotp_input_aux;
    sdotp_in_valid_d        = sdotp_in_valid;
  end

  logic [2:0][BITW-1:0]                       fma_operands_d, fma_operands_q;
  logic [2:0]                                 fma_is_boxed_int_d, fma_is_boxed_int_q;
  fpnew_pkg::roundmode_e                      fma_rnd_int_d, fma_rnd_int_q;
  fpnew_pkg::operation_e                      fma_op1_d, fma_op1_q;
  logic                                       fma_op_mod_d, fma_op_mod_q;
  TagType                                     fma_input_tag_d, fma_input_tag_q; 
  AuxType                                     fma_input_aux_d, fma_input_aux_q;
  logic                                       fma_in_valid_d, fma_in_valid_q;

  always_comb begin
    fma_operands_d        = fma_operands;
    fma_is_boxed_int_d    = fma_is_boxed_int;
    fma_rnd_int_d         = fma_rnd_int;
    fma_op1_d             = op1_i;
    fma_op_mod_d          = fma_op_mod;
    fma_input_tag_d       = fma_input_tag;
    fma_input_aux_d       = fma_input_aux;
    fma_in_valid_d        = fma_in_valid;
  end

  opope_sdotp_wrapper #(
    .LaneWidth        ( fpnew_pkg::fp_width(FpFormat) ), // Should be 32
    .FpFmtConfig      ( FpFmtConfig                   ),
    .NumPipeRegs      ( NumPipeRegs                   ),
    .PipeConfig       ( PipeConfig                    ),
    .Stallable        ( Stallable                     ) 
  ) i_sdotp (
    .clk_i            ( sdotp_clk           ), 
    .rst_ni           ( rst_ni              ),
    .sdotp_hart_id_i  ( '0                  ),
    .operands_i       ( sdotp_operands      ),
    .is_boxed_i       ( sdotq_is_boxed_int  ), 
    .rnd_mode_i       ( sdotp_rnd_int       ),
    .op_i             ( op1_i               ),    
    .op_mod_i         ( sdotp_op_mod        ),
    .src_fmt_i        ( computing_fmt_fpnew ),
    .dst_fmt_i        ( memory_fmt_fpnew    ),
    .tag_i            ( sdotp_input_tag     ),
    .mask_i           ( '0                  ),
    .aux_i            ( sdotp_input_aux     ),
    .in_valid_i       ( sdotp_in_valid      ),
    .in_ready_o       ( sdotp_in_ready      ),
    .reg_enable_i     ( sdotp_reg_enable    ), 
    .flush_i          ( sdotp_flush         ),
    .result_o         ( sdotp_res           ),
    .status_o         ( sdotp_status        ),
    .extension_bit_o  ( sdotp_extension_bit ),
    .tag_o            ( sdotp_output_tag    ),
    .mask_o           (                     ),
    .aux_o            ( sdotp_output_aux    ),
    .out_valid_o      ( sdotp_out_valid     ),
    .out_ready_i      ( sdotp_out_ready     ),
    .busy_o           ( sdotp_busy          )
  );



  opope_fma   #(
    .FpFormat    ( FpFormat    ),
    .NumPipeRegs ( NumPipeRegs ),
    .PipeConfig  ( PipeConfig  ),
    .Stallable   ( Stallable   )
  ) i_fma    (
    .clk_i           ( fma_clk           ),
    .rst_ni          ( rst_ni            ),
    .operands_i      ( fma_operands      ),
    .is_boxed_i      ( fma_is_boxed_int  ),
    .rnd_mode_i      ( fma_rnd_int       ),
    .op_i            ( op1_i             ),
    .op_mod_i        ( fma_op_mod        ),
    .tag_i           ( fma_input_tag     ),
    .aux_i           ( fma_input_aux     ),
    .in_valid_i      ( fma_in_valid      ),
    .in_ready_o      ( fma_in_ready      ),
    .reg_enable_i    ( fma_reg_enable    ),
    .flush_i         ( fma_flush         ),
    .result_o        ( fma_res           ),
    .status_o        ( fma_status        ),
    .extension_bit_o ( fma_extension_bit ),
    .tag_o           ( fma_output_tag    ),
    .aux_o           ( fma_output_aux     ),
    .out_valid_o     ( fma_out_valid      ),
    .out_ready_i     ( fma_out_ready     ),
    .busy_o          ( fma_busy          )
  );

  always_comb begin : output_selector
    in_ready_o      = '0;
    z_output_o      = '0;
    status_o        = '0;
    extension_bit_o = '0;
    class_mask_o    = fpnew_pkg::QNAN;
    is_class_o      = '0;
    tag_o           = '0;
    aux_o           = '0;
    out_valid_o     = '0;
    busy_o          = '0;

    if (same_fmt_i) begin: fma_selected
      in_ready_o      = fma_in_ready;
      z_output_o      = fma_res;
      status_o        = fma_status;
      extension_bit_o = fma_extension_bit;
      tag_o           = fma_output_tag;
      aux_o           = fma_output_aux;
      out_valid_o     = fma_out_valid;
      busy_o          = fma_busy;
    end else begin : sdotp_selected
      in_ready_o      = sdotp_in_ready;
      z_output_o      = sdotp_res;
      status_o        = sdotp_status;
      extension_bit_o = sdotp_extension_bit;
      tag_o           = sdotp_output_tag;
      aux_o           = sdotp_output_aux;
      out_valid_o     = sdotp_out_valid;
      busy_o          = sdotp_busy;
    end
  end : output_selector

endmodule: opope_ce
