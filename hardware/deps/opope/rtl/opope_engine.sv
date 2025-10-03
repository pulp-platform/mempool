// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Danilo Cammarata <dcammarata@iis.ee.ethz.ch>


module opope_engine
  import fpnew_pkg::*;
  import opope_pkg::*;
#(
 parameter  fp_format_e   FpFormat    = fpnew_pkg::FP32              ,
 parameter  int unsigned  Height      = 4                            , // Number of PEs per row
 parameter  int unsigned  Width       = 8                            , // Number of parallel index
 parameter  int unsigned  NumPipeRegs = 3                            ,
 parameter  pipe_config_t PipeConfig  = DISTRIBUTED                  ,
 parameter  type          TagType     = logic                        ,
 parameter  type          AuxType     = logic                        ,
 localparam int unsigned  BITW        = fpnew_pkg::fp_width(FpFormat), // Number of bits for the given format
 parameter logic          Stallable   = 1'b1                         ,
 localparam int unsigned  MUX_SH_n    = 1
)(
  input  logic                          clk_i              ,
  input  logic                          rst_ni             ,
  input  logic                          clk_en_i           ,
  input  logic [ Height-1:0][BITW-1:0]  x_input_i          , // Column of inputs
  input  logic [  Width-1:0][BITW-1:0]  w_input_i          , // Row of weights
  input  logic [2*Width-1:0][BITW-1:0]  y_bias_i           , // Row of biases
  output logic [2*Width-1:0][BITW-1:0]  z_output_o         , // Row of outputs

  input  cntrl_engine_t                 cntrl_engine_i  // This include the mode (idle, load, compute, read) and the row_index
);


  logic [Height-1:0][Width-1:0][2*BITW-1:0] reg_out_data;

  logic [Height-1:0][Width-1:0][BITW-1:0] engine_to_reg_output;

  logic ce_clk;
  logic [Height-1:0][Width-1:0]             acc_in_valid;
  logic [Height-1:0][Width-1:0][2*BITW-1:0] acc_in_data;
  logic [$clog2(REG_PER_CE)-1:0]            acc_write_index;
  logic [$clog2(REG_PER_CE)-1:0]            acc_read_index ;

  /*---------------------------------------------------------------*/
  /* |                  Accumulator Read and Write               | */
  /*---------------------------------------------------------------*/
  

  always_comb begin : acc_rd_wr
    
    // Multiplexer-based write-in and read-out 
    if(MUX_SH_n) begin
      for (int col_index = 0; col_index < Width; col_index++) begin
        
        // Write logic
        for (int row_index = 0; row_index < Height; row_index++) begin
          if (cntrl_engine_i.acc_input_selector) begin // Load from the engine
            acc_in_valid[row_index][col_index] = 1'b1;
            acc_in_data [row_index][col_index] = {engine_to_reg_output[row_index][col_index],engine_to_reg_output[row_index][col_index]};
            acc_write_index                    = cntrl_engine_i.reg_write_to_engine;
          end else begin // Load from external
            acc_in_valid[row_index][col_index] = cntrl_engine_i.y_in_valid && (row_index == cntrl_engine_i.y_write_row_index) && cntrl_engine_i.external_loading;
            acc_in_data [row_index][col_index] = {y_bias_i[2*col_index+1],y_bias_i[2*col_index]};
            acc_write_index                    = cntrl_engine_i.y_write_reg_index;
          end
        end

        // Read logic
        z_output_o[2*col_index  ] = reg_out_data[cntrl_engine_i.z_read_row_index][col_index][  BITW-1:0   ];
        z_output_o[2*col_index+1] = reg_out_data[cntrl_engine_i.z_read_row_index][col_index][2*BITW-1:BITW];
      end
      acc_read_index = cntrl_engine_i.z_read_reg_index;
    end

    // Shift-based write-in and read-out 
    else begin
      acc_read_index = cntrl_engine_i.z_read_reg_index;
      for (int col_index = 0; col_index < Width; col_index++) begin        
        
        // Write logic
        for (int row_index = 0; row_index < Height; row_index++) begin
          if (cntrl_engine_i.acc_input_selector) begin // Load from the engine
            acc_in_valid[row_index][col_index] = 1'b1;
            acc_in_data [row_index][col_index] = {engine_to_reg_output[row_index][col_index],engine_to_reg_output[row_index][col_index]};
            acc_write_index                    = cntrl_engine_i.reg_write_to_engine;
          end else begin // Load from external
            acc_in_valid[row_index][col_index] = (cntrl_engine_i.y_in_valid && cntrl_engine_i.external_loading) | cntrl_engine_i.shift_acc;
            acc_in_data [row_index][col_index] = row_index != Height-1 ? reg_out_data[row_index + 1][col_index]
                                                                       : {y_bias_i[2*col_index+1],y_bias_i[2*col_index]};
            acc_write_index  = cntrl_engine_i.shift_acc &~ cntrl_engine_i.y_in_valid ? cntrl_engine_i.z_read_reg_index  
                                                                                     : cntrl_engine_i.y_write_reg_index;
            acc_read_index   = cntrl_engine_i.shift_acc &  cntrl_engine_i.y_in_valid ? cntrl_engine_i.y_write_reg_index 
                                                                                     : cntrl_engine_i.z_read_reg_index ;
          end
        end

        // Read logic
        z_output_o[2*col_index  ] = reg_out_data[0][col_index][  BITW-1:0   ];
        z_output_o[2*col_index+1] = reg_out_data[0][col_index][2*BITW-1:BITW];
      end
    end
  end

  /*---------------------------------------------------------------*/
  /* |                    Accumulation Registers                 | */
  /*---------------------------------------------------------------*/
  
  generate
    for (genvar row_index = 0; row_index < Height; row_index++) begin: accumulation_reg_row
      for (genvar col_index = 0; col_index < Width; col_index++) begin: accumulation_reg_col
        opope_accumulator #(
          .DATA_WIDTH ( BITW          ),
          .DEPTH      ( REG_PER_CE    )
        ) i_accumulator (
          .clk_i              ( clk_i                                                ),
          .rst_ni             ( rst_ni                                               ),
          .flush_i            ( 1'b0                                                 ),
          .iteration_change_i ( 1'b0                                                 ),     
          .input_i            ( acc_in_data[row_index][col_index]                    ),         
          .write_en_i         ( acc_in_valid[row_index][col_index]                   ),
          .write_index_i      ( acc_write_index                                      ),
          .external_loading   ( cntrl_engine_i.external_loading                      ),
          .read_index_i       ( acc_read_index                                       ),
          .output_o           ( reg_out_data[row_index][col_index]                   )        
        );
      end
    end
  endgenerate

  /*---------------------------------------------------------------*/
  /* |                      Computing Elements                   | */
  /*---------------------------------------------------------------*/

  // ******** Compute Engine 2D array ********  
  tc_clk_gating ce_clock_gating (
    .clk_i      ( clk_i     ),
    .en_i       ( clk_en_i  ),
    .test_en_i  ( '0        ),
    .clk_o      ( ce_clk    )    
  );

  logic [Height-1:0][Width-1:0][2:0][BITW-1:0] ce_operands;
  logic [Height-1:0][Width-1:0][BITW-1:0]      acc_operand;
  logic same_fmt;

  always_comb begin 
    same_fmt         = (cntrl_engine_i.memory_format == cntrl_engine_i.computing_format)? 1'b1 : 1'b0;
    for (int row_index = 0; row_index < Height; row_index++) begin 
      for (int col_index = 0; col_index < Width; col_index++) begin 
        acc_operand[row_index][col_index]    = reg_out_data[row_index][col_index][cntrl_engine_i.z_read_reg_index[0]*BITW +: BITW];
        ce_operands[row_index][col_index][0] = x_input_i[row_index];
        ce_operands[row_index][col_index][1] = w_input_i[col_index];
        ce_operands[row_index][col_index][2] = (cntrl_engine_i.y_bias_selector) ? acc_operand[row_index][col_index]: engine_to_reg_output[row_index][col_index] ;
      end
    end
  end
  generate
    for(genvar row_index = 0; row_index < Height; row_index++) begin: ce_row
      for (genvar col_index = 0; col_index < Width; col_index++) begin: ce_col
      opope_ce   #(
        .FpFormat    ( FpFormat    ),
        .NumPipeRegs ( NumPipeRegs ),
        .PipeConfig  ( PipeConfig  ),
        .Stallable   ( Stallable   )
      ) i_ce (
        .clk_i              ( ce_clk                                          ),
        .rst_ni             ( rst_ni                                          ),
        .x_input_i          ( ce_operands[row_index][col_index][0]            ),
        .w_input_i          ( ce_operands[row_index][col_index][1]            ),
        .y_bias_i           ( ce_operands[row_index][col_index][2]            ),
        .fma_is_boxed_i     ( cntrl_engine_i.fma_is_boxed                     ),
        .noncomp_is_boxed_i ( 2'b11                                           ),
        .stage1_rnd_i       ( cntrl_engine_i.stage1_rnd                       ),
        .stage2_rnd_i       ( cntrl_engine_i.stage2_rnd                       ),
        .op1_i              ( cntrl_engine_i.op1                              ),
        .op2_i              ( cntrl_engine_i.op2                              ),
        .memory_fmt_i       ( cntrl_engine_i.memory_format                    ),
        .computing_fmt_i    ( cntrl_engine_i.computing_format                 ),
        .same_fmt_i         ( same_fmt                                        ),
        .op_mod_i           ( cntrl_engine_i.op_mod                           ),
        .tag_i              ( 1'b0                                            ),
        .aux_i              ( 1'b0                                            ),
        .in_valid_i         ( cntrl_engine_i.in_valid & cntrl_engine_i.in_ready), 
        .in_ready_o         (                                                 ),
        .reg_enable_i       ( cntrl_engine_i.reg_enable                       ),
        .flush_i            ( 1'b0                                            ),
        .z_output_o         ( engine_to_reg_output[row_index][col_index]      ),
        .status_o           (                                                 ), // Not used 
        .extension_bit_o    (                                                 ), // Not used
        .class_mask_o       (                                                 ), // Not used
        .is_class_o         (                                                 ), // Not used
        .tag_o              (                                                 ), // Not used
        .aux_o              (                                                 ), // Not used
        .out_valid_o        (                                                 ),
        .out_ready_i        ( 1'b1                                            ),
        .busy_o             (                                                 )  // Not used
      );
      end
    end
  endgenerate


endmodule 