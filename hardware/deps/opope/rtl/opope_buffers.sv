// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Danilo Cammarata <dcammarata@iis.ee.ethz.ch>

module opope_buffers  
  import opope_pkg::*;
  import hwpe_stream_package::*;
#(
  parameter int unsigned DATA_WIDTH     = opope_pkg::DATAW,
  parameter int unsigned DEPTH          = 2
) (
  input  logic                         clk_i, 
  input  logic                         rst_ni,
  input  logic                         clear_i,
  
  // From/To Streamer 
  hwpe_stream_intf_stream.sink   x_stream_i,
  hwpe_stream_intf_stream.sink   w_stream_i,
  hwpe_stream_intf_stream.sink   y_stream_i,
  hwpe_stream_intf_stream.source z_stream_o,

  // Engine
  input  logic                         in_ready_i,
  output logic                         in_valid_o,
  output logic [DATA_WIDTH/DEPTH-1:0]  x_data_o  , 
  output logic [DATA_WIDTH/DEPTH-1:0]  w_data_o  ,

  input  logic                         y_ready_i,
  input  logic                         mask_y_i ,
  output logic                         y_valid_o,
  output logic [DATA_WIDTH      -1:0]  y_data_o , 

  output logic                         z_ready_o,
  input  logic                         mask_z_i ,
  input  logic                         z_valid_i,
  input  logic [DATA_WIDTH      -1:0]  z_data_i  
);

  localparam int unsigned X_FIFO_DEPTH = 0;
  localparam int unsigned W_FIFO_DEPTH = 0;
  localparam int unsigned Y_FIFO_DEPTH = 0;
  localparam int unsigned Z_FIFO_DEPTH = 0;

  hwpe_stream_intf_stream #( .DATA_WIDTH ( DATAW ) ) x_fifo      ( .clk( clk_i ) );
  hwpe_stream_intf_stream #( .DATA_WIDTH ( DATAW ) ) w_fifo      ( .clk( clk_i ) );
  hwpe_stream_intf_stream #( .DATA_WIDTH ( DATAW ) ) y_fifo      ( .clk( clk_i ) );
  hwpe_stream_intf_stream #( .DATA_WIDTH ( DATAW ) ) z_fifo      ( .clk( clk_i ) );
  hwpe_stream_intf_stream #( .DATA_WIDTH ( DATAW ) ) z_fifo_out  ( .clk( clk_i ) );

  if (X_FIFO_DEPTH > 0) begin : gen_x_fifo
    hwpe_stream_fifo #(
      .DATA_WIDTH     ( DATAW         ),
      .FIFO_DEPTH     ( X_FIFO_DEPTH  )
    ) i_x_fifo (
      .clk_i          ( clk_i         ),
      .rst_ni         ( rst_ni        ),
      .clear_i        ( clear_i       ),
      .flags_o        (               ),
      .push_i         ( x_stream_i    ),
      .pop_o          ( x_fifo        )
    );
  end else begin : no_x_fifo
      hwpe_stream_assign i_no_x_fifo (.push_i(x_stream_i), .pop_o(x_fifo));
  end

  if (W_FIFO_DEPTH > 0) begin : gen_w_fifo
    hwpe_stream_fifo #(
      .DATA_WIDTH     ( DATAW         ),
      .FIFO_DEPTH     ( W_FIFO_DEPTH  )
    ) i_w_fifo (
      .clk_i          ( clk_i         ),
      .rst_ni         ( rst_ni        ),
      .clear_i        ( clear_i       ),
      .flags_o        (               ),
      .push_i         ( w_stream_i    ),
      .pop_o          ( w_fifo        )
    );
  end else begin : no_w_fifo
      hwpe_stream_assign i_no_w_fifo (.push_i(w_stream_i), .pop_o(w_fifo));
  end

  if (Y_FIFO_DEPTH > 0) begin : gen_y_fifo
    hwpe_stream_fifo #(
      .DATA_WIDTH     ( DATAW         ),
      .FIFO_DEPTH     ( Y_FIFO_DEPTH  )
    ) i_y_fifo (
      .clk_i          ( clk_i         ),
      .rst_ni         ( rst_ni        ),
      .clear_i        ( clear_i       ),
      .flags_o        (               ),
      .push_i         ( y_stream_i    ),
      .pop_o          ( y_fifo        )
    );
  end else begin : no_y_fifo
      hwpe_stream_assign i_no_y_fifo (.push_i(y_stream_i), .pop_o(y_fifo));
  end

  if (Z_FIFO_DEPTH > 0) begin : gen_z_fifo
    hwpe_stream_fifo #(
      .DATA_WIDTH     ( DATAW         ),
      .FIFO_DEPTH     ( Z_FIFO_DEPTH  )
    ) i_z_fifo (
      .clk_i          ( clk_i         ),
      .rst_ni         ( rst_ni        ),
      .clear_i        ( clear_i       ),
      .flags_o        (               ),
      .push_i         ( z_fifo        ),
      .pop_o          ( z_fifo_out    )
    );
  end else begin : no_z_fifo
    hwpe_stream_assign i_no_z_fifo (.push_i(z_fifo), .pop_o(z_fifo_out));
  end

  // Y stream
  logic y_ready_d,y_ready_q;
  assign y_ready_d    = y_ready_i &~ mask_y_i ? 1'b1 :
                        y_fifo.valid          ? 1'b0 : y_ready_q;
                        
  assign y_fifo.ready = y_ready_q;
  assign y_valid_o    = y_fifo.valid & y_ready_q;
  assign y_data_o     = y_fifo.data      ;

  // Z stream
  assign z_fifo.data  = z_data_i         ;
  assign z_fifo.valid = z_valid_i        ;
  assign z_fifo.strb  = {{DATAW/8{1'b1}}};
  assign z_ready_o    = z_fifo.ready     ;

  assign z_stream_o.strb  = z_fifo_out.strb             ;
  assign z_stream_o.valid = z_fifo_out.valid &~ mask_z_i;
  assign z_stream_o.data  = z_fifo_out.data             ;
  assign z_fifo_out.ready = z_stream_o.ready &~ mask_z_i;

// X and W stream
  typedef enum logic [3:0] {
    BUFFER_IDLE,
    BUFFER_X_VALID,
    BUFFER_W_VALID,
    BUFFER_VALID,
    BUFFER_LAST_VALID
  } buffer_state_e;
  buffer_state_e buffer_current, buffer_next;

  logic [DEPTH-1:0][DATA_WIDTH/DEPTH-1:0] x_reg_d, x_reg_q;
  logic [DEPTH-1:0][DATA_WIDTH/DEPTH-1:0] w_reg_d, w_reg_q;
  logic [DEPTH-1:0]                       ready_cnt_d, ready_cnt_q; 
  logic change_x_data,change_w_data;

  always_comb begin : buffer_fsm
    case (buffer_current)
    // -----------------------------------------------------------------------------------------------------------
      BUFFER_IDLE      : buffer_next = x_fifo.valid & w_fifo.valid      ? BUFFER_VALID      :
                                       x_fifo.valid                     ? BUFFER_X_VALID    :
                                       w_fifo.valid                     ? BUFFER_W_VALID    : buffer_current;
    // -----------------------------------------------------------------------------------------------------------
      BUFFER_X_VALID   : buffer_next = w_fifo.valid                     ? BUFFER_VALID      : buffer_current;
    // -----------------------------------------------------------------------------------------------------------
      BUFFER_W_VALID   : buffer_next = x_fifo.valid                     ? BUFFER_VALID      : buffer_current;
    // -----------------------------------------------------------------------------------------------------------
      BUFFER_VALID     : buffer_next = (ready_cnt_d == DEPTH*DEPTH-1)   ? BUFFER_LAST_VALID : buffer_current;
    // -----------------------------------------------------------------------------------------------------------
      BUFFER_LAST_VALID: buffer_next = x_fifo.valid & w_fifo.valid      ? BUFFER_VALID      :
                                       x_fifo.valid                     ? BUFFER_X_VALID    :
                                       w_fifo.valid                     ? BUFFER_W_VALID    : BUFFER_IDLE   ;
    // -----------------------------------------------------------------------------------------------------------
      default          : buffer_next = BUFFER_IDLE;
    // -----------------------------------------------------------------------------------------------------------
    endcase
    
    if (clear_i) buffer_next = BUFFER_IDLE;
  end
  
  always_comb begin : buffer_values
    ready_cnt_d  = ready_cnt_q;
    in_valid_o   = 1'b0;
    x_fifo.ready = 1'b0;
    w_fifo.ready = 1'b0;
 
    case (buffer_current)
      BUFFER_IDLE      : begin
       x_fifo.ready = 1'b1;
       w_fifo.ready = 1'b1;
       ready_cnt_d  = '0;
      end
      BUFFER_X_VALID   : begin
       w_fifo.ready = 1'b1;
      end
      BUFFER_W_VALID   : begin
       x_fifo.ready = 1'b1;
      end
      BUFFER_VALID     : begin
        in_valid_o  = 1'b1;
        ready_cnt_d = ready_cnt_q + in_ready_i;
      end 
      BUFFER_LAST_VALID: begin
       in_valid_o   = 1'b1;
       x_fifo.ready = 1'b1;
       w_fifo.ready = 1'b1;
       ready_cnt_d  = '0;
      end 
      default: ready_cnt_d = '0;
    endcase    
  end

  always_comb begin : x_w_data
    change_x_data = x_fifo.valid & x_fifo.ready;
    change_w_data = w_fifo.valid & w_fifo.ready;
    for(int ii=0; ii< DATA_WIDTH/BITW; ii++) begin
      x_reg_d[ii%DEPTH][ii/DEPTH*BITW +: BITW]  = clear_i       ? '0 :
                                                  change_x_data ? x_fifo.data[ii*BITW +: BITW] : x_reg_q[ii%DEPTH][ii/DEPTH*BITW +: BITW]; 
      w_reg_d[ii%DEPTH][ii/DEPTH*BITW +: BITW]  = clear_i       ? '0 :
                                                  change_w_data ? w_fifo.data[ii*BITW +: BITW] : w_reg_q[ii%DEPTH][ii/DEPTH*BITW +: BITW];
    end
    w_data_o = w_reg_q[ready_cnt_q[$clog2(DEPTH) - 1:0]];
    x_data_o = x_reg_q[ready_cnt_q[DEPTH-1 : $clog2(DEPTH)]];
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin 
    if (~rst_ni) begin
      y_ready_q      <= '0;
      buffer_current <= BUFFER_IDLE;
      ready_cnt_q    <= '0;
      w_reg_q        <= '0;
      x_reg_q        <= '0;
    end else begin 
      y_ready_q      <= y_ready_d  ;
      buffer_current <= buffer_next;
      ready_cnt_q    <= ready_cnt_d;
      w_reg_q        <= w_reg_d    ;
      x_reg_q        <= x_reg_d    ;
    end
  end

endmodule: opope_buffers