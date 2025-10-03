// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Danilo Cammarata <dcammarata@iis.ee.ethz.ch>
//


module opope_ctrl
  import opope_pkg::*;
  import hwpe_ctrl_package::*;
#(
  parameter  int unsigned N_CORES       = 8            ,
  parameter  int unsigned IO_REGS       = OPOPE_REGS ,
  parameter  int unsigned ID_WIDTH      = 8            ,
  parameter  int unsigned N_CONTEXT     = 2            ,
  parameter  int unsigned Height        = 4            ,
  parameter  int unsigned Width         = 8            
)(
  input  logic                    clk_i             ,
  input  logic                    rst_ni            ,
  output logic                    busy_o            ,
  output logic                    clear_o           ,
  output logic [N_CORES-1:0][1:0] evt_o             ,
  input  logic                    start_cfg_i       ,
  output logic                    cfg_complete_o    ,
  // Control signals for the state machine
  output cntrl_engine_t           cntrl_engine_o    ,
  
  // Priority enforcer
  output logic                 mask_y_o,
  output logic                 mask_z_o,
  
  // Memory Scheduler
  input  flgs_streamer_t        flgs_streamer_i  ,
  output cntrl_streamer_t       cntrl_streamer_o,
  
  // Buffers
  input  logic       in_valid_i         ,
  input  logic       y_in_valid_i       ,
  input  logic       out_ready_i        ,
  output logic       y_ready_o,  
  output logic       out_valid_o        ,
  output logic       in_ready_o         , 
  output logic       ce_clk_en_o        ,
  
  // Peripheral slave port
  hwpe_ctrl_intf_periph.slave     periph
);
  
  // Main controller signals
  typedef enum logic [3:0] {
    OPOPE_LATCH_RST,
    OPOPE_IDLE,
    OPOPE_LOAD_X,
    OPOPE_LOAD_W,
    OPOPE_LOAD_Y,
    OPOPE_COMPUTING, 
    OPOPE_FINISHED
  } opope_ctrl_state_e;
  opope_ctrl_state_e current, next;
  
  logic clear, latch_clear;
  logic tiler_setback, tiler_valid;
  logic slave_start;
  logic change_state;
  logic last_iteration_d,last_iteration_q;
  
  hwpe_ctrl_package::ctrl_regfile_t reg_file_d, reg_file_q;
  hwpe_ctrl_package::ctrl_slave_t   cntrl_slave;
  hwpe_ctrl_package::flags_slave_t  flgs_slave;

  // Stremear controller signals
  localparam int unsigned LoadCycles = ARRAY_HEIGHT*ARRAY_WIDTH*REG_PER_CE*BITW/DATAW;
  
  typedef enum logic [1:0] {
    PRIORITY_X,
    PRIORITY_W,
    PRIORITY_YZ
  } opope_priority_level_e;

  typedef enum logic [2:0] {
    STREAMER_Y,
    STREAMER_XWY,
    STREAMER_XWM,
    STREAMER_XWZ,
    STREAMER_Z
  } opope_priority_state_e;

  opope_priority_level_e priority_level;
  opope_priority_state_e streamer_current,streamer_next;

  cntrl_scheduler_t cntrl_scheduler;

  logic streamer_change_state;
  logic grant;
  logic done_d,done_q;
  logic start_computing,finished;
  logic x_granted;
  logic w_granted;
  logic y_granted;

  logic[$clog2(LoadCycles)-1:0] y_counter_d,y_counter_q;
  logic[$clog2(LoadCycles)-1:0] extra_d,extra_q;
  logic[1:0] priority_counter_d,priority_counter_q;
  
  // Memory scheduler
  logic [31:0] total_len_x_w;
  logic [31:0] total_len_y_z;

  // Engine
  typedef enum logic [2:0] {
    ACC_IDLE,
    ACC_Y_READ,
    ACC_LOAD_ENGINE,
    ACC_Y_READ_ENGINE_RUNNING,
    ACC_ENGINE_RUNNING,
    ACC_Z_RELOAD_Y_ENGINE,
    ACC_Z_RELOAD,
    ACC_Z_STORE
  } acc_state_e;

  acc_state_e acc_state_current, acc_state_next;
  logic prefetched_d, prefetched_q;
  logic [31:0] inner_loop_counter_q, inner_loop_counter_d;

  logic [$clog2(REG_PER_CE)-1:0] y_write_reg_index_q, y_write_reg_index_d;
  logic [$clog2(Height)-1:0] y_write_row_index_q, y_write_row_index_d;

  logic [$clog2(REG_PER_CE)-1:0] z_read_reg_index_q, z_read_reg_index_d;
  logic [$clog2(Height)-1:0] z_read_row_index_q, z_read_row_index_d;

  logic [$clog2(REG_PER_CE)-1:0] reg_write_to_engine_q, reg_write_to_engine_d;  
  logic acc_change_state; 
  logic y_bias_selector; 
  logic acc_input_selector;
  logic external_loading;
  logic acc_done_d,acc_done_q;
  logic ce_enable;
  logic shift_acc;


  /*---------------------------------------------------------------------------------------------*/
  /*                                   Control slave interface                                   */
  /*---------------------------------------------------------------------------------------------*/

  hwpe_ctrl_slave  #(
    .REGFILE_SCM    ( 0            ),
    .N_CORES        ( N_CORES      ),
    .N_CONTEXT      ( N_CONTEXT    ),
    .N_IO_REGS      ( OPOPE_REGS ),
    .N_GENERIC_REGS ( 6            ),
    .ID_WIDTH       ( ID_WIDTH     )
  ) i_slave         (
    .clk_i          ( clk_i        ),
    .rst_ni         ( rst_ni       ),
    .clear_o        ( clear        ),
    .cfg            ( periph       ),
    .ctrl_i         ( cntrl_slave  ),
    .flags_o        ( flgs_slave   ),
    .reg_file       ( reg_file_d   )
  );

  opope_tiler  i_cfg_tiler (
    .clk_i       ( clk_i         ),
    .rst_ni      ( rst_ni        ),
    .clear_i     ( clear         ),
    .setback_i   ( tiler_setback ),
    .start_cfg_i ( start_cfg_i   ),
    .reg_file_i  ( reg_file_d    ),
    .valid_o     ( tiler_valid   ),
    .reg_file_o  ( reg_file_q    )
  );

  /*---------------------------------------------------------------------------------------------*/
  /*                                       Register island                                       */
  /*---------------------------------------------------------------------------------------------*/

  // State register
  always_ff @(posedge clk_i or negedge rst_ni) begin : state_register
    if(~rst_ni) begin
       current <= OPOPE_LATCH_RST;
    end else begin
      current <= next;
    end
  end

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni) begin
      slave_start <= 1'b0;
    end else begin
      if (clear || tiler_setback)
        slave_start <= 1'b0;
      else if (flgs_slave.start)
        slave_start <= 1'b1;
    end
  end

  /*---------------------------------------------------------------------------------------------*/
  /*                                   Register file assignment                                  */
  /*---------------------------------------------------------------------------------------------*/

  assign cntrl_engine_o.fma_is_boxed = 3'b111;
  assign cntrl_engine_o.noncomp_is_boxed = 2'b11;
  assign cntrl_engine_o.op_mod = 1'b0;
  assign cntrl_engine_o.stage1_rnd = fpnew_pkg::roundmode_e'(reg_file_q.hwpe_params[OP_SELECTION][31:29]);
  assign cntrl_engine_o.stage2_rnd = fpnew_pkg::roundmode_e'(reg_file_q.hwpe_params[OP_SELECTION][28:26]);
  assign cntrl_engine_o.op1 = fpnew_pkg::operation_e'(reg_file_q.hwpe_params[OP_SELECTION][25:21]);
  assign cntrl_engine_o.op2 = fpnew_pkg::operation_e'(reg_file_q.hwpe_params[OP_SELECTION][20:16]);
  assign cntrl_engine_o.memory_format = opope_pkg::fpu_fmt_e'(reg_file_q.hwpe_params[OP_SELECTION][15:13]);
  assign cntrl_engine_o.inner_loop_count = (reg_file_q.hwpe_params[N_SIZE][15:0]) * W_REGBUFFER_DEPTH * X_REGBUFFER_DEPTH;
  assign cntrl_engine_o.computing_format = opope_pkg::fpu_fmt_e'(reg_file_q.hwpe_params[OP_SELECTION][12:10]);
  assign cntrl_engine_o.mode =  cntrl_engine_mode_e'(IDLE);
  assign cntrl_engine_o.iteration_change    = 1'b0;
  assign cntrl_engine_o.y_write_reg_index   = y_write_reg_index_q;
  assign cntrl_engine_o.y_write_row_index   = y_write_row_index_q;
  assign cntrl_engine_o.z_read_reg_index    = z_read_reg_index_q ;
  assign cntrl_engine_o.z_read_row_index    = z_read_row_index_q ;
  assign cntrl_engine_o.reg_write_to_engine = reg_write_to_engine_q;
  assign cntrl_engine_o.y_bias_selector     = y_bias_selector    ;
  assign cntrl_engine_o.acc_input_selector  = acc_input_selector ;
  assign cntrl_engine_o.external_loading    = external_loading   ;
  assign cntrl_engine_o.in_valid            = in_valid_i  ;
  assign cntrl_engine_o.y_in_valid          = y_in_valid_i;
  assign cntrl_engine_o.in_ready            = in_ready_o;
  assign cntrl_engine_o.reg_enable          = ce_enable;
  assign cntrl_engine_o.shift_acc           = shift_acc;
  
  /*---------------------------------------------------------------------------------------------*/
  /*                                        Controller FSM                                       */
  /*---------------------------------------------------------------------------------------------*/
  
  always_comb begin : controller_fsm
    next = current;

    case (current)
      OPOPE_LATCH_RST: next = OPOPE_IDLE;
      OPOPE_IDLE     : next = change_state  ? OPOPE_LOAD_W    : current;
      OPOPE_LOAD_W   : next = OPOPE_LOAD_X;
      OPOPE_LOAD_X   : next = OPOPE_LOAD_Y;
      OPOPE_LOAD_Y   : next = change_state  ? OPOPE_COMPUTING : current;
      OPOPE_COMPUTING: next = change_state  ? OPOPE_FINISHED  : current;
      OPOPE_FINISHED : next = OPOPE_IDLE;
    endcase
    
    if (clear)       next = OPOPE_IDLE;
  end

  always_comb begin : controller_values
    change_state                  = 1'b0;
    tiler_setback                 = 1'b0;
    latch_clear                   = 1'b0;
    cntrl_slave.done              = 1'b0;
    busy_o                        = 1'b1;
    ce_clk_en_o                   = 1'b0;
    cntrl_scheduler.rst           = 1'b0;
    cntrl_scheduler.finished      = 1'b0;
    cntrl_scheduler.start_load_w  = 1'b0;
    cntrl_scheduler.start_load_x  = 1'b0;
    cntrl_scheduler.start_store_z = 1'b0;
    cntrl_scheduler.start_load_y  = 1'b0;
    case (current)
      OPOPE_LATCH_RST: begin
        latch_clear = 1'b1;
        busy_o      = 1'b0;
      end
      OPOPE_IDLE     : begin
        change_state                   = slave_start & tiler_valid;
        tiler_setback                  = change_state;
        cntrl_scheduler.start_load_w = change_state;
        busy_o      = 1'b0;
      end
      OPOPE_LOAD_W   : begin
        cntrl_scheduler.start_load_x  = 1'b1;
      end
      OPOPE_LOAD_X   : begin
        cntrl_scheduler.start_store_z = 1'b1;
        cntrl_scheduler.start_load_y  = 1'b1;
      end
      OPOPE_LOAD_Y   : begin
        change_state = start_computing;
      end
      OPOPE_COMPUTING: begin
        change_state = finished;
        ce_clk_en_o  = 1'b1;
      end
      OPOPE_FINISHED : begin
        cntrl_slave.done           = 1'b1;
        cntrl_scheduler.rst      = 1'b1;
        cntrl_scheduler.finished = 1'b1;
        busy_o                     = 1'b0;
      end
    endcase
  end

  /*---------------------------------------------------------------------------------------------*/
  /*                                         Streamer FSM                                        */
  /*---------------------------------------------------------------------------------------------*/
  
  assign x_granted = flgs_streamer_i.x_granted;
  assign w_granted = flgs_streamer_i.w_granted;
  assign y_granted = flgs_streamer_i.y_granted;
  assign grant = x_granted | w_granted | y_granted;

  always_comb begin : streamer_fsm
    case (streamer_current)
    // -----------------------------------------------------------------------------------------------------------
      STREAMER_Y  : streamer_next = streamer_change_state                     ? STREAMER_XWY : streamer_current;
    // -----------------------------------------------------------------------------------------------------------
      STREAMER_XWY: streamer_next = streamer_change_state | last_iteration_q  ? STREAMER_XWM : streamer_current;
    // -----------------------------------------------------------------------------------------------------------
      STREAMER_XWZ: streamer_next = streamer_change_state && last_iteration_q ? STREAMER_XWM :
                                    streamer_change_state                     ? STREAMER_XWY : streamer_current;
    // -----------------------------------------------------------------------------------------------------------
      STREAMER_Z  : streamer_next = streamer_change_state                     ? STREAMER_Y   : streamer_current;
    // -----------------------------------------------------------------------------------------------------------
      STREAMER_XWM: streamer_next = streamer_change_state && done_q           ? STREAMER_Z   : 
                                    streamer_change_state                     ? STREAMER_XWZ : streamer_current;
    // -----------------------------------------------------------------------------------------------------------
      default     : streamer_next = STREAMER_Y;
    // -----------------------------------------------------------------------------------------------------------
    endcase
  end
  
  always_comb begin : streamer_values
    y_counter_d        = y_counter_q       ;
    priority_counter_d = priority_counter_q;
    mask_y_o           = 1'b0;
    mask_z_o           = 1'b1;
    extra_d            = extra_q;
    done_d             = done_q ;
    finished           = 1'b0;
    start_computing    = 1'b0;
    
    case (streamer_current)
      STREAMER_Y  : begin
       y_counter_d           = y_counter_q + y_granted;
       streamer_change_state = (y_counter_q == LoadCycles-1) & (y_counter_d =='0);
       priority_counter_d    = 2'b11 + streamer_change_state;
       start_computing       = streamer_change_state;
      end
      STREAMER_XWY: begin
        extra_d               = 1'b0;
        y_counter_d           = y_counter_q + y_granted;
        streamer_change_state = (y_counter_q == LoadCycles-1) & (y_counter_d =='0);
        priority_counter_d    = priority_counter_q + grant;
        done_d                = last_iteration_q;
      end
      STREAMER_XWM: begin
        extra_d               = extra_q + y_granted;
        priority_counter_d    = priority_counter_q + grant;
        mask_y_o              = priority_counter_q[1];
        streamer_change_state = out_valid_o;
        mask_z_o              = ~(streamer_change_state & done_q);
      end
      STREAMER_XWZ: begin
        streamer_change_state = (y_counter_q == LoadCycles-1) & y_granted;
        y_counter_d           = streamer_change_state ? extra_q : y_counter_q + y_granted;
        priority_counter_d    = priority_counter_q + grant;
        mask_y_o              = 1'b1;
        mask_z_o              = 1'b0;
        done_d                = last_iteration_q;
      end 
      STREAMER_Z  : begin
        y_counter_d           = y_counter_q + y_granted;
        streamer_change_state = (y_counter_q == LoadCycles-1) & (y_counter_d =='0);
        priority_counter_d    = 2'b11;
        mask_z_o              = 1'b0;
        done_d                = 1'b0;
        finished              = streamer_change_state;
      end 
    endcase    
  end

  always_comb begin : priority_values
    case (priority_counter_q)
      2'b00  : priority_level = PRIORITY_X ;
      2'b01  : priority_level = PRIORITY_W ;
      2'b10  : priority_level = PRIORITY_YZ;
      default: priority_level = PRIORITY_YZ;
    endcase

    case (priority_level)
      PRIORITY_X   : begin
        cntrl_streamer_o.custom_priority[0] = XsourceStreamId;
        cntrl_streamer_o.custom_priority[1] = WsourceStreamId;
        cntrl_streamer_o.custom_priority[2] = YsourceStreamId;
      end
      PRIORITY_W   : begin
        cntrl_streamer_o.custom_priority[0] = WsourceStreamId;
        cntrl_streamer_o.custom_priority[1] = YsourceStreamId;
        cntrl_streamer_o.custom_priority[2] = XsourceStreamId;
      end
      PRIORITY_YZ  :begin
        cntrl_streamer_o.custom_priority[0] = YsourceStreamId;
        cntrl_streamer_o.custom_priority[1] = XsourceStreamId;
        cntrl_streamer_o.custom_priority[2] = WsourceStreamId;
      end
    endcase
  end
  
  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni) begin
      y_counter_q        <= '0;
      priority_counter_q <= '0;
      streamer_current   <= STREAMER_Y;
      extra_q            <= '0;
      done_q             <= '0;
    end else begin
      y_counter_q        <= y_counter_d       ;
      priority_counter_q <= priority_counter_d;
      streamer_current   <= streamer_next     ;
      extra_q            <= extra_d           ;
      done_q             <= done_d            ;
    end
  end  

  /*---------------------------------------------------------------------------------------------*/
  /*                                       Memory Scheduler                                      */
  /*---------------------------------------------------------------------------------------------*/

  assign total_len_x_w = reg_file_q.hwpe_params[N_K_M] * X_REGBUFFER_DEPTH  / (Width*W_REGBUFFER_DEPTH * Height*X_REGBUFFER_DEPTH) / 2;
  assign total_len_y_z = W_REGBUFFER_DEPTH * X_REGBUFFER_DEPTH * Height * reg_file_q.hwpe_params[K_M] / (Width*W_REGBUFFER_DEPTH*Height*X_REGBUFFER_DEPTH) / 2;

  always_comb begin : address_gen_signals
    // Here we initialize the streamer source signals
    // for the X stream source
    // X: M*N | W: N*K | Y: M*K | Z: M*K -> X is transposed
    cntrl_streamer_o.x_stream_source_ctrl.addressgen_ctrl.base_addr     = reg_file_q.hwpe_params[X_ADDR];
    cntrl_streamer_o.x_stream_source_ctrl.addressgen_ctrl.tot_len       = total_len_x_w;
    cntrl_streamer_o.x_stream_source_ctrl.addressgen_ctrl.d0_len        = reg_file_q.hwpe_params[N_SIZE];
    cntrl_streamer_o.x_stream_source_ctrl.addressgen_ctrl.d0_stride     = reg_file_q.hwpe_params[M_SIZE] * (BITW/8);
    cntrl_streamer_o.x_stream_source_ctrl.addressgen_ctrl.d1_len        = reg_file_q.hwpe_params[K_SIZE] / (Width*W_REGBUFFER_DEPTH);
    cntrl_streamer_o.x_stream_source_ctrl.addressgen_ctrl.d1_stride     = 'b0;
    cntrl_streamer_o.x_stream_source_ctrl.addressgen_ctrl.d2_len        = reg_file_q.hwpe_params[M_SIZE] / (Height*X_REGBUFFER_DEPTH);
    cntrl_streamer_o.x_stream_source_ctrl.addressgen_ctrl.d2_stride     = Height * X_REGBUFFER_DEPTH * (BITW/8);
    cntrl_streamer_o.x_stream_source_ctrl.addressgen_ctrl.d3_stride     = 'b0;
    cntrl_streamer_o.x_stream_source_ctrl.addressgen_ctrl.dim_enable_1h = 3'b111;

    // Here we initialize the streamer source signals
    // for the W stream source
    cntrl_streamer_o.w_stream_source_ctrl.addressgen_ctrl.base_addr     = reg_file_q.hwpe_params[W_ADDR];
    cntrl_streamer_o.w_stream_source_ctrl.addressgen_ctrl.tot_len       = total_len_x_w;
    cntrl_streamer_o.w_stream_source_ctrl.addressgen_ctrl.d0_len        = reg_file_q.hwpe_params[N_SIZE];
    cntrl_streamer_o.w_stream_source_ctrl.addressgen_ctrl.d0_stride     = reg_file_q.hwpe_params[K_SIZE] * (BITW/8);
    cntrl_streamer_o.w_stream_source_ctrl.addressgen_ctrl.d1_len        = reg_file_q.hwpe_params[K_SIZE] / (Width*W_REGBUFFER_DEPTH);
    cntrl_streamer_o.w_stream_source_ctrl.addressgen_ctrl.d1_stride     = Width * W_REGBUFFER_DEPTH * (BITW/8);
    cntrl_streamer_o.w_stream_source_ctrl.addressgen_ctrl.d2_len        = reg_file_q.hwpe_params[M_SIZE] / (Height*X_REGBUFFER_DEPTH);
    cntrl_streamer_o.w_stream_source_ctrl.addressgen_ctrl.d2_stride     = 'b0;
    cntrl_streamer_o.w_stream_source_ctrl.addressgen_ctrl.d3_stride     = 'b0;
    cntrl_streamer_o.w_stream_source_ctrl.addressgen_ctrl.dim_enable_1h = 3'b111;

    // Here we initialize the streamer source signals
    cntrl_streamer_o.y_stream_source_ctrl.addressgen_ctrl.base_addr     = reg_file_q.hwpe_params[Z_ADDR];
    cntrl_streamer_o.y_stream_source_ctrl.addressgen_ctrl.tot_len       = total_len_y_z;
    cntrl_streamer_o.y_stream_source_ctrl.addressgen_ctrl.d0_len        = 2 * Height;
    cntrl_streamer_o.y_stream_source_ctrl.addressgen_ctrl.d0_stride     = reg_file_q.hwpe_params[K_SIZE] * (BITW/8);
    cntrl_streamer_o.y_stream_source_ctrl.addressgen_ctrl.d1_len        = reg_file_q.hwpe_params[K_SIZE] / (Width*W_REGBUFFER_DEPTH);
    cntrl_streamer_o.y_stream_source_ctrl.addressgen_ctrl.d1_stride     = (BITW/8) * Height * W_REGBUFFER_DEPTH;
    cntrl_streamer_o.y_stream_source_ctrl.addressgen_ctrl.d2_len        = reg_file_q.hwpe_params[M_SIZE] / (Height*X_REGBUFFER_DEPTH);
    cntrl_streamer_o.y_stream_source_ctrl.addressgen_ctrl.d2_stride     = reg_file_q.hwpe_params[K_SIZE] * Height*X_REGBUFFER_DEPTH * (BITW/8);
    cntrl_streamer_o.y_stream_source_ctrl.addressgen_ctrl.d3_stride     = 'b0;
    cntrl_streamer_o.y_stream_source_ctrl.addressgen_ctrl.dim_enable_1h = 3'b111;

    // Here we initialize the streamer sink signals for
    cntrl_streamer_o.z_stream_sink_ctrl.addressgen_ctrl.base_addr       = reg_file_q.hwpe_params[Z_ADDR];
    cntrl_streamer_o.z_stream_sink_ctrl.addressgen_ctrl.tot_len         = total_len_y_z;
    cntrl_streamer_o.z_stream_sink_ctrl.addressgen_ctrl.d0_len          = 2 * Height;
    cntrl_streamer_o.z_stream_sink_ctrl.addressgen_ctrl.d0_stride       = reg_file_q.hwpe_params[K_SIZE] * (BITW/8);
    cntrl_streamer_o.z_stream_sink_ctrl.addressgen_ctrl.d1_len          = reg_file_q.hwpe_params[K_SIZE] / (Width*W_REGBUFFER_DEPTH);
    cntrl_streamer_o.z_stream_sink_ctrl.addressgen_ctrl.d1_stride       = (BITW/8) * Height * W_REGBUFFER_DEPTH;
    cntrl_streamer_o.z_stream_sink_ctrl.addressgen_ctrl.d2_len          = reg_file_q.hwpe_params[M_SIZE] / (Height*X_REGBUFFER_DEPTH);
    cntrl_streamer_o.z_stream_sink_ctrl.addressgen_ctrl.d2_stride       = reg_file_q.hwpe_params[K_SIZE] * Height*X_REGBUFFER_DEPTH * (BITW/8);
    cntrl_streamer_o.z_stream_sink_ctrl.addressgen_ctrl.d3_stride       = 'b0;
    cntrl_streamer_o.z_stream_sink_ctrl.addressgen_ctrl.dim_enable_1h   = 3'b111;
  end

  always_comb begin : req_start_assignment
    cntrl_streamer_o.x_stream_source_ctrl.req_start    = cntrl_scheduler.start_load_x  && flgs_streamer_i.x_stream_source_flags.ready_start;
    cntrl_streamer_o.w_stream_source_ctrl.req_start    = cntrl_scheduler.start_load_w  && flgs_streamer_i.w_stream_source_flags.ready_start;
    cntrl_streamer_o.y_stream_source_ctrl.req_start    = cntrl_scheduler.start_load_y  && flgs_streamer_i.y_stream_source_flags.ready_start;
    cntrl_streamer_o.z_stream_sink_ctrl.req_start      = cntrl_scheduler.start_store_z && flgs_streamer_i.z_stream_sink_flags.ready_start  ;
  end

  // NOTE: these are used for the casting, don't care for now
  assign cntrl_streamer_o.input_cast_src_fmt  = fpnew_pkg::fp_format_e'(reg_file_q.hwpe_params[OP_SELECTION][15:13]);
  assign cntrl_streamer_o.input_cast_dst_fmt  = fpnew_pkg::fp_format_e'(reg_file_q.hwpe_params[OP_SELECTION][12:10]);
  assign cntrl_streamer_o.output_cast_src_fmt = fpnew_pkg::fp_format_e'(reg_file_q.hwpe_params[OP_SELECTION][12:10]);
  assign cntrl_streamer_o.output_cast_dst_fmt = fpnew_pkg::fp_format_e'(reg_file_q.hwpe_params[OP_SELECTION][15:13]);

  /*---------------------------------------------------------------------------------------------*/
  /*                                          Engine FSM                                         */
  /*---------------------------------------------------------------------------------------------*/

  always_comb begin : acc_fsm
    acc_state_next = acc_state_current;

    case (acc_state_current)
    // -------------------------------------------------------------------------------------------------------------------------------------
      ACC_IDLE                  : acc_state_next = acc_change_state                     ? ACC_Y_READ                : ACC_IDLE                 ;
    // -------------------------------------------------------------------------------------------------------------------------------------
      ACC_Y_READ                : acc_state_next = acc_change_state                     ? ACC_LOAD_ENGINE           : ACC_Y_READ               ;
    // -------------------------------------------------------------------------------------------------------------------------------------
      ACC_LOAD_ENGINE           : acc_state_next = acc_change_state && last_iteration_q ? ACC_ENGINE_RUNNING        :
                                                   acc_change_state                     ? ACC_Y_READ_ENGINE_RUNNING : ACC_LOAD_ENGINE          ;
    // -------------------------------------------------------------------------------------------------------------------------------------       
      ACC_Y_READ_ENGINE_RUNNING : acc_state_next = acc_change_state                     ? ACC_Z_RELOAD_Y_ENGINE     : ACC_Y_READ_ENGINE_RUNNING;
    // -------------------------------------------------------------------------------------------------------------------------------------
      ACC_ENGINE_RUNNING        : acc_state_next = acc_change_state                     ? ACC_Z_RELOAD              : ACC_ENGINE_RUNNING       ; 
    // -------------------------------------------------------------------------------------------------------------------------------------
      ACC_Z_RELOAD_Y_ENGINE     : acc_state_next = acc_change_state                     ? ACC_Z_STORE               : ACC_Z_RELOAD_Y_ENGINE    ; 
    // -------------------------------------------------------------------------------------------------------------------------------------
      ACC_Z_RELOAD              : acc_state_next = acc_change_state                     ? ACC_Z_STORE               : ACC_Z_RELOAD             ;
    // -------------------------------------------------------------------------------------------------------------------------------------
      ACC_Z_STORE               : acc_state_next = acc_change_state && acc_done_q       ? ACC_IDLE                  :
                                                   acc_change_state && last_iteration_q ? ACC_ENGINE_RUNNING        : 
                                                   acc_change_state                     ? ACC_Y_READ_ENGINE_RUNNING : ACC_Z_STORE              ; 
    // -------------------------------------------------------------------------------------------------------------------------------------
      default                   : acc_state_next = ACC_IDLE;
    // -------------------------------------------------------------------------------------------------------------------------------------
    endcase
  end

  always_comb begin : acc_values
    y_write_reg_index_d   = y_write_reg_index_q  ;
    y_write_row_index_d   = y_write_row_index_q  ;
    inner_loop_counter_d  = inner_loop_counter_q ;
    reg_write_to_engine_d = reg_write_to_engine_q;
    z_read_reg_index_d    = z_read_reg_index_q   ;
    z_read_row_index_d    = z_read_row_index_q   ;
    prefetched_d          = prefetched_q         ;
    acc_done_d            = acc_done_q           ;

    acc_change_state              = 1'b0;
    y_bias_selector               = 1'b0;
    acc_input_selector            = 1'b0;
    external_loading              = 1'b0;
    in_ready_o                    = 1'b0;
    out_valid_o                   = 1'b0;
    y_ready_o                     = 1'b0;
    shift_acc                     = 1'b0;

    case (acc_state_current)
    // -------------------------------------------------------------------------------------------------------------------------------------
      ACC_IDLE: begin
        acc_change_state           = cntrl_scheduler.start_load_x;
        y_ready_o = acc_change_state;
        acc_done_d                 = '0;
        y_write_reg_index_d        = '0;
        y_write_row_index_d        = '0;
        z_read_reg_index_d         = '0;
        inner_loop_counter_d       = '0;
        reg_write_to_engine_d      = '0;
        prefetched_d               = '0;
      end
    // -------------------------------------------------------------------------------------------------------------------------------------
      ACC_Y_READ: begin
        if (y_in_valid_i) begin
          y_write_reg_index_d = (y_write_reg_index_q == REG_PER_CE - 2) ? 'b0 : y_write_reg_index_q + 2;
          y_write_row_index_d = (y_write_reg_index_q == REG_PER_CE - 2) ? (y_write_row_index_q == Height-1) ? 'b0: y_write_row_index_q + 1 : y_write_row_index_q;
          acc_change_state    = (y_write_row_index_q == Height - 1 && y_write_reg_index_q == REG_PER_CE - 2);
          shift_acc             = 1'b1;
        end
        external_loading      = 1'b1;
        y_ready_o             = 1'b1;
      end
    // -------------------------------------------------------------------------------------------------------------------------------------
      ACC_LOAD_ENGINE: begin
        if (in_valid_i) begin
          inner_loop_counter_d = (inner_loop_counter_q == (cntrl_engine_o.inner_loop_count - 1)) ? 'b0 : inner_loop_counter_q + 1;
          z_read_reg_index_d = (z_read_reg_index_q == REG_PER_CE - 1) ? 'b0: z_read_reg_index_q + 1; // This can be used both ways
          acc_change_state = (z_read_reg_index_q == REG_PER_CE - 1);
        end
        if (y_in_valid_i && prefetched_q == 1'b0) begin // Prefetch the y values
          y_write_reg_index_d = (y_write_reg_index_q == REG_PER_CE - 2) ? 'b0 : y_write_reg_index_q + 2;
          y_write_row_index_d = (y_write_reg_index_q == REG_PER_CE - 2) ? (y_write_row_index_q == Height-1) ? 'b0: y_write_row_index_q + 1 : y_write_row_index_q;
          prefetched_d        = (y_write_row_index_q == Height - 1 && y_write_reg_index_q == REG_PER_CE - 2) ?  1'b1 : prefetched_q;
          shift_acc           = |y_write_row_index_q;
        end
        y_ready_o = 1'b1;
        external_loading = 1'b1;
        y_bias_selector  = 1'b1;
        in_ready_o       = 1'b1;
        ce_enable        = in_valid_i;
      end
    // -------------------------------------------------------------------------------------------------------------------------------------
      ACC_Y_READ_ENGINE_RUNNING: begin
        if (y_in_valid_i && prefetched_q == 1'b0) begin // Prefetch the y values
          y_write_reg_index_d = (y_write_reg_index_q == REG_PER_CE - 2) ? 'b0 : y_write_reg_index_q + 2;
          y_write_row_index_d = (y_write_reg_index_q == REG_PER_CE - 2) ? (y_write_row_index_q == Height-1) ? 'b0: y_write_row_index_q + 1 : y_write_row_index_q;
          prefetched_d        = (y_write_row_index_q == Height - 1 && y_write_reg_index_q == REG_PER_CE - 2) ?  1'b1 : prefetched_q;
          shift_acc           = |y_write_row_index_q;
        end
        if (in_valid_i) begin // This has to happen after the prefetched y is loaded
          inner_loop_counter_d = (inner_loop_counter_q == (cntrl_engine_o.inner_loop_count - 1)) ? 'b0 : inner_loop_counter_q + 1;
          acc_change_state = inner_loop_counter_q == (cntrl_engine_o.inner_loop_count - 1 );
        end
        if (prefetched_q == 1'b1 && acc_state_current == ACC_Y_READ_ENGINE_RUNNING && acc_state_next == ACC_Z_RELOAD_Y_ENGINE) prefetched_d = 1'b0; // Reloaded value completed
        y_ready_o        = ~(prefetched_d ) &~ prefetched_q; //~acc_change_state;
        in_ready_o       = 1'b1;
        external_loading = ~(prefetched_q );
        ce_enable        = in_valid_i;
      end
    // -------------------------------------------------------------------------------------------------------------------------------------
      ACC_ENGINE_RUNNING: begin
        if (in_valid_i) begin 
          inner_loop_counter_d = (inner_loop_counter_q == (cntrl_engine_o.inner_loop_count - 1)) ? 'b0 : inner_loop_counter_q + 1;
          acc_change_state = inner_loop_counter_q == (cntrl_engine_o.inner_loop_count - 1 );
        end
        in_ready_o                 = 1'b1;
        ce_enable        = in_valid_i;
      end
    // -------------------------------------------------------------------------------------------------------------------------------------
      ACC_Z_RELOAD_Y_ENGINE: begin // Storing the z values to acc, reload the y values to the engine
        if (in_valid_i) inner_loop_counter_d = (inner_loop_counter_q == (cntrl_engine_o.inner_loop_count - 1)) ? 'b0 : inner_loop_counter_q + 1; // NOTE: should never 0 here
        z_read_reg_index_d         = (z_read_reg_index_q == REG_PER_CE - 1) ? 'b0: z_read_reg_index_q + 1;
        reg_write_to_engine_d      = (reg_write_to_engine_q == REG_PER_CE - 1) ? 'b0: reg_write_to_engine_q + 1; 
        acc_change_state           = (z_read_reg_index_q == REG_PER_CE - 1);
        acc_input_selector         = 1'b1;
        y_bias_selector            = 1'b1;
        in_ready_o                 = 1'b1;
        ce_enable                  = in_valid_i;
      end
    // -------------------------------------------------------------------------------------------------------------------------------------
      ACC_Z_RELOAD: begin // Storing the z values to acc
        z_read_reg_index_d    = (z_read_reg_index_q == REG_PER_CE - 1) ? 'b0: z_read_reg_index_q + 1;
        reg_write_to_engine_d = (reg_write_to_engine_q == REG_PER_CE - 1) ? 'b0: reg_write_to_engine_q + 1; 
        acc_change_state      = (z_read_reg_index_q == REG_PER_CE - 1);
        acc_input_selector    = 1'b1;
        acc_done_d            = 1'b1;
        ce_enable             = 1'b1;
      end
    // -------------------------------------------------------------------------------------------------------------------------------------
      ACC_Z_STORE: begin // Stream out the z values to the memory
        out_valid_o = 1'b1;
        in_ready_o  = ~acc_done_q;
        if (in_valid_i) inner_loop_counter_d = (inner_loop_counter_q == (cntrl_engine_o.inner_loop_count - 1)) ? 'b0 : inner_loop_counter_q + 1; // NOTE: should never 0 here
        if (out_ready_i) begin
          z_read_reg_index_d = (z_read_reg_index_q == REG_PER_CE - 2) ? 'b0: z_read_reg_index_q + 2;
          z_read_row_index_d = (z_read_reg_index_q == REG_PER_CE - 2) ? (z_read_row_index_q == Height - 1) ? 'b0: z_read_row_index_q + 1: z_read_row_index_q;
          acc_change_state   = (z_read_row_index_q == Height - 1 && z_read_reg_index_q == REG_PER_CE - 2);
          shift_acc = 1'b1;
        end
        external_loading = 1'b1;
        ce_enable = in_valid_i &~ acc_done_q;
      end
    // -------------------------------------------------------------------------------------------------------------------------------------
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : seq_block
    if (~rst_ni) begin
      acc_state_current     <= ACC_IDLE;
      y_write_reg_index_q   <= '0;
      y_write_row_index_q   <= '0;
      inner_loop_counter_q  <= '0;
      reg_write_to_engine_q <= '0;
      z_read_reg_index_q    <= '0;
      z_read_row_index_q    <= '0;
      prefetched_q          <= '0;
      acc_done_q            <= '0;
      last_iteration_q      <= '0;
    end else begin
      acc_state_current     <= acc_state_next       ;
      y_write_reg_index_q   <= y_write_reg_index_d  ;
      y_write_row_index_q   <= y_write_row_index_d  ;
      inner_loop_counter_q  <= inner_loop_counter_d ;
      reg_write_to_engine_q <= reg_write_to_engine_d;
      z_read_reg_index_q    <= z_read_reg_index_d   ;
      z_read_row_index_q    <= z_read_row_index_d   ;
      prefetched_q          <= prefetched_d         ;
      acc_done_q            <= acc_done_d           ;
      last_iteration_q      <= last_iteration_d     ;
    end
  end


  /*---------------------------------------------------------------------------------------------*/
  /*                            Other combinational assigmnets                                   */
  /*---------------------------------------------------------------------------------------------*/
  assign evt_o          = flgs_slave.evt[N_CORES-1:0];
  assign clear_o        = clear || latch_clear;
  assign cfg_complete_o = tiler_valid;

  assign cntrl_streamer_o.custom_priority_force = 1'b1;

  assign last_iteration_d = cntrl_scheduler.finished ? '0 : flgs_streamer_i.y_stream_source_flags.done | last_iteration_q;
endmodule : opope_ctrl
