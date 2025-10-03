// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Danilo Cammarata <dcammarata@iis.ee.ethz.ch>
//

timeunit 1ps; timeprecision 1ps;

import hci_package::*;

module opope_tb
  import opope_pkg::*;
#(
  parameter TCP = 2.0ns, // clock period, 1 GHz clock
  parameter TA  = 0.4ns, // application time
  parameter TT  = 1.6ns  // test time
)(
  input logic clk_i,
  input logic rst_ni,
  input logic fetch_enable_i
);

  localparam int unsigned DW = opope_pkg::DATA_W;

  // parameters
  localparam int unsigned PROB_STALL = 0;
  localparam int unsigned NC = 1;
  localparam int unsigned ID = 10;

  localparam int unsigned MP     = DW/32;
  
  localparam int unsigned MEMORY_SIZE = 192*1024;
  localparam int unsigned STACK_MEMORY_SIZE = 192*1024;
  localparam int unsigned PULP_XPULP = 1;
  localparam int unsigned FPU = 0;
  localparam int unsigned PULP_ZFINX = 0;
  localparam logic [31:0] BASE_ADDR = 32'h1c000000;
  localparam logic [31:0] HWPE_ADDR_BASE_BIT = 20;
  localparam bit          USE_ECC = 0;
  localparam int unsigned EW = (USE_ECC) ? 72 : DEFAULT_EW;

  // global signals
  string stim_instr, stim_data;
  logic test_mode;
  logic [31:0] core_boot_addr;
  logic opope_busy;

  hwpe_stream_intf_tcdm instr[0:0]  (.clk(clk_i));
  hwpe_stream_intf_tcdm stack[0:0]  (.clk(clk_i));
  hwpe_stream_intf_tcdm tcdm [MP:0] (.clk(clk_i));

  logic [NC-1:0][1:0] evt;

  logic [MP-1:0]       tcdm_req;
  logic [MP-1:0]       tcdm_gnt;
  logic [MP-1:0][31:0] tcdm_add;
  logic [MP-1:0]       tcdm_wen;
  logic [MP-1:0][3:0]  tcdm_be;
  logic [MP-1:0][31:0] tcdm_data;
  logic [EW-1:0]       tcdm_ecc;
  logic [MP-1:0][31:0] tcdm_r_data;
  logic [MP-1:0]       tcdm_r_valid;
  logic                tcdm_r_opc;
  logic                tcdm_r_user;
  logic [EW-1:0]       tcdm_r_ecc;

  logic          periph_req;
  logic          periph_gnt;
  logic [31:0]   periph_add;
  logic          periph_wen;
  logic [3:0]    periph_be;
  logic [31:0]   periph_data;
  logic [ID-1:0] periph_id;
  logic [31:0]   periph_r_data;
  logic          periph_r_valid;
  logic [ID-1:0] periph_r_id;

  logic          instr_req;
  logic          instr_gnt;
  logic          instr_rvalid;
  logic [31:0]   instr_addr;
  logic [31:0]   instr_rdata;

  logic          data_req;
  logic          data_gnt;
  logic          data_rvalid;
  logic          data_we;
  logic [3:0]    data_be;
  logic [31:0]   data_addr;
  logic [31:0]   data_wdata;
  logic [31:0]   data_rdata;
  logic          data_err;
  logic          core_sleep;

  // bindings
  always_comb begin : bind_periph
    periph_req  = data_req & data_addr[HWPE_ADDR_BASE_BIT];
    periph_add  = data_addr;
    periph_wen  = ~data_we;
    periph_be   = data_be;
    periph_data = data_wdata;
    periph_id   = '0;
  end

  always_comb begin : bind_instrs
    instr[0].req  = instr_req;
    instr[0].add  = instr_addr;
    instr[0].wen  = 1'b1;
    instr[0].be   = '0;
    instr[0].data = '0;
    instr_gnt    = instr[0].gnt;
    instr_rdata  = instr[0].r_data;
    instr_rvalid = instr[0].r_valid;
  end

  always_comb begin : bind_stack
    stack[0].req  = data_req & (data_addr[31:24] == '0) & ~data_addr[HWPE_ADDR_BASE_BIT];
    stack[0].add  = data_addr;
    stack[0].wen  = ~data_we;
    stack[0].be   = data_be;
    stack[0].data = data_wdata;
  end

  logic other_r_valid;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni)
      other_r_valid <= '0;
    else
      other_r_valid <= data_req & (data_addr[31:24] == 8'h80);
  end

  for(genvar ii=0; ii<MP; ii++) begin : tcdm_binding
    assign tcdm[ii].req  = tcdm_req  [ii];
    assign tcdm[ii].add  = tcdm_add  [ii];
    assign tcdm[ii].wen  = tcdm_wen  [ii];
    assign tcdm[ii].be   = tcdm_be   [ii];
    if (~USE_ECC)
      assign tcdm[ii].data = tcdm_data [ii];
    assign tcdm_gnt     [ii] = tcdm[ii].gnt;
    assign tcdm_r_data  [ii] = tcdm[ii].r_data;
    assign tcdm_r_valid [ii] = tcdm[ii].r_valid;
  end
  assign tcdm[MP].req  = data_req & (data_addr[31:24] != '0) & (data_addr[31:24] != 8'h80) & ~data_addr[HWPE_ADDR_BASE_BIT];
  assign tcdm[MP].add  = data_addr;
  assign tcdm[MP].wen  = ~data_we;
  assign tcdm[MP].be   = data_be;
  assign tcdm[MP].data = data_wdata;
  assign tcdm_r_opc   = 0;
  assign tcdm_r_user  = 0;
  assign data_gnt    = periph_req ?
                       periph_gnt : stack[0].req ?
                                    stack[0].gnt : tcdm[MP].req ?
                                                   tcdm[MP].gnt : '1;
  assign data_rdata  = periph_r_valid ? periph_r_data  :
                                        stack[0].r_valid ? stack[0].r_data  :
                                                           tcdm[MP].r_valid ? tcdm[MP].r_data : '0;
  assign data_rvalid = periph_r_valid   |
                       stack[0].r_valid |
                       tcdm[MP].r_valid |
                       other_r_valid    ;

  if (USE_ECC) begin : gen_r_ecc
    // RESPONSE PHASE ENCODING
    logic [MP-1:0][38:0] tcdm_r_data_enc;
    for(genvar ii=0; ii<MP; ii++) begin : r_data_encoding
      hsiao_ecc_enc #(
        .DataWidth ( 32 )
      ) i_r_data_enc (
        .in  (tcdm[ii].r_data),
        .out (tcdm_r_data_enc[ii])
      );
      assign tcdm_r_ecc[(ii+1)*7-1:ii*7] = tcdm_r_data_enc[ii][38:32];
    end
    assign tcdm_r_ecc[EW-1:(7*MP)] = '0;
  end else begin : gen_no_r_ecc
    assign tcdm_r_ecc = '0;
  end

  if (USE_ECC) begin : gen_ecc_dec
    // REQUEST PHASE DECODING
    for(genvar ii=0; ii<MP; ii++) begin : data_decoding
      hsiao_ecc_dec #(
        .DataWidth ( 32 )
      ) i_data_dec (
        .in         ( { tcdm_ecc[(ii+1)*7-1+9:ii*7+9], tcdm_data[ii] } ),
        .out        ( tcdm[ii].data ),
        .syndrome_o ( ),
        .err_o      ( )
      );
    end

    hsiao_ecc_dec #(
      .DataWidth ( 32+36+1 )
    ) i_meta_dec (
      .in         ( { tcdm_ecc[8:0], tcdm_add[0], tcdm_wen[0], tcdm_be } ),
      .out        (  ),
      .syndrome_o (  ),
      .err_o      (  )
    );
  end



  opope_wrap #(
    .ID_WIDTH           ( ID                 ),
    .N_CORES            ( NC                 ),
    .DW                 ( DW                 ),
    .MP                 ( DW/32              ),
    .EW                 ( EW                 )
  ) i_opope_wrap      (
    .clk_i              ( clk_i              ),
    .rst_ni             ( rst_ni             ),
    .test_mode_i        ( test_mode          ),
    .evt_o              ( evt                ),
    .busy_o             ( opope_busy       ),
    .tcdm_req_o         ( tcdm_req           ),
    .tcdm_add_o         ( tcdm_add           ),
    .tcdm_wen_o         ( tcdm_wen           ),
    .tcdm_be_o          ( tcdm_be            ),
    .tcdm_data_o        ( tcdm_data          ),
    .tcdm_ecc_o         ( tcdm_ecc           ),
    .tcdm_gnt_i         ( tcdm_gnt           ),
    .tcdm_r_data_i      ( tcdm_r_data        ),
    .tcdm_r_valid_i     ( tcdm_r_valid       ),
    .tcdm_r_opc_i       ( tcdm_r_opc         ),
    .tcdm_r_user_i      ( tcdm_r_user        ),
    .tcdm_r_ecc_i       ( tcdm_r_ecc         ),
    .periph_req_i       ( periph_req         ),
    .periph_gnt_o       ( periph_gnt         ),
    .periph_add_i       ( periph_add         ),
    .periph_wen_i       ( periph_wen         ),
    .periph_be_i        ( periph_be          ),
    .periph_data_i      ( periph_data        ),
    .periph_id_i        ( periph_id          ),
    .periph_r_data_o    ( periph_r_data      ),
    .periph_r_valid_o   ( periph_r_valid     ),
    .periph_r_id_o      ( periph_r_id        )
  );


  tb_dummy_memory  #(
    .MP             ( MP + 1        ),
    .MEMORY_SIZE    ( 512 * 1024 ),
    .BASE_ADDR      ( 32'h1c010000  ),
    .PROB_STALL     ( PROB_STALL    ),
    .TCP            ( TCP           ),
    .TA             ( TA            ),
    .TT             ( TT            )
  ) i_dummy_dmemory (
    .clk_i          ( clk_i         ),
    .rst_ni         ( rst_ni        ),
    .clk_delayed_i  ( '0            ),
    .randomize_i    ( 1'b0          ),
    .enable_i       ( 1'b1          ),
    .stallable_i    ( 1'b1          ),
    .tcdm           ( tcdm          )
  );

  tb_dummy_memory  #(
    .MP             ( 1           ),
    .MEMORY_SIZE    ( MEMORY_SIZE ),
    .BASE_ADDR      ( BASE_ADDR   ),
    .PROB_STALL     ( 0           ),
    .TCP            ( TCP         ),
    .TA             ( TA          ),
    .TT             ( TT          )
  ) i_dummy_imemory (
    .clk_i          ( clk_i       ),
    .rst_ni         ( rst_ni      ),
    .clk_delayed_i  ( '0          ),
    .randomize_i    ( 1'b0        ),
    .enable_i       ( 1'b1        ),
    .stallable_i    ( 1'b0        ),
    .tcdm           ( instr       )
  );

  tb_dummy_memory       #(
    .MP                  ( 1                 ),
    .MEMORY_SIZE         ( STACK_MEMORY_SIZE ),
    .BASE_ADDR           ( BASE_ADDR         ),
    .PROB_STALL          ( 0                 ),
    .TCP                 ( TCP               ),
    .TA                  ( TA                ),
    .TT                  ( TT                )
  ) i_dummy_stack_memory (
    .clk_i               ( clk_i             ),
    .rst_ni              ( rst_ni            ),
    .clk_delayed_i       ( '0                ),
    .randomize_i         ( 1'b0              ),
    .enable_i            ( 1'b1              ),
    .stallable_i         ( 1'b0              ),
    .tcdm                ( stack             )
  );

  cv32e40p_core #(
    .PULP_XPULP     ( PULP_XPULP ),
    .FPU            ( FPU        ),
    .PULP_ZFINX     ( PULP_ZFINX )
  ) i_cv32e40p_core (
    // Clock and Reset
    .clk_i               ( clk_i          ),
    .rst_ni              ( rst_ni         ),
    .pulp_clock_en_i     ( 1'b1           ),  // PULP clock enable (only used if PULP_CLUSTER = 1)
    .scan_cg_en_i        ( 1'b0           ),  // Enable all clock gates for testing
    // Core ID, Cluster ID, debug mode halt address and boot address are considered more or less static
    .boot_addr_i         ( core_boot_addr ),
    .mtvec_addr_i        ( '0             ),
    .dm_halt_addr_i      ( '0             ),
    .hart_id_i           ( '0             ),
    .dm_exception_addr_i ( '0             ),
    // Instruction memory interface
    .instr_req_o         ( instr_req    ),
    .instr_gnt_i         ( instr_gnt    ),
    .instr_rvalid_i      ( instr_rvalid ),
    .instr_addr_o        ( instr_addr   ),
    .instr_rdata_i       ( instr_rdata  ),
    // Data memory interface
    .data_req_o          ( data_req     ),
    .data_gnt_i          ( data_gnt     ),
    .data_rvalid_i       ( data_rvalid  ),
    .data_we_o           ( data_we      ),
    .data_be_o           ( data_be      ),
    .data_addr_o         ( data_addr    ),
    .data_wdata_o        ( data_wdata   ),
    .data_rdata_i        ( data_rdata   ),
    // apu-interconnect
    // handshake signals
    .apu_req_o           (              ),
    .apu_gnt_i           ( '0           ),
    // request channel
    .apu_operands_o      (              ),
    .apu_op_o            (              ),
    .apu_flags_o         (              ),
    // response channel
    .apu_rvalid_i        ( '0           ),
    .apu_result_i        ( '0           ),
    .apu_flags_i         ( '0           ),
    // Interrupt inputs
    .irq_i               ({28'd0, evt[0][0], 3'd0}),  // CLINT interrupts + CLINT extension interrupts
    .irq_ack_o           (              ),
    .irq_id_o            (              ),
    // Debug Interface
    .debug_req_i         ( '0           ),
    .debug_havereset_o   (              ),
    .debug_running_o     (              ),
    .debug_halted_o      (              ),
    // CPU Control Signals
    .fetch_enable_i      ( fetch_enable_i ),
    .core_sleep_o        ( core_sleep     )
  );

  integer f_x, f_W, f_y, f_tau;
  logic start;
  int cnt_rd, cnt_wr;

  int errors = -1;
  always_ff @(posedge clk_i)
  begin
    if((data_addr == 32'h80000000 ) && (data_we & data_req == 1'b1)) begin
      errors = data_wdata;
    end
    if((data_addr == 32'h80000004 ) && (data_we & data_req == 1'b1)) begin
      $write("%c", data_wdata);
    end
  end

  int counter = 0;
  int measured_count = 0;
  bit counting = 0;
  parameter int EXPECTED_VALID_COUNT = 64; //NOTE: this has an issue when the TCDM DATA_W is too large, the code returns empty data

  logic [MP-1:0][31:0] prev_tcdm_r_data;
  logic [MP-1:0][31:0] prev_tcdm_data;
  int start_counter = 0;
  int end_counter = 0;
  int global_counter = 0;
  int channel_valid_count;
  always_ff @(posedge clk_i) begin
    global_counter <= global_counter + 1;
  end
  always_ff @(posedge clk_i) begin 
    if (!counting && (prev_tcdm_r_data == 'b0) && (tcdm_r_data != 'b0)) begin // rising edge for tcdm_r_data
      counting <= 1;
      start_counter <= global_counter;
    end
    if (counting) begin 
      channel_valid_count = 0;
      for (int i = 0; i < MP; i++) begin if (tcdm_data[i] != 'b0) channel_valid_count++;end
      counter <= counter + channel_valid_count;
      if (counter >= EXPECTED_VALID_COUNT) begin
        counting <= 0;
        end_counter <= global_counter;
        measured_count <= global_counter - start_counter;
      end
    end

    prev_tcdm_r_data <= tcdm_r_data;
    prev_tcdm_data <= tcdm_data;
  end

  int periphery_start_counter = 0;
  int periphery_end_counter = 0;
  bit periphery_counting = 0;
  
  logic check_start_config, prev_check_start_config;
  logic prev_finished_opope, finished_opope;
  
  assign check_start_config = (periph_req && (periph_add[7:0] == 'h54) && (!periph_wen) && (periph_gnt)) ? 1'b1: 1'b0;

`ifdef OPOPE_HWPE_SYNTH
  assign finished_opope = i_opope_wrap.i_opope_top.i_control.cntrl_scheduler_finished_;
`else
  assign finished_opope = i_opope_wrap.i_opope_top.i_control.cntrl_scheduler.finished;
`endif

  always_ff @(posedge clk_i) begin 
    if (!periphery_counting && (prev_check_start_config == 1'b0) && (check_start_config == 1'b1)) begin 
      periphery_counting <= 1;
      periphery_start_counter <= global_counter;
    end
    if (periphery_counting &&(prev_finished_opope == 1'b0) && (finished_opope)) begin 
      periphery_counting <= 0;
      periphery_end_counter <= global_counter;
    end

  prev_check_start_config <= check_start_config;
  prev_finished_opope <= finished_opope;
  end


    // Metrics
   // TCDM access counters
   int start_tcdm_counter = 0;
   int end_tcdm_counter = 0;
   int tcdm_read_counter = 0;
   int tcdm_write_counter = 0;
 
   always_ff @(posedge clk_i) begin
     if (tcdm_req && start_tcdm_counter == 0) start_tcdm_counter <= global_counter;
     if (tcdm_req) end_tcdm_counter <= global_counter;
     if (tcdm_req && tcdm_wen) tcdm_read_counter++; 
     if (tcdm_req && !tcdm_wen) tcdm_write_counter++;
   end 


/**************
 *  VCD Dump  *
 **************/

`ifdef VCD_DUMP
  initial begin: vcd_dump
    wait (rst_ni);
    while (!(check_start_config)) begin
      @(posedge clk_i);
    end
    $display("[TB] %d - VCD dump started", global_counter);

    $dumpfile(`VCD_DUMP_FILE);
    $dumpvars(0, i_opope_wrap);
    $dumpon;

    while (!(finished_opope)) begin
      @(posedge clk_i);
    end
    $display("[TB] %d - VCD dump finished", global_counter);

    $dumpoff;
    $finish(0);
  end: vcd_dump
`endif

  initial begin

    if (!$value$plusargs("STIM_INSTR=%s", stim_instr)) $fatal("Can't find  sw/build/stim_instr.txt");
    if (!$value$plusargs("STIM_DATA=%s", stim_data)) $fatal("Can't find  sw/build/stim_data.txt");

    test_mode = 1'b0;
    core_boot_addr = 32'h1C000084;

    // Load instruction and data memory
    $readmemh(stim_instr, opope_tb.i_dummy_imemory.memory);
    $readmemh(stim_data,  opope_tb.i_dummy_dmemory.memory);

    // End: WFI + returned != -1 signals end-of-computation
    while(~core_sleep || errors==-1) @(posedge clk_i);
    cnt_rd = opope_tb.i_dummy_dmemory.cnt_rd[0] +
             opope_tb.i_dummy_dmemory.cnt_rd[1] +
             opope_tb.i_dummy_dmemory.cnt_rd[2] +
             opope_tb.i_dummy_dmemory.cnt_rd[3] +
             opope_tb.i_dummy_dmemory.cnt_rd[4] +
             opope_tb.i_dummy_dmemory.cnt_rd[5] +
             opope_tb.i_dummy_dmemory.cnt_rd[6] +
             opope_tb.i_dummy_dmemory.cnt_rd[7] +
             opope_tb.i_dummy_dmemory.cnt_rd[8];
    cnt_wr = opope_tb.i_dummy_dmemory.cnt_wr[0] +
             opope_tb.i_dummy_dmemory.cnt_wr[1] +
             opope_tb.i_dummy_dmemory.cnt_wr[2] +
             opope_tb.i_dummy_dmemory.cnt_wr[3] +
             opope_tb.i_dummy_dmemory.cnt_wr[4] +
             opope_tb.i_dummy_dmemory.cnt_wr[5] +
             opope_tb.i_dummy_dmemory.cnt_wr[6] +
             opope_tb.i_dummy_dmemory.cnt_wr[7] +
             opope_tb.i_dummy_dmemory.cnt_wr[8];
    $display("[TB] - cnt_rd= %-8d", cnt_rd);
    $display("[TB] - cnt_wr= %-8d", cnt_wr);
    if(errors != 0) begin
      $display("[SAVE] - [TB] - Fail!");
      $error("[SAVE] - [TB] - errors=%08x", errors);
    end else begin
      $display("[SAVE] - [TB] - Success!");
      $display("[SAVE] - [TB] - errors=%08x", errors);
    end
    $display("[SAVE] - Measured count: %0d, Start counter: %0d, End counter: %0d", measured_count, start_counter, end_counter);
    $display("[SAVE] - Periphery Measured count: %0d, Start counter: %0d, End counter: %0d", periphery_end_counter - periphery_start_counter, periphery_start_counter, periphery_end_counter);
    $display("[SAVE] - TCDM Measured count: %0d, Start counter: %0d, End counter: %0d", end_tcdm_counter - start_tcdm_counter + 1, start_tcdm_counter, end_tcdm_counter);
    $display("[SAVE] - TCDM Request Read count: %0d | Write count: %0d | Element read: %0d | Element write: %0d", tcdm_read_counter, tcdm_write_counter, tcdm_read_counter*8, tcdm_write_counter*8);
    $display("[SAVE] - TCDM Request count: %0d", tcdm_read_counter + tcdm_write_counter);

    $display("[SAVE] - ");
    $display("[SAVE] - [Data]: Cycles: %0d | TCDM Request count: %0d | TCDM Start - Finish: %0d", periphery_end_counter - periphery_start_counter, tcdm_read_counter + tcdm_write_counter, end_tcdm_counter - start_tcdm_counter+1);
    $display("[SAVE] - ");
    $finish;
  end

  initial begin
    int ENABLE_ENGINE_OUTPUT  = 0;
    int ENABLE_ENGINE_Y_INPUT = 0;
    int cnt = 0;
    wait (rst_ni);
    // ----------------------------------------------------------------------- 
      if(ENABLE_ENGINE_OUTPUT) begin 
        if(i_opope_wrap.i_opope_top.i_control.out_ready_i && 
           i_opope_wrap.i_opope_top.i_control.out_valid_o) begin
          cnt =  cnt+1 ;
          $display("[Engine] - Engine Output=0x%04x",i_opope_wrap.i_opope_top.i_engine.z_output_o[0]);
          // $display("[Engine] - Engine Output=0x%04x, 0x%04x, 0x%04x, 0x%04x, 0x%04x, 0x%04x, 0x%04x, 0x%04x, 0x%04x, 0x%04x, 0x%04x, 0x%04x, 0x%04x, 0x%04x, 0x%04x, 0x%04x, ", 
          //         i_opope_wrap.i_opope_top.i_engine.z_output_o[0],
          //         i_opope_wrap.i_opope_top.i_engine.z_output_o[1],
          //         i_opope_wrap.i_opope_top.i_engine.z_output_o[2],
          //         i_opope_wrap.i_opope_top.i_engine.z_output_o[3],
          //         i_opope_wrap.i_opope_top.i_engine.z_output_o[4],
          //         i_opope_wrap.i_opope_top.i_engine.z_output_o[5],
          //         i_opope_wrap.i_opope_top.i_engine.z_output_o[6],
          //         i_opope_wrap.i_opope_top.i_engine.z_output_o[7],
          //         i_opope_wrap.i_opope_top.i_engine.z_output_o[8],
          //         i_opope_wrap.i_opope_top.i_engine.z_output_o[9],
          //         i_opope_wrap.i_opope_top.i_engine.z_output_o[10],
          //         i_opope_wrap.i_opope_top.i_engine.z_output_o[11],
          //         i_opope_wrap.i_opope_top.i_engine.z_output_o[12],
          //         i_opope_wrap.i_opope_top.i_engine.z_output_o[13],
          //         i_opope_wrap.i_opope_top.i_engine.z_output_o[14],
          //         i_opope_wrap.i_opope_top.i_engine.z_output_o[15],
          //         );
          if(cnt%16 == 0) $display("----------------------------------");
        end
      end
    // ----------------------------------------------------------------------- 
      @(posedge clk_i);
  end
endmodule // opope_tb
