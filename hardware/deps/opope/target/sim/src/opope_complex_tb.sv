// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Danilo Cammarata <dcammarata@iis.ee.ethz.ch>
//

timeunit 1ps; timeprecision 1ps;

module opope_tb
  import opope_pkg::*;
#(
  parameter TCP = 1.0ns, // clock period, 1 GHz clock
  parameter TA  = 0.2ns, // application time
  parameter TT  = 0.8ns  // test time
)(
  input logic clk_i,
  input logic rst_ni,
  input logic fetch_enable_i
);

  // parameters
  localparam int unsigned PROB_STALL = 0;
  localparam int unsigned NC = 1;
  localparam int unsigned ID = 10;
  localparam int unsigned DW = opope_pkg::DATA_W;
  localparam int unsigned MP = DW/32;
  localparam int unsigned MEMORY_SIZE = 192*1024;
  localparam int unsigned STACK_MEMORY_SIZE = 192*1024;
  localparam int unsigned PULP_XPULP = 1;
  localparam int unsigned FPU = 0;
  localparam int unsigned PULP_ZFINX = 0;
  localparam logic [31:0] BASE_ADDR = 32'h1c000000;
  localparam logic [31:0] HWPE_ADDR_BASE_BIT = 20;

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
  logic [MP-1:0][31:0] tcdm_r_data;
  logic [MP-1:0]       tcdm_r_valid;
  logic                tcdm_r_opc;
  logic                tcdm_r_user;
   
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

  typedef struct packed {
    logic        req;
    logic [31:0] addr;
  } core_inst_req_t;

  typedef struct packed {
    logic        gnt;
    logic        valid;
    logic [31:0] data;
  } core_inst_rsp_t;

  typedef struct packed {
    logic req;
    logic we;
    logic [3:0] be;
    logic [31:0] addr;
    logic [31:0] data;
  } core_data_req_t;

  typedef struct packed {
    logic gnt;
    logic valid;
    logic [31:0] data;
  } core_data_rsp_t;

  hci_core_intf #(.DW(DW)) opope_tcdm (.clk(clk_i));

  core_inst_req_t core_inst_req;
  core_inst_rsp_t core_inst_rsp;

  core_data_req_t core_data_req;
  core_data_rsp_t core_data_rsp;

  // bindings
  always_comb begin : bind_periph
    periph_req     = '0;
    periph_add     = core_data_req.addr;
    periph_wen     = ~core_data_req.we;
    periph_be      = core_data_req.be;
    periph_data    = core_data_req.data;
    periph_id      = '0;
    periph_r_valid = '0;
  end

  always_comb begin : bind_instrs
    instr[0].req  = core_inst_req.req;
    instr[0].add  = core_inst_req.addr;
    instr[0].wen  = 1'b1;
    instr[0].be   = '0;
    instr[0].data = '0;
    core_inst_rsp.gnt   = instr[0].gnt;
    core_inst_rsp.valid = instr[0].r_valid;
    core_inst_rsp.data  = instr[0].r_data;
  end

  always_comb begin : bind_stack
    stack[0].req  = core_data_req.req & (core_data_req.addr[31:24] == '0) &
                    ~core_data_req.addr[HWPE_ADDR_BASE_BIT];
    stack[0].add  = core_data_req.addr;
    stack[0].wen  = ~core_data_req.we;
    stack[0].be   = core_data_req.be;
    stack[0].data = core_data_req.data;
  end

  logic other_r_valid;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni)
      other_r_valid <= '0;
    else
      other_r_valid <= core_data_req.req & (core_data_req.addr[31:24] == 8'h80);
  end

  for(genvar ii=0; ii<MP; ii++) begin : tcdm_binding
    assign tcdm[ii].req  = opope_tcdm.req;
    assign tcdm[ii].add  = opope_tcdm.add + ii*4;
    assign tcdm[ii].wen  = opope_tcdm.wen;
    assign tcdm[ii].be   = opope_tcdm.be[(ii+1)*4-1:ii*4];
    assign tcdm[ii].data = opope_tcdm.data[(ii+1)*32-1:ii*32];
    assign tcdm_gnt[ii]     = tcdm[ii].gnt;
    assign tcdm_r_valid[ii] = tcdm[ii].r_valid;
    assign tcdm_r_data[ii]  = tcdm[ii].r_data;
  end
  assign opope_tcdm.gnt     = &tcdm_gnt;
  assign opope_tcdm.r_data  = { >> {tcdm_r_data} };
  assign opope_tcdm.r_valid = &tcdm_r_valid;
  assign opope_tcdm.r_opc   = '0;
  assign opope_tcdm.r_user  = '0;

  assign tcdm[MP].req  = core_data_req.req &
                         (core_data_req.addr[31:24] != '0) &
                         (core_data_req.addr[31:24] != 8'h80) &
                         ~core_data_req.addr[HWPE_ADDR_BASE_BIT];
  assign tcdm[MP].add  = core_data_req.addr;
  assign tcdm[MP].wen  = ~core_data_req.we;
  assign tcdm[MP].be   = core_data_req.be;
  assign tcdm[MP].data = core_data_req.data;

  assign core_data_rsp.gnt = periph_req ?
                             periph_gnt : stack[0].req ?
                                          stack[0].gnt : tcdm[MP].req ?
                                                         tcdm[MP].gnt : '1;

  assign core_data_rsp.data = periph_r_valid   ? periph_r_data    :
                              stack[0].r_valid ? stack[0].r_data  :
                                                 tcdm[MP].r_valid ? tcdm[MP].r_data : '0;
  assign core_data_rsp.valid = periph_r_valid   |
                               stack[0].r_valid |
                               tcdm[MP].r_valid |
                               other_r_valid    ;

  tb_dummy_memory  #(
    .MP             ( MP + 1        ),
    .MEMORY_SIZE    ( MEMORY_SIZE   ),
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

  opope_complex #(
    .CoreType           ( opope_pkg::CV32X  ), // CV32E40P, CV32E40X, IBEX, SNITCH, CVA6
    .ID_WIDTH           ( ID                  ),
    .N_CORES            ( NC                  ),
    .DW                 ( DW                  ), // TCDM port dimension (in bits)
    .MP                 ( DW/32               ),
    .NumIrqs            ( 0                   ),
    .AddrWidth          ( 32                  ),
    .core_data_req_t    ( core_data_req_t     ),
    .core_data_rsp_t    ( core_data_rsp_t     ),
    .core_inst_req_t    ( core_inst_req_t     ),
    .core_inst_rsp_t    ( core_inst_rsp_t     )
  ) i_dut               (
    .clk_i              ( clk_i            ),
    .rst_ni             ( rst_ni           ),
    .test_mode_i        ( test_mode        ),
    .fetch_enable_i     ( fetch_enable_i   ),
    .boot_addr_i        ( core_boot_addr   ),
    .irq_i              ( '0               ),
    .irq_id_o           (                  ),
    .irq_ack_o          (                  ),
    .core_sleep_o       ( core_sleep       ),
    .core_inst_rsp_i    ( core_inst_rsp    ),
    .core_inst_req_o    ( core_inst_req    ),
    .core_data_rsp_i    ( core_data_rsp    ),
    .core_data_req_o    ( core_data_req    ),
    .tcdm               ( opope_tcdm     )
  );

  integer f_x, f_W, f_y, f_tau;
  logic start;

  int errors = -1;
  always_ff @(posedge clk_i)
  begin
    if((core_data_req.addr == 32'h80000000 ) &&
       (core_data_req.we & core_data_req.req == 1'b1)) begin
      errors = core_data_req.data;
    end
    if((core_data_req.addr == 32'h80000004 ) &&
       (core_data_req.we & core_data_req.req == 1'b1)) begin
      $write("%c", core_data_req.data);
    end
  end

  initial begin
    integer id;
    int cnt_rd, cnt_wr;

    if (!$value$plusargs("STIM_INSTR=%s", stim_instr)) stim_instr = "../../../sw/build/stim_instr.txt";
    if (!$value$plusargs("STIM_DATA=%s", stim_data)) stim_data = "../../../sw/build/stim_data.txt";

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

    $display("[TB] - cnt_rd=%-8d", cnt_rd);
    $display("[TB] - cnt_wr=%-8d", cnt_wr);
    if(errors != 0) begin
      $display("[TB] - Fail!");
      $error("[TB] - errors=%08x", errors);
    end else begin
      $display("[TB] - Success!");
      $display("[TB] - errors=%08x", errors);
    end
    $finish;
  end

endmodule // opope_tb
