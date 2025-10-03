// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Danilo Cammarata <dcammarata@iis.ee.ethz.ch>
//

module opope_inst_decoder
  import opope_pkg::*;
  import cv32e40x_pkg::*;
#(
  parameter  int unsigned SysInstWidth  = 32            ,
  parameter  int unsigned SysDataWidth  = 32            ,
  parameter  int unsigned NumRfReadPrts = 2             ,
  parameter  int unsigned OpWidth       = 3             ,
  parameter  int unsigned FormatWidth   = 3             ,
  parameter  int unsigned OpCodeWidth   = 7             ,
  parameter  int unsigned NumCfgRegs    = 6             ,
  localparam int unsigned SizeLarge     = SysDataWidth/2,
  localparam int unsigned SizeSmall     = SysDataWidth/4
)(
  input  logic                     clk_i          ,
  input  logic                     rst_ni         ,
  input  logic                     clear_i        ,
  cv32e40x_if_xif.coproc_issue     xif_issue_if_i ,
  cv32e40x_if_xif.coproc_result    xif_result_if_o,
  cv32e40x_if_xif.coproc_compressed xif_compressed_if_i,
  cv32e40x_if_xif.coproc_mem        xif_mem_if_o,
  hwpe_ctrl_intf_periph.master     periph       ,
  input  logic                     cfg_complete_i ,
  output logic                     start_cfg_o
);

logic [OpCodeWidth-1:0] op_code;
logic [    OpWidth-1:0] operation_d;
logic [FormatWidth-1:0] format_d;
logic [NumCfgRegs-1:0][SysDataWidth-1:0] cfg_reg_d, cfg_reg_q;
logic is_gemm_d,
      widening_d,
      custom_fmt_d;
logic clk_en, clk_int;
logic cfg_ready;
logic count_rst, count_update;
logic [NumCfgRegs-1:0] reg_offs;

typedef enum logic [1:0] {
  Idle,
  WriteCfg,
  Trigger
} opopope_instr_cfg_state_e;

opopope_instr_cfg_state_e current, next;

// Xif static binding
assign xif_compressed_if_i.compressed_ready = 1'b0;
assign xif_compressed_if_i.compressed_resp  = '0;

assign xif_mem_if_o.mem_valid = 1'b0;
assign xif_mem_if_o.mem_req   = '0;

tc_clk_gating i_arith_clock_gating (
  .clk_i     ( clk_i   ),
  .en_i      ( clk_en  ),
  .test_en_i ( '0      ),
  .clk_o     ( clk_int )
);

assign op_code = xif_issue_if_i.issue_req.instr[OpCodeWidth-1:0];
assign xif_result_if_o.result_valid = (xif_result_if_o.result_ready) ? 1'b1 : 1'b0;
assign xif_result_if_o.result = '0;

always_comb begin: opcode_decoder
  clk_en       = '0;
  cfg_ready    = '0;
  cfg_reg_d    = cfg_reg_q;
  xif_issue_if_i.issue_ready = 1'b0;
  xif_issue_if_i.issue_resp = '0;
  is_gemm_d    = '0;
  widening_d   = '0;
  custom_fmt_d = '0;
  format_d     = '0;
  operation_d  = '0;

  if (xif_issue_if_i.issue_valid) begin
    case (op_code)
      MCNFIG: begin
        xif_issue_if_i.issue_ready = 1'b1;
        xif_issue_if_i.issue_resp.accept = 1'b1;
        clk_en = 1'b1 | clear_i;
        if (xif_issue_if_i.issue_req.rs_valid) begin
          // HalfWord[0] of Rs1 contains M size
          cfg_reg_d[3][SizeLarge-1:0] = xif_issue_if_i.issue_req.rs[0][SizeLarge-1:0];
          // BalfWord[1] of Rs1 contains K size
          cfg_reg_d[3][SysDataWidth-1:SizeLarge] = xif_issue_if_i.issue_req.rs[0][SysDataWidth-1:SizeLarge];
          // Rs2 contains N size
          cfg_reg_d[4] = xif_issue_if_i.issue_req.rs[1];
        end
      end

      MARITH: begin
        xif_issue_if_i.issue_ready = 1'b1;
        xif_issue_if_i.issue_resp.accept = 1'b1;
        clk_en = 1'b1 | clear_i;
        cfg_reg_d[5] = xif_issue_if_i.issue_req.instr; // Arithmetic instruction
        if (xif_issue_if_i.issue_req.rs_valid) begin
          cfg_ready = 1'b1;
          cfg_reg_d[0] = xif_issue_if_i.issue_req.rs[0]; // Rs1 contains X start pointer
          cfg_reg_d[1] = xif_issue_if_i.issue_req.rs[1]; // Rs2 contains W start pointer
          cfg_reg_d[2] = xif_issue_if_i.issue_req.rs[2]; // Rs3 contains Z start pointer
        end
      end

      /* The core will try to offload all CSR instructions to the coupled co-processor, so we need to
         check if the offloaded CSR instruction tries to access one of the CSRs available in O-POPE or
         not. If not, we need to raise the issue_ready to signal that we received the offload request,
         but keep the issue_resp.accept low to signal that we are not accepting the instruction.
         For furhter details, look at the CORE-V Extension Interface documentation
         (https://docs.openhwgroup.org/projects/openhw-group-core-v-xif/en/latest/x_ext.html#issue-interface)
         and at the following issue: https://github.com/openhwgroup/cv32e40x/issues/945. */
      RVCSR: begin
      xif_issue_if_i.issue_ready = 1'b1;
        if (xif_issue_if_i.issue_req.instr[31:20] <= CSR_OPOPE_MACFG &&
            xif_issue_if_i.issue_req.instr[31:20] >= CSR_OPOPE_MACFG) begin
          xif_issue_if_i.issue_resp.accept = 1'b1;
        end else begin
          xif_issue_if_i.issue_resp.accept = 1'b0;
        end
      end
    endcase
  end
end

always_ff @(posedge clk_int, negedge rst_ni) begin : arith_pipe
  if (~rst_ni) begin
    cfg_reg_q <= '0;
  end else begin
    if (clear_i) begin
      cfg_reg_q <= '0;
    end else begin
      cfg_reg_q <= cfg_reg_d;
    end
  end
end

always_ff @(posedge clk_i, negedge rst_ni) begin : slave_cfg
  if (~rst_ni) begin
    current <= Idle;
  end else begin
    if (clear_i)
      current <= Idle;
    else
      current <= next;
  end
end

always_ff @(posedge clk_i, negedge rst_ni) begin : ptrs_counter
  if (~rst_ni) begin
    reg_offs <= '0;
  end else begin
    if (clear_i | count_rst)
      reg_offs <= '0;
    else if (count_update)
      reg_offs <= reg_offs + 1;
  end
end

always_comb begin : cfg_fsm
  count_rst    = '0;
  count_update = '0;
  next       = current;
  periph.req  = '0;
  periph.wen  = '0;
  periph.be   = '0;
  periph.add  = '0;
  periph.id   = '0;
  periph.data = '0;
  start_cfg_o = 1'b0;

  case (current)
    Idle: begin
      if (cfg_ready)
        next = WriteCfg;
    end

    WriteCfg: begin
      periph.req  = 1'b1;
      periph.wen  = 1'b0;
      periph.be   = '1;
      periph.add  = 'h40 + 4*reg_offs;
      periph.id   = '0;
      periph.data = cfg_reg_q[reg_offs];
      if (periph.gnt) begin
        count_update = 1'b1;
        if (reg_offs == NumCfgRegs - 1) begin
          next = Trigger;
          start_cfg_o = 1'b1;
          count_rst = 1'b1;
        end
      end
    end

    Trigger: begin
      if (cfg_complete_i) begin
        periph.req  = 1'b1;
        periph.wen  = 1'b0;
        periph.be   = '1;
        periph.add  = '0;
        periph.id   = '0;
        periph.data = '0;

        if (periph.gnt)
          next = Idle;
      end
    end
  endcase
end

endmodule: opope_inst_decoder
