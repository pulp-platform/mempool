// Copyright 2024 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "axi/assign.svh"
`include "common_cells/registers.svh"


module axi_L2_interleaver
  import mempool_pkg::*;
#(
  parameter int NumAXIMasters   = 1,
  parameter int NumL2           = 16,
  parameter int L2Size          = 16777216
) (
  input logic clk_i,
  input logic rst_ni,
  // Slave interfaces (original unmodified requests and responses)
  input  axi_tile_req_t  [NumAXIMasters-1:0] axi_l2_req_i,
  output axi_tile_resp_t [NumAXIMasters-1:0] axi_l2_resp_o,
  // Master interfaces (interleaved and splitted requests and responses)
  output axi_tile_req_t  [NumAXIMasters-1:0] axi_l2_req_interleaved_o,
  input  axi_tile_resp_t [NumAXIMasters-1:0] axi_l2_resp_interleaved_i
);

  // Local parameters for address manipulation
  localparam int unsigned LSBConstantBits = $clog2(L2BankBeWidth * Interleave);
  localparam int unsigned MSBConstantBits = 32 - $clog2(L2Size);
  localparam int unsigned ScrambleBits    = (NumL2 == 1) ? 1 : $clog2(NumL2);
  localparam int unsigned ReminderBits    = AddrWidth - ScrambleBits - LSBConstantBits - MSBConstantBits;

  // Logic variables for address scrambling
  logic [NumAXIMasters-1:0][LSBConstantBits-1:0] aw_lsb_const;
  logic [NumAXIMasters-1:0][MSBConstantBits-1:0] aw_msb_const;
  logic [NumAXIMasters-1:0][ScrambleBits-1:0   ] aw_scramble;
  logic [NumAXIMasters-1:0][ReminderBits-1:0   ] aw_reminder;
  logic [NumAXIMasters-1:0][AddrWidth-1:0      ] aw_scramble_addr;

  logic [NumAXIMasters-1:0][LSBConstantBits-1:0] ar_lsb_const;
  logic [NumAXIMasters-1:0][MSBConstantBits-1:0] ar_msb_const;
  logic [NumAXIMasters-1:0][ScrambleBits-1:0   ] ar_scramble;
  logic [NumAXIMasters-1:0][ReminderBits-1:0   ] ar_reminder;
  logic [NumAXIMasters-1:0][AddrWidth-1:0      ] ar_scramble_addr;

  // Address scrambling logic
  for (genvar i = 0; i < NumAXIMasters; i++) begin : addr_scrambler
    always_comb begin
      axi_l2_req_interleaved_o[i] = axi_l2_req_i[i];
      axi_l2_resp_o[i]            = axi_l2_resp_interleaved_i[i];

      // Default assignments for scrambled addresses
      aw_scramble_addr[i] = axi_l2_req_interleaved_o[i].aw.addr;
      ar_scramble_addr[i] = axi_l2_req_interleaved_o[i].ar.addr;

      // AW Channel
      if ((axi_l2_req_interleaved_o[i].aw.addr >= 32'h80000000) && (axi_l2_req_interleaved_o[i].aw.addr < 32'h90000000)) begin
        // Decompose address for scrambling
        aw_lsb_const[i]     = axi_l2_req_interleaved_o[i].aw.addr[LSBConstantBits-1 : 0];
        aw_msb_const[i]     = axi_l2_req_interleaved_o[i].aw.addr[AddrWidth-1 -: MSBConstantBits];
        aw_scramble[i]      = axi_l2_req_interleaved_o[i].aw.addr[ScrambleBits+LSBConstantBits-1 : LSBConstantBits];
        aw_reminder[i]      = axi_l2_req_interleaved_o[i].aw.addr[AddrWidth-MSBConstantBits-1 : ScrambleBits+LSBConstantBits];
        aw_scramble_addr[i] = {aw_msb_const[i], aw_scramble[i], aw_reminder[i], aw_lsb_const[i]};
        // Assign scrambled address back to request
        axi_l2_req_interleaved_o[i].aw.addr = aw_scramble_addr[i];
      end

      // AR Channel
      if ((axi_l2_req_interleaved_o[i].ar.addr >= 32'h80000000) && (axi_l2_req_interleaved_o[i].ar.addr < 32'h90000000)) begin
        // Decompose address for scrambling
        ar_lsb_const[i]     = axi_l2_req_interleaved_o[i].ar.addr[LSBConstantBits-1 : 0];
        ar_msb_const[i]     = axi_l2_req_interleaved_o[i].ar.addr[AddrWidth-1 -: MSBConstantBits];
        ar_scramble[i]      = axi_l2_req_interleaved_o[i].ar.addr[ScrambleBits+LSBConstantBits-1 : LSBConstantBits];
        ar_reminder[i]      = axi_l2_req_interleaved_o[i].ar.addr[AddrWidth-MSBConstantBits-1 : ScrambleBits+LSBConstantBits];
        ar_scramble_addr[i] = {ar_msb_const[i], ar_scramble[i], ar_reminder[i], ar_lsb_const[i]};
        // Assign scrambled address back to request
        axi_l2_req_interleaved_o[i].ar.addr = ar_scramble_addr[i];
      end
    end
  end

endmodule
