// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Description: Address scrambler for iDMA Midend, scramble scheme is determined
// by tiles_das
// Current constraints:

// Author: Bowen Wang <bowwang@student.ethz.ch>
// Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

module idma_address_scrambler #(
  parameter int unsigned AddrWidth         = 32,
  parameter int unsigned DataWidth         = 32,
  parameter int unsigned ByteOffset        = 2,
  parameter bit          Bypass            = 0,
  parameter int unsigned NumTiles          = 128,
  parameter int unsigned NumBanksPerTile   = 32,
  parameter int unsigned TCDMSizePerBank   = 1024,
  parameter int unsigned RowsInterleavingWidth = $clog2(TCDMSizePerBank) - ByteOffset,
  parameter int unsigned NumDASPartitions  = 4,
  parameter int unsigned DASStartAddr      = 1024,
  parameter int unsigned MemSizePerTile    = NumBanksPerTile*TCDMSizePerBank,
  parameter int unsigned MemSizePerRow     = (1 << ByteOffset)*NumBanksPerTile*NumTiles
) (
  input  logic [AddrWidth-1:0]                            address_i,
  input  logic [31:0]                                     num_bytes_i,
  input  logic [NumDASPartitions-1:0][$clog2(NumTiles):0] tiles_das_i,
  input  logic [NumDASPartitions-1:0][RowsInterleavingWidth-1:0] rows_das_i,
  input  logic [NumDASPartitions-1:0][DataWidth-1:0]      start_das_i,
  output logic [$clog2(NumTiles):0]                       tiles_das_o,
  output logic [RowsInterleavingWidth:0]                  rows_das_o,
  output logic [AddrWidth-1:0]                            address_o
);
  // Basic Settings
  localparam int unsigned BankOffsetBits    = $clog2(NumBanksPerTile);
  localparam int unsigned TileIdBits        = $clog2(NumTiles);
  localparam int unsigned ConstantBitsLSB   = ByteOffset + BankOffsetBits;

  if (Bypass || NumTiles < 2) begin
    assign address_o = address_i;
  end else begin

    // ------ Heap Sequential Signals ------ //

    // `tile_index` : how many bits to shift for TileID bits in each partition
    // `row_index`: how many bits need to swap within Row Index
    logic [NumDASPartitions-1:0][$clog2($clog2(NumTiles)+1)-1:0] tile_index;
    logic [NumDASPartitions-1:0][$clog2(RowsInterleavingWidth)-1:0] row_index;

    for (genvar i = 0; i < NumDASPartitions; i++) begin : gen_shift_index
      lzc #(
        .WIDTH ($clog2(NumTiles)+1),
        .MODE  (1'b0              )
      ) i_log_tile_index (
        .in_i    (tiles_das_i[i]),
        .cnt_o   (tile_index[i]    ),
        .empty_o (/* Unused */     )
      );
      lzc #(
        .WIDTH (RowsInterleavingWidth),
        .MODE  (1'b0            )
      ) i_log_row_index (
        .in_i    (rows_das_i[i]),
        .cnt_o   (row_index[i] ),
        .empty_o (/* Unused */  )
      );
    end

    always_comb begin

      // Default: Unscrambled
      address_o = address_i;
      tiles_das_o   = '0;
      rows_das_o = '0;

      // TODO (bowwang): add a new register to indicate the start addr of sequential heap region, currently hard coded
      if (address_i < DASStartAddr) begin
        tiles_das_o   = NumTiles; // fully interleaved
        rows_das_o = num_bytes_i / MemSizePerRow;

      // DAS address scrambling
      end else begin

        for (int p = 0; p < NumDASPartitions; p++) begin
          if ( (address_i >= start_das_i[p]) && (address_i < start_das_i[p]+MemSizePerRow*rows_das_i[p]) ) begin
            address_o = '0;
            address_o |= address_i & ((1 << (tile_index[p]+ConstantBitsLSB)) - 1);
            address_o |= ((address_i >> (row_index[p]+tile_index[p]+ConstantBitsLSB)) << (tile_index[p]+ConstantBitsLSB)) & ((1 << (TileIdBits+ConstantBitsLSB)) - 1);
            address_o |= ((address_i >> (tile_index[p]+ConstantBitsLSB)) << (TileIdBits + ConstantBitsLSB)) & ((1 << (row_index[p]+TileIdBits+ConstantBitsLSB)) - 1);
            address_o |= address_i & ~((1 << (row_index[p]+TileIdBits+ConstantBitsLSB)) - 1);
            tiles_das_o   = tiles_das_i[p];
            rows_das_o = rows_das_i[p];
          end
        end

      end
    end

  end

  // Check for unsupported configurations
  if (NumBanksPerTile < 2)
    $fatal(1, "NumBanksPerTile must be greater than 2. The special case '1' is currently not supported!");

endmodule : idma_address_scrambler
