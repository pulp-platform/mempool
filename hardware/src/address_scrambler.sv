// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Description: Scrambles the address in such a way, that part of the memory is accessed
// sequentially and part is interleaved.
// Current constraints:

// Author: Samuel Riedel <sriedel@iis.ee.ethz.ch>
// Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

module address_scrambler #(
  parameter int unsigned AddrWidth         = 32,
  parameter int unsigned DataWidth         = 32,
  parameter int unsigned ByteOffset        = 2,
  parameter bit          Bypass            = 0,
  parameter int unsigned NumTiles          = 2,
  parameter int unsigned NumBanksPerTile   = 2,
  parameter int unsigned TCDMSizePerBank   = 1024,
  parameter int unsigned SeqMemSizePerTile = 4096,
  parameter int unsigned NumDASPartitions  = 4,
  // Dependant parameters, do not change
  parameter int unsigned RowsWidth            = $clog2(TCDMSizePerBank) - ByteOffset + 1,
  parameter int unsigned MaxPartitionRowWidth = $clog2(TCDMSizePerBank) - ByteOffset,     // maximum half of L1
  parameter int unsigned MemSizePerTile       = NumBanksPerTile*TCDMSizePerBank,
  parameter int unsigned MemSizePerRow        = (1 << ByteOffset)*NumBanksPerTile*NumTiles
) (
  input  logic [AddrWidth-1:0]                                       address_i,
  input  logic [NumDASPartitions-1:0][$clog2(NumTiles):0]            tiles_das_i,
  input  logic [NumDASPartitions-1:0][AddrWidth-1:0]                 start_das_i,
  input  logic [NumDASPartitions-1:0][MaxPartitionRowWidth-1:0]      rows_das_i,
  output logic [AddrWidth-1:0]                                       address_o
);
  // Stack Sequential Settings
  localparam int unsigned BankOffsetBits    = $clog2(NumBanksPerTile);
  localparam int unsigned TileIdBits        = $clog2(NumTiles);
  localparam int unsigned SeqPerTileBits    = $clog2(SeqMemSizePerTile);
  localparam int unsigned SeqTotalBits      = SeqPerTileBits+TileIdBits;
  localparam int unsigned ConstantBitsLSB   = ByteOffset + BankOffsetBits;
  localparam int unsigned ScrambleBits      = SeqPerTileBits-ConstantBitsLSB;

  if (Bypass || NumTiles < 2) begin: gen_bypass
    assign address_o = address_i;

  end else begin: gen_scrambling
    // ------ Stack Region Logic ------ //
    logic [ScrambleBits-1:0]    scramble;    // Address bits that have to be shuffled around
    logic [TileIdBits-1:0]      tile_id;     // Which tile does  this address region belong to

    // Scramble the middle part
    // Bits that would have gone to different tiles but now go to increasing lines in the same tile
    assign scramble = address_i[SeqPerTileBits-1:ConstantBitsLSB]; // Bits that would
    // Bits that would have gone to increasing lines in the same tile but now go to different tiles
    assign tile_id  = address_i[SeqTotalBits-1:SeqPerTileBits];

    // ------ Heap Sequential Signals ------ //

    // `tile_bits` : how many fixed TileID bits
    // `row_bits`  : how many bits need to swap to the start of Row Index
    logic [NumDASPartitions-1:0][$clog2($clog2(NumTiles)+1)-1:0]   tile_bits;
    logic [NumDASPartitions-1:0][$clog2(MaxPartitionRowWidth)-1:0] row_bits;

    for (genvar i = 0; i < NumDASPartitions; i++) begin : gen_shift_index
      lzc #(
        .WIDTH   ($clog2(NumTiles)+1 ),
        .MODE    (1'b0               )
      ) i_log_tile_bits (
        .in_i    (tiles_das_i[i] ),
        .cnt_o   (tile_bits[i]       ),
        .empty_o (/* Unused */       )
      );
      lzc #(
        .WIDTH   (MaxPartitionRowWidth ),
        .MODE    (1'b0                 )
      ) i_log_row_bits (
        .in_i    (rows_das_i[i]        ),
        .cnt_o   (row_bits[i]          ),
        .empty_o (/* Unused */         )
      );
    end

    logic [NumDASPartitions-1:0][AddrWidth-1:0] lsb_addr;
    logic [NumDASPartitions-1:0][AddrWidth-1:0] row_addr;
    logic [NumDASPartitions-1:0][AddrWidth-1:0] prt_addr;
    logic [NumDASPartitions-1:0][AddrWidth-1:0] msb_addr;
    logic [NumDASPartitions-1:0][AddrWidth-1:0] aligned_addr;

    // Narrow row-index field signals (MaxPartitionRowWidth-bit) to replace the
    // 32-bit adders that were on the critical path. Only the row-index bits at
    // [TileIdBits+ConstantBitsLSB +: MaxPartitionRowWidth] are affected by the
    // subtract/add — all other bits pass through unchanged.
    localparam int unsigned RowFieldLSB = TileIdBits + ConstantBitsLSB;
    logic [NumDASPartitions-1:0][MaxPartitionRowWidth-1:0] start_row_field;

    always_comb begin

      // Default: Unscrambled
      address_o = address_i;

      // Stack Region
      if (address_i < (NumTiles * SeqMemSizePerTile)) begin: gen_stack_scrambling
        address_o[ConstantBitsLSB-1:0] = address_i[ConstantBitsLSB-1:0];
        address_o[SeqTotalBits-1:ConstantBitsLSB] = {scramble, tile_id};
        address_o[AddrWidth-1:SeqTotalBits] = address_i[AddrWidth-1:SeqTotalBits];

      // DAS address scrambling
      end else begin: gen_das_scrambling

        for (int p = 0; p < NumDASPartitions; p++) begin
          if ( (address_i >= start_das_i[p]) && (address_i < start_das_i[p]+MemSizePerRow*rows_das_i[p]) && (tiles_das_i[p] != NumTiles) ) begin

            lsb_addr[p]       = address_i & ((1 << (tile_bits[p]+ConstantBitsLSB)) - 1);
            msb_addr[p]       = address_i & ~((1 << (row_bits[p]+TileIdBits+ConstantBitsLSB)) - 1);

            // Narrow subtract: extract the row-index field from the partition
            // start address (masked to row_bits width via rows_das-1), then
            // subtract from the address row field to get the partition-relative
            // row index. Only MaxPartitionRowWidth bits (~8 bits) instead of 32.
            start_row_field[p] = start_das_i[p][RowFieldLSB +: MaxPartitionRowWidth]
                                 & (rows_das_i[p] - 1);
            aligned_addr[p]    = address_i;
            aligned_addr[p][RowFieldLSB +: MaxPartitionRowWidth] =
                address_i[RowFieldLSB +: MaxPartitionRowWidth] - start_row_field[p];

            prt_addr[p]     = (aligned_addr[p] >> row_bits[p]                )  & (((1 << (TileIdBits - tile_bits[p])) - 1) << (ConstantBitsLSB + tile_bits[p]));
            row_addr[p]     = (aligned_addr[p] << (TileIdBits - tile_bits[p]))  & (((1 << (row_bits[p])              ) - 1) << (TileIdBits + ConstantBitsLSB  ));
            address_o       = msb_addr[p] | row_addr[p] | prt_addr[p] | lsb_addr[p];

            // Narrow add: restore the absolute row-index offset.
            // Only the row-index field is modified — MSB and LSB bits are
            // already correct from msb_addr and lsb_addr.
            address_o[RowFieldLSB +: MaxPartitionRowWidth] =
                address_o[RowFieldLSB +: MaxPartitionRowWidth] + start_row_field[p];

          end
        end

      end
    end
  end

  // Check for unsupported configurations
  if (NumBanksPerTile < 2)
    $fatal(1, "NumBanksPerTile must be greater than 2. The special case '1' is currently not supported!");
  if (SeqMemSizePerTile % (2**ByteOffset*NumBanksPerTile) != 0)
    $fatal(1, "SeqMemSizePerTile must be a multiple of BankWidth*NumBanksPerTile!");
endmodule : address_scrambler
