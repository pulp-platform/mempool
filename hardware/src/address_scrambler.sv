// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Description: Scrambles the address in such a way, that part of the memory is accessed
// sequentially and part is interleaved.
// Current constraints:

// Author: Samuel Riedel <sriedel@iis.ee.ethz.ch>

module address_scrambler #(
  parameter int unsigned AddrWidth         = 32,
  parameter int unsigned ByteOffset        = 2,
  parameter int unsigned NumTiles          = 2,
  parameter int unsigned NumBanksPerTile   = 2,
  parameter bit          Bypass            = 0,
  parameter int unsigned SeqMemSizePerTile = 4*1024
) (
  input  logic [AddrWidth-1:0] address_i,
  output logic [AddrWidth-1:0] address_o
);
  localparam int unsigned BankOffsetBits    = $clog2(NumBanksPerTile);
  localparam int unsigned TileIdBits        = $clog2(NumTiles);// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Description: Scrambles the address in such a way, that part of the memory is accessed
// sequentially and part is interleaved.
// Current constraints:

// Author: Samuel Riedel <sriedel@iis.ee.ethz.ch>

module address_scrambler #(
  parameter int unsigned AddrWidth         = 32,
  parameter int unsigned DataWidth         = 32,
  parameter int unsigned ByteOffset        = 2,
  parameter int unsigned NumTiles          = 2,
  parameter int unsigned NumBanksPerTile   = 2,
  parameter bit          Bypass            = 0,
  parameter int unsigned SeqMemSizePerTile = 4*1024,
  parameter int unsigned HeapSeqMemSizePerTile = 8*2048,
  parameter int unsigned MemSizePerTile = 8*4*1024,
  parameter int unsigned MemSizePerRow  = 4*4*1024,  // 4bytes * 4096 banks
  parameter int unsigned TCDMSize = 1024*1024
) (
  input  logic [AddrWidth-1:0] address_i,
  input  logic [3:0][7:0]           group_factor_i,
  // For each allocation, the maximum number of rows assigned can be 128 rows
  input  logic [3:0][7:0]           allocated_size_i,
  input  logic [3:0][DataWidth-1:0] start_addr_scheme_i,
  output logic [AddrWidth-1:0] address_o
);
  // Stack Sequential Settings
  localparam int unsigned BankOffsetBits    = $clog2(NumBanksPerTile);
  localparam int unsigned TileIdBits        = $clog2(NumTiles);
  localparam int unsigned SeqPerTileBits    = $clog2(SeqMemSizePerTile);
  localparam int unsigned SeqTotalBits      = SeqPerTileBits+TileIdBits;
  localparam int unsigned ConstantBitsLSB   = ByteOffset + BankOffsetBits;
  localparam int unsigned ScrambleBits      = SeqPerTileBits-ConstantBitsLSB;

  // Heap Sequential Settings
  localparam int unsigned HeapSeqPerTileBits = $clog2(MemSizePerTile);             // log2(8*4096) = 15 | RowIndexBits + ConstBits
  localparam int unsigned HeapSeqTotalBits   = HeapSeqPerTileBits+TileIdBits;      // 15+7=22           | used for address_o assignment 
  localparam int unsigned RowIndexBits       = HeapSeqPerTileBits-ConstantBitsLSB; // 15-7=8            | RowIndex
  

  if (Bypass || NumTiles < 2) begin
    assign address_o = address_i;
  end else begin
    // ------ Stack Region Logic ------ //
    logic [ScrambleBits-1:0]    scramble;    // Address bits that have to be shuffled around
    logic [TileIdBits-1:0]      tile_id;     // Which tile does  this address region belong to

    // Scramble the middle part
    // Bits that would have gone to different tiles but now go to increasing lines in the same tile
    assign scramble = address_i[SeqPerTileBits-1:ConstantBitsLSB]; // Bits that would
    // Bits that would have gone to increasing lines in the same tile but now go to different tiles
    assign tile_id  = address_i[SeqTotalBits-1:SeqPerTileBits];

    // ------ Heap Sequential Signals ------ //
    
    // `shift_index`   : how many bits to shift for TileID bits in each partition
    // `shift_index_sc`: how many bits need to swap within Row Index 
    logic [3:0][2:0] shift_index; 
    logic [3:0][2:0] shift_index_sc;
    for (genvar i = 0; i < 4; i++) begin : gen_shift_index
        always_comb begin
            case(group_factor_i[i])
                128: shift_index[i] = 7;
                64:  shift_index[i] = 6;
                32:  shift_index[i] = 5;
                16:  shift_index[i] = 4;
                8:   shift_index[i] = 3;
                4:   shift_index[i] = 2;
                2:   shift_index[i] = 1;
                default: shift_index[i] = 0;
            endcase

            case(allocated_size_i[i])
                128: shift_index_sc[i] = 7;
                64:  shift_index_sc[i] = 6;
                32:  shift_index_sc[i] = 5;
                16:  shift_index_sc[i] = 4;
                8:   shift_index_sc[i] = 3;
                4:   shift_index_sc[i] = 2;
                2:   shift_index_sc[i] = 1;
                default: shift_index_sc[i] = 0;
            endcase
        end
    end


    // post-scramble row index
    logic [RowIndexBits-1:0]      post_scramble_row_index;
    logic [TileIdBits-1:0]        post_scramble_tile_id;

    logic [3:0][RowIndexBits-1:0] mask_row_index, mask_row_index_n;
    logic [3:0][TileIdBits-1:0]   mask_tile_id,   mask_tile_id_n;

    logic [TileIdBits-1:0]        heap_tile_id;

    for (genvar j = 0; j < 4; j++) begin : gen_mask
      assign mask_row_index[j] = (shift_index_sc[j] == 0) ? {RowIndexBits{1'b0}} : ({RowIndexBits{1'b1}} >> (RowIndexBits-shift_index_sc[j]));
      assign mask_tile_id[j]   = (shift_index[j] == 0)    ? {TileIdBits{1'b0}}   : ({TileIdBits{1'b1}}   >> (TileIdBits  -shift_index[j]));
      
      assign mask_row_index_n[j] = ~mask_row_index[j];
      assign mask_tile_id_n[j]   = ~mask_tile_id[j];
    end

    assign heap_tile_id = address_i[(TileIdBits+ConstantBitsLSB-1):ConstantBitsLSB];

    always_comb begin
      // Default: Unscrambled
      address_o[ConstantBitsLSB-1:0] = address_i[ConstantBitsLSB-1:0];
      address_o[SeqTotalBits-1:ConstantBitsLSB] = {tile_id, scramble};
      address_o[AddrWidth-1:SeqTotalBits] = address_i[AddrWidth-1:SeqTotalBits];
      post_scramble_row_index  = 'b0;
      post_scramble_tile_id    = 'b0;

      // Stack Region
      if (address_i < (NumTiles * SeqMemSizePerTile)) begin
        address_o[SeqTotalBits-1:ConstantBitsLSB] = {scramble, tile_id};

      // Sequential Heap Region 
      end else if ( (address_i >= start_addr_scheme_i[0]) && (address_i < start_addr_scheme_i[0]+MemSizePerRow*allocated_size_i[0]) ) begin

        post_scramble_row_index  = 'b0;
        post_scramble_tile_id    = 'b0;
        // 1. `post_scramble_row_index` generation
        post_scramble_row_index |= (address_i >> (ConstantBitsLSB + shift_index[0])) & mask_row_index[0];
        post_scramble_row_index |= (address_i >> (ConstantBitsLSB + TileIdBits    )) & mask_row_index_n[0];

        // 2. `post_scramble_tile_id` generation
        post_scramble_tile_id   |= heap_tile_id & mask_tile_id[0];
        post_scramble_tile_id   |= (address_i >> (ConstantBitsLSB + shift_index_sc[0])) & mask_tile_id_n[0];

        address_o[HeapSeqTotalBits-1:ConstantBitsLSB] = {post_scramble_row_index, post_scramble_tile_id};
      end else if ( (address_i >= start_addr_scheme_i[1]) && (address_i < start_addr_scheme_i[1]+MemSizePerRow*allocated_size_i[1]) ) begin

        post_scramble_row_index  = 'b0;
        post_scramble_tile_id    = 'b0;
        // 1. `post_scramble_row_index` generation
        post_scramble_row_index |= (address_i >> (ConstantBitsLSB + shift_index[1])) & mask_row_index[1];
        post_scramble_row_index |= (address_i >> (ConstantBitsLSB + TileIdBits    )) & mask_row_index_n[1];

        // 2. `post_scramble_tile_id` generation
        post_scramble_tile_id   |= heap_tile_id & mask_tile_id[1];
        post_scramble_tile_id   |= (address_i >> (ConstantBitsLSB + shift_index_sc[1])) & mask_tile_id_n[1];

        address_o[HeapSeqTotalBits-1:ConstantBitsLSB] = {post_scramble_row_index, post_scramble_tile_id};
      end else if ( (address_i >= start_addr_scheme_i[2]) && (address_i < start_addr_scheme_i[2]+MemSizePerRow*allocated_size_i[2]) ) begin

        post_scramble_row_index  = 'b0;
        post_scramble_tile_id    = 'b0;
        // 1. `post_scramble_row_index` generation
        post_scramble_row_index |= (address_i >> (ConstantBitsLSB + shift_index[2])) & mask_row_index[2];
        post_scramble_row_index |= (address_i >> (ConstantBitsLSB + TileIdBits    )) & mask_row_index_n[2];

        // 2. `post_scramble_tile_id` generation
        post_scramble_tile_id   |= heap_tile_id & mask_tile_id[2];
        post_scramble_tile_id   |= (address_i >> (ConstantBitsLSB + shift_index_sc[2])) & mask_tile_id_n[2];

        address_o[HeapSeqTotalBits-1:ConstantBitsLSB] = {post_scramble_row_index, post_scramble_tile_id};
      end else if ( (address_i >= start_addr_scheme_i[3]) && (address_i < start_addr_scheme_i[3]+MemSizePerRow*allocated_size_i[3]) ) begin

        post_scramble_row_index  = 'b0;
        post_scramble_tile_id    = 'b0;
        // 1. `post_scramble_row_index` generation
        post_scramble_row_index |= (address_i >> (ConstantBitsLSB + shift_index[3])) & mask_row_index[3];
        post_scramble_row_index |= (address_i >> (ConstantBitsLSB + TileIdBits    )) & mask_row_index_n[3];

        // 2. `post_scramble_tile_id` generation
        post_scramble_tile_id   |= heap_tile_id & mask_tile_id[3];
        post_scramble_tile_id   |= (address_i >> (ConstantBitsLSB + shift_index_sc[3])) & mask_tile_id_n[3];

        address_o[HeapSeqTotalBits-1:ConstantBitsLSB] = {post_scramble_row_index, post_scramble_tile_id};
      end 
    end
  end

  // Check for unsupported configurations
  if (NumBanksPerTile < 2)
    $fatal(1, "NumBanksPerTile must be greater than 2. The special case '1' is currently not supported!");
  if (SeqMemSizePerTile % (2**ByteOffset*NumBanksPerTile) != 0)
    $fatal(1, "SeqMemSizePerTile must be a multiple of BankWidth*NumBanksPerTile!");
endmodule : address_scrambler

  localparam int unsigned SeqPerTileBits    = $clog2(SeqMemSizePerTile);
  localparam int unsigned SeqTotalBits      = SeqPerTileBits+TileIdBits;
  localparam int unsigned ConstantBitsLSB   = ByteOffset + BankOffsetBits;
  localparam int unsigned ScrambleBits      = SeqPerTileBits-ConstantBitsLSB;

  if (Bypass || NumTiles < 2) begin
    assign address_o = address_i;
  end else begin
    logic [ScrambleBits-1:0]    scramble;    // Address bits that have to be shuffled around
    logic [TileIdBits-1:0]      tile_id;     // Which tile does  this address region belong to

    // Leave this part of the address unchanged
    // The LSBs that correspond to the offset inside a tile. These are the byte offset (bank width)
    // and the Bank offset (Number of Banks in tile)
    assign address_o[ConstantBitsLSB-1:0] = address_i[ConstantBitsLSB-1:0];
    // The MSBs that are outside of the sequential memory size. Currently the sequential memory size
    // always starts at 0. These are all the MSBs up to SeqMemSizePerTile*NumTiles
    assign address_o[AddrWidth-1:SeqTotalBits] = address_i[AddrWidth-1:SeqTotalBits];

    // Scramble the middle part
    // Bits that would have gone to different tiles but now go to increasing lines in the same tile
    assign scramble = address_i[SeqPerTileBits-1:ConstantBitsLSB]; // Bits that would
    // Bits that would have gone to increasing lines in the same tile but now go to different tiles
    assign tile_id  = address_i[SeqTotalBits-1:SeqPerTileBits];

    always_comb begin
      // Default: Unscrambled
      address_o[SeqTotalBits-1:ConstantBitsLSB] = {tile_id, scramble};
      // If not in bypass mode and address is in sequential region and more than one tile
      if (address_i < (NumTiles * SeqMemSizePerTile)) begin
        address_o[SeqTotalBits-1:ConstantBitsLSB] = {scramble, tile_id};
      end
    end
  end

  // Check for unsupported configurations
  if (NumBanksPerTile < 2)
    $fatal(1, "NumBanksPerTile must be greater than 2. The special case '1' is currently not supported!");
  if (SeqMemSizePerTile % (2**ByteOffset*NumBanksPerTile) != 0)
    $fatal(1, "SeqMemSizePerTile must be a multiple of BankWidth*NumBanksPerTile!");
endmodule : address_scrambler
