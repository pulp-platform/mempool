/// Description: Scrambles the address in such a way, that part of the memory is accessed
/// sequentially and part is interleaved.
/// Current constraints:

/// Author: Samuel Riedel <sriedel@iis.ee.ethz.ch>

module address_scrambler #(
  parameter int unsigned AddrWidth         = 32,
  parameter int unsigned ByteOffset        = 2,
  parameter int unsigned NumTiles          = 2,
  parameter int unsigned NumBanksPerTile   = 2,
  parameter int unsigned SeqMemSizePerTile = 4*1024
) (
  input  logic [AddrWidth-1:0] address_i,
  output logic [AddrWidth-1:0] address_o
);
  localparam int unsigned BankOffsetBits  = $clog2(NumBanksPerTile);
  localparam int unsigned TileIdBits      = $clog2(NumTiles);
  localparam int unsigned ScrambleBits    = $clog2(SeqMemSizePerTile)-BankOffsetBits-ByteOffset;
  localparam int unsigned InterleavedBits = AddrWidth-$clog2(SeqMemSizePerTile)+TileIdBits;

  logic [ByteOffset-1:0]      byte_offset;
  logic [BankOffsetBits-1:0]  bank_offset; // Offset of Bank inside Tile
  logic [ScrambleBits-1:0]    scramble;    // Address bits that have to be shuffled around
  logic [TileIdBits-1:0]      tile_id;     // Which tile does  this address region belong to
  logic [InterleavedBits-1:0] interleaved; // MSB address bits that stay unchanged

  // Pick correct chunks from input address
  assign byte_offset = address_i[0                         +: ByteOffset                                         ];
  assign bank_offset = address_i[ByteOffset                +: BankOffsetBits                                     ];
  assign scramble    = address_i[ByteOffset+BankOffsetBits +: $clog2(SeqMemSizePerTile)-BankOffsetBits-ByteOffset];
  assign tile_id     = address_i[$clog2(SeqMemSizePerTile) +: TileIdBits                                         ];
  assign interleaved = address_i[AddrWidth-1                : $clog2(SeqMemSizePerTile)+TileIdBits               ];
  // Scramble the address back together
  assign address_o   = address_i < SeqMemSizePerTile*NumTiles ? {interleaved, scramble, tile_id, bank_offset, byte_offset} : address_i;

  // Check for unsupported configurations
  // pragma translate_off
`ifndef VERILATOR
  initial begin: p_assertions
    assert (NumTiles >= 2) else $fatal(1, "NumTiles must be at least two. The special case '1' is currently not supported (and makes no sense)!");
    assert (NumBanksPerTile >= 2) else $fatal(1, "NumBanksPerTile must be greater than 2. The special case '1' is currently not supported!");
    assert (SeqMemSizePerTile % (2**ByteOffset*NumBanksPerTile) == 0) else $fatal(1, "SeqMemSizePerTile must be a multiple of BankWidth*NumBanksPerTile!");
  end
`endif
// pragma translate_on
endmodule : address_scrambler
