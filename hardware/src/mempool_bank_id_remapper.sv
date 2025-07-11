// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "mempool/mempool.svh"

module mempool_bank_id_remapper
  import mempool_pkg::*;
  import cf_math_pkg::idx_width;
#(
  parameter int unsigned NumCoresPerTile              = 4,
  parameter int unsigned NumRemoteReqPortsPerTile     = 4,
  parameter int unsigned NumBanksPerTile              = 16,
  parameter int unsigned TCDMAddrMemWidth             = 8,
  parameter bit          SpmBankIdRemap               = 0
) (
  input  tcdm_dma_req_t                                      tcdm_dma_req_i,
  input  tcdm_slave_req_t     [NumRemoteReqPortsPerTile-1:0] tcdm_slave_req_i,
  input  tcdm_slave_req_t     [NumCoresPerTile-1:0]          local_req_interco_payload_i,
  output tcdm_dma_req_t                                      tcdm_dma_req_remapped_o,
  output tcdm_slave_req_t     [NumRemoteReqPortsPerTile-1:0] tcdm_slave_req_remapped_o,
  output tcdm_slave_req_t     [NumCoresPerTile-1:0]          local_req_interco_payload_remapped_o
);

  /*****************
   *  Definitions  *
   *****************/

  // Compute shift amount: use lower of address width and bank index bits
  `define min(a,b) (((a) < (b))? (a) : (b))
  `define max(a,b) (((a) > (b))? (a) : (b))

  typedef logic [idx_width(NumRemoteReqPortsPerTile)-1:0] remote_ports_index_t;
  localparam SHIFT_AMOUNT = `min(TCDMAddrMemWidth, idx_width(NumBanksPerTile)); // or 4
  localparam RemoteReqBits = `max(1, $clog2(NumRemoteReqPortsPerTile-1));

  // Rotate bank ID by index bits for spreading
  function automatic logic [idx_width(NumBanksPerTile)-1:0] spm_bank_id_remap (
    logic [idx_width(NumBanksPerTile)-1:0] data_in,
    logic [SHIFT_AMOUNT-1:0] idx_i
  );
  if (SpmBankIdRemap == 1) begin
    spm_bank_id_remap = data_in + idx_i;
  end else begin
    spm_bank_id_remap = data_in;
  end
  endfunction

  /************************
   *  Bank Address Remap  *
   ************************/
  // Apply to DMA, remote, and local requests
  tcdm_dma_req_t                                  tcdm_dma_req_remapped;
  tcdm_slave_req_t [NumRemoteReqPortsPerTile-1:0] tcdm_slave_req_remapped;
  tcdm_slave_req_t [NumCoresPerTile-1:0]          local_req_interco_payload_remapped;

  always_comb begin
    // DMA request: remap low bits of tgt_addr
    tcdm_dma_req_remapped = tcdm_dma_req_i;
    tcdm_dma_req_remapped.tgt_addr[idx_width(NumBanksPerTile)-1:0] =
    spm_bank_id_remap(
      tcdm_dma_req_i.tgt_addr[idx_width(NumBanksPerTile)-1:0],
      tcdm_dma_req_i.tgt_addr[idx_width(NumBanksPerTile) +: SHIFT_AMOUNT]
    );
    // Remote requests: remap low bits of tgt_addr
    for(int rp = 0; rp < NumRemoteReqPortsPerTile; rp++) begin
      tcdm_slave_req_remapped[rp] = tcdm_slave_req_i[rp];
      tcdm_slave_req_remapped[rp].tgt_addr[idx_width(NumBanksPerTile)-1:0] =
      spm_bank_id_remap(
        tcdm_slave_req_i[rp].tgt_addr[idx_width(NumBanksPerTile)-1:0],
        tcdm_slave_req_i[rp].tgt_addr[idx_width(NumBanksPerTile) +: SHIFT_AMOUNT]
      );
    end
    // Local requests: remap low bits of tgt_addr
    for(int c = 0; c < NumCoresPerTile; c++) begin
      local_req_interco_payload_remapped[c] = local_req_interco_payload_i[c];
      local_req_interco_payload_remapped[c].tgt_addr[idx_width(NumBanksPerTile)-1:0] =
      spm_bank_id_remap(
        local_req_interco_payload_i[c].tgt_addr[idx_width(NumBanksPerTile)-1:0],
        local_req_interco_payload_i[c].tgt_addr[idx_width(NumBanksPerTile) +: SHIFT_AMOUNT]
      );
    end
  end

  // Drive outputs
  assign tcdm_dma_req_remapped_o              = tcdm_dma_req_remapped;
  assign tcdm_slave_req_remapped_o            = tcdm_slave_req_remapped;
  assign local_req_interco_payload_remapped_o = local_req_interco_payload_remapped;
endmodule
