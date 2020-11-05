// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module slice_top
 #(
    parameter N_SLICES        = 16,
    parameter N_REGS          = 4*N_SLICES,
    parameter ADDR_WIDTH_PHYS = 40,
    parameter ADDR_WIDTH_VIRT = 32
    )
   (
    input   logic   [N_REGS-1:0] [63:0] int_cfg_regs,
    input   logic                       int_rw,
    input   logic [ADDR_WIDTH_VIRT-1:0] int_addr_min,
    input   logic [ADDR_WIDTH_VIRT-1:0] int_addr_max,
    input   logic                       partial_match_allow,
    input   logic                       multi_hit_allow,
    output  logic                       multi_hit,
    output  logic        [N_SLICES-1:0] prot,
    output  logic        [N_SLICES-1:0] hit,
    output  logic                       cache_coherent,
    output  logic [ADDR_WIDTH_PHYS-1:0] out_addr
  );

  logic first_hit;

  genvar  i;
  integer j;

  logic [ADDR_WIDTH_PHYS*N_SLICES-1:0]  slice_out_addr;

  generate
    for ( i=0; i<N_SLICES; i++ )
      begin
        rab_slice
          #(
            .ADDR_WIDTH_PHYS ( ADDR_WIDTH_PHYS ),
            .ADDR_WIDTH_VIRT ( ADDR_WIDTH_VIRT )
            )
          u_slice
          (
            .cfg_min          ( int_cfg_regs[4*i]  [ADDR_WIDTH_VIRT-1:0]                              ),
            .cfg_max          ( int_cfg_regs[4*i+1][ADDR_WIDTH_VIRT-1:0]                              ),
            .cfg_offset       ( int_cfg_regs[4*i+2][ADDR_WIDTH_PHYS-1:0]                              ),
            .cfg_wen          ( int_cfg_regs[4*i+3][2]                                                ),
            .cfg_ren          ( int_cfg_regs[4*i+3][1]                                                ),
            .cfg_en           ( int_cfg_regs[4*i+3][0]                                                ),
            .in_partial_match ( partial_match_allow                                                   ),
            .in_trans_type    ( int_rw                                                                ),
            .in_addr_min      ( int_addr_min                                                          ),
            .in_addr_max      ( int_addr_max                                                          ),
            .out_addr         ( slice_out_addr[ADDR_WIDTH_PHYS*i+ADDR_WIDTH_PHYS-1:ADDR_WIDTH_PHYS*i] ),
            .out_prot         ( prot[i]                                                               ),
            .out_hit          ( hit[i]                                                                )
          );
     end
  endgenerate

  // In case of a multi hit, the lowest slice with a hit is selected.
  always_comb begin : HIT_CHECK
    first_hit      =  0;
    multi_hit      =  0;
    out_addr       = '0;
    cache_coherent =  0;
    for (j = 0; j < N_SLICES; j++) begin
      if (hit[j] == 1'b1) begin
        if (first_hit == 1'b1) begin
          if (multi_hit_allow == 1'b0) begin
            multi_hit = 1'b1;
          end
        end else begin
          first_hit       = 1'b1;
          out_addr        = slice_out_addr[ADDR_WIDTH_PHYS*j +: ADDR_WIDTH_PHYS];
          cache_coherent  = int_cfg_regs[4*j+3][3];
        end
      end
    end
  end

endmodule

// vim: ts=2 sw=2 sts=2 et nosmartindent autoindent foldmethod=marker
