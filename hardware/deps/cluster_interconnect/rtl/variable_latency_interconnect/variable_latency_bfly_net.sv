// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
//         Matheus Cavalcante <matheusd@iis.ee.ethz.ch>, ETH Zurich

// Date: 17.01.2020

// Description: Radix-2/4 butterfly network. If parameterized to Radix-4,
// the network will be built with 4x4 xbar switchboxes, but depending on the
// amount of end-points, a Radix-2 layer will be added to accomodate non-power
// of 4 parameterizations.

// Note that additional radices would not be too difficult to add - just the mixed
// radix layers need to be written in parametric form in order to accommodate
// non-power-of-radix parameterizations.

module variable_latency_bfly_net #(
    parameter int unsigned NumIn             = 32   , // Number of Initiators. Needs to be a power of 2
    parameter int unsigned NumOut            = 32   , // Number of Targets. Needs to be a power of 2
    parameter int unsigned ReqDataWidth      = 32   , // Request Data Width
    parameter int unsigned RespDataWidth     = 32   , // Response Data Width
    parameter bit ExtPrio                    = 1'b0 , // Use external arbiter priority flags
    parameter int unsigned Radix             = 2    , // Butterfly Radix. Currently supported: 2 or 4.
    parameter bit AxiVldRdy                  = 1'b1 , // Valid/ready signaling
    // Spill registers
    // A bit set at position i indicates a spill register at the i-th crossbar layer.
    // The layers are counted starting at 0 from the initiator, for the requests, and from the target, for the responses.
    parameter logic [63:0] SpillRegisterReq  = 64'h0,
    parameter logic [63:0] SpillRegisterResp = 64'h0
  ) (
    input  logic                                 clk_i,
    input  logic                                 rst_ni,
    // External priority signals
    input  logic [$clog2(NumOut)-1:0]            req_rr_i,
    input  logic [$clog2(NumOut)-1:0]            resp_rr_i,
    // Initiator side
    input  logic [NumIn-1:0]                     req_valid_i,     // Request valid
    output logic [NumIn-1:0]                     req_ready_o,     // Request ready
    input  logic [NumIn-1:0][$clog2(NumOut)-1:0] req_tgt_addr_i,  // Target address
    input  logic [NumIn-1:0][ReqDataWidth-1:0]   req_wdata_i,     // Write data
    output logic [NumIn-1:0]                     resp_valid_o,    // Response valid
    input  logic [NumIn-1:0]                     resp_ready_i,    // Response ready
    output logic [NumIn-1:0][RespDataWidth-1:0]  resp_rdata_o,    // Data response (for load commands)
    // Target side
    output logic [NumOut-1:0]                    req_valid_o,     // Request valid
    input  logic [NumOut-1:0]                    req_ready_i,     // Request ready
    output logic [NumOut-1:0][$clog2(NumIn)-1:0] req_ini_addr_o,  // Initiator address
    output logic [NumOut-1:0][ReqDataWidth-1:0]  req_wdata_o,     // Write data
    input  logic [NumOut-1:0]                    resp_valid_i,    // Response valid
    output logic [NumOut-1:0]                    resp_ready_o,    // Response ready
    input  logic [NumOut-1:0][$clog2(NumIn)-1:0] resp_ini_addr_i, // Initiator address
    input  logic [NumOut-1:0][RespDataWidth-1:0] resp_rdata_i     // Data response (for load commands)
  );

  /****************
   *   Includes   *
   ****************/

  `include "common_cells/registers.svh"

  /*******************
   *   Network I/O   *
   *******************/

  localparam int unsigned IniAddWidth     = $clog2(NumIn);
  localparam int unsigned AddWidth        = $clog2(NumOut);
  localparam int unsigned NumRouters      = NumOut/Radix;
  localparam int unsigned NumStages       = ($clog2(NumOut) + $clog2(Radix) - 1)/$clog2(Radix);
  localparam int unsigned BankFact        = NumOut/NumIn;
  localparam int unsigned RespIniAddWidth = NumStages * $clog2(Radix);

  // Check if the Radix-4 network needs a Radix-2 stage
  localparam bit NeedsR2Stage = (Radix == 4) && (AddWidth[0] == 1'b1);

  /* verilator lint_off UNOPTFLAT */
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0]                      router_req_valid_in;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0]                      router_req_valid_out;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0]                      router_req_ready_in;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0]                      router_req_ready_out;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][AddWidth-1:0]        router_req_tgt_addr_in;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][AddWidth-1:0]        router_req_tgt_addr_out;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][ReqDataWidth-1:0]    router_req_wdata_in;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][ReqDataWidth-1:0]    router_req_wdata_out;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0]                      router_resp_valid_in;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0]                      router_resp_valid_out;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0]                      router_resp_ready_in;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0]                      router_resp_ready_out;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][IniAddWidth-1:0]     router_req_ini_add_in;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][IniAddWidth-1:0]     router_req_ini_add_out;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][RespDataWidth-1:0]   router_resp_rdata_in;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][RespDataWidth-1:0]   router_resp_rdata_out;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][RespIniAddWidth-1:0] router_resp_ini_add_in;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][RespIniAddWidth-1:0] router_resp_ini_add_out;
  /* verilator lint_on UNOPTFLAT */

  /******************************
   *   Arbitration priorities   *
   ******************************/

  // We use a round robin arbiter here

  logic [$clog2(NumOut)-1:0] req_rr;
  logic [$clog2(NumOut)-1:0] resp_rr;

  if (ExtPrio) begin : gen_ext_prio
    assign req_rr  = req_rr_i ;
    assign resp_rr = resp_rr_i;
  end else begin : gen_no_ext_prio
    assign req_rr  = '0;
    assign resp_rr = '0;
  end

  /**************************
   *   Interstage routing   *
   **************************/

  // Inputs are on the first stage.
  // Make sure to evenly distribute masters, if BankFact > 1.
  for (genvar j = 0; j < Radix*NumRouters; j++) begin : gen_inputs
    // Leave out input connections in interleaved way until we reach the radix.
    if (BankFact < Radix) begin : gen_interleaved
      if ((j % BankFact) == 0) begin : gen_connect
        // Req
        assign router_req_valid_in[0][j/Radix][j%Radix]    = req_valid_i[j/BankFact]                  ;
        assign req_ready_o[j/BankFact]                     = router_req_ready_out[0][j/Radix][j%Radix];
        assign router_req_tgt_addr_in[0][j/Radix][j%Radix] = req_tgt_addr_i[j/BankFact]               ;
        assign router_req_wdata_in[0][j/Radix][j%Radix]    = req_wdata_i[j/BankFact]                  ;
        assign router_req_ini_add_in[0][j/Radix][j%Radix]  = j/BankFact                               ; // Constant
        assign router_resp_ready_in[0][j/Radix][j%Radix]   = resp_ready_i[j/BankFact]                 ;

        // Resp
        assign resp_rdata_o[j/BankFact] = router_resp_rdata_out[0][j/Radix][j%Radix] ;
        assign resp_valid_o[j/BankFact] = router_resp_valid_out[0][j/Radix][j%Radix] ;
      end else begin : gen_tie_off
        // Req
        assign router_req_valid_in[0][j/Radix][j%Radix]    = 1'b0;
        assign router_req_ini_add_in[0][j/Radix][j%Radix]  = '0  ;
        assign router_req_tgt_addr_in[0][j/Radix][j%Radix] = '0  ;
        assign router_req_wdata_in[0][j/Radix][j%Radix]    = '0  ;
        assign router_resp_ready_in[0][j/Radix][j%Radix]   = '1  ;
      end
    // We only enter this case if each input switchbox has 1 or zero connections.
    // Only connect to lower portion of switchboxes and tie off upper portion. This allows
    // us to reduce arbitration confligs on the first network layers.
    end else begin : gen_linear
      if (((j % Radix) == 0) && (j/Radix < NumIn)) begin : gen_connect
        // Req
        assign router_req_valid_in[0][j/Radix][j%Radix]    = req_valid_i[j/Radix]                     ;
        assign router_req_ini_add_in[0][j/Radix][j%Radix]  = j/Radix                                  ;
        assign req_ready_o[j/Radix]                        = router_req_ready_out[0][j/Radix][j%Radix];
        assign router_req_tgt_addr_in[0][j/Radix][j%Radix] = req_tgt_addr_i[j/Radix]                  ;
        assign router_req_wdata_in[0][j/Radix][j%Radix]    = req_wdata_i[j/Radix]                     ;
        assign router_resp_ready_in[0][j/Radix][j%Radix]   = resp_ready_i[j/Radix]                    ;

        // Resp
        assign resp_rdata_o[j/Radix] = router_resp_rdata_out[0][j/Radix][j%Radix] ;
        assign resp_valid_o[j/Radix] = router_resp_valid_out[0][j/Radix][j%Radix] ;
      end else begin : gen_tie_off
        // Req
        assign router_req_valid_in[0][j/Radix][j%Radix]    = 1'b0;
        assign router_req_ini_add_in[0][j/Radix][j%Radix]  = '0  ;
        assign router_req_tgt_addr_in[0][j/Radix][j%Radix] = '0  ;
        assign router_req_wdata_in[0][j/Radix][j%Radix]    = '0  ;
        assign router_resp_ready_in[0][j/Radix][j%Radix]   = '1  ;
      end
    end
  end

  // Outputs are on the last stage.
  for (genvar j = 0; j < Radix*NumRouters; j++) begin : gen_outputs
    if (j < NumOut) begin : gen_connect
      // Req
      assign req_valid_o[j]                                     = router_req_valid_out[NumStages-1][j/Radix][j%Radix]   ;
      assign req_ini_addr_o[j]                                  = router_req_ini_add_out[NumStages-1][j/Radix][j%Radix] ;
      assign router_req_ready_in[NumStages-1][j/Radix][j%Radix] = req_ready_i[j]                                        ;
      assign req_wdata_o[j]                                     = router_req_wdata_out[NumStages-1][j/Radix][j%Radix]   ;
      assign resp_ready_o[j]                                    = router_resp_ready_out[NumStages-1][j/Radix][j%Radix]  ;

      // Resp
      assign router_resp_rdata_in[NumStages-1][j/Radix][j%Radix] = resp_rdata_i[j] ;
      assign router_resp_valid_in[NumStages-1][j/Radix][j%Radix] = resp_valid_i[j] ;

      if (BankFact < Radix) begin : gen_interleaved
        // How many bits are used to address the first level routers?
        localparam FirstLevelBits                                    = NumRouters*Radix > NumIn ? $clog2(NumRouters*Radix/NumIn) : $clog2(Radix);
        // If the first level routers are not fully connected, how many extra bits does this stage need?
        localparam FirstLevelPadBits                                 = RespIniAddWidth - IniAddWidth - NeedsR2Stage                                                                                                                               ;
        // If there is an R2 stage, we need to add an extra bit at stage 1 indicating which Radix-2 router at stage 0 will receive this request
        assign router_resp_ini_add_in[NumStages-1][j/Radix][j%Radix] = {resp_ini_addr_i[j][FirstLevelBits-1:0], {FirstLevelPadBits{1'b0}}, {NeedsR2Stage{resp_ini_addr_i[j][FirstLevelBits-1]}}, resp_ini_addr_i[j][IniAddWidth-1:FirstLevelBits]};
      end else begin: gen_linear
        // If we are here, the first level switch box has a single connection. Zero-padding should route the data back to the initiator.
        assign router_resp_ini_add_in[NumStages-1][j/Radix][j%Radix] = resp_ini_addr_i[j];
      end
    end else begin : gen_tie_off
      // Req
      assign router_req_ready_in[NumStages-1][j/Radix][j%Radix] = '1;

      // Resp
      assign router_resp_rdata_in[NumStages-1][j/Radix][j%Radix]   = '0  ;
      assign router_resp_valid_in[NumStages-1][j/Radix][j%Radix]   = 1'b0;
      assign router_resp_ini_add_in[NumStages-1][j/Radix][j%Radix] = '0  ;
    end
  end

  // Wire up connections between Stages
  for (genvar l = 0; l < NumStages-1; l++) begin : gen_stages
    // Do we need to add a Radix-2?
    if (l == 0 && NeedsR2Stage) begin : gen_r4r2_stage
      localparam int unsigned pow = 2*Radix**(NumStages-l-2);

      for (genvar r = 0; r < 2*NumRouters; r++) begin : gen_routers
        for (genvar s = 0; s < 2; s++) begin : gen_ports
          localparam int unsigned k = pow * s + (r % pow) + (r / pow / 2) * pow * 2;
          localparam int unsigned j = (r / pow) % 2                                ;

          assign router_req_valid_in[l+1][k/2][(k%2)*2+j]    = router_req_valid_out[l][r/2][(r%2)*2+s]      ;
          assign router_req_ini_add_in[l+1][k/2][(k%2)*2+j]  = router_req_ini_add_out[l][r/2][(r%2)*2+s]    ;
          assign router_resp_ready_in[l+1][k/2][(k%2)*2+j]   = router_resp_ready_out[l][r/2][(r%2)*2+s]     ;
          assign router_req_tgt_addr_in[l+1][k/2][(k%2)*2+j] = router_req_tgt_addr_out[l][r/2][(r%2)*2+s]   ;
          assign router_req_wdata_in[l+1][k/2][(k%2)*2+j]    = router_req_wdata_out[l][r/2][(r%2)*2+s]      ;
          assign router_req_ready_in[l][r/2][(r%2)*2+s]      = router_req_ready_out[l+1][k/2][(k%2)*2+j]    ;
          assign router_resp_rdata_in[l][r/2][(r%2)*2+s]     = router_resp_rdata_out[l+1][k/2][(k%2)*2+j]   ;
          assign router_resp_ini_add_in[l][r/2][(r%2)*2+s]   = router_resp_ini_add_out[l+1][k/2][(k%2)*2+j] ;
          assign router_resp_valid_in[l][r/2][(r%2)*2+s]     = router_resp_valid_out[l+1][k/2][(k%2)*2+j]   ;
        end
      end
    end else begin : gen_std_stage
      localparam int unsigned pow = Radix**(NumStages-l-2);

      for (genvar s = 0; unsigned'(s) < Radix; s++) begin : gen_routers
        for (genvar r = 0; unsigned'(r) < NumRouters; r++) begin : gen_ports
          localparam int unsigned k = pow * s + (r % pow) + (r / pow / Radix) * pow * Radix;
          localparam int unsigned j = (r / pow) % Radix                                    ;

          assign router_req_valid_in[l+1][k][j]    = router_req_valid_out[l][r][s]      ;
          assign router_req_ini_add_in[l+1][k][j]  = router_req_ini_add_out[l][r][s]    ;
          assign router_resp_ready_in[l+1][k][j]   = router_resp_ready_out[l][r][s]     ;
          assign router_req_tgt_addr_in[l+1][k][j] = router_req_tgt_addr_out[l][r][s]   ;
          assign router_req_wdata_in[l+1][k][j]    = router_req_wdata_out[l][r][s]      ;
          assign router_req_ready_in[l][r][s]      = router_req_ready_out[l+1][k][j]    ;
          assign router_resp_rdata_in[l][r][s]     = router_resp_rdata_out[l+1][k][j]   ;
          assign router_resp_valid_in[l][r][s]     = router_resp_valid_out[l+1][k][j]   ;
          assign router_resp_ini_add_in[l][r][s]   = router_resp_ini_add_out[l+1][k][j] ;
        end
      end
    end
  end

  /*****************
   *   Crossbars   *
   *****************/

  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][AddWidth+IniAddWidth+ReqDataWidth-1:0] req_data_in , req_data_out ;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][RespIniAddWidth+RespDataWidth-1:0]     resp_data_in, resp_data_out;

  for (genvar l = 0; l < NumStages; l++) begin : gen_routers1
    for (genvar r = 0; r < NumRouters; r++) begin: gen_routers2

      // Do we need to add a Radix-2 stage?
      if (l == 0 && NeedsR2Stage) begin : gen_r4r2_stage
        logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][0:0] add         ;
        logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][0:0] resp_ini_add;
        logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][0:0] req_prio    ;
        logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][0:0] resp_prio   ;

        for (genvar k = 0; k < Radix; k++) begin : gen_map
          assign add[l][r][k]                                                                                       = router_req_tgt_addr_in[l][r][k][AddWidth-1]                                                       ;
          assign resp_ini_add[l][r][k]                                                                              = router_resp_ini_add_in[l][r][k][0]                                                                ;
          assign req_data_in[l][r][k]                                                                               = {router_req_tgt_addr_in[l][r][k]<<1, router_req_ini_add_in[l][r][k], router_req_wdata_in[l][r][k]};
          assign {router_req_tgt_addr_out[l][r][k], router_req_ini_add_out[l][r][k], router_req_wdata_out[l][r][k]} = req_data_out[l][r][k]                                                                             ;
          assign resp_data_in[l][r][k]                                                                              = {router_resp_ini_add_in[l][r][k]>>1, router_resp_rdata_in[l][r][k]}                               ;
          assign {router_resp_ini_add_out[l][r][k], router_resp_rdata_out[l][r][k]}                                 = resp_data_out[l][r][k]                                                                            ;
          assign req_prio[l][r][k]                                                                                  = req_rr[$clog2(NumOut)-1]                                                                          ;
          assign resp_prio[l][r][k]                                                                                 = resp_rr[$clog2(NumOut)-1]                                                                         ;
        end

        for (genvar k = 0; k < 2; k++) begin: gen_xbar
          full_duplex_xbar #(
            .NumIn            (2                                    ),
            .NumOut           (2                                    ),
            .ReqDataWidth     (AddWidth + IniAddWidth + ReqDataWidth),
            .RespDataWidth    (RespDataWidth + RespIniAddWidth      ),
            .ExtPrio          (ExtPrio                              ),
            .SpillRegisterReq (SpillRegisterReq[l]                  ),
            .SpillRegisterResp(SpillRegisterResp[NumStages-l-1]     ),
            .AxiVldRdy        (AxiVldRdy                            )
          ) i_xbar (
            .clk_i          (clk_i                                ),
            .rst_ni         (rst_ni                               ),
            // External priority flags
            .req_rr_i       (req_prio[l][r][k*2 +: 2]             ),
            .resp_rr_i      (resp_prio[l][r][k*2 +: 2]            ),
            // Initiator side
            .req_valid_i    (router_req_valid_in[l][r][k*2 +: 2]  ),
            .req_ready_o    (router_req_ready_out[l][r][k*2 +: 2] ),
            .req_tgt_addr_i (add[l][r][k*2 +: 2]                  ),
            .req_wdata_i    (req_data_in[l][r][k*2 +: 2]          ),
            .resp_valid_o   (router_resp_valid_out[l][r][k*2 +: 2]),
            .resp_ready_i   (router_resp_ready_in[l][r][k*2 +: 2] ),
            .resp_rdata_o   (resp_data_out[l][r][k*2 +: 2]        ),
            // Target side
            .req_valid_o    (router_req_valid_out[l][r][k*2 +: 2] ),
            .req_ini_addr_o (/* Unused */                         ),
            .req_ready_i    (router_req_ready_in[l][r][k*2 +: 2]  ),
            .req_wdata_o    (req_data_out[l][r][k*2 +: 2]         ),
            .resp_valid_i   (router_resp_valid_in[l][r][k*2 +: 2] ),
            .resp_ready_o   (router_resp_ready_out[l][r][k*2 +: 2]),
            .resp_ini_addr_i(resp_ini_add[l][r][k*2 +: 2]         ),
            .resp_rdata_i   (resp_data_in[l][r][k*2 +: 2]         )
          );
        end

      // Instantiate switchbox of the chosen Radix.
      end else begin : gen_std_stage
        logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][$clog2(Radix)-1:0] add         ;
        logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][$clog2(Radix)-1:0] resp_ini_add;
        logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][$clog2(Radix)-1:0] req_prio    ;
        logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][$clog2(Radix)-1:0] resp_prio   ;

        for (genvar k = 0; k < Radix; k++) begin : gen_map
          assign add[l][r][k]                                                                                       = router_req_tgt_addr_in[l][r][k][AddWidth-1 -: $clog2(Radix)]                                                  ;
          assign resp_ini_add[l][r][k]                                                                              = router_resp_ini_add_in[l][r][k][$clog2(Radix)-1:0]                                                            ;
          assign req_data_in[l][r][k]                                                                               = {router_req_tgt_addr_in[l][r][k]<<$clog2(Radix), router_req_ini_add_in[l][r][k], router_req_wdata_in[l][r][k]};
          assign {router_req_tgt_addr_out[l][r][k], router_req_ini_add_out[l][r][k], router_req_wdata_out[l][r][k]} = req_data_out[l][r][k]                                                                                         ;
          assign resp_data_in[l][r][k]                                                                              = {router_resp_ini_add_in[l][r][k]>>$clog2(Radix), router_resp_rdata_in[l][r][k]}                               ;
          assign {router_resp_ini_add_out[l][r][k], router_resp_rdata_out[l][r][k]}                                 = resp_data_out[l][r][k]                                                                                        ;

          // depending on where the requests are connected in the radix 4 case, we have to flip the priority vector
          // this is needed because one of the bits may be constantly set to zero
          if (BankFact < Radix) begin : gen_reverse
            for (genvar j = 0; unsigned'(j) < $clog2(Radix); j++) begin : gen_connect
              assign req_prio[l][r][k][$clog2(Radix)-1-j]  = req_rr[$clog2(NumOut)-(unsigned'(l)+1-32'(NeedsR2Stage))*$clog2(Radix)-32'(NeedsR2Stage) + unsigned'(j)] ;
              assign resp_prio[l][r][k][$clog2(Radix)-1-j] = resp_rr[$clog2(NumOut)-(unsigned'(l)+1-32'(NeedsR2Stage))*$clog2(Radix)-32'(NeedsR2Stage) + unsigned'(j)];
            end
          end else begin : gen_no_reverse
            for (genvar j = 0; unsigned'(j) < $clog2(Radix); j++) begin : gen_connect
              assign req_prio[l][r][k][j]  = req_rr[$clog2(NumOut)-(unsigned'(l)+1-32'(NeedsR2Stage))*$clog2(Radix)-32'(NeedsR2Stage) + unsigned'(j)] ;
              assign resp_prio[l][r][k][j] = resp_rr[$clog2(NumOut)-(unsigned'(l)+1-32'(NeedsR2Stage))*$clog2(Radix)-32'(NeedsR2Stage) + unsigned'(j)];
            end
          end
        end

        full_duplex_xbar #(
          .NumIn            (Radix                                ),
          .NumOut           (Radix                                ),
          .ReqDataWidth     (AddWidth + IniAddWidth + ReqDataWidth),
          .RespDataWidth    (RespDataWidth + RespIniAddWidth      ),
          .ExtPrio          (ExtPrio                              ),
          .SpillRegisterReq (SpillRegisterReq[l]                  ),
          .SpillRegisterResp(SpillRegisterResp[NumStages-l-1]     ),
          .AxiVldRdy        (AxiVldRdy                            )
        ) i_xbar (
          .clk_i          (clk_i                      ),
          .rst_ni         (rst_ni                     ),
          // External priority flags
          .req_rr_i       (req_prio[l][r]             ),
          .resp_rr_i      (resp_prio[l][r]            ),
          // Initiator side
          .req_valid_i    (router_req_valid_in[l][r]  ),
          .req_ready_o    (router_req_ready_out[l][r] ),
          .req_tgt_addr_i (add[l][r]                  ),
          .req_wdata_i    (req_data_in[l][r]          ),
          .resp_valid_o   (router_resp_valid_out[l][r]),
          .resp_ready_i   (router_resp_ready_in[l][r] ),
          .resp_rdata_o   (resp_data_out[l][r]        ),
          // Target side
          .req_valid_o    (router_req_valid_out[l][r] ),
          .req_ini_addr_o (/* Unused */               ),
          .req_ready_i    (router_req_ready_in[l][r]  ),
          .req_wdata_o    (req_data_out[l][r]         ),
          .resp_valid_i   (router_resp_valid_in[l][r] ),
          .resp_ready_o   (router_resp_ready_out[l][r]),
          .resp_ini_addr_i(resp_ini_add[l][r]         ),
          .resp_rdata_i   (resp_data_in[l][r]         )
        );

      end
    end
  end

  /******************
   *   Assertions   *
   ******************/

  if (!(Radix == 2 || Radix == 4))
    $fatal(1, "[variable_latency_bfly_net] Only Radix-2 and Radix-4 are supported.");

  if (2**$clog2(NumIn) != NumIn)
    $fatal(1, "[variable_latency_bfly_net] NumIn is not aligned with a power of 2.");

  if (2**$clog2(NumOut) != NumOut)
    $fatal(1, "[variable_latency_bfly_net] NumOut is not aligned with a power of 2.");

  if (NumOut < NumIn)
    $fatal(1, "[variable_latency_bfly_net] NumOut < NumIn is not supported.");

endmodule : variable_latency_bfly_net
