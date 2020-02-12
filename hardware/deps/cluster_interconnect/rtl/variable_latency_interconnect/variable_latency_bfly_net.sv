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
    parameter int unsigned NumIn         = 32  , // Number of Initiators. Needs to be a power of 2
    parameter int unsigned NumOut        = 32  , // Number of Targets. Needs to be a power of 2
    parameter int unsigned ReqDataWidth  = 32  , // Request Data Width
    parameter int unsigned RespDataWidth = 32  , // Response Data Width
    parameter bit ExtPrio                = 1'b0, // Use external arbiter priority flags
    parameter int unsigned Radix         = 2     // Butterfly Radix. Currently supported: 2 or 4.
  ) (
    input  logic                                 clk_i,
    input  logic                                 rst_ni,
    // External priority signals
    input  logic [$clog2(NumOut)-1:0]            req_rr_i,
    input  logic [$clog2(NumOut)-1:0]            resp_rr_i,
    // Initiator side
    input  logic [NumIn-1:0]                     req_i,     // Request signal
    output logic [NumIn-1:0]                     gnt_o,     // Grant signal
    input  logic [NumIn-1:0][$clog2(NumOut)-1:0] add_i,     // Target address
    input  logic [NumIn-1:0][ReqDataWidth-1:0]   wdata_i,   // Write data
    output logic [NumIn-1:0]                     vld_o,     // Response valid
    input  logic [NumIn-1:0]                     rdy_i,     // Response ready
    output logic [NumIn-1:0][RespDataWidth-1:0]  rdata_o,   // Data response (for load commands)
    // Target side
    output logic [NumOut-1:0]                    req_o,     // Request signal
    output logic [NumOut-1:0][$clog2(NumIn)-1:0] ini_add_o, // Initiator address
    input  logic [NumOut-1:0]                    gnt_i,     // Grant signal
    output logic [NumOut-1:0][ReqDataWidth-1:0]  wdata_o,   // Write data
    input  logic [NumOut-1:0]                    vld_i,     // Response valid
    output logic [NumOut-1:0]                    rdy_o,     // Response ready
    input  logic [NumOut-1:0][$clog2(NumIn)-1:0] ini_add_i, // Initiator address (response path)
    input  logic [NumOut-1:0][RespDataWidth-1:0] rdata_i    // Data response (for load commands)
  );

  /*******************
   *   Network I/O   *
   *******************/

  localparam int unsigned IdxWidth   = $clog2(NumIn);
  localparam int unsigned AddWidth   = $clog2(NumOut);
  localparam int unsigned NumRouters = NumOut/Radix;
  localparam int unsigned NumStages  = ($clog2(NumOut) + $clog2(Radix) - 1)/$clog2(Radix);
  localparam int unsigned BankFact   = NumOut/NumIn;

  // Check if the Radix-4 network needs a Radix-2 stage
  localparam bit NeedsR2Stage = (Radix == 4) && (AddWidth[0] == 1'b1);

  /* verilator lint_off UNOPTFLAT */
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0]                    router_req_in ;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0]                    router_req_out ;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0]                    router_gnt_in ;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0]                    router_gnt_out ;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][AddWidth-1:0]      router_add_in ;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][AddWidth-1:0]      router_add_out ;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0]                    router_vld_in;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0]                    router_vld_out;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0]                    router_rdy_in;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0]                    router_rdy_out;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][ReqDataWidth-1:0]  router_data_in ;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][ReqDataWidth-1:0]  router_data_out ;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][IdxWidth-1:0]      router_ini_add_in;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][IdxWidth-1:0]      router_ini_add_out;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][RespDataWidth-1:0] router_resp_data_in ;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][RespDataWidth-1:0] router_resp_data_out;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][IdxWidth-1:0]      router_resp_ini_add_in;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][IdxWidth-1:0]      router_resp_ini_add_out;
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
    // Although round robin arbitration works in some cases, it
    // it is quite likely that it interferes with linear access patterns
    // hence we use a relatively long LFSR + block cipher here to create a
    // pseudo random sequence with good randomness. the block cipher layers
    // are used to break shift register linearity.
    lfsr #(
      .LfsrWidth   (64              ),
      .OutWidth    (2*$clog2(NumOut)),
      .CipherLayers(3               ),
      .CipherReg   (1'b1            )
    ) lfsr_i (
      .clk_i (clk_i            ),
      .rst_ni(rst_ni           ),
      .en_i  (|(gnt_i & req_o) ),
      .out_o ({resp_rr, req_rr})
    );
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
        assign router_req_in[0][j/Radix][j%Radix]     = req_i[j/BankFact]                  ;
        assign gnt_o[j/BankFact]                      = router_gnt_out[0][j/Radix][j%Radix];
        assign router_add_in[0][j/Radix][j%Radix]     = add_i[j/BankFact]                  ;
        assign router_data_in[0][j/Radix][j%Radix]    = wdata_i[j/BankFact]                ;
        assign router_ini_add_in[0][j/Radix][j%Radix] = '0                                 ;
        assign router_rdy_in[0][j/Radix][j%Radix]     = rdy_i[j/BankFact]                  ;

        // Resp
        assign rdata_o[j/BankFact] = router_resp_data_out[0][j/Radix][j%Radix];
        assign vld_o[j/BankFact]   = router_vld_out[0][j/Radix][j%Radix]      ;
      end else begin : gen_tie_off
        // Req
        assign router_req_in[0][j/Radix][j%Radix]     = 1'b0;
        assign router_ini_add_in[0][j/Radix][j%Radix] = '0  ;
        assign router_add_in[0][j/Radix][j%Radix]     = '0  ;
        assign router_data_in[0][j/Radix][j%Radix]    = '0  ;
        assign router_rdy_in[0][j/Radix][j%Radix]     = 1'b0;
      end
    // We only enter this case if each input switchbox has 1 or zero connections.
    // Only connect to lower portion of switchboxes and tie off upper portion. This allows
    // us to reduce arbitration confligs on the first network layers.
    end else begin : gen_linear
      if (((j % Radix) == 0) && (j/Radix < NumIn)) begin : gen_connect
        // Req
        assign router_req_in[0][j/Radix][j%Radix]     = req_i[j/Radix]                     ;
        assign router_ini_add_in[0][j/Radix][j%Radix] = '0                                 ;
        assign gnt_o[j/Radix]                         = router_gnt_out[0][j/Radix][j%Radix];
        assign router_add_in[0][j/Radix][j%Radix]     = add_i[j/Radix]                     ;
        assign router_data_in[0][j/Radix][j%Radix]    = wdata_i[j/Radix]                   ;
        assign router_rdy_in[0][j/Radix][j%Radix]     = rdy_i[j/Radix]                     ;

        // Resp
        assign rdata_o[j/Radix] = router_resp_data_out[0][j/Radix][j%Radix];
        assign vld_o[j/Radix]   = router_vld_out[0][j/Radix][j%Radix]      ;
      end else begin : gen_tie_off
        // Req
        assign router_req_in[0][j/Radix][j%Radix]     = 1'b0;
        assign router_ini_add_in[0][j/Radix][j%Radix] = '0  ;
        assign router_add_in[0][j/Radix][j%Radix]     = '0  ;
        assign router_data_in[0][j/Radix][j%Radix]    = '0  ;
        assign router_rdy_in[0][j/Radix][j%Radix]     = 1'b0;
      end
    end
  end

  // Outputs are on the last stage.
  for (genvar j = 0; j < Radix*NumRouters; j++) begin : gen_outputs
    if (j < NumOut) begin : gen_connect
      // Req
      assign req_o[j]                                     = router_req_out[NumStages-1][j/Radix][j%Radix]     ;
      assign ini_add_o[j]                                 = router_ini_add_out[NumStages-1][j/Radix][j%Radix] ;
      assign router_gnt_in[NumStages-1][j/Radix][j%Radix] = gnt_i[j]                                          ;
      assign wdata_o[j]                                   = router_data_out[NumStages-1][j/Radix][j%Radix]    ;
      assign rdy_o[j]                                     = router_rdy_out[NumStages-1][j/Radix][j%Radix]     ;

      // Resp
      assign router_resp_data_in[NumStages-1][j/Radix][j%Radix]    = rdata_i[j]   ;
      assign router_resp_ini_add_in[NumStages-1][j/Radix][j%Radix] = ini_add_i[j] ;
      assign router_vld_in[NumStages-1][j/Radix][j%Radix]          = vld_i[j]     ;
    end else begin : gen_tie_off
      // Req
      assign router_gnt_in[NumStages-1][j/Radix][j%Radix] = 1'b0;

      // Resp
      assign router_resp_data_in[NumStages-1][j/Radix][j%Radix]    = '0  ;
      assign router_resp_ini_add_in[NumStages-1][j/Radix][j%Radix] = '0  ;
      assign router_vld_in[NumStages-1][j/Radix][j%Radix]          = 1'b0;
    end
  end

  // Wire up connections between Stages
  for (genvar l = 0; l < NumStages-1; l++) begin : gen_stages
    // Do we need to add a Radix-2?
    if (l == 0 && NeedsR2Stage ) begin : gen_r4r2_stage
      localparam int unsigned pow = 2*Radix**(NumStages-l-2);

      for (genvar r = 0; r < 2*NumRouters; r++) begin : gen_routers
        for (genvar s = 0; s < 2; s++) begin : gen_ports
          localparam int unsigned k = pow * s + (r % pow) + (r / pow / 2) * pow * 2;
          localparam int unsigned j = (r / pow) % 2                                ;

          assign router_req_in[l+1][k/2][(k%2)*2+j]        = router_req_out[l][r/2][(r%2)*2+s]            ;
          assign router_ini_add_in[l+1][k/2][(k%2)*2+j]    = router_ini_add_out[l][r/2][(r%2)*2+s]        ;
          assign router_rdy_in[l+1][k/2][(k%2)*2+j]        = router_rdy_out[l][r/2][(r%2)*2+s]            ;
          assign router_add_in[l+1][k/2][(k%2)*2+j]        = router_add_out[l][r/2][(r%2)*2+s]            ;
          assign router_data_in[l+1][k/2][(k%2)*2+j]       = router_data_out[l][r/2][(r%2)*2+s]           ;
          assign router_gnt_in[l][r/2][(r%2)*2+s]          = router_gnt_out[l+1][k/2][(k%2)*2+j]          ;
          assign router_resp_data_in[l][r/2][(r%2)*2+s]    = router_resp_data_out[l+1][k/2][(k%2)*2+j]    ;
          assign router_resp_ini_add_in[l][r/2][(r%2)*2+s] = router_resp_ini_add_out[l+1][k/2][(k%2)*2+j] ;
          assign router_vld_in[l][r/2][(r%2)*2+s]          = router_vld_out[l+1][k/2][(k%2)*2+j]          ;
        end
      end
    end else begin : gen_std_stage
      localparam int unsigned pow = Radix**(NumStages-l-2);

      for (genvar s = 0; unsigned'(s) < Radix; s++) begin : gen_routers
        for (genvar r = 0; unsigned'(r) < NumRouters; r++) begin : gen_ports
          localparam int unsigned k = pow * s + (r % pow) + (r / pow / Radix) * pow * Radix;
          localparam int unsigned j = (r / pow) % Radix                                    ;

          assign router_req_in[l+1][k][j]        = router_req_out[l][r][s]            ;
          assign router_ini_add_in[l+1][k][j]    = router_ini_add_out[l][r][s]        ;
          assign router_rdy_in[l+1][k][j]        = router_rdy_out[l][r][s]            ;
          assign router_add_in[l+1][k][j]        = router_add_out[l][r][s]            ;
          assign router_data_in[l+1][k][j]       = router_data_out[l][r][s]           ;
          assign router_gnt_in[l][r][s]          = router_gnt_out[l+1][k][j]          ;
          assign router_resp_data_in[l][r][s]    = router_resp_data_out[l+1][k][j]    ;
          assign router_vld_in[l][r][s]          = router_vld_out[l+1][k][j]          ;
          assign router_resp_ini_add_in[l][r][s] = router_resp_ini_add_out[l+1][k][j] ;
        end
      end
    end
  end

  /*****************
   *   Crossbars   *
   *****************/

  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][AddWidth+IdxWidth+ReqDataWidth-1:0] data_in, data_out;
  logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][IdxWidth+RespDataWidth-1:0]         resp_data_in, resp_data_out;

  for (genvar l = 0; l < NumStages; l++) begin: gen_routers1
    for (genvar r = 0; r < NumRouters; r++) begin: gen_routers2

      // Do we need to add a Radix-2 stage?
      if (l == 0 && NeedsR2Stage) begin : gen_r4r2_stage
        logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][0:0] add                 ;
        logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][0:0] ini_add             ;
        logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][IdxWidth-1:0] ini_add_tmp;
        logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][0:0] resp_ini_add        ;
        logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][0:0] req_prio            ;
        logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][0:0] resp_prio           ;

        for (genvar k = 0; k < Radix; k++) begin : gen_map
          assign add[l][r][k]                                                              = router_add_in[l][r][k][AddWidth-1]                                               ;
          assign resp_ini_add[l][r][k]                                                     = router_resp_ini_add_in[l][r][k][0]                                               ;
          assign data_in[l][r][k]                                                          = {router_add_in[l][r][k]<<1, router_ini_add_in[l][r][k], router_data_in[l][r][k]} ;
          assign {router_add_out[l][r][k], ini_add_tmp[l][r][k], router_data_out[l][r][k]} = data_out[l][r][k]                                                                ;
          assign router_ini_add_out[l][r][k]                                               = {ini_add_tmp[l][r][k], ini_add[l][r][k]}                                         ;
          assign resp_data_in[l][r][k]                                                     = {router_resp_ini_add_in[l][r][k]>>1, router_resp_data_in[l][r][k]}               ;
          assign {router_resp_ini_add_out[l][r][k], router_resp_data_out[l][r][k]}         = resp_data_out[l][r][k]                                                           ;
          assign req_prio[l][r][k]                                                         = req_rr[$clog2(NumOut)-1]                                                         ;
          assign resp_prio[l][r][k]                                                        = resp_rr[$clog2(NumOut)-1]                                                        ;
        end

        for (genvar k = 0; k < 2; k++) begin: gen_xbar
          full_duplex_xbar #(
            .NumIn        (2                                 ),
            .NumOut       (2                                 ),
            .ReqDataWidth (AddWidth + IdxWidth + ReqDataWidth),
            .RespDataWidth(RespDataWidth + IdxWidth          ),
            .ExtPrio      (1'b1                              )
          ) i_xbar (
            .clk_i    (clk_i                         ),
            .rst_ni   (rst_ni                        ),
            // External priority flags
            .req_rr_i (req_prio[l][r][k*2 +: 2]      ),
            .resp_rr_i(resp_prio[l][r][k*2 +: 2]     ),
            // Initiator side
            .req_i    (router_req_in[l][r][k*2 +: 2] ),
            .gnt_o    (router_gnt_out[l][r][k*2 +: 2]),
            .add_i    (add[l][r][k*2 +: 2]           ),
            .wdata_i  (data_in[l][r][k*2 +: 2]       ),
            .vld_o    (router_vld_out[l][r][k*2 +: 2]),
            .rdy_i    (router_rdy_in[l][r][k*2 +: 2] ),
            .rdata_o  (resp_data_out[l][r][k*2 +: 2] ),
            // Target side
            .req_o    (router_req_out[l][r][k*2 +: 2]),
            .ini_add_o(ini_add[l][r][k*2 +: 2]       ),
            .gnt_i    (router_gnt_in[l][r][k*2 +: 2] ),
            .wdata_o  (data_out[l][r][k*2 +: 2]      ),
            .vld_i    (router_vld_in[l][r][k*2 +: 2] ),
            .rdy_o    (router_rdy_out[l][r][k*2 +: 2]),
            .ini_add_i(resp_ini_add[l][r][k*2 +: 2]  ),
            .rdata_i  (resp_data_in[l][r][k*2 +: 2]  )
          );
        end

      // Instantiate switchbox of the chosen Radix.
      end else begin : gen_std_stage
        logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][$clog2(Radix)-1:0] add         ;
        logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][$clog2(Radix)-1:0] ini_add     ;
        logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][IdxWidth-1:0] ini_add_tmp      ;
        logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][$clog2(Radix)-1:0] resp_ini_add;
        logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][$clog2(Radix)-1:0] req_prio    ;
        logic [NumStages-1:0][NumRouters-1:0][Radix-1:0][$clog2(Radix)-1:0] resp_prio   ;

        for (genvar k = 0; k < Radix; k++) begin : gen_map
          assign add[l][r][k]                                                              = router_add_in[l][r][k][AddWidth-1:AddWidth-$clog2(Radix)]                                    ;
          assign resp_ini_add[l][r][k]                                                     = router_resp_ini_add_in[l][r][k][$clog2(Radix)-1:0]                                           ;
          assign data_in[l][r][k]                                                          = {router_add_in[l][r][k]<<$clog2(Radix), router_ini_add_in[l][r][k], router_data_in[l][r][k]} ;
          assign {router_add_out[l][r][k], ini_add_tmp[l][r][k], router_data_out[l][r][k]} = data_out[l][r][k]                                                                            ;
          assign router_ini_add_out[l][r][k]                                               = {ini_add_tmp[l][r][k], ini_add[l][r][k]}                                                     ;
          assign resp_data_in[l][r][k]                                                     = {router_resp_ini_add_in[l][r][k]>>$clog2(Radix), router_resp_data_in[l][r][k]}               ;
          assign {router_resp_ini_add_out[l][r][k], router_resp_data_out[l][r][k]}         = resp_data_out[l][r][k]                                                                       ;

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
          .NumIn        (Radix                             ),
          .NumOut       (Radix                             ),
          .ReqDataWidth (AddWidth + IdxWidth + ReqDataWidth),
          .RespDataWidth(RespDataWidth + IdxWidth          ),
          .ExtPrio      (1'b1                              )
        ) i_xbar (
          .clk_i    (clk_i               ),
          .rst_ni   (rst_ni              ),
          // External priority flags
          .req_rr_i (req_prio[l][r]      ),
          .resp_rr_i(resp_prio[l][r]     ),
          // Initiator side
          .req_i    (router_req_in[l][r] ),
          .gnt_o    (router_gnt_out[l][r]),
          .add_i    (add[l][r]           ),
          .wdata_i  (data_in[l][r]       ),
          .vld_o    (router_vld_out[l][r]),
          .rdy_i    (router_rdy_in[l][r] ),
          .rdata_o  (resp_data_out[l][r] ),
          // Target side
          .req_o    (router_req_out[l][r]),
          .ini_add_o(ini_add[l][r]       ),
          .gnt_i    (router_gnt_in[l][r] ),
          .wdata_o  (data_out[l][r]      ),
          .vld_i    (router_vld_in[l][r] ),
          .rdy_o    (router_rdy_out[l][r]),
          .ini_add_i(resp_ini_add[l][r]  ),
          .rdata_i  (resp_data_in[l][r]  )
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
