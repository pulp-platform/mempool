// TCDM Shim

// Description: Converts propper handshaking (ready/valid) to TCDM signaling
// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>

import mempool_pkg::address_map_t;

module tcdm_shim #(
    parameter int unsigned AddrWidth           = 32         ,
    parameter int unsigned DataWidth           = 32         ,
    parameter int unsigned MaxOutStandingReads = 2          ,
    parameter bit InclDemux                    = 1'b1       ,
    parameter int unsigned NrTCDM              = 2          ,
    parameter int unsigned NrSoC               = 1          ,
    parameter int unsigned NumRules            = 1          , // Routing rules
    localparam int unsigned StrbWidth          = DataWidth/8,
    localparam int unsigned NumOutput          = NrTCDM + NrSoC
  ) (
    input  logic                                     clk_i,
    input  logic                                     rst_ni,
    // to TCDM
    output logic         [NrTCDM-1:0]                tcdm_req_valid_o,
    output logic         [NrTCDM-1:0][AddrWidth-1:0] tcdm_req_tgt_addr_o,
    output logic         [NrTCDM-1:0]                tcdm_req_wen_o,
    output logic         [NrTCDM-1:0][DataWidth-1:0] tcdm_req_wdata_o,
    output logic         [NrTCDM-1:0][StrbWidth-1:0] tcdm_req_be_o,
    input  logic         [NrTCDM-1:0]                tcdm_req_ready_i,
    input  logic         [NrTCDM-1:0]                tcdm_resp_valid_i,
    output logic         [NrTCDM-1:0]                tcdm_resp_ready_o,
    input  logic         [NrTCDM-1:0][DataWidth-1:0] tcdm_resp_rdata_i,
    // to SoC
    output logic         [NrSoC-1:0] [AddrWidth-1:0] soc_qaddr_o,
    output logic         [NrSoC-1:0]                 soc_qwrite_o,
    output logic         [NrSoC-1:0] [3:0]           soc_qamo_o,
    output logic         [NrSoC-1:0] [DataWidth-1:0] soc_qdata_o,
    output logic         [NrSoC-1:0] [StrbWidth-1:0] soc_qstrb_o,
    output logic         [NrSoC-1:0]                 soc_qvalid_o,
    input  logic         [NrSoC-1:0]                 soc_qready_i,
    input  logic         [NrSoC-1:0] [DataWidth-1:0] soc_pdata_i,
    input  logic         [NrSoC-1:0]                 soc_perror_i,
    input  logic         [NrSoC-1:0]                 soc_pvalid_i,
    output logic         [NrSoC-1:0]                 soc_pready_o,
    // from core
    input  logic         [AddrWidth-1:0]             data_qaddr_i,
    input  logic                                     data_qwrite_i,
    input  logic         [3:0]                       data_qamo_i,
    input  logic         [DataWidth-1:0]             data_qdata_i,
    input  logic         [StrbWidth-1:0]             data_qstrb_i,
    input  logic                                     data_qvalid_i,
    output logic                                     data_qready_o,
    output logic         [DataWidth-1:0]             data_pdata_o,
    output logic                                     data_perror_o,
    output logic                                     data_pvalid_o,
    input  logic                                     data_pready_i,
    // Address map
    input  address_map_t [NumRules-1:0]              address_map_i
  );

  // Imports
  import snitch_pkg::dreq_t ;
  import snitch_pkg::dresp_t;

  // Includes
  `include "common_cells/registers.svh"

  dreq_t              data_qpayload ;
  dreq_t [NrSoC-1:0]  soc_qpayload ;
  dreq_t [NrTCDM-1:0] tcdm_qpayload;

  dresp_t              data_ppayload ;
  dresp_t [NrSoC-1:0]  soc_ppayload ;
  dresp_t [NrTCDM-1:0] tcdm_ppayload;

  logic [NrTCDM-1:0] tcdm_qvalid;
  logic [NrTCDM-1:0] tcdm_qready;
  logic [NrTCDM-1:0] tcdm_pvalid;
  logic [NrTCDM-1:0] tcdm_pready;

  for (genvar i = 0; i < NrTCDM; i++) begin : gen_tcdm_credits
    // TCDM Request credits
    mempool_pkg::credit_t tcdm_req_credits_q, tcdm_req_credits_d;
    `FF(tcdm_req_credits_q, tcdm_req_credits_d, 0)

    always_comb begin
      tcdm_req_credits_d = tcdm_req_credits_q;
      if (tcdm_req_ready_i[i]) tcdm_req_credits_d++ ;
      if (tcdm_req_valid_o[i]) tcdm_req_credits_d-- ;
    end
    assign tcdm_req_valid_o[i] = tcdm_qvalid[i] & (tcdm_req_credits_q != '0);
    assign tcdm_qready[i]      = (tcdm_req_credits_q != '0)                 ;

    // TCDM Response credits
    logic [$clog2(MaxOutStandingReads):0] tcdm_resp_credits_q, tcdm_resp_credits_d;
    logic tcdm_resp_fifo_empty ;
    logic tcdm_resp_fifo_pop   ;

    `FF(tcdm_resp_credits_q, tcdm_resp_credits_d, MaxOutStandingReads)
    `FF(tcdm_resp_ready_o[i], (tcdm_resp_credits_d != '0), 1'b0)
    always_comb begin
      tcdm_resp_credits_d = tcdm_resp_credits_q;
      if (tcdm_resp_ready_o[i]) tcdm_resp_credits_d-- ;
      if (tcdm_resp_fifo_pop) tcdm_resp_credits_d++   ;
    end

    fifo_v3 #(
      .DATA_WIDTH  (DataWidth          ),
      .DEPTH       (MaxOutStandingReads),
      .FALL_THROUGH(1'b1               )
    ) i_resp_fifo (
      .clk_i     (clk_i                ),
      .rst_ni    (rst_ni               ),
      .flush_i   (1'b0                 ),
      .testmode_i(1'b0                 ),
      .data_i    (tcdm_resp_rdata_i[i] ),
      .push_i    (tcdm_resp_valid_i[i] ),
      .full_o    (/* Unused */         ),
      .data_o    (tcdm_ppayload[i].data),
      .pop_i     (tcdm_resp_fifo_pop   ),
      .empty_o   (tcdm_resp_fifo_empty ),
      .usage_o   (/* Unused */         )
    );

    assign tcdm_ppayload[i].error = 1'b0                           ;
    assign tcdm_pvalid[i]         = ~tcdm_resp_fifo_empty          ;
    assign tcdm_resp_fifo_pop     = tcdm_pvalid[i] & tcdm_pready[i];
  end

  // Demux according to address
  if (InclDemux) begin : gen_addr_demux
    snitch_addr_demux #(
      .NrOutput           (NumOutput),
      .AddressWidth       (AddrWidth),
      .NumRules           (NumRules ), // TODO
      .MaxOutStandingReads(NumOutput), // TODO
      .req_t              (dreq_t   ),
      .resp_t             (dresp_t  )
    ) i_snitch_addr_demux (
      .clk_i         (clk_i                        ),
      .rst_ni        (rst_ni                       ),
      .req_addr_i    (data_qaddr_i                 ),
      .req_write_i   (data_qwrite_i                ),
      .req_payload_i (data_qpayload                ),
      .req_valid_i   (data_qvalid_i                ),
      .req_ready_o   (data_qready_o                ),
      .resp_payload_o(data_ppayload                ),
      .resp_valid_o  (data_pvalid_o                ),
      .resp_ready_i  (data_pready_i                ),
      .req_payload_o ({soc_qpayload, tcdm_qpayload}),
      .req_valid_o   ({soc_qvalid_o, tcdm_qvalid}  ),
      .req_ready_i   ({soc_qready_i, tcdm_qready}  ),
      .resp_payload_i({soc_ppayload, tcdm_ppayload}),
      .resp_valid_i  ({soc_pvalid_i, tcdm_pvalid}  ),
      .resp_ready_o  ({soc_pready_o, tcdm_pready}  ),
      .address_map_i (address_map_i                )
    );
  end else begin : gen_no_addr_demux
    always_comb begin
      // tie-off unused TCDM and SoC ports
      tcdm_qpayload    = '0              ;
      tcdm_qvalid      = '0              ;
      tcdm_pready      = '0              ;
      soc_qpayload     = '0              ;
      soc_qvalid_o     = '0              ;
      soc_pready_o     = '0              ;
      // directly connect first TCDM port
      tcdm_qpayload[0] = data_qpayload   ;
      tcdm_qvalid[0]   = data_qvalid_i   ;
      data_qready_o    = tcdm_qready[0]  ;
      data_ppayload    = tcdm_ppayload[0];
      data_pvalid_o    = tcdm_pvalid[0]  ;
      tcdm_pready[0]   = data_pready_i   ;
    end
  end

  // Connect output ports
  for (genvar i = 0; i < NrTCDM; i++) begin : gen_tcdm_con
    assign tcdm_req_tgt_addr_o[i] = tcdm_qpayload[i].addr ;
    assign tcdm_req_wdata_o[i]    = tcdm_qpayload[i].data ;
    assign tcdm_req_wen_o[i]      = tcdm_qpayload[i].write;
    assign tcdm_req_be_o[i]       = tcdm_qpayload[i].strb ;
  end

  // Request interface
  assign data_qpayload.addr  = data_qaddr_i       ;
  assign data_qpayload.write = data_qwrite_i      ;
  assign data_qpayload.data  = data_qdata_i       ;
  assign data_qpayload.strb  = data_qstrb_i       ;
  assign data_pdata_o        = data_ppayload.data ;
  assign data_perror_o       = data_ppayload.error;


  for (genvar i = 0; i < NrSoC; i++) begin : gen_soc_con
    assign soc_qaddr_o[i]        = soc_qpayload[i].addr ;
    assign soc_qwrite_o[i]       = soc_qpayload[i].write;
    assign soc_qamo_o[i]         = '0                   ;
    assign soc_qdata_o[i]        = soc_qpayload[i].data ;
    assign soc_qstrb_o[i]        = soc_qpayload[i].strb ;
    assign soc_ppayload[i].data  = soc_pdata_i[i]       ;
    assign soc_ppayload[i].error = soc_perror_i[i]      ;
  end

  // Elaboration-time assertions

  if (AddrWidth != 32)
    $fatal(1, "[tcdm_shim] Only support 32-bit wide addresses.");

  if (DataWidth != 32)
    $fatal(1, "[tcdm_shim] Only support a data width of 32 bits.");

endmodule
