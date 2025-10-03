// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Danilo Cammarata <dcammarata@iis.ee.ethz.ch>

`include "hci_helpers.svh"

module opope_streamer
  import fpnew_pkg::*;
  import opope_pkg::*;
  import hci_package::*;
  import hwpe_stream_package::*;
#(
  parameter  int unsigned DW      = 288   ,
  parameter  int unsigned AW      = ADDR_W,
  localparam int unsigned REALIGN = 1     ,
  parameter hci_size_parameter_t `HCI_SIZE_PARAM(tcdm) = '0
)(
  input logic                    clk_i,
  input logic                    rst_ni,
  // Control signals
  input logic                    test_mode_i,
  input logic                    enable_i,
  input logic                    clear_i,
  input  cntrl_streamer_t        ctrl_i,
  output flgs_streamer_t         flags_o,
  // Engine X input + HS signals (output for the streamer)
  hwpe_stream_intf_stream.source x_stream_o,
  // Engine W input + HS signals (output for the streamer)
  hwpe_stream_intf_stream.source w_stream_o,
  // Engine Y input + HS signals (output for the streamer)
  hwpe_stream_intf_stream.source y_stream_o,
  // Engine Z output + HS signals (intput for the streamer)
  hwpe_stream_intf_stream.sink   z_stream_i,
  // TCDM interface between the streamer and the memory
  hci_core_intf.initiator        tcdm      
);

localparam int unsigned UW  = `HCI_SIZE_GET_UW(tcdm);
localparam int unsigned EW  = `HCI_SIZE_GET_EW(tcdm);

// this localparam is reused for all internal, non-ecc HCI interfaces
localparam hci_size_parameter_t `HCI_SIZE_PARAM(ldst_tcdm) = '{
  DW:  DW,
  AW:  DEFAULT_AW,
  BW:  DEFAULT_BW,
  UW:  UW,
  IW:  DEFAULT_IW,
  EW:  DEFAULT_EW,
  EHW: DEFAULT_EHW
};

// this localparam is reused for the  internal ecc HCI interface
localparam hci_size_parameter_t `HCI_SIZE_PARAM(ecc_ldst_tcdm) = '{
  DW:  DW,
  AW:  DEFAULT_AW,
  BW:  DEFAULT_BW,
  UW:  UW,
  IW:  DEFAULT_IW,
  EW:  EW,
  EHW: DEFAULT_EHW
};

// Here the dynamic mux for virtual_tcdm interfaces
// coming/going from/to the accelerator to/from the memory
hci_core_intf #(
`ifndef SYNTHESIS
  .WAIVE_RSP3_ASSERT ( 1'b1 ), // waive RSP-3 on memory-side of HCI FIFO
  .WAIVE_RSP5_ASSERT ( 1'b1 ), // waive RSP-5 on memory-side of HCI FIFO
`endif
  .DW ( DW ),
  .UW ( UW )
) ldst_tcdm ( .clk ( clk_i ) );

hci_core_intf #(
`ifndef SYNTHESIS
  .WAIVE_RSP3_ASSERT ( 1'b1 ), // waive RSP-3 on memory-side of HCI FIFO
  .WAIVE_RSP5_ASSERT ( 1'b1 ), // waive RSP-5 on memory-side of HCI FIFO
`endif
  .DW ( DW ),
  .UW ( UW )
) ldst_tcdm_pre_r_id ( .clk ( clk_i ) );

hci_core_intf #(
`ifndef SYNTHESIS
  .WAIVE_RSP3_ASSERT ( 1'b1 ), // waive RSP-3 on memory-side of HCI FIFO
  .WAIVE_RSP5_ASSERT ( 1'b1 ), // waive RSP-5 on memory-side of HCI FIFO
`endif
  .DW ( DW ),
  .UW ( UW )
) ldst_tcdm_pre_r_valid ( .clk ( clk_i ) );

hci_core_intf #(
`ifndef SYNTHESIS
  .WAIVE_RSP3_ASSERT ( 1'b1 ), // waive RSP-3 on memory-side of HCI FIFO
  .WAIVE_RSP5_ASSERT ( 1'b1 ), // waive RSP-5 on memory-side of HCI FIFO
  .WAIVE_RQ4_ASSERT  ( 1'b1 ),
`endif
  .DW ( DW ),
  .UW ( UW )
) yz_tcdm_pre_r_id ( .clk ( clk_i ) );

if (EW > 1) begin : gen_ecc_encoder
  logic [ECC_N_CHUNK-1:0] data_single_err, data_multi_err;
  logic                   meta_single_err, meta_multi_err;

  hci_ecc_enc #(
    .DW ( DW ),
    .`HCI_SIZE_PARAM(tcdm_target)    ( `HCI_SIZE_PARAM(ldst_tcdm)     ),
    .`HCI_SIZE_PARAM(tcdm_initiator) ( `HCI_SIZE_PARAM(ecc_ldst_tcdm) )
  ) i_ecc_enc (
    .r_data_single_err_o ( data_single_err ),
    .r_data_multi_err_o  ( data_multi_err  ),
    .r_meta_single_err_o ( meta_single_err ),
    .r_meta_multi_err_o  ( meta_multi_err  ),
    .tcdm_target         ( ldst_tcdm       ),
    .tcdm_initiator      ( tcdm            )
  );
end else begin : gen_ldst_assign
  hci_core_assign i_ldst_assign ( .tcdm_target (ldst_tcdm), .tcdm_initiator (tcdm) );
end

// Virtual internal TCDM interface used by the y and z channels
// * Channel 0 - y channel
// * Channel 1 - z channel
hci_core_intf #(
`ifndef SYNTHESIS
  .WAIVE_RSP3_ASSERT ( 1'b1 ), // waive RSP-3 on memory-side of HCI FIFO
  .WAIVE_RSP5_ASSERT ( 1'b1 ), // waive RSP-5 on memory-side of HCI FIFO
  .WAIVE_RQ3_ASSERT  ( 1'b1 ),
  .WAIVE_RQ4_ASSERT  ( 1'b1 ),
`endif
  .DW ( DW ),
  .UW ( UW )
) yz_tcdm [0:1] ( .clk ( clk_i ) );

// Virtual internal TCDM interface splitting the upstream TCDM
hci_core_intf #(
`ifndef SYNTHESIS
  .WAIVE_RSP3_ASSERT ( 1'b1 ), // waive RSP-3 on memory-side of HCI FIFO
  .WAIVE_RSP5_ASSERT ( 1'b1 ), // waive RSP-5 on memory-side of HCI FIFO
  .WAIVE_RQ3_ASSERT  ( 1'b1 ),
  .WAIVE_RQ4_ASSERT  ( 1'b1 ),
`endif
  .DW ( DW ),
  .UW ( UW )
) virt_tcdm [0:NumStreamSources-1] ( .clk ( clk_i ) );


hci_core_mux_ooo #(
  .NB_CHAN              ( 2                          ),
  .`HCI_SIZE_PARAM(out) ( `HCI_SIZE_PARAM(ldst_tcdm) )
) i_yz_mux            (
  .clk_i              ( clk_i                ),
  .rst_ni             ( rst_ni               ),
  .clear_i            ( clear_i              ),
  .priority_force_i   ( '1                   ),
  .priority_i         ( {1'b1, 1'b0}         ), // The z channel always has priority over the y channel
  .in                 ( yz_tcdm              ),
  .out                ( yz_tcdm_pre_r_id     )
);

hci_core_r_id_filter #(
  .`HCI_SIZE_PARAM(tcdm_target)   (   `HCI_SIZE_PARAM(ldst_tcdm) )
) i_yz_r_id_filter (
  .clk_i          (   clk_i                      ),
  .rst_ni         (   rst_ni                     ),
  .clear_i        (   clear_i                    ),
  .enable_i       (   1'b1                       ),
  .tcdm_target    (   yz_tcdm_pre_r_id           ),
  .tcdm_initiator (   virt_tcdm[YsourceStreamId] )
);


hci_core_mux_ooo #(
  .NB_CHAN              ( NumStreamSources           ),
  .`HCI_SIZE_PARAM(out) ( `HCI_SIZE_PARAM(ldst_tcdm) )
) i_ldst_mux          (
  .clk_i              ( clk_i                   ),
  .rst_ni             ( rst_ni                  ),
  .clear_i            ( clear_i                 ),
  // .priority_force_i   ( 'b0 ),
  // .priority_i         ( 'b0       ),
  .priority_force_i   ( ctrl_i.custom_priority_force ),
  .priority_i         ( ctrl_i.custom_priority       ),
  .in                 ( virt_tcdm               ),
  .out                ( ldst_tcdm_pre_r_id      )
);

hci_core_r_id_filter #(
  .`HCI_SIZE_PARAM(tcdm_target)   (   `HCI_SIZE_PARAM(ldst_tcdm) )
) i_load_r_id_filter (
  .clk_i          (   clk_i                 ),
  .rst_ni         (   rst_ni                ),
  .clear_i        (   clear_i               ),
  .enable_i       (   1'b1                  ),
  .tcdm_target    (   ldst_tcdm_pre_r_id    ),
  .tcdm_initiator (   ldst_tcdm_pre_r_valid )
);

hci_core_r_valid_filter #(
  .`HCI_SIZE_PARAM(tcdm_target)   ( `HCI_SIZE_PARAM(ldst_tcdm) )
) i_tcdm_r_valid_filter (
    .clk_i          (  clk_i                 ),
    .rst_ni         (  rst_ni                ),
    .clear_i        (  clear_i               ),
    .enable_i       (  1'b1                  ),
    .tcdm_target    (  ldst_tcdm_pre_r_valid ),
    .tcdm_initiator (  ldst_tcdm             )
);

/************************************ Store Channel *************************************/
/* The store channel of the streamer connects the incoming stream interface (Z stream)  *
 * to an HCI core sink module that translates the stream into a TCDM protocol. This     *
 * sink module then connects to a cast unit to cast data from one FP format to another. *
 * The result of the cast unit enters a TCDM FIFO that eventually connects to the store *
 * side (virt_tcdm[NumStreamSources]) of the LD/ST multiplexer.                         */

// Sink module that turns the incoming Z stream into TCDM.
// FIXME: Explain that 
hci_core_intf #( .DW ( DW ),
                 .UW ( UW ) ) zstream2cast ( .clk ( clk_i ) );
hci_core_sink         #(
  // .MISALIGNED_ACCESSES ( 1'b0                      ),
    .MISALIGNED_ACCESSES   ( REALIGN                    ),
  .`HCI_SIZE_PARAM(tcdm) ( `HCI_SIZE_PARAM(ldst_tcdm) )
) i_stream_sink        (
  .clk_i               ( clk_i                       ),
  .rst_ni              ( rst_ni                      ),
  .test_mode_i         ( test_mode_i                 ),
  .clear_i             ( clear_i                     ),
  .enable_i            ( enable_i                    ),
  .tcdm                ( zstream2cast                ),
  .stream              ( z_stream_i                  ),
  .ctrl_i              ( ctrl_i.z_stream_sink_ctrl   ),
  .flags_o             ( flags_o.z_stream_sink_flags )
);

// Store interface FIFO buses.
hci_core_intf #(
`ifndef SYNTHESIS
  .WAIVE_RSP3_ASSERT ( 1'b1 ), // waive RSP-3 on memory-side of HCI FIFO
  .WAIVE_RSP5_ASSERT ( 1'b1 ),  // waive RSP-5 on memory-side of HCI FIFO
`endif
  .DW ( DW ),
  .UW ( UW )
) z_fifo_d ( .clk ( clk_i ) );
hci_core_intf #( .DW ( DW ),
                 .UW ( UW ) ) z_fifo_q ( .clk ( clk_i ) );


assign z_fifo_d.data      = zstream2cast.data;

// Left TCDM buses assignment.
assign z_fifo_d.req          = zstream2cast.req;
assign zstream2cast.gnt      = z_fifo_d.gnt;
assign z_fifo_d.add          = zstream2cast.add;
assign z_fifo_d.wen          = zstream2cast.wen;
// do not assign z_fifo_d.data <-> zstream2cast.data
assign z_fifo_d.be           = zstream2cast.be;
assign z_fifo_d.r_ready      = zstream2cast.r_ready;
assign z_fifo_d.user         = zstream2cast.user;
assign z_fifo_d.id           = zstream2cast.id;
assign zstream2cast.r_data   = z_fifo_d.r_data;
assign zstream2cast.r_valid  = z_fifo_d.r_valid;
assign zstream2cast.r_user   = z_fifo_d.r_user;
assign zstream2cast.r_id     = z_fifo_d.r_id;
assign z_fifo_d.ereq         = zstream2cast.ereq;
assign zstream2cast.egnt     = z_fifo_d.egnt;
assign zstream2cast.r_evalid = z_fifo_d.r_evalid;
assign z_fifo_d.r_eready     = zstream2cast.r_eready;
assign z_fifo_d.ecc          = zstream2cast.ecc;
assign zstream2cast.r_ecc    = z_fifo_d.r_ecc;

// HCI store fifo.
hci_core_fifo #(
  .FIFO_DEPTH                      ( 2                          ),
  .`HCI_SIZE_PARAM(tcdm_initiator) ( `HCI_SIZE_PARAM(ldst_tcdm) )
) i_store_fifo (
  .clk_i          ( clk_i    ),
  .rst_ni         ( rst_ni   ),
  .clear_i        ( clear_i  ),
  .flags_o        (          ),
  .tcdm_target    ( z_fifo_d ),
  .tcdm_initiator ( z_fifo_q )
);

// Assigning the store FIFO output to the store side of the y/z multiplexer.
hci_core_assign i_store_assign ( .tcdm_target (z_fifo_q), .tcdm_initiator (yz_tcdm[1]) );

/**************************************** Load Channel ****************************************/
/* The load channel of the streamer connects the incoming TCDM interface to three different   *
 * stream interfaces: X stream (ID: 0), W stream (ID: 1), and Y stream (ID: 2). The load side *
 * (virt_tcdm[0]) of the LD/ST multiplexer connects to another multiplexer that splits the    *
 * icoming TCDM bus into three TCDM interfaces (X, W, and Y). Each interface connects to its  *
 * own FIFO, and then to a cas unit that casts the data from one FP format to another. Then,  *
 * the output of the cast connects to a dedicated HCI core source unit used to translate the  *
 * incoming TCDM protocls into stream.                        */

// Virtual TCDM interfaces
// X   -> virt_tcdm[0]
// W   -> virt_tcdm[1]
// Y/Z -> virt_tcdm[2]

// One TCDM FIFO and one HCI core source unit per stream channel.
hci_core_intf #(
`ifndef SYNTHESIS
  .WAIVE_RSP3_ASSERT ( 1'b1 ), // waive RSP-3 on memory-side of HCI FIFO
  .WAIVE_RSP5_ASSERT ( 1'b1 ),  // waive RSP-5 on memory-side of HCI FIFO
  .WAIVE_RQ4_ASSERT  ( 1'b1 ),
`endif
  .DW ( DW ),
  .UW ( UW )
) load_fifo_d [0:NumStreamSources-1] ( .clk ( clk_i ) );

hci_core_intf #(
`ifndef SYNTHESIS
  .WAIVE_RSP3_ASSERT ( 1'b1 ),
  .WAIVE_RSP5_ASSERT ( 1'b1 ),
  .WAIVE_RQ4_ASSERT  ( 1'b1 ),
`endif
  .DW ( DW ),
  .UW ( UW )
) load_fifo_q [0:NumStreamSources-1] ( .clk ( clk_i ) );

hci_core_intf #(
`ifndef SYNTHESIS
  .WAIVE_RSP3_ASSERT ( 1'b1 ),
  .WAIVE_RSP5_ASSERT ( 1'b1 ),
  .WAIVE_RQ4_ASSERT  ( 1'b1 ),
`endif
  .DW ( DW ),
  .UW ( UW ) ) tcdm_cast [0:NumStreamSources-1] ( .clk ( clk_i ) );

hwpe_stream_intf_stream #( .DATA_WIDTH ( DATAW ) ) out_stream [NumStreamSources-1:0] ( .clk( clk_i ) );

hci_package::hci_streamer_ctrl_t  [NumStreamSources-1:0] source_ctrl;
hci_package::hci_streamer_flags_t [NumStreamSources-1:0] source_flags;

// Assign input control buses to the relative ID in the vector.
assign source_ctrl[XsourceStreamId]      = ctrl_i.x_stream_source_ctrl;
assign source_ctrl[WsourceStreamId]      = ctrl_i.w_stream_source_ctrl;
assign source_ctrl[YsourceStreamId]      = ctrl_i.y_stream_source_ctrl;

for (genvar i = 0; i < NumStreamSources; i++) begin: gen_tcdm2stream

  if (i != YsourceStreamId) begin
    hci_core_assign i_load_assign ( .tcdm_target (load_fifo_d[i]), .tcdm_initiator (virt_tcdm[i]) );
  end else begin
    hci_core_assign i_load_assign ( .tcdm_target (load_fifo_d[i]), .tcdm_initiator (yz_tcdm[0]) );
  end

  hci_core_fifo #(
    .FIFO_DEPTH  ( 4  ), // to avoid protocol violations, as the consumer has a throughput
                         // of 1 packet over 4 cycles, we need a depth of 4 elements.
    .`HCI_SIZE_PARAM(tcdm_initiator) ( `HCI_SIZE_PARAM(ldst_tcdm) )
  ) i_load_tcdm_fifo (
    .clk_i          ( clk_i          ),
    .rst_ni         ( rst_ni         ),
    .clear_i        ( clear_i        ),
    .flags_o        (                ),
    .tcdm_target    ( load_fifo_q[i] ),
    .tcdm_initiator ( load_fifo_d[i] )
  );


  assign tcdm_cast[i].r_data = load_fifo_q[i].r_data;

  // Left TCDM buses assignment.
  assign load_fifo_q[i].req      = tcdm_cast[i].req;
  assign tcdm_cast[i].gnt        = load_fifo_q[i].gnt;
  assign load_fifo_q[i].add      = tcdm_cast[i].add;
  assign load_fifo_q[i].wen      = tcdm_cast[i].wen;
  assign load_fifo_q[i].data     = tcdm_cast[i].data;
  assign load_fifo_q[i].be       = tcdm_cast[i].be;
  assign load_fifo_q[i].r_ready  = tcdm_cast[i].r_ready;
  assign load_fifo_q[i].user     = tcdm_cast[i].user;
  assign load_fifo_q[i].id       = tcdm_cast[i].id;
  assign tcdm_cast[i].r_valid    = load_fifo_q[i].r_valid;
  // do not assign tcdm_cast[i].r_data = load_fifo_q[i].r_data
  assign tcdm_cast[i].r_opc      = load_fifo_q[i].r_opc;
  assign tcdm_cast[i].r_user     = load_fifo_q[i].r_user;
  assign tcdm_cast[i].r_id       = load_fifo_q[i].r_id;
  assign load_fifo_q[i].ereq     = tcdm_cast[i].ereq;
  assign tcdm_cast[i].egnt       = load_fifo_q[i].egnt;
  assign tcdm_cast[i].r_evalid   = load_fifo_q[i].r_evalid;
  assign load_fifo_q[i].r_eready = tcdm_cast[i].r_eready;
  assign load_fifo_q[i].ecc      = tcdm_cast[i].ecc;
  assign tcdm_cast[i].r_ecc      = load_fifo_q[i].r_ecc;

  hci_core_source       #(
    .MISALIGNED_ACCESSES   ( REALIGN                    ),
    .`HCI_SIZE_PARAM(tcdm) ( `HCI_SIZE_PARAM(ldst_tcdm) )
  ) i_stream_source      (
    .clk_i               ( clk_i           ),
    .rst_ni              ( rst_ni          ),
    .test_mode_i         ( test_mode_i     ),
    .clear_i             ( clear_i         ),
    .enable_i            ( enable_i        ),
    .tcdm                ( tcdm_cast[i]    ),
    .stream              ( out_stream[i]   ),
    .ctrl_i              ( source_ctrl[i]  ),
    .flags_o             ( source_flags[i] )
  );
end

// Assign flags in the vector to the relative output buses.
assign flags_o.x_stream_source_flags = source_flags[XsourceStreamId];
assign flags_o.w_stream_source_flags = source_flags[WsourceStreamId];
assign flags_o.y_stream_source_flags = source_flags[YsourceStreamId];

assign flags_o.x_granted = virt_tcdm[XsourceStreamId].gnt;
assign flags_o.w_granted = virt_tcdm[WsourceStreamId].gnt;
assign flags_o.y_granted = virt_tcdm[YsourceStreamId].gnt;

// Assign resulting streams.
hwpe_stream_assign i_xstream_assign ( .push_i( out_stream[XsourceStreamId] ) ,
      .pop_o ( x_stream_o                  ) );

hwpe_stream_assign i_wstream_assign ( .push_i( out_stream[WsourceStreamId] ) ,
      .pop_o ( w_stream_o                  ) );

hwpe_stream_assign i_ystream_assign ( .push_i( out_stream[YsourceStreamId] ) ,
      .pop_o ( y_stream_o                  ) );

endmodule : opope_streamer
