module mempool_cc #(
  parameter logic [31:0] BootAddr   = 32'h0000_1000,
  parameter logic [31:0] MTVEC      = BootAddr,
  parameter bit          RVE        = 0,  // Reduced-register extension
  parameter bit          RVM        = 1,  // Enable IntegerMmultiplication & Division Extension
  parameter bit RegisterOffloadReq  = 1,
  parameter bit RegisterOffloadResp = 1,
  parameter bit RegisterTCDMReq     = 0,
  parameter bit RegisterTCDMResp    = 0
) (
  input  logic               clk_i,
  input  logic               rst_i,
  input  logic [31:0]        hart_id_i,
  // Instruction Port
  output logic [31:0]        inst_addr_o,
  input  logic [31:0]        inst_data_i,
  output logic               inst_valid_o,
  input  logic               inst_ready_i,
  // TCDM Ports
  output logic [31:0]        data_qaddr_o,
  output logic               data_qwrite_o,
  output logic [3:0]         data_qamo_o,
  output logic [31:0]        data_qdata_o,
  output logic [3:0]         data_qstrb_o,
  output logic               data_qvalid_o,
  input  logic               data_qready_i,
  input  logic [31:0]        data_pdata_i,
  input  logic               data_perror_i,
  input  logic               data_pvalid_i,
  output logic               data_pready_o,
  input  logic               wake_up_sync_i,
  // Core event strobes
  output snitch_pkg::core_events_t core_events_o
);

  // Data port signals
  snitch_pkg::dreq_t  data_req_d, data_req_q;
  snitch_pkg::dresp_t data_resp_d, data_resp_q;

  logic data_req_d_valid, data_req_d_ready, data_resp_d_valid, data_resp_d_ready;
  logic data_req_q_valid, data_req_q_ready, data_resp_q_valid, data_resp_q_ready;

  // Accelerator signals
  snitch_pkg::acc_req_t  acc_req_d,  acc_req_q;
  snitch_pkg::acc_resp_t acc_resp_d, acc_resp_q;

  logic acc_req_d_valid, acc_req_d_ready, acc_resp_d_valid, acc_resp_d_ready;
  logic acc_req_q_valid, acc_req_q_ready, acc_resp_q_valid, acc_resp_q_ready;

  // Snitch Integer Core
  snitch #(
    .BootAddr ( BootAddr ),
    .MTVEC    ( MTVEC    ),
    .RVE      ( RVE      ),
    .RVM      ( RVM      )
  ) i_snitch (
    .clk_i                                   ,
    .rst_i                                   ,
    .hart_id_i                               ,
    .inst_addr_o                             ,
    .inst_data_i                             ,
    .inst_valid_o                            ,
    .inst_ready_i                            ,
    .acc_qaddr_o      ( acc_req_d.addr      ),
    .acc_qid_o        ( acc_req_d.id        ),
    .acc_qdata_op_o   ( acc_req_d.data_op   ),
    .acc_qdata_arga_o ( acc_req_d.data_arga ),
    .acc_qdata_argb_o ( acc_req_d.data_argb ),
    .acc_qdata_argc_o ( acc_req_d.data_argc ),
    .acc_qvalid_o     ( acc_req_d_valid     ),
    .acc_qready_i     ( acc_req_d_ready     ),
    .acc_pdata_i      ( acc_resp_q.data     ),
    .acc_pid_i        ( acc_resp_q.id       ),
    .acc_perror_i     ( acc_resp_q.error    ),
    .acc_pvalid_i     ( acc_resp_q_valid    ),
    .acc_pready_o     ( acc_resp_q_ready    ),
    .data_qaddr_o     ( data_req_d.addr     ),
    .data_qwrite_o    ( data_req_d.write    ),
    .data_qamo_o      ( data_req_d.amo      ),
    .data_qdata_o     ( data_req_d.data     ),
    .data_qstrb_o     ( data_req_d.strb     ),
    .data_qvalid_o    ( data_req_d_valid    ),
    .data_qready_i    ( data_req_d_ready    ),
    .data_pdata_i     ( data_resp_q.data    ),
    .data_perror_i    ( data_resp_q.error   ),
    .data_pvalid_i    ( data_resp_q_valid   ),
    .data_pready_o    ( data_resp_q_ready   ),
    .wake_up_sync_i   ( wake_up_sync_i      ),
    .core_events_o    ( core_events_o       )
  );

  // Cut off-loading request path
  spill_register #(
    .T      ( snitch_pkg::acc_req_t ),
    .Bypass ( !RegisterOffloadReq   )
  ) i_spill_register_acc_req (
    .clk_i   ,
    .rst_ni  ( ~rst_i          ),
    .valid_i ( acc_req_d_valid ),
    .ready_o ( acc_req_d_ready ),
    .data_i  ( acc_req_d       ),
    .valid_o ( acc_req_q_valid ),
    .ready_i ( acc_req_q_ready ),
    .data_o  ( acc_req_q       )
  );

  // Cut off-loading response path
  spill_register #(
    .T      ( snitch_pkg::acc_resp_t ),
    .Bypass ( !RegisterOffloadResp   )
  ) i_spill_register_acc_resp (
    .clk_i                       ,
    .rst_ni  ( ~rst_i           ),
    .valid_i ( acc_resp_d_valid ),
    .ready_o ( acc_resp_d_ready ),
    .data_i  ( acc_resp_d       ),
    .valid_o ( acc_resp_q_valid ),
    .ready_i ( acc_resp_q_ready ),
    .data_o  ( acc_resp_q       )
  );

  if (snitch_pkg::XPULPIMG) begin : gen_ipu
    // Snitch IPU accelerator
    snitch_ipu #(
      .IdWidth ( 5 )
    ) i_snitch_ipu (
      .clk_i                                   ,
      .rst_i                                   ,
      .acc_qaddr_i      ( acc_req_q.addr      ),
      .acc_qid_i        ( acc_req_q.id        ),
      .acc_qdata_op_i   ( acc_req_q.data_op   ),
      .acc_qdata_arga_i ( acc_req_q.data_arga ),
      .acc_qdata_argb_i ( acc_req_q.data_argb ),
      .acc_qdata_argc_i ( acc_req_q.data_argc ),
      .acc_qvalid_i     ( acc_req_q_valid     ),
      .acc_qready_o     ( acc_req_q_ready     ),
      .acc_pdata_o      ( acc_resp_d.data     ),
      .acc_pid_o        ( acc_resp_d.id       ),
      .acc_perror_o     ( acc_resp_d.error    ),
      .acc_pvalid_o     ( acc_resp_d_valid    ),
      .acc_pready_i     ( acc_resp_d_ready    )
    );
  end else begin : gen_shared_muldiv
    // Snitch Multiplier/Divider accelerator
    snitch_shared_muldiv #(
      .IdWidth ( 5 )
    ) i_snitch_shared_muldiv (
      .clk_i                                   ,
      .rst_i                                   ,
      .acc_qaddr_i      ( acc_req_q.addr      ),
      .acc_qid_i        ( acc_req_q.id        ),
      .acc_qdata_op_i   ( acc_req_q.data_op   ),
      .acc_qdata_arga_i ( acc_req_q.data_arga ),
      .acc_qdata_argb_i ( acc_req_q.data_argb ),
      .acc_qdata_argc_i ( acc_req_q.data_argc ),
      .acc_qvalid_i     ( acc_req_q_valid     ),
      .acc_qready_o     ( acc_req_q_ready     ),
      .acc_pdata_o      ( acc_resp_d.data     ),
      .acc_pid_o        ( acc_resp_d.id       ),
      .acc_perror_o     ( acc_resp_d.error    ),
      .acc_pvalid_o     ( acc_resp_d_valid    ),
      .acc_pready_i     ( acc_resp_d_ready    )
    );
  end

  // Cut TCDM data request path
  spill_register #(
    .T      ( snitch_pkg::dreq_t ),
    .Bypass ( !RegisterTCDMReq   )
  ) i_spill_register_tcdm_req (
    .clk_i                       ,
    .rst_ni  ( ~rst_i           ),
    .valid_i ( data_req_d_valid ),
    .ready_o ( data_req_d_ready ),
    .data_i  ( data_req_d       ),
    .valid_o ( data_req_q_valid ),
    .ready_i ( data_req_q_ready ),
    .data_o  ( data_req_q       )
  );

  // Cut TCDM data response path
  spill_register #(
    .T      ( snitch_pkg::dresp_t ),
    .Bypass ( !RegisterTCDMResp   )
  ) i_spill_register_tcdm_resp (
    .clk_i                       ,
    .rst_ni  ( ~rst_i           ),
    .valid_i ( data_resp_d_valid ),
    .ready_o ( data_resp_d_ready ),
    .data_i  ( data_resp_d       ),
    .valid_o ( data_resp_q_valid ),
    .ready_i ( data_resp_q_ready ),
    .data_o  ( data_resp_q       )
  );

  // Assign TCDM data interface
  assign data_qaddr_o      = data_req_q.addr;
  assign data_qwrite_o     = data_req_q.write;
  assign data_qamo_o       = data_req_q.amo;
  assign data_qdata_o      = data_req_q.data;
  assign data_qstrb_o      = data_req_q.strb;
  assign data_qvalid_o     = data_req_q_valid;
  assign data_req_q_ready  = data_qready_i;
  assign data_resp_d.data  = data_pdata_i;
  assign data_resp_d.error = data_perror_i;
  assign data_resp_d_valid = data_pvalid_i;
  assign data_pready_o     = data_resp_d_ready;

  // --------------------------
  // Tracer
  // --------------------------
  // pragma translate_off
  int f;
  string fn;
  logic [63:0] cycle;

  always_ff @(posedge rst_i) begin
    if(rst_i) begin
      $sformat(fn, "trace_hart_%04.0f.dasm", hart_id_i);
      f = $fopen(fn, "w");
      $display("[Tracer] Logging Hart %d to %s", hart_id_i, fn);
    end
  end

  logic stall_instr;
  always_ff @(posedge clk_i) begin
    if(rst_i) begin
      stall_instr <= 0;
    end else begin
      stall_instr <= (!i_snitch.inst_ready_i) && (i_snitch.inst_valid_o);
    end
  end

  typedef enum logic [1:0] {SrcSnitch =  0, SrcFpu = 1, SrcFpuSeq = 2} trace_src_e;

  longint extras_snitch       [string];

  assign extras_snitch = '{
    // State
    "source":       SrcSnitch,
    "stall":        i_snitch.stall,
    "stall_instr":  stall_instr,
    "stall_data":   ((!i_snitch.operands_ready) || (!i_snitch.dst_ready)),
    "stall_lsu":    i_snitch.lsu_stall,
    "stall_acc":    i_snitch.acc_stall,
    // Decoding
    "rs1":          i_snitch.rs1,
    "rs2":          i_snitch.rs2,
    "rd":           i_snitch.rd,
    "is_load":      i_snitch.is_load,
    "is_store":     i_snitch.is_store,
    "is_branch":    i_snitch.is_branch,
    "pc_d":         i_snitch.pc_d,
    // Operands
    "opa":          i_snitch.opa,
    "opb":          i_snitch.opb,
    "opa_select":   i_snitch.opa_select,
    "opb_select":   i_snitch.opb_select,
    "write_rd":     i_snitch.write_rd,
    "csr_addr":     i_snitch.inst_data_i[31:20],
    // Pipeline writeback
    "writeback":    i_snitch.alu_writeback,
    // Load/Store
    "gpr_rdata_1":  i_snitch.gpr_rdata[1],
    "ls_size":      i_snitch.ls_size,
    "ld_result_32": i_snitch.ld_result[31:0],
    "lsu_rd":       i_snitch.lsu_rd,
    "retire_load":  i_snitch.retire_load,
    "alu_result":   i_snitch.alu_result,
    // Atomics
    "ls_amo":       i_snitch.ls_amo,
    // Accumulator
    "retire_acc":   i_snitch.retire_acc,
    "acc_pid":      i_snitch.acc_pid_i,
    "acc_pdata_32": i_snitch.acc_pdata_i[31:0],
    // FPU offload
    "fpu_offload":  (i_snitch.acc_qready_i && i_snitch.acc_qvalid_o && !snitch_pkg::shared_offload(i_snitch.acc_qdata_op_o)),
    "is_seq_insn":  (i_snitch.inst_data_i ==? riscv_instr::FREP)
  };

  task fmt_extras (
    input longint extras [string],
    output string extras_str
  );
    extras_str = "{";
    foreach(extras[key]) extras_str = $sformatf("%s'%s': 0x%8x, ", extras_str, key, extras[key]);
    extras_str = $sformatf("%s}", extras_str);
  endtask

  always_ff @(posedge clk_i) begin
      automatic string trace_entry;
      automatic string extras_str;

      if (!rst_i) begin
        cycle++;
        // Trace snitch iff:
        // we are not stalled <==> we have issued and processed an instruction (including offloads)
        // OR we are retiring (issuing a writeback from) a load or accelerator instruction
        if (
            !i_snitch.stall || i_snitch.retire_load || i_snitch.retire_acc
        ) begin
          fmt_extras(extras_snitch, extras_str);
          $sformat(trace_entry, "%t %8d 0x%h DASM(%h) #; %s\n",
              $time, cycle, i_snitch.pc_q, i_snitch.inst_data_i, extras_str);
          $fwrite(f, trace_entry);
        end
      end else begin
        cycle = '0;
      end
    end

  final begin
    $fclose(f);
  end
  // pragma translate_on

endmodule
