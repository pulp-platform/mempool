// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Authors: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
//          Sergio Mazzola <smazzola@student.ethz.ch>
//          Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>
// Description: Top-Level of Snitch Integer Core RV32E

`include "common_cells/registers.svh"
`include "common_cells/assertions.svh"

// `SNITCH_ENABLE_PERF Enables mcycle, minstret performance counters (read only)
// `SNITCH_ENABLE_STALL_COUNTER Enables stall_ins, stall_raw, stall_lsu performance counters (read only)

module snitch
  import snitch_pkg::meta_id_t;
  import snitch_pkg::acc_addr_e;
#(
  parameter logic [31:0] BootAddr  = 32'h0000_1000,
  parameter logic [31:0] MTVEC     = BootAddr, // Exception Base Address (see privileged spec 3.1.7)
  parameter bit          RVE       = 0,   // Reduced-register Extension
  parameter bit          RVM       = 1,   // Enable IntegerMmultiplication & Division Extension
  parameter int    RegNrWritePorts = 2    // Implement one or two write ports into the register file
) (
  input  logic          clk_i,
  input  logic          rst_ni,
  input  logic [31:0]   hart_id_i,
  // Instruction Refill Port
  output logic [31:0]   inst_addr_o,
  input  logic [31:0]   inst_data_i,
  output logic          inst_valid_o,
  input  logic          inst_ready_i,
`ifdef RISCV_FORMAL
  output logic [0:0]       rvfi_valid,
  output logic [0:0][63:0] rvfi_order,
  output logic [0:0][31:0] rvfi_insn,
  output logic [0:0]       rvfi_trap,
  output logic [0:0]       rvfi_halt,
  output logic [0:0]       rvfi_intr,
  output logic [0:0][1:0]  rvfi_mode,
  output logic [0:0][4:0]  rvfi_rs1_addr,
  output logic [0:0][4:0]  rvfi_rs2_addr,
  output logic [0:0][31:0] rvfi_rs1_rdata,
  output logic [0:0][31:0] rvfi_rs2_rdata,
  output logic [0:0][4:0]  rvfi_rd_addr,
  output logic [0:0][31:0] rvfi_rd_wdata,
  output logic [0:0][31:0] rvfi_pc_rdata,
  output logic [0:0][31:0] rvfi_pc_wdata,
  output logic [0:0][31:0] rvfi_mem_addr,
  output logic [0:0][3:0]  rvfi_mem_rmask,
  output logic [0:0][3:0]  rvfi_mem_wmask,
  output logic [0:0][31:0] rvfi_mem_rdata,
  output logic [0:0][31:0] rvfi_mem_wdata,
`endif
  /// Accelerator Interface - Master Port
  /// Independent channels for transaction request and read completion.
  /// AXI-like handshaking.
  /// Same IDs need to be handled in-order.
  output acc_addr_e     acc_qaddr_o,
  output logic [4:0]    acc_qid_o,
  output logic [31:0]   acc_qdata_op_o,
  output logic [31:0]   acc_qdata_arga_o,
  output logic [31:0]   acc_qdata_argb_o,
  output logic [31:0]   acc_qdata_argc_o,
  output logic          acc_qvalid_o,
  input  logic          acc_qready_i,
  input  logic [31:0]   acc_pdata_i,
  input  logic [4:0]    acc_pid_i,
  input  logic          acc_perror_i,
  input  logic          acc_pvalid_i,
  output logic          acc_pready_o,
  /// TCDM Data Interface
  /// Write transactions do not return data on the `P Channel`
  /// Transactions need to be handled strictly in-order.
  output logic [31:0]   data_qaddr_o,
  output logic          data_qwrite_o,
  output logic [3:0]    data_qamo_o,
  output logic [31:0]   data_qdata_o,
  output logic [3:0]    data_qstrb_o,
  output meta_id_t      data_qid_o,
  output logic          data_qvalid_o,
  input  logic          data_qready_i,
  input  logic [31:0]   data_pdata_i,
  input  logic          data_perror_i,
  input  meta_id_t      data_pid_i,
  input  logic          data_pvalid_i,
  output logic          data_pready_o,
  input  logic          wake_up_sync_i, // synchronous wake-up interrupt
  output fpnew_pkg::roundmode_e    fpu_rnd_mode_o,
  input  fpnew_pkg::status_t       fpu_status_i,
  // Core event strobes
  output snitch_pkg::core_events_t core_events_o
);

  localparam int RegWidth = RVE ? 4 : 5;
  localparam int RegNrReadPorts = ((snitch_pkg::XPULPIMG) || (snitch_pkg::ZFINX)) ? 3 : 2;
  localparam logic [RegWidth-1:0] SP = 2;
  localparam int OutstandingWfi = 8;

  logic illegal_inst;
  logic zero_lsb;

  // Instruction fetch
  logic [31:0] pc_d, pc_q;
  logic wfi_d, wfi_q;
  logic [$clog2(OutstandingWfi)-1:0] wake_up_d, wake_up_q;
  logic [31:0] consec_pc;
  // Immediates
  logic [31:0] iimm, uimm, jimm, bimm, simm, pbimm;
  /* verilator lint_off WIDTH */
  assign iimm = $signed({inst_data_i[31:20]});
  assign uimm = {inst_data_i[31:12], 12'b0};
  assign jimm = $signed({inst_data_i[31],
                                  inst_data_i[19:12], inst_data_i[20], inst_data_i[30:21], 1'b0});
  assign bimm = $signed({inst_data_i[31],
                                    inst_data_i[7], inst_data_i[30:25], inst_data_i[11:8], 1'b0});
  assign simm = $signed({inst_data_i[31:25], inst_data_i[11:7]});
  assign pbimm = $signed(inst_data_i[24:20]); // Xpulpimg immediate branching signed immediate
  /* verilator lint_on WIDTH */

  logic [31:0] opa, opb;
  logic [32:0] adder_result;
  logic [31:0] alu_result;

  logic [RegWidth-1:0] rd, rs1, rs2;
  logic [RegWidth-1:0] rs3;

  logic stall, lsu_stall, fence_stall;
  // Register connections
  logic [RegNrReadPorts-1:0][RegWidth-1:0]  gpr_raddr;
  logic [RegNrReadPorts-1:0][31:0]          gpr_rdata;
  logic [RegNrWritePorts-1:0][RegWidth-1:0] gpr_waddr;
  logic [RegNrWritePorts-1:0][31:0]         gpr_wdata;
  logic [RegNrWritePorts-1:0]               gpr_we;
  logic [2**RegWidth-1:0]                   sb_d, sb_q;

  // Load/Store Defines
  logic is_load, is_store, is_signed, is_postincr;
  logic is_fp_load, is_fp_store;
  logic ls_misaligned;
  logic ld_addr_misaligned;
  logic st_addr_misaligned;

  enum logic [1:0] {
    Byte = 2'b00,
    HalfWord = 2'b01,
    Word = 2'b10,
    Double = 2'b11
  } ls_size;

  enum logic [3:0] {
    AMONone = 4'h0,
    AMOSwap = 4'h1,
    AMOAdd  = 4'h2,
    AMOAnd  = 4'h3,
    AMOOr   = 4'h4,
    AMOXor  = 4'h5,
    AMOMax  = 4'h6,
    AMOMaxu = 4'h7,
    AMOMin  = 4'h8,
    AMOMinu = 4'h9,
    AMOLR   = 4'hA,
    AMOSC   = 4'hB
  } ls_amo;

  logic [31:0] ld_result;
  logic lsu_qready, lsu_qvalid;
  logic lsu_pvalid, lsu_pready;
  logic lsu_empty;
  logic [RegWidth-1:0] lsu_rd;
  logic [31:0] lsu_qaddr;

  logic retire_load; // retire a load instruction
  logic retire_p; // retire from post-increment instructions
  logic retire_i; // retire the rest of the base instruction set
  logic retire_acc; // retire an instruction we offloaded

  logic acc_stall;
  logic valid_instr;
  logic exception;

  // ALU Operations
  enum logic [3:0]  {
    // Arithmetical operations
    Add, Sub,
    // Shifts
    Sll, Srl, Sra,
    // Logical operations
    LXor, LOr, LAnd, LNAnd,
    // Comparisons
    Eq, Neq, Ge, Geu,
    Slt, Sltu,
    // Miscellaneous
    BypassA
  } alu_op;

  enum logic [3:0] {
    None, Reg, IImmediate, UImmediate, JImmediate, SImmediate, SFImmediate, PC, CSR, CSRImmediate, PBImmediate, RegRd, RegRs2
  } opa_select, opb_select, opc_select;

  logic write_rd; // write rd desitnation this cycle
  logic uses_rd;
  logic write_rs1; // write rs1 destination this cycle
  logic uses_rs1;
  enum logic [1:0] {Consec, Alu, Exception} next_pc;

  enum logic [1:0] {RdAlu, RdConsecPC, RdBypass} rd_select;
  logic [31:0] rd_bypass;

  logic is_branch;

  logic [31:0] csr_rvalue;
  logic csr_en;

  typedef struct packed {
    fpnew_pkg::roundmode_e frm;
    fpnew_pkg::status_t    fflags;
  } fcsr_t;
  fcsr_t fcsr_d, fcsr_q;

  // Registers
  `FF(pc_q, pc_d, BootAddr, clk_i, rst_ni)
  `FF(wfi_q, wfi_d, '0, clk_i, rst_ni)
  `FF(wake_up_q, wake_up_d, '0, clk_i, rst_ni)
  `FF(sb_q, sb_d, '0, clk_i, rst_ni)
  if (snitch_pkg::ZFINX) begin
    `FF(fcsr_q, fcsr_d, '0, clk_i, rst_ni)
    assign fpu_rnd_mode_o = fcsr_q.frm;
  end

  always_comb begin
    core_events_o = '0;
    core_events_o.retired_insts = ~stall;
  end

  // accelerator offloading interface
  // register int destination in scoreboard
  logic  acc_register_rd;

  assign acc_qid_o = rd;
  assign acc_qdata_op_o = inst_data_i;
  assign acc_qdata_arga_o = {{32{gpr_rdata[0][31]}}, gpr_rdata[0]};
  assign acc_qdata_argb_o = {{32{gpr_rdata[1][31]}}, gpr_rdata[1]};
  assign acc_qdata_argc_o = {{32{gpr_rdata[2][31]}}, gpr_rdata[2]};

  // instruction fetch interface
  assign inst_addr_o = pc_q;
  assign inst_valid_o = ~wfi_q;

  // --------------------
  // Control
  // --------------------
  // Scoreboard: Keep track of rd dependencies (only loads at the moment)
  logic operands_ready;
  logic dst_ready;
  logic opa_ready, opb_ready, opc_ready;
  logic dstrd_ready, dstrs1_ready;

  always_comb begin
    sb_d = sb_q;
    if (retire_load) sb_d[lsu_rd] = 1'b0;
    // only place the reservation if we actually executed the load or offload instruction
    if ((is_load | acc_register_rd) && !stall && !exception) sb_d[rd] = 1'b1;
    if (retire_acc) sb_d[acc_pid_i[RegWidth-1:0]] = 1'b0;
    sb_d[0] = 1'b0;
  end
  // TODO(zarubaf): This can probably be described a bit more efficient
  assign opa_ready = (opa_select != Reg) | ~sb_q[rs1];
  assign opb_ready = ((opb_select != Reg & opb_select != SImmediate) | ~sb_q[rs2]) & ((opb_select != RegRd) | ~sb_q[rd]);
  if (snitch_pkg::ZFINX) begin
    assign opc_ready = ((opc_select != Reg & opc_select != SImmediate) | ~sb_q[rs3]) & ((opc_select != RegRs2) | ~sb_q[rs2]);
  end else begin
    assign opc_ready = ((opc_select != Reg) | ~sb_q[rd]) & ((opc_select != RegRs2) | ~sb_q[rs2]);
  end
  assign operands_ready = opa_ready & opb_ready & opc_ready;

  // either we are not using the destination register or we need to make
  // sure that its destination operand is not marked busy in the scoreboard.
  assign dstrd_ready = ~uses_rd | (uses_rd & ~sb_q[rd]);
  assign dstrs1_ready = ~uses_rs1 | (uses_rs1 & ~sb_q[rs1]);
  assign dst_ready = dstrd_ready & dstrs1_ready;

  assign valid_instr = (inst_ready_i & inst_valid_o) & operands_ready & dst_ready;
  // the accelerator interface stalled us
  assign acc_stall = (acc_qvalid_o & ~acc_qready_i);
  // the LSU Interface didn't accept our request yet
  assign lsu_stall = (lsu_qvalid & ~lsu_qready);
  // Stall the stage if we either didn't get a valid instruction or the LSU/Accelerator is not ready
  assign stall = ~valid_instr | lsu_stall | acc_stall | fence_stall;

  // --------------------
  // Instruction Frontend
  // --------------------
  assign consec_pc = pc_q + ((is_branch & alu_result[0]) ? bimm : 'd4);

  always_comb begin
    pc_d = pc_q;
    // if we got a valid instruction word increment the PC unless we are waiting for an event
    if (!stall && !wfi_q) begin
      casez (next_pc)
        Consec: pc_d = consec_pc;
        Alu: pc_d = alu_result & {{31{1'b1}}, ~zero_lsb};
        Exception: pc_d = MTVEC;
      endcase
    end
  end

  // --------------------
  // Performance Counter
  // --------------------

  `ifdef SNITCH_ENABLE_PERF
  logic [63:0] cycle_q;
  logic [63:0] instret_q;
  logic [31:0] stall_ins_q;
  logic [31:0] stall_raw_q;
  logic [31:0] stall_lsu_q;
  `FF(cycle_q, cycle_q + 1, '0, clk_i, rst_ni);
  `FFL(instret_q, instret_q + 1, !stall, '0, clk_i, rst_ni);
  `FFL(stall_ins_q, stall_ins_q + 1, stall && (!inst_ready_i) && inst_valid_o, '0, clk_i, rst_ni)
  `FFL(stall_raw_q, stall_raw_q + 1, (!operands_ready) || (!dst_ready), '0, clk_i, rst_ni)
  `FFL(stall_lsu_q, stall_lsu_q + 1, lsu_stall, '0, clk_i, rst_ni)
  `endif


  // --------------------
  // Decoder
  // --------------------
  assign rd = inst_data_i[7 + RegWidth - 1:7];
  assign rs1 = inst_data_i[15 + RegWidth - 1:15];
  assign rs2 = inst_data_i[20 + RegWidth - 1:20];
  if (snitch_pkg::ZFINX) begin
    assign rs3 = (((acc_qaddr_o == snitch_pkg::FP_SS) || (acc_qaddr_o == snitch_pkg::FP_DIVSQRT)) & (snitch_pkg::ZFINX)) ? inst_data_i[27 + RegWidth - 1:27] :
                 ((acc_qaddr_o == snitch_pkg::XPULP_IPU) & (snitch_pkg::XPULPIMG)) ? inst_data_i[7 + RegWidth - 1:7] : '0;
  end

  always_comb begin
    illegal_inst = 1'b0;
    alu_op = Add;
    opa_select = None;
    opb_select = None;
    opc_select = None;

    next_pc = Consec;

    // Set up rd destination
    rd_select = RdAlu;
    // instruction writes rd in the decoding cycle
    write_rd = 1'b1;
    // instruction writes rd
    uses_rd = 1'b1;
    // Set up rs1 destination
    write_rs1 = 1'b0;
    uses_rs1 = write_rs1;

    rd_bypass = '0;
    zero_lsb = 1'b0;
    is_branch = 1'b0;
    // LSU interface
    is_load = 1'b0;
    is_store = 1'b0;
    is_postincr = 1'b0;
    is_fp_load = 1'b0;
    is_fp_store = 1'b0;
    is_signed = 1'b0;
    ls_size = Byte;
    ls_amo = AMONone;

    acc_qvalid_o = 1'b0;
    acc_qaddr_o = snitch_pkg::XPULP_IPU;
    acc_register_rd = 1'b0;

    csr_en = 1'b0;
    fence_stall = 1'b0;
    // Wake up if a wake-up is incoming or pending
    wfi_d = ((wake_up_q > 0) || wake_up_sync_i) ? 1'b0 : wfi_q;
    // Only store a pending wake-up if we are not asleep
    wake_up_d = (wake_up_sync_i && !wfi_q) ? wake_up_q + 1 : wake_up_q;

    unique casez (inst_data_i)
      riscv_instr::ADD: begin
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::ADDI: begin
        opa_select = Reg;
        opb_select = IImmediate;
      end
      riscv_instr::SUB: begin
        alu_op = Sub;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::XOR: begin
        opa_select = Reg;
        opb_select = Reg;
        alu_op = LXor;
      end
      riscv_instr::XORI: begin
        alu_op = LXor;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      riscv_instr::OR: begin
        opa_select = Reg;
        opb_select = Reg;
        alu_op = LOr;
      end
      riscv_instr::ORI: begin
        alu_op = LOr;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      riscv_instr::AND: begin
        alu_op = LAnd;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::ANDI: begin
        alu_op = LAnd;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      riscv_instr::SLT: begin
        alu_op = Slt;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::SLTI: begin
        alu_op = Slt;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      riscv_instr::SLTU: begin
        alu_op = Sltu;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::SLTIU: begin
        alu_op = Sltu;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      riscv_instr::SLL: begin
        alu_op = Sll;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::SRL: begin
        alu_op = Srl;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::SRA: begin
        alu_op = Sra;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::SLLI: begin
        alu_op = Sll;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      riscv_instr::SRLI: begin
        alu_op = Srl;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      riscv_instr::SRAI: begin
        alu_op = Sra;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      riscv_instr::LUI: begin
        opa_select = None;
        opb_select = None;
        rd_select = RdBypass;
        rd_bypass = uimm;
      end
      riscv_instr::AUIPC: begin
        opa_select = UImmediate;
        opb_select = PC;
      end
      riscv_instr::JAL: begin
        rd_select = RdConsecPC;
        opa_select = JImmediate;
        opb_select = PC;
        next_pc = Alu;
      end
      riscv_instr::JALR: begin
        rd_select = RdConsecPC;
        opa_select = Reg;
        opb_select = IImmediate;
        next_pc = Alu;
        zero_lsb = 1'b1;
      end
      // use the ALU for comparisons
      riscv_instr::BEQ: begin
        is_branch = 1'b1;
        write_rd = 1'b0;
        uses_rd = 1'b0;
        alu_op = Eq;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::BNE: begin
        is_branch = 1'b1;
        write_rd = 1'b0;
        uses_rd = 1'b0;
        alu_op = Neq;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::BLT: begin
        is_branch = 1'b1;
        write_rd = 1'b0;
        uses_rd = 1'b0;
        alu_op = Slt;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::BLTU: begin
        is_branch = 1'b1;
        write_rd = 1'b0;
        uses_rd = 1'b0;
        alu_op = Sltu;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::BGE: begin
        is_branch = 1'b1;
        write_rd = 1'b0;
        uses_rd = 1'b0;
        alu_op = Ge;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::BGEU: begin
        is_branch = 1'b1;
        write_rd = 1'b0;
        uses_rd = 1'b0;
        alu_op = Geu;
        opa_select = Reg;
        opb_select = Reg;
      end
      // Load/Stores
      riscv_instr::SB: begin
        write_rd = 1'b0;
        uses_rd = 1'b0;
        is_store = 1'b1;
        opa_select = Reg;
        opb_select = SImmediate;
      end
      riscv_instr::SH: begin
        write_rd = 1'b0;
        uses_rd = 1'b0;
        is_store = 1'b1;
        ls_size = HalfWord;
        opa_select = Reg;
        opb_select = SImmediate;
      end
      riscv_instr::SW: begin
        write_rd = 1'b0;
        uses_rd = 1'b0;
        is_store = 1'b1;
        ls_size = Word;
        opa_select = Reg;
        opb_select = SImmediate;
      end
      riscv_instr::LB: begin
        write_rd = 1'b0;
        is_load = 1'b1;
        is_signed = 1'b1;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      riscv_instr::LH: begin
        write_rd = 1'b0;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = HalfWord;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      riscv_instr::LW: begin
        write_rd = 1'b0;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      riscv_instr::LBU: begin
        write_rd = 1'b0;
        is_load = 1'b1;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      riscv_instr::LHU: begin
        write_rd = 1'b0;
        is_load = 1'b1;
        ls_size = HalfWord;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      // CSR Instructions
      riscv_instr::CSRRW: begin // Atomic Read/Write CSR
        opa_select = Reg;
        opb_select = None;
        rd_select = RdBypass;
        rd_bypass = csr_rvalue;
        csr_en = 1'b1;
      end
      riscv_instr::CSRRWI: begin
        opa_select = CSRImmediate;
        opb_select = None;
        rd_select = RdBypass;
        rd_bypass = csr_rvalue;
        csr_en = 1'b1;
      end
      riscv_instr::CSRRS: begin  // Atomic Read and Set Bits in CSR
          alu_op = LOr;
          opa_select = Reg;
          opb_select = CSR;
          rd_select = RdBypass;
          rd_bypass = csr_rvalue;
          csr_en = 1'b1;
      end
      riscv_instr::CSRRSI: begin
        // offload CSR enable to FP SS
        if (inst_data_i[31:20] != snitch_pkg::CSR_SSR) begin
          alu_op = LOr;
          opa_select = CSRImmediate;
          opb_select = CSR;
          rd_select = RdBypass;
          rd_bypass = csr_rvalue;
          csr_en = 1'b1;
        end else begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end
      end
      riscv_instr::CSRRC: begin // Atomic Read and Clear Bits in CSR
        alu_op = LNAnd;
        opa_select = Reg;
        opb_select = CSR;
        rd_select = RdBypass;
        rd_bypass = csr_rvalue;
        csr_en = 1'b1;
      end
      riscv_instr::CSRRCI: begin
        if (inst_data_i[31:20] != snitch_pkg::CSR_SSR) begin
          alu_op = LNAnd;
          opa_select = CSRImmediate;
          opb_select = CSR;
          rd_select = RdBypass;
          rd_bypass = csr_rvalue;
          csr_en = 1'b1;
        end else begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end
      end
      riscv_instr::ECALL,
      riscv_instr::EBREAK: begin
        // TODO(zarubaf): Trap to precise address
        write_rd = 1'b0;
        uses_rd = 1'b0;
      end
      // NOP Instructions
      riscv_instr::FENCE: begin
        write_rd = 1'b0;
        // Stall until the LSU is empty
        fence_stall = !lsu_empty;
      end
      riscv_instr::WFI: begin
        if (valid_instr) begin
          wfi_d = 1'b1;
          if ((wake_up_q > 0) || wake_up_sync_i) begin
            // Do not sleep if a wake-up is pending
            wfi_d = 1'b0;
            if (wake_up_q > 0) begin
              // Decrement outstanding wake_up pulses
              wake_up_d = wake_up_q - 1;
            end
            if (wake_up_sync_i) begin
              // Keep counter constant due to simultaneous pulse
              wake_up_d = wake_up_q;
            end
          end
        end
      end
      // Atomics
      riscv_instr::AMOADD_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOAdd;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::AMOXOR_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOXor;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::AMOOR_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOOr;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::AMOAND_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOAnd;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::AMOMIN_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOMin;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::AMOMAX_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOMax;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::AMOMINU_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOMinu;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::AMOMAXU_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOMaxu;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::AMOSWAP_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOSwap;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::LR_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOLR;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::SC_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOSC;
        opa_select = Reg;
        opb_select = Reg;
      end
      // Off-load to IPU coprocessor
      riscv_instr::MUL,
      riscv_instr::MULH,
      riscv_instr::MULHSU,
      riscv_instr::MULHU,
      riscv_instr::DIV,
      riscv_instr::DIVU,
      riscv_instr::REM,
      riscv_instr::REMU,
      riscv_instr::MULW,
      riscv_instr::DIVW,
      riscv_instr::DIVUW,
      riscv_instr::REMW,
      riscv_instr::REMUW: begin
        write_rd = 1'b0;
        acc_qvalid_o = valid_instr;
        opa_select = Reg;
        opb_select = Reg;
        acc_register_rd = 1'b1;
        acc_qaddr_o = snitch_pkg::XPULP_IPU;
      end

      /////////////////////////
      /* ZFINX extensions */
      /////////////////////////

      /////////////////////////////////////
      /* Single precision Floating-Point */
      riscv_instr::FADD_S,
      riscv_instr::FSUB_S,
      riscv_instr::FMUL_S,
      riscv_instr::FSGNJ_S,
      riscv_instr::FSGNJN_S,
      riscv_instr::FSGNJX_S,
      riscv_instr::FMIN_S,
      riscv_instr::FMAX_S: begin
        if (snitch_pkg::ZFINX) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::FP_SS;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::FDIV_S,
      riscv_instr::FSQRT_S: begin
        if (snitch_pkg::ZFINX && snitch_pkg::XDIVSQRT) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::FP_DIVSQRT;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::FLE_S,
      riscv_instr::FLT_S,
      riscv_instr::FEQ_S,
      riscv_instr::FCVT_W_S,
      riscv_instr::FCVT_WU_S,
      riscv_instr::FMV_X_W,
      riscv_instr::FCLASS_S,
      riscv_instr::FCVT_S_W,
      riscv_instr::FCVT_S_WU,
      riscv_instr::FMV_W_X: begin
        if (snitch_pkg::ZFINX) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::FP_SS;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::FMADD_S,
      riscv_instr::FMSUB_S,
      riscv_instr::FNMSUB_S,
      riscv_instr::FNMADD_S: begin
        if (snitch_pkg::ZFINX) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          opc_select = Reg;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::FP_SS;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      ///////////////////////////////////
      /* Half Precision Floating-Point */
      riscv_instr::FADD_H,
      riscv_instr::FSUB_H,
      riscv_instr::FMUL_H,
      riscv_instr::FSGNJ_H,
      riscv_instr::FSGNJN_H,
      riscv_instr::FSGNJX_H,
      riscv_instr::FMIN_H,
      riscv_instr::FMAX_H: begin
        if (snitch_pkg::ZFINX && snitch_pkg::XF16) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::FP_SS;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::FDIV_H,
      riscv_instr::FSQRT_H: begin
        if (snitch_pkg::ZFINX && snitch_pkg::XDIVSQRT && snitch_pkg::XF16) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::FP_DIVSQRT;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::FCVT_S_H,
      riscv_instr::FCVT_H_S,
      riscv_instr::FLE_H,
      riscv_instr::FLT_H,
      riscv_instr::FEQ_H,
      riscv_instr::FCVT_W_H,
      riscv_instr::FCVT_WU_H,
      riscv_instr::FMV_X_H,
      riscv_instr::FCLASS_H,
      riscv_instr::FCVT_H_W,
      riscv_instr::FCVT_H_WU,
      riscv_instr::FMV_H_X: begin
        if (snitch_pkg::ZFINX && snitch_pkg::XF16) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::FP_SS;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::FMADD_H,
      riscv_instr::FMSUB_H,
      riscv_instr::FNMSUB_H,
      riscv_instr::FNMADD_H: begin
        if (snitch_pkg::ZFINX && snitch_pkg::XF16) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          opc_select = Reg;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::FP_SS;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      ////////////////////////////////////////
      /* SIMD Half Precision Floating-Point */
      riscv_instr::VFADD_H,
      riscv_instr::VFADD_R_H,
      riscv_instr::VFSUB_H,
      riscv_instr::VFSUB_R_H,
      riscv_instr::VFMUL_H,
      riscv_instr::VFMUL_R_H,
      riscv_instr::VFMIN_H,
      riscv_instr::VFMIN_R_H,
      riscv_instr::VFMAX_H,
      riscv_instr::VFMAX_R_H,
      riscv_instr::VFCLASS_H,
      riscv_instr::VFSGNJ_H,
      riscv_instr::VFSGNJ_R_H,
      riscv_instr::VFSGNJN_H,
      riscv_instr::VFSGNJN_R_H,
      riscv_instr::VFSGNJX_H,
      riscv_instr::VFSGNJX_R_H: begin
        if (snitch_pkg::ZFINX && snitch_pkg::XFVEC && snitch_pkg::XF16) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::FP_SS;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::VFDIV_H,
      riscv_instr::VFDIV_R_H,
      riscv_instr::VFSQRT_H: begin
        if (snitch_pkg::ZFINX && snitch_pkg::XDIVSQRT && snitch_pkg::XFVEC && snitch_pkg::XF16) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::FP_DIVSQRT;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::VFCVT_H_S,
      riscv_instr::VFCVTU_H_S,
      riscv_instr::VFCVT_S_H,
      riscv_instr::VFCVTU_S_H,
      riscv_instr::VFEQ_H,
      riscv_instr::VFEQ_R_H,
      riscv_instr::VFNE_H,
      riscv_instr::VFNE_R_H,
      riscv_instr::VFLT_H,
      riscv_instr::VFLT_R_H,
      riscv_instr::VFGE_H,
      riscv_instr::VFGE_R_H,
      riscv_instr::VFLE_H,
      riscv_instr::VFLE_R_H,
      riscv_instr::VFGT_H,
      riscv_instr::VFGT_R_H,
      riscv_instr::VFMV_X_H,
      riscv_instr::VFMV_H_X,
      riscv_instr::VFCVT_X_H,
      riscv_instr::VFCVT_XU_H,
      riscv_instr::VFCVT_H_X,
      riscv_instr::VFCVT_H_XU: begin
        if (snitch_pkg::ZFINX && snitch_pkg::XFVEC && snitch_pkg::XF16) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::FP_SS;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::VFMAC_H,
      riscv_instr::VFMAC_R_H,
      riscv_instr::VFMRE_H,
      riscv_instr::VFMRE_R_H: begin
        if (snitch_pkg::ZFINX && snitch_pkg::XFVEC && snitch_pkg::XF16) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          opc_select = Reg;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::FP_SS;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::VFCPKA_H_S: begin
        if (snitch_pkg::ZFINX && snitch_pkg::XFVEC && snitch_pkg::XF16) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          opc_select = Reg;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::FP_SS;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Extended dotp
      riscv_instr::VFDOTPEX_S_H,
      riscv_instr::VFDOTPEX_S_R_H,
      riscv_instr::VFNDOTPEX_S_H,
      riscv_instr::VFNDOTPEX_S_R_H,
      riscv_instr::VFSUMEX_S_H,
      riscv_instr::VFNSUMEX_S_H: begin
        if (snitch_pkg::ZFINX && snitch_pkg::XFVEC && snitch_pkg::XF16) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          opc_select = RegRd;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::FP_SS;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Half precision complex
      riscv_instr::FCDOTPEX_S_H,
      riscv_instr::FCNDOTPEX_S_H,
      riscv_instr::FCCDOTPEX_S_H,
      riscv_instr::FCCNDOTPEX_S_H: begin
        if (snitch_pkg::ZFINX && snitch_pkg::XFVEC && snitch_pkg::XF16) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          opc_select = RegRd;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::FP_SS;
        end else begin
          illegal_inst = 1'b1;
        end
      end

      //////////////////////////////////////
      /* Quarter Precision Floating-Point */
      riscv_instr::FADD_B,
      riscv_instr::FSUB_B,
      riscv_instr::FMUL_B,
      riscv_instr::FSGNJ_B,
      riscv_instr::FSGNJN_B,
      riscv_instr::FSGNJX_B,
      riscv_instr::FMIN_B,
      riscv_instr::FMAX_B: begin
        if (snitch_pkg::ZFINX && snitch_pkg::XF8) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::FP_SS;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::FDIV_B,
      riscv_instr::FSQRT_B: begin
        if (snitch_pkg::ZFINX && snitch_pkg::XDIVSQRT && snitch_pkg::XF8) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::FP_DIVSQRT;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::FCVT_S_B,
      riscv_instr::FCVT_B_S,
      riscv_instr::FCVT_H_B,
      riscv_instr::FCVT_B_H,
      riscv_instr::FLE_B,
      riscv_instr::FLT_B,
      riscv_instr::FEQ_B,
      riscv_instr::FCVT_W_B,
      riscv_instr::FCVT_WU_B,
      riscv_instr::FMV_X_B,
      riscv_instr::FCLASS_B,
      riscv_instr::FCVT_B_W,
      riscv_instr::FCVT_B_WU: begin
        if (snitch_pkg::ZFINX && snitch_pkg::XF8) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::FP_SS;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::FMADD_B,
      riscv_instr::FMSUB_B,
      riscv_instr::FNMSUB_B,
      riscv_instr::FNMADD_B: begin
        if (snitch_pkg::ZFINX && snitch_pkg::XF8) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          opc_select = Reg;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::FP_SS;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      ///////////////////////////////////////////
      /* SIMD Quarter Precision Floating-Point */
      riscv_instr::VFADD_B,
      riscv_instr::VFADD_R_B,
      riscv_instr::VFSUB_B,
      riscv_instr::VFSUB_R_B,
      riscv_instr::VFMUL_B,
      riscv_instr::VFMUL_R_B,
      riscv_instr::VFMIN_B,
      riscv_instr::VFMIN_R_B,
      riscv_instr::VFMAX_B,
      riscv_instr::VFMAX_R_B,
      riscv_instr::VFCLASS_B,
      riscv_instr::VFSGNJ_B,
      riscv_instr::VFSGNJ_R_B,
      riscv_instr::VFSGNJN_B,
      riscv_instr::VFSGNJN_R_B,
      riscv_instr::VFSGNJX_B,
      riscv_instr::VFSGNJX_R_B: begin
        if (snitch_pkg::ZFINX && snitch_pkg::XFVEC && snitch_pkg::XF8) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::FP_SS;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::VFDIV_B,
      riscv_instr::VFDIV_R_B,
      riscv_instr::VFSQRT_B: begin
        if (snitch_pkg::ZFINX && snitch_pkg::XDIVSQRT && snitch_pkg::XFVEC && snitch_pkg::XF8) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::FP_DIVSQRT;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::VFCVT_B_S,
      riscv_instr::VFCVTU_B_S,
      riscv_instr::VFCVT_H_B,
      riscv_instr::VFCVTU_H_B,
      riscv_instr::VFCVT_B_H,
      riscv_instr::VFCVTU_B_H,
      riscv_instr::VFEQ_B,
      riscv_instr::VFEQ_R_B,
      riscv_instr::VFNE_B,
      riscv_instr::VFNE_R_B,
      riscv_instr::VFLT_B,
      riscv_instr::VFLT_R_B,
      riscv_instr::VFGE_B,
      riscv_instr::VFGE_R_B,
      riscv_instr::VFLE_B,
      riscv_instr::VFLE_R_B,
      riscv_instr::VFGT_B,
      riscv_instr::VFGT_R_B,
      riscv_instr::VFMV_X_B,
      riscv_instr::VFMV_B_X,
      riscv_instr::VFCVT_X_B,
      riscv_instr::VFCVT_XU_B,
      riscv_instr::VFCVT_B_X,
      riscv_instr::VFCVT_B_XU: begin
        if (snitch_pkg::ZFINX && snitch_pkg::XFVEC && snitch_pkg::XF8) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::FP_SS;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::VFMAC_B,
      riscv_instr::VFMAC_R_B,
      riscv_instr::VFMRE_B,
      riscv_instr::VFMRE_R_B: begin
        if (snitch_pkg::ZFINX && snitch_pkg::XFVEC && snitch_pkg::XF8) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          opc_select = Reg;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::FP_SS;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::VFCPKA_B_S,
      riscv_instr::VFCPKB_B_S: begin
        if (snitch_pkg::ZFINX && snitch_pkg::XFVEC && snitch_pkg::XF8) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          opc_select = Reg;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::FP_SS;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Extended dotp
      riscv_instr::VFDOTPEX_H_B,
      riscv_instr::VFDOTPEX_H_R_B,
      riscv_instr::VFNDOTPEX_H_B,
      riscv_instr::VFNDOTPEX_H_R_B,
      riscv_instr::VFSUMEX_H_B,
      riscv_instr::VFNSUMEX_H_B: begin
        if (snitch_pkg::ZFINX && snitch_pkg::XFVEC && snitch_pkg::XF8) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          opc_select = RegRd;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::FP_SS;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::VFDOTPEXA_S_B,
      riscv_instr::VFDOTPEXB_S_B,
      riscv_instr::VFDOTPEXA_S_R_B,
      riscv_instr::VFDOTPEXB_S_R_B: begin
        if (snitch_pkg::ZFINX && snitch_pkg::XFVEC && snitch_pkg::XF8) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          opc_select = RegRd;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::FP_SS;
        end else begin
          illegal_inst = 1'b1;
        end
      end

      ////////////////////////
      /* Xpulpimg extension */
      ////////////////////////

      // Post-increment loads/stores
      riscv_instr::P_LB_IRPOST: begin // Xpulpimg: p.lb rd,iimm(rs1!)
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          write_rs1 = 1'b1;
          is_load = 1'b1;
          is_postincr = 1'b1;
          is_signed = 1'b1;
          opa_select = Reg;
          opb_select = IImmediate;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::P_LBU_IRPOST: begin // Xpulpimg: p.lbu
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          write_rs1 = 1'b1;
          is_load = 1'b1;
          is_postincr = 1'b1;
          opa_select = Reg;
          opb_select = IImmediate;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::P_LH_IRPOST: begin  // Xpulpimg: p.lh
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          write_rs1 = 1'b1;
          is_load = 1'b1;
          is_postincr = 1'b1;
          is_signed = 1'b1;
          ls_size = HalfWord;
          opa_select = Reg;
          opb_select = IImmediate;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::P_LHU_IRPOST: begin // Xpulpimg: p.lhu
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          write_rs1 = 1'b1;
          is_load = 1'b1;
          is_postincr = 1'b1;
          ls_size = HalfWord;
          opa_select = Reg;
          opb_select = IImmediate;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::P_LW_IRPOST: begin  // Xpulpimg: p.lw
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          write_rs1 = 1'b1;
          is_load = 1'b1;
          is_postincr = 1'b1;
          is_signed = 1'b1;
          ls_size = Word;
          opa_select = Reg;
          opb_select = IImmediate;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::P_LB_RRPOST: begin  // Xpulpimg: p.lb rd,rs2(rs1!)
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          write_rs1 = 1'b1;
          is_load = 1'b1;
          is_postincr = 1'b1;
          is_signed = 1'b1;
          opa_select = Reg;
          opb_select = Reg;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::P_LBU_RRPOST: begin // Xpulpimg: p.lbu
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          write_rs1 = 1'b1;
          is_load = 1'b1;
          is_postincr = 1'b1;
          opa_select = Reg;
          opb_select = Reg;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::P_LH_RRPOST: begin  // Xpulpimg: p.lh
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          write_rs1 = 1'b1;
          is_load = 1'b1;
          is_postincr = 1'b1;
          is_signed = 1'b1;
          ls_size = HalfWord;
          opa_select = Reg;
          opb_select = Reg;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::P_LHU_RRPOST: begin // Xpulpimg: p.lhu
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          write_rs1 = 1'b1;
          is_load = 1'b1;
          is_postincr = 1'b1;
          ls_size = HalfWord;
          opa_select = Reg;
          opb_select = Reg;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::P_LW_RRPOST: begin  // Xpulpimg: p.lw
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          write_rs1 = 1'b1;
          is_load = 1'b1;
          is_postincr = 1'b1;
          is_signed = 1'b1;
          ls_size = Word;
          opa_select = Reg;
          opb_select = Reg;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::P_LB_RR: begin      // Xpulpimg: p.lb rd,rs2(rs1)
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          is_load = 1'b1;
          is_signed = 1'b1;
          opa_select = Reg;
          opb_select = Reg;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::P_LBU_RR: begin     // Xpulpimg: p.lbu
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          is_load = 1'b1;
          opa_select = Reg;
          opb_select = Reg;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::P_LH_RR: begin      // Xpulpimg: p.lh
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          is_load = 1'b1;
          is_signed = 1'b1;
          ls_size = HalfWord;
          opa_select = Reg;
          opb_select = Reg;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::P_LHU_RR: begin     // Xpulpimg: p.lhu
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          is_load = 1'b1;
          ls_size = HalfWord;
          opa_select = Reg;
          opb_select = Reg;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::P_LW_RR: begin      // Xpulpimg: p.lw
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          is_load = 1'b1;
          is_signed = 1'b1;
          ls_size = Word;
          opa_select = Reg;
          opb_select = Reg;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::P_SB_IRPOST: begin  // Xpulpimg: p.sb rs2,simm(rs1!)
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          uses_rd = 1'b0;
          write_rs1 = 1'b1;
          is_store = 1'b1;
          is_postincr = 1'b1;
          opa_select = Reg;
          opb_select = SImmediate;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::P_SH_IRPOST: begin  // Xpulpimg: p.sh
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          uses_rd = 1'b0;
          write_rs1 = 1'b1;
          is_store = 1'b1;
          is_postincr = 1'b1;
          ls_size = HalfWord;
          opa_select = Reg;
          opb_select = SImmediate;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::P_SW_IRPOST: begin  // Xpulpimg: p.sw
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          uses_rd = 1'b0;
          write_rs1 = 1'b1;
          is_store = 1'b1;
          is_postincr = 1'b1;
          ls_size = Word;
          opa_select = Reg;
          opb_select = SImmediate;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // opb is usually assigned with the content of rs2; in stores with reg-reg
      // addressing mode, however, the offset is stored in rd, so rd content is
      // instead assigned to opb: if we cross such signals now (rd -> opb,
      // rs2 -> opc) we don't have to do that in the ALU, with bigger muxes
      riscv_instr::P_SB_RRPOST: begin  // Xpulpimg: p.sb rs2,rs3(rs1!)
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          write_rs1 = 1'b1;
          is_store = 1'b1;
          is_postincr = 1'b1;
          opa_select = Reg; // rs1 base address
          opb_select = RegRd; // rs3 (i.e. rd) offset
          opc_select = RegRs2; // rs2 source data
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::P_SH_RRPOST: begin  // Xpulpimg: p.sh
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          write_rs1 = 1'b1;
          is_store = 1'b1;
          is_postincr = 1'b1;
          ls_size = HalfWord;
          opa_select = Reg;
          opb_select = RegRd;
          opc_select = RegRs2;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::P_SW_RRPOST: begin  // Xpulpimg: p.sw
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          write_rs1 = 1'b1;
          is_store = 1'b1;
          is_postincr = 1'b1;
          ls_size = Word;
          opa_select = Reg;
          opb_select = RegRd;
          opc_select = RegRs2;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::P_SB_RR: begin      // Xpulpimg: p.sb rs2,rs3(rs1)
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          is_store = 1'b1;
          opa_select = Reg;
          opb_select = RegRd;
          opc_select = RegRs2;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::P_SH_RR: begin      // Xpulpimg: p.sh
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          is_store = 1'b1;
          ls_size = HalfWord;
          opa_select = Reg;
          opb_select = RegRd;
          opc_select = RegRs2;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::P_SW_RR: begin      // Xpulpimg: p.sw
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          is_store = 1'b1;
          ls_size = Word;
          opa_select = Reg;
          opb_select = RegRd;
          opc_select = RegRs2;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Immediate branching
      riscv_instr::P_BEQIMM: begin // Xpulpimg: p.beqimm
        if (snitch_pkg::XPULPIMG) begin
          is_branch = 1'b1;
          write_rd = 1'b0;
          uses_rd = 1'b0;
          alu_op = Eq;
          opa_select = Reg;
          opb_select = PBImmediate;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::P_BNEIMM: begin // Xpulpimg: p.bneimm
        if (snitch_pkg::XPULPIMG) begin
          is_branch = 1'b1;
          write_rd = 1'b0;
          uses_rd = 1'b0;
          alu_op = Neq;
          opa_select = Reg;
          opb_select = PBImmediate;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Off-load to IPU coprocessor
      // 1 source register (rs1)
      riscv_instr::P_ABS,                // Xpulpimg: p.abs
      riscv_instr::P_EXTHS,              // Xpulpimg: p.exths
      riscv_instr::P_EXTHZ,              // Xpulpimg: p.exthz
      riscv_instr::P_EXTBS,              // Xpulpimg: p.extbs
      riscv_instr::P_EXTBZ,              // Xpulpimg: p.extbz
      riscv_instr::P_CLIP,               // Xpulpimg: p.clip
      riscv_instr::P_CLIPU,              // Xpulpimg: p.clipu
      riscv_instr::PV_ADD_SCI_H,         // Xpulpimg: pv.add.sci.h
      riscv_instr::PV_ADD_SCI_B,         // Xpulpimg: pv.add.sci.b
      riscv_instr::PV_SUB_SCI_H,         // Xpulpimg: pv.sub.sci.h
      riscv_instr::PV_SUB_SCI_B,         // Xpulpimg: pv.sub.sci.b
      riscv_instr::PV_AVG_SCI_H,         // Xpulpimg: pv.avg.sci.h
      riscv_instr::PV_AVG_SCI_B,         // Xpulpimg: pv.avg.sci.b
      riscv_instr::PV_AVGU_SCI_H,        // Xpulpimg: pv.avgu.sci.h
      riscv_instr::PV_AVGU_SCI_B,        // Xpulpimg: pv.avgu.sci.b
      riscv_instr::PV_MIN_SCI_H,         // Xpulpimg: pv.min.sci.h
      riscv_instr::PV_MIN_SCI_B,         // Xpulpimg: pv.min.sci.b
      riscv_instr::PV_MINU_SCI_H,        // Xpulpimg: pv.minu.sci.h
      riscv_instr::PV_MINU_SCI_B,        // Xpulpimg: pv.minu.sci.b
      riscv_instr::PV_MAX_SCI_H,         // Xpulpimg: pv.max.sci.h
      riscv_instr::PV_MAX_SCI_B,         // Xpulpimg: pv.max.sci.b
      riscv_instr::PV_MAXU_SCI_H,        // Xpulpimg: pv.maxu.sci.h
      riscv_instr::PV_MAXU_SCI_B,        // Xpulpimg: pv.maxu.sci.b
      riscv_instr::PV_SRL_SCI_H,         // Xpulpimg: pv.srl.sci.h
      riscv_instr::PV_SRL_SCI_B,         // Xpulpimg: pv.srl.sci.b
      riscv_instr::PV_SRA_SCI_H,         // Xpulpimg: pv.sra.sci.h
      riscv_instr::PV_SRA_SCI_B,         // Xpulpimg: pv.sra.sci.b
      riscv_instr::PV_SLL_SCI_H,         // Xpulpimg: pv.sll.sci.h
      riscv_instr::PV_SLL_SCI_B,         // Xpulpimg: pv.sll.sci.b
      riscv_instr::PV_OR_SCI_H,          // Xpulpimg: pv.or.sci.h
      riscv_instr::PV_OR_SCI_B,          // Xpulpimg: pv.or.sci.b
      riscv_instr::PV_XOR_SCI_H,         // Xpulpimg: pv.xor.sci.h
      riscv_instr::PV_XOR_SCI_B,         // Xpulpimg: pv.xor.sci.b
      riscv_instr::PV_AND_SCI_B,         // Xpulpimg: pv.and.sci.b
      riscv_instr::PV_AND_SCI_H,         // Xpulpimg: pv.and.sci.h
      riscv_instr::PV_ABS_H,             // Xpulpimg: pv.abs.h
      riscv_instr::PV_ABS_B,             // Xpulpimg: pv.abs.b
      riscv_instr::PV_EXTRACT_H,         // Xpulpimg: pv.extract.h
      riscv_instr::PV_EXTRACT_B,         // Xpulpimg: pv.extract.b
      riscv_instr::PV_EXTRACTU_H,        // Xpulpimg: pv.extractu.h
      riscv_instr::PV_EXTRACTU_B,        // Xpulpimg: pv.extractu.b
      riscv_instr::PV_DOTUP_SCI_H,       // Xpulpimg: pv.dotup.sci.h
      riscv_instr::PV_DOTUP_SCI_B,       // Xpulpimg: pv.dotup.sci.b
      riscv_instr::PV_DOTUSP_SCI_H,      // Xpulpimg: pv.dotusp.sci.h
      riscv_instr::PV_DOTUSP_SCI_B,      // Xpulpimg: pv.dotusp.sci.b
      riscv_instr::PV_DOTSP_SCI_H,       // Xpulpimg: pv.dotsp.sci.h
      riscv_instr::PV_DOTSP_SCI_B: begin // Xpulpimg: pv.dotsp.sci.b
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // 2 source registers (rs1, rs2)
      riscv_instr::P_SLET,              // Xpulpimg: p.slet
      riscv_instr::P_SLETU,             // Xpulpimg: p.sletu
      riscv_instr::P_MIN,               // Xpulpimg: p.min
      riscv_instr::P_MINU,              // Xpulpimg: p.minu
      riscv_instr::P_MAX,               // Xpulpimg: p.max
      riscv_instr::P_MAXU,              // Xpulpimg: p.maxu
      riscv_instr::P_CLIPR,             // Xpulpimg: p.clipr
      riscv_instr::P_CLIPUR,            // Xpulpimg: p.clipur
      riscv_instr::PV_ADD_H,            // Xpulpimg: pv.add.h
      riscv_instr::PV_ADD_SC_H,         // Xpulpimg: pv.add.sc.h
      riscv_instr::PV_ADD_B,            // Xpulpimg: pv.add.b
      riscv_instr::PV_ADD_SC_B,         // Xpulpimg: pv.add.sc.b
      riscv_instr::PV_SUB_H,            // Xpulpimg: pv.sub.h
      riscv_instr::PV_SUB_SC_H,         // Xpulpimg: pv.sub.sc.h
      riscv_instr::PV_SUB_B,            // Xpulpimg: pv.sub.b
      riscv_instr::PV_SUB_SC_B,         // Xpulpimg: pv.sub.sc.b
      riscv_instr::PV_AVG_H,            // Xpulpimg: pv.avg.h
      riscv_instr::PV_AVG_SC_H,         // Xpulpimg: pv.avg.sc.h
      riscv_instr::PV_AVG_B,            // Xpulpimg: pv.avg.b
      riscv_instr::PV_AVG_SC_B,         // Xpulpimg: pv.avg.sc.b
      riscv_instr::PV_AVGU_H,           // Xpulpimg: pv.avgu.h
      riscv_instr::PV_AVGU_SC_H,        // Xpulpimg: pv.avgu.sc.h
      riscv_instr::PV_AVGU_B,           // Xpulpimg: pv.avgu.b
      riscv_instr::PV_AVGU_SC_B,        // Xpulpimg: pv.avgu.sc.b
      riscv_instr::PV_MIN_H,            // Xpulpimg: pv.min.h
      riscv_instr::PV_MIN_SC_H,         // Xpulpimg: pv.min.sc.h
      riscv_instr::PV_MIN_B,            // Xpulpimg: pv.min.b
      riscv_instr::PV_MIN_SC_B,         // Xpulpimg: pv.min.sc.b
      riscv_instr::PV_MINU_H,           // Xpulpimg: pv.minu.h
      riscv_instr::PV_MINU_SC_H,        // Xpulpimg: pv.minu.sc.h
      riscv_instr::PV_MINU_B,           // Xpulpimg: pv.minu.b
      riscv_instr::PV_MINU_SC_B,        // Xpulpimg: pv.minu.sc.b
      riscv_instr::PV_MAX_H,            // Xpulpimg: pv.max.h
      riscv_instr::PV_MAX_SC_H,         // Xpulpimg: pv.max.sc.h
      riscv_instr::PV_MAX_B,            // Xpulpimg: pv.max.b
      riscv_instr::PV_MAX_SC_B,         // Xpulpimg: pv.max.sc.b
      riscv_instr::PV_MAXU_H,           // Xpulpimg: pv.maxu.h
      riscv_instr::PV_MAXU_SC_H,        // Xpulpimg: pv.maxu.sc.h
      riscv_instr::PV_MAXU_B,           // Xpulpimg: pv.maxu.b
      riscv_instr::PV_MAXU_SC_B,        // Xpulpimg: pv.maxu.sc.b
      riscv_instr::PV_SRL_H,            // Xpulpimg: pv.srl.h
      riscv_instr::PV_SRL_SC_H,         // Xpulpimg: pv.srl.sc.h
      riscv_instr::PV_SRL_B,            // Xpulpimg: pv.srl.b
      riscv_instr::PV_SRL_SC_B,         // Xpulpimg: pv.srl.sc.b
      riscv_instr::PV_SRA_H,            // Xpulpimg: pv.sra.h
      riscv_instr::PV_SRA_SC_H,         // Xpulpimg: pv.sra.sc.h
      riscv_instr::PV_SRA_B,            // Xpulpimg: pv.sra.b
      riscv_instr::PV_SRA_SC_B,         // Xpulpimg: pv.sra.sc.b
      riscv_instr::PV_SLL_H,            // Xpulpimg: pv.sll.h
      riscv_instr::PV_SLL_SC_H,         // Xpulpimg: pv.sll.sc.h
      riscv_instr::PV_SLL_B,            // Xpulpimg: pv.sll.b
      riscv_instr::PV_SLL_SC_B,         // Xpulpimg: pv.sll.sc.b
      riscv_instr::PV_OR_H,             // Xpulpimg: pv.or.h
      riscv_instr::PV_OR_SC_H,          // Xpulpimg: pv.or.sc.h
      riscv_instr::PV_OR_B,             // Xpulpimg: pv.or.b
      riscv_instr::PV_OR_SC_B,          // Xpulpimg: pv.or.sc.b
      riscv_instr::PV_XOR_H,            // Xpulpimg: pv.xor.h
      riscv_instr::PV_XOR_SC_H,         // Xpulpimg: pv.xor.sc.h
      riscv_instr::PV_XOR_B,            // Xpulpimg: pv.xor.b
      riscv_instr::PV_XOR_SC_B,         // Xpulpimg: pv.xor.sc.b
      riscv_instr::PV_AND_H,            // Xpulpimg: pv.and.h
      riscv_instr::PV_AND_SC_H,         // Xpulpimg: pv.and.sc.h
      riscv_instr::PV_AND_B,            // Xpulpimg: pv.and.b
      riscv_instr::PV_AND_SC_B,         // Xpulpimg: pv.and.sc.b
      riscv_instr::PV_DOTUP_H,          // Xpulpimg: pv.dotup.h
      riscv_instr::PV_DOTUP_SC_H,       // Xpulpimg: pv.dotup.sc.h
      riscv_instr::PV_DOTUP_B,          // Xpulpimg: pv.dotup.b
      riscv_instr::PV_DOTUP_SC_B,       // Xpulpimg: pv.dotup.sc.b
      riscv_instr::PV_DOTUSP_H,         // Xpulpimg: pv.dotusp.h
      riscv_instr::PV_DOTUSP_SC_H,      // Xpulpimg: pv.dotusp.sc.h
      riscv_instr::PV_DOTUSP_B,         // Xpulpimg: pv.dotusp.b
      riscv_instr::PV_DOTUSP_SC_B,      // Xpulpimg: pv.dotusp.sc.b
      riscv_instr::PV_DOTSP_H,          // Xpulpimg: pv.dotsp.h
      riscv_instr::PV_DOTSP_SC_H,       // Xpulpimg: pv.dotsp.sc.h
      riscv_instr::PV_DOTSP_B,          // Xpulpimg: pv.dotsp.b
      riscv_instr::PV_DOTSP_SC_B: begin // Xpulpimg: pv.dotsp.sc.b
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // 2 source registers (rs1, rd)
      riscv_instr::PV_INSERT_H,           // Xpulpimg: pv.insert.h
      riscv_instr::PV_INSERT_B,           // Xpulpimg: pv.insert.b
      riscv_instr::PV_SDOTUP_SCI_H,       // Xpulpimg: pv.sdotup.sci.h
      riscv_instr::PV_SDOTUP_SCI_B,       // Xpulpimg: pv.sdotup.sci.b
      riscv_instr::PV_SDOTUSP_SCI_H,      // Xpulpimg: pv.sdotusp.sci.h
      riscv_instr::PV_SDOTUSP_SCI_B,      // Xpulpimg: pv.sdotusp.sci.b
      riscv_instr::PV_SDOTSP_SCI_H,       // Xpulpimg: pv.sdotsp.sci.h
      riscv_instr::PV_SDOTSP_SCI_B: begin // Xpulpimg: pv.sdotsp.sci.b
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opc_select = Reg;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // 3 source registers (rs1, rs2, rd)
      riscv_instr::P_MAC,                // Xpulpimg: p.mac
      riscv_instr::P_MSU,                // Xpulpimg: p.msu
      riscv_instr::PV_SDOTUP_H,          // Xpulpimg: pv.sdotup.h
      riscv_instr::PV_SDOTUP_SC_H,       // Xpulpimg: pv.sdotup.sc.h
      riscv_instr::PV_SDOTUP_B,          // Xpulpimg: pv.sdotup.b
      riscv_instr::PV_SDOTUP_SC_B,       // Xpulpimg: pv.sdotup.sc.b
      riscv_instr::PV_SDOTUSP_H,         // Xpulpimg: pv.sdotusp.h
      riscv_instr::PV_SDOTUSP_SC_H,      // Xpulpimg: pv.sdotusp.sc.h
      riscv_instr::PV_SDOTUSP_B,         // Xpulpimg: pv.sdotusp.b
      riscv_instr::PV_SDOTUSP_SC_B,      // Xpulpimg: pv.sdotusp.sc.b
      riscv_instr::PV_SDOTSP_H,          // Xpulpimg: pv.sdotsp.h
      riscv_instr::PV_SDOTSP_SC_H,       // Xpulpimg: pv.sdotsp.sc.h
      riscv_instr::PV_SDOTSP_B,          // Xpulpimg: pv.sdotsp.b
      riscv_instr::PV_SDOTSP_SC_B,       // Xpulpimg: pv.sdotsp.sc.b
      riscv_instr::PV_SHUFFLE2_H,        // Xpulpimg: pv.shuffle2.h
      riscv_instr::PV_SHUFFLE2_B,        // Xpulpimg: pv.shuffle2.b
      riscv_instr::PV_PACK,              // Xpulpimg: pv.pack
      riscv_instr::PV_PACK_H: begin      // Xpulpimg: pv.pack.h
        if (snitch_pkg::XPULPIMG) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
          opa_select = Reg;
          opb_select = Reg;
          opc_select = Reg;
          acc_register_rd = 1'b1;
          acc_qaddr_o = snitch_pkg::XPULP_IPU;
        end else begin
          illegal_inst = 1'b1;
        end
      end

      // TODO(zarubaf): Illegal Instructions
      default: begin
        illegal_inst = 1'b1;
      end
    endcase

    // Sanitize illegal instructions so that they don't exert any side-effects.
    if (exception) begin
     write_rd = 1'b0;
     uses_rd = 1'b0;
     write_rs1 = 1'b0;
     uses_rs1 = 1'b0;
     acc_qvalid_o = 1'b0;
     next_pc = Exception;
    end
  end

  assign exception = illegal_inst | ld_addr_misaligned | st_addr_misaligned;

  // pragma translate_off
  /* verilator lint_off SYNCASYNCNET */
  always_ff @(posedge clk_i) begin
    if (rst_ni && illegal_inst && inst_valid_o && inst_ready_i) begin
      $display("[Illegal Instruction Core %0d] PC: %h Data: %h", hart_id_i, inst_addr_o, inst_data_i);
    end
    if (rst_ni && wake_up_sync_i && &wake_up_q) begin
      $display("[Missed wake-up Core %0d] Cycle: %d, Time: %t", hart_id_i, cycle_q, $time);
    end
  end
  /* verilator lint_on SYNCASYNCNET */
  // pragma translate_on

  // CSR logic
  logic csr_dump;
  logic csr_trace_en, csr_stack_limit_en;
  logic [31:0] csr_trace_q, csr_stack_limit_q;
  logic [11:0] csr_source_dest;

  assign csr_source_dest = inst_data_i[31:20];

  always_comb begin
    csr_rvalue = '0;
    csr_dump = 1'b0;
    csr_trace_en = 1'b0;
    csr_stack_limit_en = 1'b0;

    fcsr_d = fcsr_q;
    fcsr_d.fflags = fcsr_q.fflags | fpu_status_i;

    // TODO(zarubaf): Needs some more input handling, like illegal instruction exceptions.
    // Right now we skip this due to simplicity.
    if (csr_en) begin
      unique case (csr_source_dest)
        riscv_instr::CSR_MHARTID: begin
          csr_rvalue = hart_id_i;
        end
        riscv_instr::CSR_TRACE: begin
          csr_rvalue = csr_trace_q;
          csr_trace_en = 1'b1;
        end
        riscv_instr::CSR_STACKLIMIT: begin
          csr_rvalue = csr_stack_limit_q;
          csr_stack_limit_en = 1'b1;
        end
        `ifdef SNITCH_ENABLE_PERF
        riscv_instr::CSR_MCYCLE: begin
          csr_rvalue = cycle_q[31:0];
        end
        riscv_instr::CSR_MINSTRET: begin
          csr_rvalue = instret_q[31:0];
        end
        riscv_instr::CSR_MCYCLEH: begin
          csr_rvalue = cycle_q[63:32];
        end
        riscv_instr::CSR_MINSTRETH: begin
          csr_rvalue = instret_q[63:32];
        end
        `endif
        `ifdef SNITCH_ENABLE_STALL_COUNTER
        riscv_instr::CSR_MHPMCOUNTER3: begin
          csr_rvalue = stall_ins_q[31:0];
        end
        riscv_instr::CSR_MHPMCOUNTER4: begin
          csr_rvalue = stall_lsu_q[31:0];
        end
        riscv_instr::CSR_MHPMCOUNTER5: begin
          csr_rvalue = stall_raw_q[31:0];
        end
        `endif
        // F/D Extension
        riscv_instr::CSR_FFLAGS: begin
          if (snitch_pkg::ZFINX) begin
            csr_rvalue = {27'b0, fcsr_q.fflags};
            fcsr_d.fflags = fpnew_pkg::status_t'(alu_result[4:0]);
          end
        end
        riscv_instr::CSR_FRM: begin
          if (snitch_pkg::ZFINX) begin
            csr_rvalue = {29'b0, fcsr_q.frm};
            fcsr_d.frm = fpnew_pkg::roundmode_e'(alu_result[2:0]);
          end
        end
        riscv_instr::CSR_FCSR: begin
          if (snitch_pkg::ZFINX) begin
            csr_rvalue = {24'b0, fcsr_q};
            fcsr_d = fcsr_t'(alu_result[7:0]);
          end
        end
        default: begin
          csr_rvalue = '0;
          csr_dump = 1'b1;
        end
      endcase
    end
  end

  // CSR registers
  `FFL(csr_trace_q, alu_result, csr_trace_en, '0, clk_i, rst_ni);
  `FFL(csr_stack_limit_q, alu_result, csr_stack_limit_en, 32'hFFFF_FFFF, clk_i, rst_ni);

  // pragma translate_off
  /* verilator lint_off SYNCASYNCNET */
  always_ff @(posedge clk_i) begin
    // Display CSR write if the CSR does not exist
    if (rst_ni && csr_dump && inst_valid_o && inst_ready_i && !stall) begin
      $timeformat(-9, 0, " ns", 0);
      $display("[DUMP] %t Core %3d: 0x%3h = 0x%08h, %d", $time, hart_id_i, inst_data_i[31:20], alu_result, alu_result);
    end
  end
  /* verilator lint_off SYNCASYNCNET */
  // pragma translate_on

  snitch_regfile #(
    .DATA_WIDTH     ( 32              ),
    .NR_READ_PORTS  ( RegNrReadPorts  ),
    .NR_WRITE_PORTS ( RegNrWritePorts ),
    .ZERO_REG_ZERO  ( 1               ),
    .ADDR_WIDTH     ( RegWidth        )
  ) i_snitch_regfile (
    .clk_i,
    .rst_ni,
    .raddr_i   ( gpr_raddr ),
    .rdata_o   ( gpr_rdata ),
    .waddr_i   ( gpr_waddr ),
    .wdata_i   ( gpr_wdata ),
    .we_i      ( gpr_we    )
  );

  // --------------------
  // Operand Select
  // --------------------
  always_comb begin
    unique case (opa_select)
      None: opa = '0;
      Reg: opa = gpr_rdata[0];
      UImmediate: opa = uimm;
      JImmediate: opa = jimm;
      CSRImmediate: opa = {{{32-RegWidth}{1'b0}}, rs1};
      default: opa = '0;
    endcase
  end

  always_comb begin
    unique case (opb_select)
      None: opb = '0;
      Reg: opb = gpr_rdata[1];
      IImmediate: opb = iimm;
      SFImmediate, SImmediate: opb = simm;
      PC: opb = pc_q;
      CSR: opb = csr_rvalue;
      PBImmediate: opb = pbimm;
      RegRd: opb = gpr_rdata[2];
      default: opb = '0;
    endcase
  end

  assign gpr_raddr[0] = rs1;
  assign gpr_raddr[1] = rs2;
  // connect third read port only if present
  if (RegNrReadPorts >= 3) begin : gpr_raddr_2
    if (snitch_pkg::ZFINX) begin
      assign gpr_raddr[2] = ((snitch_pkg::ZFINX) || (snitch_pkg::XPULPIMG) && (opc_select == RegRd)) ? rd  :
                            ((snitch_pkg::ZFINX) || (snitch_pkg::XPULPIMG) && (opc_select == Reg))   ? rs3 : '0;
    end else begin
      assign gpr_raddr[2] = rd;
    end
  end

  // --------------------
  // ALU
  // --------------------
  // Main Shifter
  logic [31:0] shift_opa, shift_opa_reversed;
  logic [31:0] shift_right_result, shift_left_result;
  logic [32:0] shift_opa_ext, shift_right_result_ext;
  logic shift_left, shift_arithmetic; // shift control
  for (genvar i = 0; i < 32; i++) begin : gen_reverse_opa
    assign shift_opa_reversed[i] = opa[31-i];
    assign shift_left_result[i] = shift_right_result[31-i];
  end
  assign shift_opa = shift_left ? shift_opa_reversed : opa;
  assign shift_opa_ext = {shift_opa[31] & shift_arithmetic, shift_opa};
  assign shift_right_result_ext = $unsigned($signed(shift_opa_ext) >>> opb[4:0]);
  assign shift_right_result = shift_right_result_ext[31:0];

  // Main Adder
  logic [32:0] alu_opa, alu_opb;
  assign adder_result = alu_opa + alu_opb;

  // ALU
  /* verilator lint_off WIDTH */
  always_comb begin
    alu_opa = $signed(opa);
    alu_opb = $signed(opb);

    alu_result = adder_result[31:0];
    shift_left = 1'b0;
    shift_arithmetic = 1'b0;

    unique case (alu_op)
      // Arithmetical operations
      Sub: alu_opb = -$signed(opb);
      // Comparisons
      Slt: begin
        alu_opb = -$signed(opb);
        alu_result = {30'b0, adder_result[32]};
      end
      Ge: begin
        alu_opb = -$signed(opb);
        alu_result = {30'b0, ~adder_result[32]};
      end
      Sltu: begin
        alu_opa = $unsigned(opa);
        alu_opb = -$unsigned(opb);
        alu_result = {30'b0, adder_result[32]};
      end
      Geu: begin
        alu_opa = $unsigned(opa);
        alu_opb = -$unsigned(opb);
        alu_result = {30'b0, ~adder_result[32]};
      end
      // Shifts
      Sll: begin
        shift_left = 1'b1;
        alu_result = shift_left_result;
      end
      Srl: alu_result = shift_right_result;
      Sra: begin
        shift_arithmetic = 1'b1;
        alu_result = shift_right_result;
      end
      // Logical operations
      LXor: alu_result = opa ^ opb;
      LAnd: alu_result = opa & opb;
      LNAnd: alu_result = (~opa) & opb;
      LOr: alu_result = opa | opb;
      // Equal, not equal
      Eq: begin
        alu_opb = -$signed(opb);
        alu_result = ~|adder_result;
      end
      Neq: begin
        alu_opb = -$signed(opb);
        alu_result = |adder_result;
      end
      // Miscellaneous
      BypassA: begin
        alu_result = opa;
      end
      default: alu_result = adder_result[31:0];
    endcase
  end
  /* verilator lint_on WIDTH */

  // --------------------
  // LSU
  // --------------------
  logic [RegWidth-1:0] lsu_qtag;
  logic [31:0] lsu_qdata;

  // Send the return register if it is a read or an AMO
  assign lsu_qtag = (lsu_qvalid && (!is_store || ls_amo != AMONone)) ? rd : '0;
  // Send the data if it is a write or an AMO
  assign lsu_qdata = (lsu_qvalid && (is_store || ls_amo != AMONone)) ? gpr_rdata[1] : '0;

  snitch_lsu #(
    .tag_t               ( logic[RegWidth-1:0]                ),
    .NumOutstandingLoads ( snitch_pkg::NumIntOutstandingLoads )
  ) i_snitch_lsu (
    .clk_i                                ,
    .rst_ni                               ,
    .lsu_qtag_i   ( lsu_qtag              ),
    .lsu_qwrite   ( is_store              ),
    .lsu_qsigned  ( is_signed             ),
    .lsu_qaddr_i  ( lsu_qaddr             ),
    .lsu_qdata_i  ( lsu_qdata             ),
    .lsu_qsize_i  ( ls_size               ),
    .lsu_qamo_i   ( ls_amo                ),
    .lsu_qvalid_i ( lsu_qvalid            ),
    .lsu_qready_o ( lsu_qready            ),
    .lsu_pdata_o  ( ld_result             ),
    .lsu_ptag_o   ( lsu_rd                ),
    .lsu_perror_o (                       ), // ignored for the moment
    .lsu_pvalid_o ( lsu_pvalid            ),
    .lsu_pready_i ( lsu_pready            ),
    .lsu_empty_o  ( lsu_empty             ),
    .data_qaddr_o                          ,
    .data_qwrite_o                         ,
    .data_qdata_o                          ,
    .data_qamo_o                           ,
    .data_qstrb_o                          ,
    .data_qid_o                            ,
    .data_qvalid_o                         ,
    .data_qready_i                         ,
    .data_pdata_i                          ,
    .data_perror_i                         ,
    .data_pid_i                            ,
    .data_pvalid_i                         ,
    .data_pready_o
  );

  // address can be alu_result (i.e. rs1 + iimm/simm) or rs1 (for post-increment load/stores)
  assign lsu_qaddr = lsu_qvalid ? (is_postincr ? gpr_rdata[0] : alu_result) : '0;

  assign lsu_qvalid = valid_instr & (is_load | is_store) & ~(ld_addr_misaligned | st_addr_misaligned);

  // NOTE(smazzola): write-backs "on rd from non-load or non-acc instructions" and "on rs1 from
  // post-increment instructions" in the same cycle should be mutually exclusive (currently valid
  // assumption since write-back to rs1 happens on the cycle in which the post-increment load/store
  // is issued, if that cycle is not a stall, and it is not postponed like offloaded instructions,
  // so no other instructions writing back on rd can be issued in the same cycle)
  // retire post-incremented address on rs1 if valid postincr instruction and LSU not stalling
  assign retire_p = write_rs1 & ~stall & (rs1 != 0);
  // we can retire if we are not stalling and if the instruction is writing a register
  assign retire_i = write_rd & valid_instr & (rd != 0);

  // -----------------------
  // Unaligned Address Check
  // -----------------------
  always_comb begin
    ls_misaligned = 1'b0;
    unique case (ls_size)
      HalfWord: if (alu_result[0] != 1'b0) ls_misaligned = 1'b1;
      Word: if (alu_result[1:0] != 2'b00) ls_misaligned = 1'b1;
      Double: if (alu_result[2:0] != 3'b000) ls_misaligned = 1'b1;
      default: ls_misaligned = 1'b0;
    endcase
  end

  assign st_addr_misaligned = ls_misaligned & (is_store | is_fp_store);
  assign ld_addr_misaligned = ls_misaligned & (is_load | is_fp_load);

  // pragma translate_off
  always_ff @(posedge clk_i) begin
    if (rst_ni && (ld_addr_misaligned || st_addr_misaligned) && valid_instr && inst_ready_i) begin
      $display("%t: [Misaligned Load/Store Core %0d] PC: %h Address: %h Data: %h", $time, hart_id_i, inst_addr_o, alu_result, inst_data_i);
    end
  end
  // pragma translate_on

  // --------------------
  // Write-Back
  // --------------------
  // Write-back data, can come from:
  // 1. ALU/Jump Target/Bypass
  // 2. LSU
  // 3. Accelerator Bus
  logic [31:0] alu_writeback;
  always_comb begin
    casez (rd_select)
      RdAlu: alu_writeback = alu_result;
      RdConsecPC: alu_writeback = consec_pc;
      RdBypass: alu_writeback = rd_bypass;
      default: alu_writeback = alu_result;
    endcase
  end

  if (RegNrWritePorts == 1) begin
    always_comb begin
      gpr_we[0] = 1'b0;
      // NOTE(smazzola): this works because write-backs on rd and rs1 in the same cycle are mutually
      // exclusive; if this should change, the following statement has to be written in another form
      gpr_waddr[0] = retire_p ? rs1 : rd; // choose whether to writeback at RF[rs1] for post-increment load/stores
      gpr_wdata[0] = alu_writeback;
      // external interfaces
      lsu_pready = 1'b0;
      acc_pready_o = 1'b0;
      retire_acc = 1'b0;
      retire_load = 1'b0;

      if (retire_i | retire_p) begin
        gpr_we[0] = 1'b1;
      end else begin
        // if we are not retiring another instruction retire the load now
        lsu_pready = 1'b1;
        if (lsu_pvalid) begin
          retire_load = 1'b1;
          gpr_we[0] = 1'b1;
          gpr_waddr[0] = lsu_rd;
          gpr_wdata[0] = ld_result[31:0];
        end else if (acc_pvalid_i) begin
          // if we are not retiring another instruction retire the accelerated one now
          retire_acc = 1'b1;
          gpr_we[0] = 1'b1;
          gpr_waddr[0] = acc_pid_i;
          gpr_wdata[0] = acc_pdata_i[31:0];
          acc_pready_o = 1'b1;
        end
      end
    end
  end else if (RegNrWritePorts == 2) begin
    always_comb begin
      gpr_we[0] = 1'b0;
      // NOTE(smazzola): this works because write-backs on rd and rs1 in the same cycle are mutually
      // exclusive; if this should change, the following statement has to be written in another form
      gpr_waddr[0] = retire_p ? rs1 : rd; // choose whether to writeback at RF[rs1] for post-increment load/stores
      gpr_wdata[0] = alu_writeback;
      gpr_we[1] = 1'b0;
      gpr_waddr[1] = lsu_rd;
      gpr_wdata[1] = ld_result[31:0];
      // external interfaces
      // Snitch and LSU have priority
      lsu_pready = 1'b1;
      acc_pready_o = 1'b0;
      retire_acc = 1'b0;
      retire_load = 1'b0;

      if (retire_i | retire_p) begin
        gpr_we[0] = 1'b1;
        if (lsu_pvalid) begin
          retire_load = 1'b1;
          gpr_we[1] = 1'b1;
        end else if (acc_pvalid_i) begin
          retire_acc = 1'b1;
          gpr_we[1] = 1'b1;
          gpr_waddr[1] = acc_pid_i;
          gpr_wdata[1] = acc_pdata_i[31:0];
          acc_pready_o = 1'b1;
        end
      // if we are not retiring another instruction retire the load now
      end else begin
        if (acc_pvalid_i) begin
          retire_acc = 1'b1;
          gpr_we[0] = 1'b1;
          gpr_waddr[0] = acc_pid_i;
          gpr_wdata[0] = acc_pdata_i[31:0];
          acc_pready_o = 1'b1;
        end
        if (lsu_pvalid) begin
          retire_load = 1'b1;
          gpr_we[1] = 1'b1;
        end
      end
    end
  end else begin
    $fatal(1, "[snitch] Unsupported RegNrWritePorts.");
  end

  // --------------------
  // Stack overflow check
  // --------------------

  // pragma translate_off
  for (genvar i = 0; i < RegNrWritePorts; i++) begin : gen_stack_overflow_check
    logic [31:0] sp_new_value;
    assign sp_new_value = gpr_wdata[i];
    always_ff @(posedge clk_i) begin
      if (rst_ni && gpr_we[i] && gpr_waddr[i] == SP && csr_stack_limit_q != 32'hFFFF_FFFF && ($signed(sp_new_value) < $signed(csr_stack_limit_q))) begin
        $warning("[Stackoverflow: Core %0d] Set SP to 0x%08h, limit is 0x%08h", hart_id_i, sp_new_value, csr_stack_limit_q);
      end
    end
  end
  // pragma translate_on

  // --------------------------
  // RISC-V Formal Interface
  // --------------------------
  `ifdef RISCV_FORMAL
    logic instr_addr_misaligned;
    logic ld_addr_misaligned_q;
    // check that the instruction is a control transfer instruction
    assign instr_addr_misaligned = (inst_data_i inside {
      riscv_instr::JAL,
      riscv_instr::JALR,
      riscv_instr::BEQ,
      riscv_instr::BNE,
      riscv_instr::BLT,
      riscv_instr::BLTU,
      riscv_instr::BGE,
      riscv_instr::BGEU
    }) && (pc_d[1:0] != 2'b0);


    // retire an instruction and increase ordering bit
    `FFL(rvfi_order[0], rvfi_order[0] + 1, rvfi_valid[0], '0, clk_i, rst_ni)

    logic [31:0] ld_instr_q;
    logic [31:0] ld_addr_q;
    logic [4:0]  rs1_q;
    logic [31:0] rs1_data_q;
    logic [31:0] pc_qq;
    // we need to latch the load
    `FFL(ld_instr_q, inst_data_i, latch_load, '0, clk_i, rst_ni)
    `FFL(ld_addr_q, data_qaddr_o, latch_load, '0, clk_i, rst_ni)
    `FFL(rs1_q, rs1, latch_load, '0, clk_i, rst_ni)
    `FFL(rs1_data_q, gpr_rdata[0], latch_load, '0, clk_i, rst_ni)
    `FFL(pc_qq, pc_d, latch_load, '0, clk_i, rst_ni)
    `FFL(ld_addr_misaligned_q, ld_addr_misaligned, latch_load, '0, clk_i, rst_ni)

    // in case we don't retire another instruction on port 1 we can use it for loads
    logic retire_load_port1;

    assign retire_load_port1 = retire_load & stall;
    // NRET: 1
    assign rvfi_halt[0] = 1'b0;
    assign rvfi_mode[0] = 2'b11;
    assign rvfi_intr[0] = 1'b0;
    assign rvfi_valid[0] = !stall | retire_load;
    assign rvfi_insn[0] = retire_load_port1 ? ld_instr_q : (is_load ? '0 : inst_data_i);
    assign rvfi_trap[0] = retire_load_port1 ? ld_addr_misaligned_q : illegal_inst
                                                                   | instr_addr_misaligned
                                                                   | st_addr_misaligned;
    assign rvfi_rs1_addr[0]  = (retire_load_port1) ? rs1_q : rs1;
    assign rvfi_rs1_rdata[0] = (retire_load_port1) ? rs1_data_q : gpr_rdata[0];
    assign rvfi_rs2_addr[0]  = (retire_load_port1) ? '0 : rs2;
    assign rvfi_rs2_rdata[0] = (retire_load_port1) ? '0 : gpr_rdata[1];
    assign rvfi_rd_addr[0]   = (retire_load_port1) ? lsu_rd : ((gpr_we[0] && write_rd) ? rd : '0);
    assign rvfi_rd_wdata[0]  = (retire_load_port1) ? (lsu_rd != 0 ? ld_result[31:0] : '0) : (rd != 0 && gpr_we[0] && write_rd) ? gpr_wdata[0] : 0;
    assign rvfi_pc_rdata[0]  = (retire_load_port1) ? pc_qq : pc_q;
    assign rvfi_pc_wdata[0]  = (retire_load_port1) ? (pc_qq + 4) : pc_d;
    assign rvfi_mem_addr[0]  = (retire_load_port1) ? ld_addr_q : data_qaddr_o;
    assign rvfi_mem_wmask[0] = (retire_load_port1) ? '0 : ((data_qvalid_o && data_qready_i) ? data_qstrb_o[3:0] : '0);
    assign rvfi_mem_rmask[0] = (retire_load_port1) ? 4'hf : '0;
    assign rvfi_mem_rdata[0] = (retire_load_port1) ? data_pdata_i[31:0] : '0;
    assign rvfi_mem_wdata[0] = (retire_load_port1) ? '0 : data_qdata_o[31:0];
  `endif

  // ----------
  // Assertions
  // ----------
  // Make sure the instruction interface is stable. Otherwise, Snitch might violate the protocol at
  // the LSU or accelerator interface by withdrawing the valid signal.
  `ASSERT(InstructionInterfaceStable,
      (inst_valid_o && inst_ready_i) ##1 (inst_valid_o && $stable(inst_addr_o))
      |-> inst_ready_i && $stable(inst_data_i), clk_i, rst_ni)

endmodule
