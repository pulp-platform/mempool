#=======================================================================
# Makefrag for instructions in Snitch ISA employed in MemPool
#-----------------------------------------------------------------------

rv32ui_snitch_sc_tests = \
	simple \
	add addi \
	and andi \
	auipc \
	beq bge bgeu blt bltu bne \
	jal jalr \
	lb lbu lh lhu lw \
	lui \
	or ori \
	sb sh sw \
	sll slli \
	slt slti sltiu sltu \
	sra srai \
	srl srli \
	sub \
	xor xori
	# fence_i

rv32ua_snitch_sc_tests = \
	amoadd_w amoand_w amomax_w amomaxu_w amomin_w amominu_w amoor_w amoxor_w amoswap_w lrsc

rv32um_snitch_sc_tests = \
	div divu \
	mul mulh mulhsu mulhu \
	rem remu \

# rv32si_snitch_sc_tests = \
# 	csr \
# 	dirty \
# 	ma_fetch \
# 	scall \
# 	sbreak \
# 	wfi \

# rv32mi_snitch_sc_tests = \
# 	breakpoint \
# 	csr \
# 	mcsr \
# 	illegal \
# 	ma_fetch \
# 	ma_addr \
# 	scall \
# 	sbreak \
# 	shamt \

rv32ui_mempool_tests = $(addprefix rv32ui-mempool-, $(rv32ui_snitch_sc_tests))
rv32ua_mempool_tests = $(addprefix rv32ua-mempool-, $(rv32ua_snitch_sc_tests))
rv32um_mempool_tests = $(addprefix rv32um-mempool-, $(rv32um_snitch_sc_tests))
# rv32si_mempool_tests = $(addprefix rv32si-mempool-, $(rv32si_snitch_sc_tests))
# rv32mi_mempool_tests = $(addprefix rv32mi-mempool-, $(rv32mi_snitch_sc_tests))

rtl_mempool_tests = $(rv32ui_mempool_tests)
rtl_mempool_tests += $(rv32ua_mempool_tests)
rtl_mempool_tests += $(rv32um_mempool_tests)
#rtl_mempool_tests += $(rv32si_mempool_tests)
#rtl_mempool_tests += $(rv32mi_mempool_tests)

ifneq ($(COMPILER), llvm)
ifeq ($(xpulpimg),1)

	rv32uxpulpimg_snitch_sc_tests = \
		p_lb_irpost p_lbu_irpost p_lh_irpost p_lhu_irpost p_lw_irpost \
		p_lb_rrpost p_lbu_rrpost p_lh_rrpost p_lhu_rrpost p_lw_rrpost \
		p_lb_rr p_lbu_rr p_lh_rr p_lhu_rr p_lw_rr \
		p_sb_irpost p_sh_irpost p_sw_irpost \
		p_sb_rrpost p_sh_rrpost p_sw_rrpost \
		p_sb_rr p_sh_rr p_sw_rr \
		p_abs \
		p_slet p_sletu \
		p_min p_minu \
		p_max p_maxu \
		p_exths p_exthz \
		p_extbs p_extbz \
		p_clip p_clipu \
		p_clipr p_clipur \
		p_beqimm p_bneimm \
  	p_mac p_msu \
		pv_add \
		pv_sub \
		pv_avg pv_avgu \
		pv_min pv_minu \
		pv_max pv_maxu \
		pv_srl \
		pv_sra \
		pv_sll \
		pv_or \
		pv_xor \
		pv_and \
		pv_abs \
		pv_extract pv_extractu \
		pv_insert \
		pv_dotup \
		pv_dotusp \
		pv_dotsp \
		pv_sdotup \
		pv_sdotusp \
		pv_sdotsp \
		pv_shuffle2 \
		pv_pack \
		pv_pack_h
	rv32uxpulpimg_mempool_tests = $(addprefix rv32uxpulpimg-mempool-, $(rv32uxpulpimg_snitch_sc_tests))
	rtl_mempool_tests += $(rv32uxpulpimg_mempool_tests)

endif
endif

ifeq ($(COMPILER), llvm)
ifeq ($(zfinx_rv),1)

	rv32uzfinx_snitch_sc_tests = \
		fadd \
		fdiv \
		fmadd \
		fmin \
		fsgnj
	rv32uzhinx_snitch_sc_tests = \
		fadd_h \
		fdiv_h \
		fmadd_h \
		fmin_h \
		fsgnj_h
	rv32uzquarterinx_snitch_sc_tests = \
		fadd_b \
		fmadd_b \
		fmin_b \
		fsgnj_b
	rv32uzfinx_mempool_tests = $(addprefix rv32uzfinx-mempool-, $(rv32uzfinx_snitch_sc_tests))
	rv32uzhinx_mempool_tests = $(addprefix rv32uzhinx-mempool-, $(rv32uzhinx_snitch_sc_tests))
	rv32uzquarterinx_mempool_tests = $(addprefix rv32uzquarterinx-mempool-, $(rv32uzquarterinx_snitch_sc_tests))
	rtl_mempool_tests += $(rv32uzfinx_mempool_tests)
	rtl_mempool_tests += $(rv32uzhinx_mempool_tests)
	rtl_mempool_tests += $(rv32uzquarterinx_mempool_tests)

endif
endif
