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
	amoadd_w amoand_w amomax_w amomaxu_w amomin_w amominu_w amoor_w amoxor_w amoswap_w
	# lrsc

rv32um_snitch_sc_tests = \
	div divu \
	mul mulh mulhsu mulhu \
	rem remu \

ifeq ($(xpulpimg),1)

	rv32uxpulpimg_sc_tests = \
		p_abs \
		p_slet p_sletu \
		p_min p_minu \
		p_max p_maxu \
		p_exths p_exthz \
		p_extbs p_extbz \
		p_clip p_clipu \
		p_clipr p_clipur \

endif

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
ifeq ($(xpulpimg),1)
	rv32uxpulpimg_mempool_tests = $(addprefix rv32uxpulpimg-mempool-, $(rv32uxpulpimg_snitch_sc_tests))
endif
# rv32si_mempool_tests = $(addprefix rv32si-mempool-, $(rv32si_snitch_sc_tests))
# rv32mi_mempool_tests = $(addprefix rv32mi-mempool-, $(rv32mi_snitch_sc_tests))

rtl_mempool_tests = \
	$(rv32ui_mempool_tests) \
	$(rv32ua_mempool_tests) \
	$(rv32um_mempool_tests)
#	$(rv32si_mempool_tests) \
#	$(rv32mi_mempool_tests)
ifeq ($(xpulpimg),1)
	rtl_mempool_tests += $(rv32uxpulpimg_mempool_tests)
endif
