#=======================================================================
# Makefrag for instructions in Spatz ISA employed in MemPool
#-----------------------------------------------------------------------

rv32uv_spatz_sc_tests = \
	vl vls vlx vs vss vsx \
	vadd vsub vrsub \
	vand vor vxor \
	vsll vsrl vsra \
	vmin vminu vmax vmaxu \
	vmul vmulh vmulhu vmulhsu \
	vwmul vwmulu vwmulsu \
	vmacc vmadd vnmsac vnmsub \
	vwmacc vwmaccu vwmaccus vwmaccsu \
	vredsum vredand vredor vredxor vredmin vredminu vredmax vredmaxu \
	vmv \
	vslide1up vslideup vslide1down vslidedown \
	vdiv vdivu vrem vremu

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
	rem remu


ifneq ($(n_fpu),0)
rv32uv_spatz_sc_tests += \
	vfadd vfsub vfrsub \
	vfmin vfmax \
	vfmul vfmacc vfnmacc vfmsac vfnmsac vfmadd vfnmadd vfmsub vfnmsub \
	vfredmax vfredmin vfredosum vfredusum \
	vfwadd vfwsub vfwmul vfwmacc vfwmsac vfwnmsac \
	vfsgnj vfsgnjn vfsgnjx vfcvt vfncvt \
	vfmv
endif

# LLVM has issues decompiling these instructions.
# After upgrading to a newer release version,
# these instructions can be added again:

rv32ui_mempool_tests = $(addprefix rv32ui-mempool-, $(rv32ui_snitch_sc_tests))
rv32ua_mempool_tests = $(addprefix rv32ua-mempool-, $(rv32ua_snitch_sc_tests))
rv32um_mempool_tests = $(addprefix rv32um-mempool-, $(rv32um_snitch_sc_tests))

rv32uv_spatz_tests  = $(addprefix rv32uv-spatz-,  $(rv32uv_spatz_sc_tests))

rtl_mempool_tests = \
	$(rv32ui_mempool_tests) \
	$(rv32ua_mempool_tests) \
	$(rv32um_mempool_tests)

rtl_spatz_tests += $(rv32uv_spatz_tests)
