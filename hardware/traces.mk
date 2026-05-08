# Copyright 2025 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

trace                 := $(patsubst $(buildpath)/%.dasm,$(buildpath)/%.trace,$(wildcard $(buildpath)/*.dasm))
SN_GENTRACE_PY        ?= $(ROOT_DIR)/scripts/gen_trace.py
SN_CSV_TRACES         ?= $(buildpath)/results.csv

SN_RISCV_MC           ?= $(INSTALL_DIR)/llvm/bin/llvm-mc
SN_RISCV_MATTR_FLAG    = +m,+a,+xpulpmacsi,+xpulppostmod,+xpulpvect,+xpulpvectshufflepack,+zfinx
SN_RISCV_MC_FLAGS     ?= -disassemble -triple=riscv32 --mattr=$(SN_RISCV_MATTR_FLAG)
SN_GENTRACE_PY_FLAGS  += --mc-exec $(SN_RISCV_MC) --mc-flags "$(SN_RISCV_MC_FLAGS)" --csv $(SN_CSV_TRACES)

# Give configuration in env
SN_ENV_TRACES         += NUM_CORES=$(num_cores)
SN_ENV_TRACES         += SEQ_MEM_SIZE=$(seq_mem_size)

trace: $(trace) post-trace

$(buildpath)/%.trace: $(buildpath)/%.dasm
	$(SN_ENV_TRACES) $(python) $(SN_GENTRACE_PY) -p --output $@ $(SN_GENTRACE_PY_FLAGS) $<

post-trace:
	mkdir -p "$(result_dir)"
	cp $(buildpath)/transcript "$(result_dir)/" | true
	cp $(SN_CSV_TRACES) "$(result_dir)"
	cp $(trace) "$(result_dir)"
	$(python) $(ROOT_DIR)/scripts/gen_avg.py --folder "$(result_dir)" | tee $(result_dir)/avg.txt

tracevis:
	$(MEMPOOL_DIR)/scripts/tracevis.py $(preload) $(buildpath)/*.trace -o $(buildpath)/tracevis.json
