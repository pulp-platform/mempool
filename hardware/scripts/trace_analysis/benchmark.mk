# Copyright 2026 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# Two-stage benchmark workflow (see README.md in this directory):
#   make benchmark    build `app`, simulate it, and extract benchmark CSVs
#   make plots        render stall and communication figures from those CSVs

# Defaults for the workflow goals only; inherited targets are unaffected.
ifneq ($(filter build_app benchmark plots,$(MAKECMDGOALS)),)
app        ?= matmul_i32
variant    ?= $(if $(filter 1,$(das)),das,baseline)$(if $(filter 1,$(back2local)),_back2local)
result_dir ?= $(resultpath)/$(app)_$(config)/$(variant)
# Limit lookup to bare-metal apps. build_app creates the selected binary before
# simulation, so parse-time validation is skipped.
app_path   ?= $(abspath $(ROOT_DIR)/../software/bin/apps/baremetal)
skip_app_validation := 1
endif

# Extraction defaults.
benchmark_sim      ?= simc
extract_jobs       ?= 16
extract_dir        := $(ROOT_DIR)/scripts/trace_analysis/extract
extract_args        = --benchmark-only -p --force -j $(extract_jobs)

# Plot defaults.
plot_section       ?= 1
plot_indiv_tiles   ?= 0
plot_window_cycles ?= 64
plot_comm          ?= 1
plot_jobs          ?= 1

section_arg = $(if $(plot_section),--section $(plot_section))
plot_args   = $(section_arg) --overview \
              $(if $(filter 1,$(plot_indiv_tiles)),,--skip-tile-details) \
              --window $(plot_window_cycles) -j $(plot_jobs)

# Topology metadata for the analysis scripts.
topology_env = CONFIG=$(config) \
               NUM_CORES=$(num_cores) NUM_GROUPS=$(num_groups) \
               NUM_CORES_PER_TILE=$(num_cores_per_tile) \
               SEQ_MEM_SIZE=$(seq_mem_size) BANKING_FACTOR=$(banking_factor) \
               L1_BANK_SIZE=$(l1_bank_size) \
               NUM_SUB_GROUPS_PER_GROUP=$(num_sub_groups_per_group) \
               REMOTE_GROUP_LATENCY_CYCLES=$(remote_group_latency_cycles)

# Check elaboration defines on every invocation and update the stamp only when
# they change, so Questa and VCS rebuild only when needed.
vlog_defs_stamp := $(buildpath)/.vlog_defs
$(vlog_defs_stamp): export _vlog_defs = $(vlog_defs)
$(vlog_defs_stamp): FORCE | $(buildpath)
	@printf '%s\n' "$$_vlog_defs" | cmp -s - $@ || \
		printf '%s\n' "$$_vlog_defs" > $@
$(buildpath)/compile.tcl: $(vlog_defs_stamp)
$(buildpath)/compilevcs.sh: $(vlog_defs_stamp)

.PHONY: FORCE build_app benchmark plots

build_app:
	$(MAKE) -B -C $(MEMPOOL_DIR)/software/apps/baremetal config="$(config)" "$(app)"

benchmark:
	@[ "$(force)" = "1" ] || \
		{ [ ! -f "$(result_dir)/data/stall_timeseries_benchmark.csv" ] && \
		  [ ! -f "$(result_dir)/data/comm_events_benchmark.csv" ]; } || \
		{ echo "ERROR: $(result_dir) already has results (set force=1 to overwrite)" >&2; exit 1; }
	$(MAKE) build_app
	mkdir -p "$(result_dir)/data"
	cp "$(preload)" "$(preload).dump" "$(result_dir)"
	printf '%s\n' $(topology_env) > "$(result_dir)/topology.env"
	$(MAKE) app="$(app)" app_path="$(app_path)" tcdm_addr_trace=1 $(benchmark_sim)
# A fresh sub-make discovers the traces.
# Clearing app skips another binary lookup.
	result_dir="$(result_dir)" $(MAKE) -j $(extract_jobs) app= trace copy_traces=0 tcdm_addr_trace=1
	$(python) $(extract_dir)/extract_benchmark_csvs.py $(extract_args) \
		--folder "$(tracepath)" \
		--comm-csv "$(result_dir)/data/comm_events_benchmark.csv" \
		--stall-csv "$(result_dir)/data/stall_timeseries_benchmark.csv"
	rm -f $(buildpath)/trace_hart_*.dasm $(buildpath)/trace_hart_*.trace \
		$(buildpath)/tcdm_addr_hart_*.csv
	rm -rf $(tracepath)
	@printf '\nBenchmark results: %s\nPlot with:\n  make plots python="%s" result_dir="%s"\n' \
		"$(result_dir)" "$(python)" "$(result_dir)"

plots:
	@[ -f "$(result_dir)/data/stall_timeseries_benchmark.csv" ] || \
		{ echo "ERROR: missing $(result_dir)/data/stall_timeseries_benchmark.csv (run 'make benchmark' first)" >&2; exit 1; }
	@[ "$(plot_comm)" != "1" ] || [ -f "$(result_dir)/data/comm_events_benchmark.csv" ] || \
		{ echo "ERROR: missing $(result_dir)/data/comm_events_benchmark.csv (run 'make benchmark' first or pass plot_comm=0)" >&2; exit 1; }
	$(python) $(ROOT_DIR)/scripts/trace_analysis/plot/plot_all_tiles.py "$(result_dir)" $(plot_args)
	@[ "$(plot_comm)" != "1" ] || \
		$(python) $(ROOT_DIR)/scripts/trace_analysis/plot/plot_comm.py "$(result_dir)" \
			$(section_arg) --window $(plot_window_cycles)
