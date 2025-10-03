# Copyright 2025 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Danilo Cammarata <dcammarata@iis.ee.ethz.ch>
#

synth_targs +=

ifeq ($(OPOPE_COMPLEX),1)
	synth_defs += -D OPOPE_COMPLEX_SYNTH
else
	synth_defs += -D OPOPE_HWPE_SYNTH
endif


synth_defs += -D DEBUG
