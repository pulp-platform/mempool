# Copyright 2025 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Danilo Cammarata <dcammarata@iis.ee.ethz.ch>
#

sim_targs += -t rtl

ifeq ($(OPOPE_COMPLEX),1)
	sim_targs += -t opope_test_complex
else
	sim_targs += -t opope_test_hwpe
endif

	sim_targs += -t DEBUG
