# Copyright 2025 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Danilo Cammarata <dcammarata@iis.ee.ethz.ch>
#

common_targs += -t cv32e40p_exclude_tracer

ifeq ($(OPOPE_COMPLEX),1)
	common_targs += -t opope_complex
	common_targs += -e cv32e40p
else
	common_targs += -t opope_hwpe
	common_targs += -e cv32e40x
endif

common_targs += -t DEBUG

common_defs  += -D COREV_ASSERT_OFF
