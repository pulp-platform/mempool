# Copyright 2025 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Danilo Cammarata <dcammarata@iis.ee.ethz.ch>
#

export PYTHON=python3
export PENV=$(pwd)/venv
$PYTHON -m venv $PENV
source $PENV/bin/activate
pip3 install --upgrade pip
pip3 install numpy
pip3 install torch
deactivate
