// Copyright 2024 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "omp.h"
#include "kmp/runtime.hpp"
#include "kmp/team.hpp"

void not_implemented(void) { printf("Not implemented\n"); }

uint32_t omp_get_num_threads(void) {
  return kmp::runtime::getCurrentThread().getCurrentTeam()->getNumThreads();
}

uint32_t omp_get_thread_num(void) {
  return kmp::runtime::getCurrentThread().getTid();
};

uint32_t omp_get_num_teams(void) { return kmp::runtime::numTeams; }
uint32_t omp_get_team_num(void) { return kmp::runtime::getCurrentThread().getCurrentTeam()->getTeamId(); }
