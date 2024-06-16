// Copyright 2024 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "omp.h"
#include "kmp/runtime.hpp"
#include "kmp/team.hpp"

void not_implemented(void) { printf("Not implemented\n"); }

int omp_get_num_threads(void) {
  return kmp::runtime::getCurrentThread().getCurrentTeam()->getNumThreads();
}

int omp_get_thread_num(void) {
  return kmp::runtime::getCurrentThread().getTid();
};

int omp_get_num_teams(void) { return kmp::runtime::numTeams; }
int omp_get_team_num(void) {
  return kmp::runtime::getCurrentThread().getCurrentTeam()->getTeamId();
}
