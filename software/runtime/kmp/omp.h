// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/* Standard public APIs */

#pragma once

#ifdef __cplusplus
extern "C" {
#endif

extern int omp_get_num_threads(void);
extern int omp_get_thread_num(void);

extern int omp_get_num_teams(void);
extern int omp_get_team_num(void);

#ifdef __cplusplus
}
#endif
