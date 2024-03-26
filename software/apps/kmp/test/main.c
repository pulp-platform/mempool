// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "omp.h"
#include "printf.h"
#include "runtime.h"

int main(){
#pragma omp parallel
    {
#pragma omp critical
        {printf("First critical\n");
}

#pragma omp critical
{ printf("Second critical\n"); }
}
}
;
