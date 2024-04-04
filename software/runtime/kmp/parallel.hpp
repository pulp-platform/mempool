#pragma once

#include "kmp.h"
#include "stdarg.h"

int __kmp_fork_call(ident_t *loc, kmp_int32 argc, kmpc_micro microtask,
                    va_list ap);
