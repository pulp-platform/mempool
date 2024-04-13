#include <cstdlib>
#include <new>

extern "C" {
#include "alloc.h"
}

void *operator new(size_t size) { return simple_malloc(size); }

void operator delete(void *p) noexcept { return simple_free(p); }

namespace std {
void __throw_bad_alloc() { printf("Bad alloc\n"); }
} // namespace std
