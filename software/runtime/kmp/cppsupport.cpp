#include "printf.h"
#include <cstdlib>
#include <stdint.h>

extern "C" {
#include "alloc.h"
}

void *operator new(size_t size) {
  return simple_malloc(size);
}

void operator delete(void *p) noexcept {
  return simple_free(p);
}
