#include <cstdlib>

extern "C" {
#include "runtime.h"
#include "alloc.h"
}

void *operator new(size_t size) { return simple_malloc(size); }

void operator delete(void *p) noexcept { return simple_free(p); }

namespace std {
void __throw_bad_alloc() { printf("Bad alloc\n"); }
} // namespace std

extern "C" int __cxa_atexit(void (*func)(void *), void *arg, void *dso_handle) {
  (void)func;
  (void)arg;
  (void)dso_handle;
  return 0;
}

extern "C" void __assert_func(const char *file, int line, const char *func,
                              const char *failedexpr) {
  printf("Assertion failed: %s, file %s, line %d, function %s\n", failedexpr,
         file, line, func);
  mempool_wfi();
}
