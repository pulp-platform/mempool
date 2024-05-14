#include <mutex>

// Comment so that <mutex> is imported before
#include "kmp/util.hpp"

extern "C" {
#include "alloc.h"
#include "runtime.h"
}

kmp::Mutex allocLock;

void *operator new(size_t size) {
  std::lock_guard<kmp::Mutex> lock(allocLock);
  return simple_malloc(size);
}

void operator delete(void *ptr) noexcept {
  std::lock_guard<kmp::Mutex> lock(allocLock);
  return simple_free(ptr);
}

void *operator new[](size_t size) { return operator new(size); }

void operator delete[](void *ptr) noexcept { return operator delete(ptr); }

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
