#include "mutex.hpp"

extern "C" {
#include "runtime.h"
}

// https://rigtorp.se/spinlock/
namespace kmp {
void Mutex::lock() {
  while (true) {
    if (!locked.exchange(true, std::memory_order_acquire)) {
      return;
    }

    while (locked.load(std::memory_order_relaxed)) {
      mempool_wait(10);
    }
  }
}

bool Mutex::tryLock() {
  return !locked.exchange(true, std::memory_order_acquire);
}

void Mutex::unlock() {
  locked.store(false, std::memory_order_release);
}

} // namespace kmp
