#pragma once

#include <atomic>

namespace kmp {
class Mutex {
public:
  void lock();
  bool tryLock();
  void unlock();

private:
  std::atomic<bool> locked = false;
};
} // namespace kmp
