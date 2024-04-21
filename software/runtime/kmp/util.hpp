#pragma once

#include <atomic>

extern "C" {
#include "printf.h"
#include "runtime.h"
}

namespace kmp {

class Mutex {
public:
  inline void lock() {
    while (true) {
      if (!locked.exchange(true, std::memory_order_acquire)) {
        return;
      }

      while (locked.load(std::memory_order_relaxed)) {
        mempool_wait(10);
      }
    }
  }

  inline bool tryLock() {
    return !locked.exchange(true, std::memory_order_acquire);
  }

  inline void unlock() { locked.store(false, std::memory_order_release); }

private:
  std::atomic<bool> locked = false;
};

template <typename T> class SharedPointer {
public:
  explicit SharedPointer(T *ptr) : ptr(ptr) {
    refCount = new std::atomic<uint32_t>(1);
  }

  SharedPointer(const SharedPointer &other) {
    ptr = other.ptr;
    refCount = other.refCount;
    (*refCount)++;
  }

  SharedPointer &operator=(const SharedPointer &other) {
    if (this != &other) {
      ptr = other.ptr;
      refCount = other.refCount;
      (*refCount)++;
    }
    return *this;
  }

  ~SharedPointer() {
    if (--(*refCount) == 0) {
      delete ptr;
      delete refCount;
    }
  }

  T *get() { return ptr; }
  const T *get() const { return ptr; }

  T *operator->() { return ptr; }
  const T *operator->() const { return ptr; }

  T &operator*() { return *ptr; }
  const T &operator*() const { return *ptr; }

private:
  std::atomic<uint32_t> *refCount;
  T *ptr;
};
} // namespace kmp
