#pragma once

#include <atomic>

extern "C" {
#include "printf.h"
#include "runtime.h"
}

namespace kmp {

#ifndef NDEBUG
#define DEBUG_PRINT(...) printf(__VA_ARGS__)
#else
#define DEBUG_PRINT(...)
#endif

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
  explicit SharedPointer(T *ptr)
      : refCount(new std::atomic<uint32_t>(1)), ptr(ptr) {}

  SharedPointer(const SharedPointer &other)
      : refCount(other.refCount), ptr(other.ptr) {
    (*refCount)++;
  }

  SharedPointer(SharedPointer &&other) noexcept
      : refCount(other.refCount), ptr(other.ptr) {
    other.ptr = nullptr;
    other.refCount = nullptr;
  }

  SharedPointer &operator=(SharedPointer && other) noexcept {
    if (this != &other) {
      ptr = other.ptr;
      refCount = other.refCount;
      other.ptr = nullptr;
      other.refCount = nullptr;
    }
    return *this;
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
    if (refCount == nullptr) {
      return;
    }

    if (--(*refCount) == 0) {
      DEBUG_PRINT("Deleting shared pointer %p\n", ptr);
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

template <typename T> class UniquePointer {
public:
  explicit UniquePointer(T *ptr) : ptr(ptr) {}

  // Move constructor
  UniquePointer(UniquePointer &&other) noexcept : ptr(other.ptr) {
    other.ptr = nullptr;
  }

  // Move assignment
  UniquePointer &operator=(UniquePointer &&other) noexcept {
    if (this != &other) {
      delete ptr;
      ptr = other.ptr;
      other.ptr = nullptr;
    }
    return *this;
  }

  // Disallow copy constructor and assignment
  UniquePointer(const UniquePointer &other) = delete;
  UniquePointer &operator=(const UniquePointer &other) = delete;

  ~UniquePointer() { delete ptr; }

  T *get() { return ptr; }
  const T *get() const { return ptr; }

  T *operator->() { return ptr; }
  const T *operator->() const { return ptr; }

  T &operator*() { return *ptr; }
  const T &operator*() const { return *ptr; }

private:
  T *ptr;
};
} // namespace kmp
