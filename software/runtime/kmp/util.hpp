#pragma once

#include <atomic>
#include <cassert>
#include <limits>
#include <mutex>

extern "C" {
#include "printf.h"
#include "runtime.h"
}

namespace kmp {
class Mutex;
}

extern kmp::Mutex allocLock;

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
  SharedPointer() : refCount(nullptr), ptr(nullptr) {}

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

  SharedPointer &operator=(SharedPointer &&other) noexcept {
    if (this != &other) {
      std::swap(ptr, other.ptr);
      std::swap(refCount, other.refCount);
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

  inline void reset() {
    DEBUG_PRINT("Resetting shared pointer\n");
    if (refCount == nullptr) {
      return;
    }

    if (--(*refCount) == 0) {
      delete ptr;
      delete refCount;
    }

    refCount = nullptr;
    ptr = nullptr;
  }

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

template <class T> struct Allocator {
  typedef T value_type;

  Allocator() = default;

  template <class U>
  constexpr Allocator(const Allocator<U> & /*unused*/) noexcept {}

  [[nodiscard]] T *allocate(std::size_t n) {
    assert(n <= std::numeric_limits<std::size_t>::max() / sizeof(T));
    std::lock_guard<kmp::Mutex> lock(allocLock);

    DEBUG_PRINT("Allocating %lu bytes\n", n * sizeof(T));
    if (auto ptr = static_cast<T *>(simple_malloc(n * sizeof(T)))) {
      DEBUG_PRINT("Allocated %lu bytes at %p\n", n * sizeof(T), ptr);
      return ptr;
    }

    assert(false && "Allocation failed");
    return nullptr;
  }

  void deallocate(T *ptr, std::size_t n) noexcept {
    std::lock_guard<kmp::Mutex> lock(allocLock);

    simple_free(ptr);
    DEBUG_PRINT("Deallocated %lu bytes at %p\n", n * sizeof(T), ptr);
  }
};

} // namespace kmp
