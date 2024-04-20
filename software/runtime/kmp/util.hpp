#pragma once

#include "printf.h"
#include <atomic>

namespace kmp {

template <typename T> class SharedPointer {
public:
  SharedPointer(T *ptr) : ptr(ptr) {
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
