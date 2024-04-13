#pragma once

#include <stdint.h>

namespace kmp {
  class Barrier {
    public:
      Barrier(uint32_t root, uint32_t numCores);
      ~Barrier();
      void wait();
      void reset();
    private:
      uint32_t* barrier;
      uint32_t root;
      uint32_t numCores;
  };
};
