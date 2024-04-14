#pragma once

#include <stdint.h>

namespace kmp {
  class Barrier {
    public:
      Barrier(uint32_t numCores);
      ~Barrier();
      void wait();
    private:
      volatile uint32_t* barrier;
      uint32_t numCores;
  };
};
