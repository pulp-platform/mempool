#pragma once

#include "etl/list.h"
#include "etl/optional.h"
#include "mutex.hpp"
#include "printf.h"
#include "task.hpp"
#include "types.h"

namespace kmp {

class Thread {
public:
  Thread(kmp_uint32 gtid);
  Thread(const Thread &other);

  void run();
  void wakeUp();

  void pushTask(const Task &task);
  etl::optional<etl::reference_wrapper<const Task>> getCurrentTask();

  kmp_uint32 getGtid() const;
  kmp_uint32 getTid() const;

  void pushNumThreads(kmp_int32 numThreads);
  void forkCall(const Microtask &microtask);

  /**
   * @brief Schedule a static for loop. See
   * https://github.com/llvm/llvm-project/blob/f28c006a5895fc0e329fe15fead81e37457cb1d1/clang/lib/CodeGen/CGStmtOpenMP.cpp#L2900
   *
   * @tparam T Loop index type
   * @param loc Source code location
   * @param gtid  Global thread ID
   * @param schedtype Scheduling type
   * @param plastiter Pointer to last iteration flag, true if the current thread
   * executes the last iteration, false otherwise
   * @param plower Pointer to lower bound for this thread
   * @param pupper Pointer to upper bound for this thread
   * @param pstride Pointer to stride for this thread
   * @param incr Loop increment (this is always 1 in LLVM 14)
   * @param chunk Chunk size
   */
  template <typename T>
  void forStaticInit(ident_t *loc, kmp_int32 gtid, kmp_sched_type schedtype,
                     T *plastiter, T *plower, T *pupper,
                     typename std::make_signed<T>::type *pstride,
                     typename std::make_signed<T>::type incr,
                     typename std::make_signed<T>::type chunk) {

    assert(incr == 1 && "Loop increment is not 1");
    assert(chunk > 0 && "Chunk size is not positive");
    assert((static_cast<T>(chunk) <= *pupper - *plower + 1) && "Chunk size is greater than loop size");

    kmp_uint32 numThreads = this->tasks.front().getNumThreads();
    kmp_uint32 numChunks = (pupper - plower + chunk) / chunk;

    switch (schedtype) {
    case kmp_sch_static: {

      // Calculate chunk size
      // https://stackoverflow.com/a/14878734
      chunk = (*pupper - *plower + 1) / numThreads + ((*pupper - *plower + 1) % numThreads != 0);

      // Same as static chunked
      kmp_uint32 span = incr * chunk;
      *pstride = span * numThreads;
      *plower = *plower + gtid * span;
      *pupper = *plower + span - incr;
      *plastiter = (gtid == (numChunks - 1) % numThreads);

      break;
    }
    case kmp_sch_static_chunked: {
      assert(incr != 0 && "Loop increment must be non-zero");

      kmp_uint32 span = incr * chunk;
      *pstride = span * numThreads;
      *plower = *plower + gtid * span;
      *pupper = *plower + span - incr;
      *plastiter = (gtid == (numChunks - 1) % numThreads);

      break;
    }
    default: {
      assert(false && "Unsupported scheduling type");
      break;
    }
    }
  }

public:
  etl::list<Task, 10> tasks;

protected:
  kmp_uint32 gtid;
  kmp_uint32 tid;

private:
  std::atomic<bool> running = false;
  etl::optional<kmp_int32> numThreads;
  Mutex tasksLock;
};
}; // namespace kmp
