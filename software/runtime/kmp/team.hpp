#pragma once

#include "etl/flat_map.h"
#include "kmp/barrier.hpp"
#include "kmp/thread.hpp"
#include "kmp/types.h"
#include "kmp/util.hpp"
#include <mutex>

namespace kmp {

// Forward declaration
class Thread;

class Team {

  struct DynamicSchedule {
    kmp_uint32 lowerNext;
    kmp_uint32 upper;
    kmp_uint32 chunk;
    kmp_uint32 incr;
    kmp_uint32 stride;

    std::atomic<bool> valid;
    Mutex mutex;
  };

public:
  Team(kmp_uint32 numThreads, Task implicitTask);

  /**
   * @brief Push task to all threads in the team
   *
   * @param task Taks to push
   */
  void pushTaskAll(Task task) const;

  inline const Barrier &getBarrier() const { return barrier; }

  inline const Task &getImplicitTask() const { return implicitTask; }

  inline auto getThreadTid(kmp_uint32 gtid) const { return gtid - masterGtid; }

  inline auto getThreadGtid(kmp_uint32 tid) const { return masterGtid + tid; }

  inline auto getNumThreads() const { return numThreads; }

  inline auto setCopyPrivateData(void *data) { copyPrivateData = data; }

  inline auto getCopyPrivateData() const { return copyPrivateData; }

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
                     typename std::make_signed<T>::type chunk) const {

    assert(incr == 1 && "Loop increment is not 1");
    assert(chunk > 0 && "Chunk size is not positive");
    assert((static_cast<T>(chunk) <= *pupper - *plower + 1) &&
           "Chunk size is greater than loop size");

    kmp_uint32 tid = getThreadTid(gtid);
    kmp_uint32 numChunks = (pupper - plower + chunk) / chunk;

    switch (schedtype) {
    case kmp_sch_static: {

      // Calculate chunk size
      // https://stackoverflow.com/a/14878734
      chunk = (*pupper - *plower + 1) / numThreads +
              ((*pupper - *plower + 1) % numThreads != 0);

      // Same as static chunked
      kmp_uint32 span = incr * chunk;
      *pstride = span * numThreads;
      *plower = *plower + tid * span;
      *pupper = *plower + span - incr;
      *plastiter = (tid == (numChunks - 1) % numThreads);

      break;
    }
    case kmp_sch_static_chunked: {
      assert(incr != 0 && "Loop increment must be non-zero");

      kmp_uint32 span = incr * chunk;
      *pstride = span * numThreads;
      *plower = *plower + tid * span;
      *pupper = *plower + span - incr;
      *plastiter = (tid == (numChunks - 1) % numThreads);

      break;
    }
    default: {
      assert(false && "Unsupported scheduling type");
      break;
    }
    }
  }

  template <typename T>
  void dispatchInit(ident_t *loc, kmp_int32 gtid, kmp_sched_type schedtype,
                    T lower, T upper, typename std::make_signed<T>::type incr,
                    typename std::make_signed<T>::type chunk) {

    assert(incr == 1 && "Loop increment is not 1");
    assert(chunk > 0 && "Chunk size is not positive");
    assert((static_cast<T>(chunk) <= upper - lower + 1) &&
           "Chunk size is greater than loop size");

    switch (schedtype) {
    case kmp_sch_dynamic_chunked: {
      std::lock_guard<Mutex> lock(dynamicSchedule.mutex);
      if (dynamicSchedule.valid) {
        return;
      }

      kmp_uint32 span = incr * chunk;

      dynamicSchedule.lowerNext = lower;
      dynamicSchedule.upper = upper;
      dynamicSchedule.chunk = chunk;
      dynamicSchedule.incr = incr;
      dynamicSchedule.stride = span * numThreads;

      DEBUG_PRINT(
          "Dynamic schedule: lowerNext=%d, upper=%d, chunk=%d, incr=%d, "
          "stride=%d\n",
          dynamicSchedule.lowerNext, dynamicSchedule.upper,
          dynamicSchedule.chunk, dynamicSchedule.incr, dynamicSchedule.stride);

      dynamicSchedule.valid = true;
      break;
    }
    default: {
      printf("Unsupported scheduling type: %d\n", schedtype);
      assert(false && "Unsupported scheduling type");
      break;
    }
    };
  }

  template <typename T>
  bool dispatchNext(ident_t *loc, kmp_int32 gtid,
                    typename std::make_signed<T>::type *plastiter, T *plower,
                    T *pupper, typename std::make_signed<T>::type *pstride) {

    std::lock_guard<Mutex> lock(dynamicSchedule.mutex);
    assert(dynamicSchedule.valid && "Dynamic schedule not initialized");

    if (dynamicSchedule.lowerNext > dynamicSchedule.upper) {
      return false;
    } else {

      *plower = dynamicSchedule.lowerNext;

      dynamicSchedule.lowerNext += dynamicSchedule.chunk;
      if (dynamicSchedule.lowerNext > dynamicSchedule.upper) {
        *pupper = dynamicSchedule.upper;
        *plastiter = true;
      } else {
        *pupper = dynamicSchedule.lowerNext - 1;
        *plastiter = false;
      }

      *pstride = dynamicSchedule.stride;

      return true;
    }
  };

private:
  kmp_uint32 masterGtid;

  kmp_uint32 numThreads;
  std::vector<Thread *, kmp::Allocator<Thread *>> threads;

  Barrier barrier;

  DynamicSchedule dynamicSchedule;

  void *copyPrivateData;

  Task implicitTask;
};

} // namespace kmp
