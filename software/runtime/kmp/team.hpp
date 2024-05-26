#pragma once

#include "kmp/barrier.hpp"
#include "kmp/runtime.hpp"
#include "kmp/types.h"
#include "kmp/util.hpp"
#include "printf.h"
#include <array>
#include <mutex>
#include <optional>
#include <variant>

namespace kmp {

class Thread;
class Task;
class Barrier;

class Team {

  template <typename T, typename SignedT = typename std::make_signed<T>::type,
            typename UnsignedT = typename std::make_unsigned<T>::type>
  struct DynamicSchedule {
    DynamicSchedule() {}

    T lowerNext = 0;
    T upper = 0;
    SignedT chunk = 0;
    SignedT incr = 0;
    SignedT stride = 0;

    bool valid = false;
    kmp_uint32 numDone = 0;

    Mutex mutex;
  };

public:
  Team(kmp_uint32 masterGtid, kmp_uint32 numThreads,
       std::optional<Task> implicitTask = std::nullopt);

  inline Barrier &getBarrier() { return barrier; }

  inline const std::optional<Task> &getImplicitTask() const {
    return implicitTask;
  }

  inline void setImplicitTask(Task task) { implicitTask = std::move(task); }

  inline auto getNumThreads() const { return numThreads; }

  inline void setNumThreads(kmp_uint32 numThreads) {
    this->numThreads = numThreads;
    this->barrier.setNumThreads(numThreads);
  }

  inline auto setCopyPrivateData(void *data) { copyPrivateData = data; }

  inline auto getCopyPrivateData() const { return copyPrivateData; }

  inline void run() {
    for (kmp_uint32 i = 0; i < numThreads; i++) {
      runtime::threads[i].setCurrentTeam(this);

      if (i != masterGtid) {
        runtime::threads[i].wakeUp();
      }
    }
  }

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
  template <typename T, typename SignedT = typename std::make_signed<T>::type,
            typename UnsignedT = typename std::make_unsigned<T>::type>
  void forStaticInit(ident_t * /*loc*/, kmp_int32 /*gtid*/,
                     kmp_sched_type schedtype, T *plastiter, T *plower,
                     T *pupper, SignedT *pstride, SignedT incr,
                     SignedT chunk) const {

    assert(incr == 1 && "Loop increment is not 1");
    assert(chunk > 0 && "Chunk size is not positive");
    assert((static_cast<T>(chunk) <= *pupper - *plower + 1) &&
           "Chunk size is greater than loop size");

    kmp_uint32 tid = runtime::getCurrentThread().getTid();

    UnsignedT numChunks = (static_cast<UnsignedT>(pupper - plower) +
                           static_cast<UnsignedT>(chunk)) /
                          static_cast<UnsignedT>(chunk);

    switch (schedtype) {
    case kmp_sch_static: {

      // Calculate chunk size
      // https://stackoverflow.com/a/14878734
      chunk = static_cast<SignedT>(*pupper - *plower + 1) /
                  static_cast<SignedT>(numThreads) +
              (static_cast<SignedT>(*pupper - *plower + 1) %
                   static_cast<SignedT>(numThreads) !=
               0);

      // Fall through to static chunked
    }
    case kmp_sch_static_chunked: {
      assert(incr != 0 && "Loop increment must be non-zero");

      SignedT span = incr * chunk;
      *pstride = span * static_cast<SignedT>(numThreads);
      *plower = *plower + static_cast<T>(tid) * static_cast<T>(span);
      *pupper = *plower + static_cast<T>(span - incr);
      *plastiter = (tid == (numChunks - 1) % numThreads);

      break;
    }
    default: {
      assert(false && "Unsupported scheduling type");
      break;
    }
    }
  }

  template <typename T, typename SignedT = typename std::make_signed<T>::type,
            typename UnsignedT = typename std::make_unsigned<T>::type>
  void dispatchInit(ident_t * /*loc*/, kmp_int32 /*gtid*/,
                    kmp_sched_type schedtype, T lower, T upper, SignedT incr,
                    SignedT chunk) {

    assert(incr == 1 && "Loop increment is not 1");
    assert(chunk > 0 && "Chunk size is not positive");
    assert((static_cast<T>(chunk) <= upper - lower + 1) &&
           "Chunk size is greater than loop size");

    DEBUG_PRINT("Dispatch init\n");

    auto &dynamicSchedule = std::get<DynamicSchedule<T>>(this->dynamicSchedule);

    switch (schedtype) {
    case kmp_sch_dynamic_chunked: {
      std::lock_guard<Mutex> lock(dynamicSchedule.mutex);

      if (dynamicSchedule.valid) {
        DEBUG_PRINT("Dynamic schedule is already valid\n");
        return;
      }

      SignedT span = incr * chunk;

      dynamicSchedule.lowerNext = lower;
      dynamicSchedule.upper = upper;
      dynamicSchedule.chunk = chunk;
      dynamicSchedule.incr = incr;
      dynamicSchedule.stride = span * static_cast<SignedT>(numThreads);

      DEBUG_PRINT(
          "Dynamic schedule: lowerNext=%d, upper=%d, chunk=%d, incr=%d, "
          "stride=%d, addr: %p\n",
          dynamicSchedule.lowerNext, dynamicSchedule.upper,
          dynamicSchedule.chunk, dynamicSchedule.incr, dynamicSchedule.stride,
          &dynamicSchedule);

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

  template <typename T, typename SignedT = typename std::make_signed<T>::type>
  bool dispatchNext(ident_t * /*loc*/, kmp_int32 /*gtid*/, SignedT *plastiter,
                    T *plower, T *pupper, SignedT *pstride) {

    DEBUG_PRINT("Dispatch next\n");

    auto &dynamicSchedule = std::get<DynamicSchedule<T>>(this->dynamicSchedule);

    std::lock_guard<Mutex> lock(dynamicSchedule.mutex);
    assert(dynamicSchedule.valid && "Dynamic schedule is not valid");

    if (dynamicSchedule.lowerNext > dynamicSchedule.upper) {
      DEBUG_PRINT("Dynamic loop done\n");
      if (++dynamicSchedule.numDone == numThreads) {
        dynamicSchedule.valid = false;
        dynamicSchedule.numDone = 0;
      }

      return false;
    }

    *plower = dynamicSchedule.lowerNext;

    dynamicSchedule.lowerNext += static_cast<T>(dynamicSchedule.chunk);
    if (dynamicSchedule.lowerNext > dynamicSchedule.upper) {
      *pupper = dynamicSchedule.upper;
      *plastiter = true;
    } else {
      *pupper = dynamicSchedule.lowerNext - 1;
      *plastiter = false;
    }

    *pstride = dynamicSchedule.stride;

    return true;
  };

private:
  kmp_uint32 masterGtid;

  kmp_uint32 numThreads;

  Barrier barrier;

  std::variant<DynamicSchedule<kmp_int32>, DynamicSchedule<kmp_uint32>>
      dynamicSchedule;

  void *copyPrivateData = nullptr;

  std::optional<Task> implicitTask;
};

} // namespace kmp
