// Copyright 2024 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#pragma once

#include <array>
#include <mutex>
#include <optional>

#include "kmp/barrier.hpp"
#include "kmp/runtime.hpp"
#include "kmp/types.h"
#include "kmp/util.hpp"
#include "printf.h"

namespace kmp {

class Thread;
class Task;
class Barrier;

class Team {

  struct DynamicSchedule {
    kmp_uint32 lowerNext = 0;
    kmp_uint32 upper = 0;
    kmp_uint32 chunk = 0; // Chunk size assumed to be positive
    kmp_int32 incr = 0;
    kmp_int32 stride = 0;

    bool valid = false;
    kmp_int32 numDone = 0;

    Mutex mutex;
  };

public:
  Team(const Team &) = delete;
  Team(Team &&) = delete;
  Team &operator=(const Team &) = delete;
  Team &operator=(Team &&) = delete;

  inline Team(kmp_int32 masterGtid, kmp_int32 teamId)
      : masterGtid(masterGtid), teamId(teamId), barrier(numThreads),
        implicitTask(nullptr, nullptr, 0) {}

  inline ~Team() {
    for (kmp_int32 i = masterGtid + 1; i < masterGtid + numThreads; i++) {
      while (runtime::getThread(i).isRunning()) {
        // Wait for thread to finish
        DEBUG_PRINT("Waiting for thread %d to finish\n", i);
      }
    }
  }

  inline Barrier &getBarrier() { return barrier; }

  inline const Task &getImplicitTask() const { return implicitTask; }

  inline void setImplicitTask(Task task) { implicitTask = task; }

  inline auto getNumThreads() const { return numThreads; }

  inline void setNumThreads(kmp_int32 numThreads) {
    if (teamId == runtime::numTeams - 1) {
      // Last team gets the remaining threads
      numThreads = std::min(numThreads, NUM_CORES - masterGtid);
    } else {
      // Limit thread number
      numThreads = std::min(numThreads, NUM_CORES / runtime::numTeams);
    }

    DEBUG_PRINT("Team %d has %d threads\n", teamId, numThreads);

    this->numThreads = numThreads;
    this->barrier.setNumThreads(numThreads);
  }

  inline auto setCopyPrivateData(void *data) { copyPrivateData = data; }

  inline auto getCopyPrivateData() const { return copyPrivateData; }

  inline void run() {
    if (runtime::numTeams > 1) {
      for (kmp_int32 i = masterGtid + 1; i < masterGtid + numThreads; i++) {
        auto &thread = runtime::getThread(i);
        thread.setTid(i - masterGtid);

        if (i != masterGtid) {
          thread.setCurrentTeam(this);
          thread.wakeUp();
        }
      }
    } else {
      for (kmp_int32 i = masterGtid + 1; i < masterGtid + numThreads; i++) {
        auto &thread = runtime::getThread(i);
        thread.setCurrentTeam(this);
      }

      wake_up_all();
      mempool_wfi();
    }
  }

  inline auto getTeamId() const { return teamId; }

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
   * @param chunk Chunk size
   */
  template <typename T, typename SignedT = typename std::make_signed<T>::type,
            typename UnsignedT = typename std::make_unsigned<T>::type>
  void forStaticInit(ident_t * /*loc*/, kmp_int32 gtid,
                     kmp_sched_type schedtype, T *plastiter, T *plower,
                     T *pupper, SignedT *pstride, SignedT incr,
                     SignedT chunk) const {

    assert(incr == 1 && "Loop increment is not 1");

    switch (schedtype) {
    case kmp_sch_static: {

      // Calculate chunk size
      // https://stackoverflow.com/a/14878734
      chunk = static_cast<SignedT>(*pupper - *plower + 1) / numThreads +
              (static_cast<SignedT>(*pupper - *plower + 1) % numThreads != 0);

      // Fall through to static chunked
    }
    case kmp_sch_static_chunked: {
      assert(incr != 0 && "Loop increment must be non-zero");
      assert(chunk > 0 && "Chunk size is not positive");
      assert((static_cast<T>(chunk) <= *pupper - *plower + 1) &&
             "Chunk size is greater than loop size");

      kmp_int32 tid = runtime::getThread(gtid).getTid();

      SignedT numChunks =
          (static_cast<SignedT>(*pupper - *plower) + chunk) / chunk;

      SignedT span = incr * chunk;
      *pstride = span * static_cast<SignedT>(numThreads);
      *plower = *plower + static_cast<T>(tid) * static_cast<T>(span);
      *pupper = *plower + static_cast<T>(span - incr);
      *plastiter = (tid == (numChunks - 1) % numThreads);

      break;
    }

    // Distribute (teams)
    case kmp_distribute_static: {

      // Calculate chunk size
      // https://stackoverflow.com/a/14878734
      chunk =
          static_cast<SignedT>(*pupper - *plower + 1) / runtime::numTeams +
          (static_cast<SignedT>(*pupper - *plower + 1) % runtime::numTeams !=
           0);

      // Fall through to static chunked
    }
    case kmp_distribute_static_chunked: {
      assert(incr != 0 && "Loop increment must be non-zero");
      assert(chunk > 0 && "Chunk size is not positive");
      assert((static_cast<T>(chunk) <= *pupper - *plower + 1) &&
             "Chunk size is greater than loop size");

      SignedT numChunks =
          (static_cast<SignedT>(*pupper - *plower) + chunk) / chunk;

      SignedT span = incr * chunk;
      *pstride = span * static_cast<SignedT>(runtime::numTeams);
      *plower = *plower + static_cast<T>(teamId) * static_cast<T>(span);
      *pupper = *plower + static_cast<T>(span - incr);
      *plastiter = (teamId == (numChunks - 1) % runtime::numTeams);

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

    DEBUG_PRINT("Got dynamic schedule\n");

    switch (schedtype) {
    case kmp_sch_dynamic_chunked: {
      std::lock_guard<Mutex> lock(dynamicSchedule.mutex);

      if (dynamicSchedule.valid) {
        DEBUG_PRINT("Dynamic schedule is already valid\n");
        return;
      }

      SignedT span = incr * chunk;

      dynamicSchedule.lowerNext = static_cast<kmp_uint32>(lower);
      dynamicSchedule.upper = static_cast<kmp_uint32>(upper);
      dynamicSchedule.chunk = static_cast<kmp_uint32>(chunk);
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

    *plower = static_cast<T>(dynamicSchedule.lowerNext);

    dynamicSchedule.lowerNext += dynamicSchedule.chunk;
    if (dynamicSchedule.lowerNext > dynamicSchedule.upper) {
      *pupper = static_cast<T>(dynamicSchedule.upper);
      *plastiter = true;
    } else {
      *pupper = static_cast<T>(dynamicSchedule.lowerNext - 1);
      *plastiter = false;
    }

    *pstride = dynamicSchedule.stride;

    return true;
  };

  inline void copyPrivate(ident_t * /*loc*/, kmp_int32 gtid,
                          size_t /*cpy_size*/, void *cpy_data,
                          void (*cpy_func)(void *, void *), kmp_int32 didit) {
    if (didit != 0) {
      copyPrivateData = cpy_data;
      DEBUG_PRINT("Thread %d set copyprivate data to %p\n", gtid, cpy_data);
    }

    barrier.wait();

    if (didit == 0) {
      DEBUG_PRINT("Thread %d copying copyprivate data from %p to %p\n", gtid,
                  copyPrivateData, cpy_data);
      cpy_func(cpy_data, copyPrivateData);
    }

    barrier.wait();
  };

private:
  kmp_int32 masterGtid = 0;
  kmp_int32 teamId = 0;
  kmp_int32 numThreads = 1;

  Barrier barrier;

  DynamicSchedule dynamicSchedule;

  void *copyPrivateData = nullptr;

  Task implicitTask;
};

} // namespace kmp
