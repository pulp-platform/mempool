// Copyright 2024 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#pragma once

#include <optional>

#include "kmp/task.hpp"
#include "kmp/types.h"
#include "kmp/util.hpp"
#include "runtime.h"

namespace kmp {

// Forward declaration
class Team;

class Thread {

public:
  Thread(kmp_int32 gtid);
  Thread(kmp_int32 gtid, std::optional<kmp_int32> tid);

  Thread(const Thread &other) = delete;
  Thread(Thread &&) = delete;
  Thread &operator=(const Thread &) = delete;
  Thread &operator=(Thread &&) = delete;

  ~Thread() = default;

  void run();

  inline void wakeUp() {
    std::lock_guard<Mutex> lock(running);
    DEBUG_PRINT("Waking up thread %d\n", gtid);
    wake_up(static_cast<uint32_t>(gtid));
  };

  inline Team *getCurrentTeam() { return currentTeam; };

  inline void setCurrentTeam(Team *team) {
    DEBUG_PRINT("Setting current team for %d: %p\n", this->gtid, team);
    currentTeam = team;
  };

  inline void setTeamsRegion(Task teamsRegion) {
    this->teamsRegion = teamsRegion;
  };

  inline auto getGtid() const { return gtid; };

  inline auto getTid() const { return tid.value_or(0); };

  inline void setTid(kmp_int32 tid) { this->tid = tid; };

  inline bool isRunning() { return running.isLocked(); };

  void requestNumThreads(kmp_int32 numThreads);

  void forkCall(Task microtask);

  void forkTeams(Task microtask);

  void copyPrivate(ident_t *loc, kmp_int32 gtid, size_t cpy_size,
                   void *cpy_data, void (*cpy_func)(void *, void *),
                   kmp_int32 didit);

private:
  kmp_int32 gtid;
  std::optional<kmp_int32> tid;

  // Contains task if this is the initial thread (master) of the teams region
  std::optional<Task> teamsRegion;

  std::atomic<Team *> currentTeam;
  Mutex running;

  std::optional<kmp_int32> requestedNumThreads;
};
}; // namespace kmp
