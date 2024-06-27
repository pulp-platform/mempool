// Copyright 2024 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "kmp/thread.hpp"
#include "kmp/team.hpp"
#include "kmp/util.hpp"

extern "C" {
#include "runtime.h"
}

namespace kmp {

Thread::Thread(kmp_int32 gtid) : Thread(gtid, gtid) {}

Thread::Thread(kmp_int32 gtid, kmp_int32 tid)
    : gtid(gtid), tid(tid),
      currentTeam(gtid == 0 ? &runtime::defaultTeam : nullptr){};
;

void Thread::run() {
  while (true) {
    DEBUG_PRINT("Thread %d went to sleep\n", gtid);
    mempool_wfi();
    std::lock_guard<Mutex> lock(running);

    DEBUG_PRINT("Thread %d woke up\n", gtid);

    if (currentTeam != nullptr && !teamsRegion.has_value()) {

      (*currentTeam).getImplicitTask().run(gtid, tid);
      DEBUG_PRINT("Done running task\n");

      Team *prevTeam = currentTeam;
      currentTeam = nullptr;
      tid = gtid;

      (*prevTeam).getBarrier().wait();

    } else if (teamsRegion.has_value()) {
      teamsRegion->run(gtid, tid);
      DEBUG_PRINT("Done running teams region\n");

      teamsRegion.reset();

      delete currentTeam;
      currentTeam = nullptr;
      tid = gtid;

      runtime::teamsBarrier.wait();

    } else {
      DEBUG_PRINT("Thread %d woke up to no work. currentTeam: %p, "
                  "teamsRegion.has_value(): %d\n",
                  gtid, currentTeam, teamsRegion.has_value());
    }
  }
};

void Thread::forkCall(Task parallelRegion) {
  kmp_int32 numThreads = this->requestedNumThreads.value_or(NUM_CORES);
  this->requestedNumThreads.reset();

  DEBUG_PRINT("Forking call with %d threads\n", numThreads);

  Team *team = currentTeam;

  // Setup
  team->setNumThreads(numThreads);
  team->setImplicitTask(parallelRegion);

  // Run on all threads
  team->run();
  parallelRegion.run(gtid, tid);

  DEBUG_PRINT("Done running task\n");
  DEBUG_PRINT("Fork call done\n");

  team->getBarrier().wait();
};

void Thread::forkTeams(Task teamsRegion) {
  runtime::numTeams = runtime::requestedNumTeams.value_or(NUM_GROUPS);
  runtime::teamsBarrier.setNumThreads(runtime::numTeams);
  runtime::requestedNumTeams.reset();

  DEBUG_PRINT("Forking call with %d teams\n", runtime::numTeams);

  kmp_int32 coresPerTeam = NUM_CORES / runtime::numTeams;

  for (kmp_int32 i = 1; i < runtime::numTeams; i++) {
    kmp_int32 coreId = i * coresPerTeam;

    Thread &thread = runtime::getThread(coreId);

    thread.setCurrentTeam(new Team(coreId, i));
    thread.setTeamsRegion(teamsRegion);
    thread.setTid(0);

    if (runtime::requestedThreadLimit) {
      thread.requestNumThreads(runtime::requestedThreadLimit.value());
    }

    thread.wakeUp();
  }

  this->setTeamsRegion(teamsRegion);
  if (runtime::requestedThreadLimit) {
    this->requestNumThreads(runtime::requestedThreadLimit.value());
  }

  teamsRegion.run(gtid, tid);
  this->teamsRegion.reset();

  DEBUG_PRINT("Fork teams done\n");

  runtime::teamsBarrier.wait();

  runtime::numTeams = 1;
};

} // namespace kmp
