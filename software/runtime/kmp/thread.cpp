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

Thread::Thread(kmp_int32 gtid, std::optional<kmp_int32> tid)
    : gtid(gtid), tid(tid),
      currentTeam(gtid == 0 ? &runtime::defaultTeam : nullptr){};

void Thread::run() {
  while (true) {
    mempool_wfi();
    std::lock_guard<Mutex> lock(running);

    DEBUG_PRINT("Thread %d woke up\n", gtid);

    if (currentTeam != nullptr && !teamsRegion.has_value()) {

      (*currentTeam).getImplicitTask()->run(gtid, *tid);
      DEBUG_PRINT("Done running task\n");

      (*currentTeam).getBarrier().wait();

      currentTeam = nullptr;
    } else if (teamsRegion.has_value()) {
      teamsRegion->run(gtid, *tid);
      DEBUG_PRINT("Done running teams region\n");

      teamsRegion.reset();

      runtime::teamsBarrier.wait();

      delete currentTeam;
      currentTeam = nullptr;
    } else {
      DEBUG_PRINT("Thread %d woke up to no work\n", gtid);
    }
  }
};

void Thread::forkCall(Task microtask) {
  kmp_int32 numThreads = this->requestedNumThreads.value_or(NUM_CORES);
  this->requestedNumThreads.reset();

  DEBUG_PRINT("Forking call with %d threads\n", numThreads);

  kmp::Task task(microtask);

  Team *team = currentTeam;

  // Setup
  team->setNumThreads(numThreads);
  team->setImplicitTask(task);

  // Run on all threads
  team->run();
  task.run(gtid, *tid);

  DEBUG_PRINT("Done running task\n");

  team->getBarrier().wait();
};

void Thread::forkTeams(Task microtask) {
  runtime::numTeams = runtime::requestedNumTeams.value_or(NUM_GROUPS);
  runtime::teamsBarrier.setNumThreads(runtime::numTeams);
  runtime::requestedNumTeams.reset();

  DEBUG_PRINT("Forking call with %d teams\n", runtime::numTeams);

  kmp_int32 coresPerTeam = NUM_CORES / runtime::numTeams;

  kmp::Task teamsRegion(microtask);

  kmp_int32 threadLimit = runtime::requestedThreadLimit.value_or(0);

  for (kmp_int32 i = 1; i < runtime::numTeams; i++) {
    kmp_int32 coreId = i * coresPerTeam;

    Thread &thread = runtime::getThread(coreId);

    thread.setCurrentTeam(new Team(coreId, i));
    thread.setTeamsRegion(teamsRegion);
    if (threadLimit > 0) {
      thread.requestNumThreads(threadLimit);
    }

    thread.wakeUp();
  }

  this->setTeamsRegion(teamsRegion);
  if (threadLimit > 0) {
    this->requestNumThreads(threadLimit);
  }
  teamsRegion.run(gtid, *tid);
  this->teamsRegion.reset();

  runtime::teamsBarrier.wait();

  runtime::numTeams = 1;
};

void Thread::requestNumThreads(kmp_int32 numThreads) {
  this->requestedNumThreads = numThreads;
}

void Thread::copyPrivate(ident_t * /*loc*/, kmp_int32 gtid, size_t /*cpy_size*/,
                         void *cpy_data, void (*cpy_func)(void *, void *),
                         kmp_int32 didit) {
  auto *team = getCurrentTeam();

  if (didit != 0) {
    team->setCopyPrivateData(cpy_data);
    DEBUG_PRINT("Thread %d set copyprivate data to %p\n", gtid, cpy_data);
  }

  team->getBarrier().wait();

  if (didit == 0) {
    DEBUG_PRINT("Thread %d copying copyprivate data from %p to %p\n", gtid,
                team->getCopyPrivateData(), cpy_data);
    cpy_func(cpy_data, team->getCopyPrivateData());
  }

  team->getBarrier().wait();
};

} // namespace kmp
