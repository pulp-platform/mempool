#include "kmp/thread.hpp"
#include "kmp/team.hpp"
#include "kmp/util.hpp"

extern "C" {
#include "runtime.h"
}

namespace kmp {

Thread::Thread(kmp_uint32 gtid) : Thread(gtid, gtid) {}

Thread::Thread(kmp_uint32 gtid, std::optional<kmp_uint32> tid)
    : gtid(gtid), tid(tid),
      currentTeam(gtid == 0 ? &runtime::defaultTeam : nullptr){};

void Thread::run() {
  while (true) {
    mempool_wfi();
    std::lock_guard<Mutex> lock(running);

    DEBUG_PRINT("Thread %d woke up\n", gtid);

    if (currentTeam != nullptr && !teamsRegion.has_value()) {

      (*currentTeam).getImplicitTask()->run();
      DEBUG_PRINT("Done running task\n");

      auto &barrier = (*currentTeam).getBarrier();
      currentTeam = nullptr;

      barrier.wait();

    } else if (teamsRegion.has_value()) {
      teamsRegion->run();
      teamsRegion.reset();
      delete currentTeam;
      runtime::teamsBarrier.wait();
    } else {
      DEBUG_PRINT("Thread %d woke up to no work\n", gtid);
    }
  }
};

void Thread::forkCall(Microtask microtask) {
  kmp_uint32 numThreads = this->requestedNumThreads.value_or(NUM_CORES);
  this->requestedNumThreads.reset();

  DEBUG_PRINT("Forking call with %d threads\n", numThreads);

  kmp::Task task(std::move(microtask));

  Team *team = currentTeam;

  // Setup
  team->setNumThreads(numThreads);
  team->setImplicitTask(std::move(task));

  // Run on all threads
  team->run();
  team->getImplicitTask()->run();

  DEBUG_PRINT("Done running task\n");

  team->getBarrier().wait();
};

void Thread::forkTeams(Microtask microtask) {
  runtime::numTeams = runtime::requestedNumTeams.value_or(NUM_GROUPS);
  runtime::teamsBarrier.setNumThreads(runtime::numTeams);
  runtime::requestedNumTeams.reset();

  DEBUG_PRINT("Forking call with %d teams\n", runtime::numTeams);

  kmp_uint32 coresPerTeam = NUM_CORES / runtime::numTeams;

  kmp::Task teamsRegion(std::move(microtask));

  for (kmp_uint32 i = 1; i < runtime::numTeams; i++) {
    uint32_t coreId = i * coresPerTeam;

    Thread &thread = runtime::threads[coreId];

    thread.setCurrentTeam(new Team(coreId, i));
    thread.setTeamsRegion(teamsRegion);
    if (runtime::requestedThreadLimit.has_value()) {
      thread.requestNumThreads(runtime::requestedThreadLimit.value());
    }

    thread.wakeUp();
  }

  this->setTeamsRegion(teamsRegion);
  teamsRegion.run();
  this->teamsRegion.reset();

  runtime::teamsBarrier.wait();

  runtime::numTeams = 1;
};

void Thread::requestNumThreads(kmp_uint32 numThreads) {
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
