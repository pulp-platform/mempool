#include "kmp/thread.hpp"
#include "kmp/team.hpp"
#include "kmp/util.hpp"

extern "C" {
#include "runtime.h"
}

namespace kmp {

Thread::Thread(kmp_uint32 gtid) : Thread(gtid, gtid) {}

Thread::Thread(kmp_uint32 gtid, std::optional<kmp_uint32> tid)
    : gtid(gtid), tid(tid), currentTeam(nullptr){};

void Thread::run() {
  while (true) {
    mempool_wfi();
    std::lock_guard<Mutex> lock(running);

    DEBUG_PRINT("Thread %d woke up\n", gtid);
    if (currentTeam == nullptr) {
      DEBUG_PRINT("Thread %d has no team\n", gtid);
      continue;
    }

    (*currentTeam).getImplicitTask()->run();

    DEBUG_PRINT("Done running task\n");

    auto &barrier = (*currentTeam).getBarrier();

    currentTeam = nullptr;

    barrier.wait();
  }
};

void Thread::forkCall(Microtask microtask) {
  kmp_uint32 numThreads = this->requestedNumThreads.value_or(NUM_CORES);
  this->requestedNumThreads.reset();

  DEBUG_PRINT("Forking call with %d threads\n", numThreads);

  kmp::Task task(std::move(microtask));
  Team *team = &runtime::defaultTeam; // new Team(this->gtid, numThreads,
                                      ////        std::move(task)); // Do not
                                      /// use shared pointer here
                                      // since it will cause double free

  team->setNumThreads(numThreads);
  team->setImplicitTask(std::move(task));
  team->run();

  team->getImplicitTask()->run();

  DEBUG_PRINT("Done running task\n");

  team->getBarrier().wait();
};

void Thread::requestNumThreads(kmp_int32 numThreads) {
  this->requestedNumThreads = numThreads;
}

void Thread::copyPrivate(ident_t * /*loc*/, kmp_int32 gtid, size_t  /*cpy_size*/,
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
