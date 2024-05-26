#pragma once

#include "kmp/task.hpp"
#include "kmp/types.h"
#include "kmp/util.hpp"

#include <optional>

namespace kmp {

// Forward declaration
class Team;

class Thread {

public:
  Thread(kmp_uint32 gtid);
  Thread(kmp_uint32 gtid, std::optional<kmp_uint32> tid);

  Thread(const Thread &other) = delete;
  Thread(Thread &&) = delete;
  Thread &operator=(const Thread &) = delete;
  Thread &operator=(Thread &&) = delete;

  ~Thread() = default;

  void run();

  inline void wakeUp() {
    DEBUG_PRINT("Waking up thread %d\n", gtid);
    std::lock_guard<Mutex> lock(running);
    wake_up(gtid);
  };

  inline Team *getCurrentTeam() { return currentTeam; };

  inline void setCurrentTeam(Team *team) {
    DEBUG_PRINT("Setting current team for %d\n", this->gtid);
    currentTeam = team;
  };

  inline kmp_uint32 getGtid() const { return gtid; };

  inline kmp_uint32 getTid() const { return tid.value_or(0); };

  inline void setTid(kmp_uint32 tid) { this->tid = tid; };

  void requestNumThreads(kmp_int32 numThreads);

  void forkCall(Microtask microtask);

  void copyPrivate(ident_t *loc, kmp_int32 gtid, size_t cpy_size,
                   void *cpy_data, void (*cpy_func)(void *, void *),
                   kmp_int32 didit);

private:
  kmp_uint32 gtid;
  std::optional<kmp_uint32> tid;

  std::atomic<Team *> currentTeam;
  Mutex running;

  std::optional<kmp_uint32> requestedNumThreads;
};
}; // namespace kmp
