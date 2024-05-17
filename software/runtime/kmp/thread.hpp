#pragma once

#include "etl/optional.h"
#include "kmp/task.hpp"
#include "kmp/types.h"
#include "kmp/util.hpp"
#include "kmp/barrier.hpp"

namespace kmp {

// Forward declaration
class Team;

class Thread {

public:
  Thread(kmp_uint32 gtid);
  Thread(kmp_uint32 gtid, kmp_uint32 tid);

  Thread(const Thread &other) = delete;
  Thread(Thread &&) = delete;
  Thread &operator=(const Thread &) = delete;
  Thread &operator=(Thread &&) = delete;

  ~Thread() = default;

  void run();
  void wakeUp();
  bool isRunning() const;

  void pushTask(Task task);

  inline Team *getCurrentTeam() { return currentTeam.get(); };
  inline void setCurrentTeam(SharedPointer<Team> team) {
    DEBUG_PRINT("Setting current team for %d\n", this->gtid);
    currentTeam = std::move(team);
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
  etl::optional<volatile kmp_uint32> tid;

  std::atomic<bool> running = false;

  SharedPointer<Team> currentTeam;

  etl::optional<kmp_int32> requestedNumThreads;

  // Cached values
  etl::optional<SharedPointer<Barrier>> barrier;
};
}; // namespace kmp
