#pragma once

#include "etl/list.h"
#include "etl/optional.h"
#include "etl/stack.h"
#include "kmp/task.hpp"
#include "kmp/team.hpp"
#include "kmp/types.h"
#include "kmp/util.hpp"

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
  etl::optional<etl::reference_wrapper<const Task>> getCurrentTask();

  // void pushTeam(SharedPointer<Team> team);
  // void popTeam();

  inline SharedPointer<Team> getCurrentTeam() { return currentTeam; };
  inline void setCurrentTeam(SharedPointer<Team> team) {
    DEBUG_PRINT("Setting current team for %d\n", this->gtid);
    currentTeam = std::move(team);
  };

  inline kmp_uint32 getGtid() const { return gtid; };

  inline kmp_uint32 getTid() const { return tid; };

  inline void setTid(kmp_uint32 tid) { this->tid = tid; };

  void requestNumThreads(kmp_int32 numThreads);
  void forkCall(Microtask microtask);

  void copyPrivate(ident_t *loc, kmp_int32 gtid, size_t cpy_size,
                   void *cpy_data, void (*cpy_func)(void *, void *),
                   kmp_int32 didit);

  etl::list<Task, 10> tasks;

private:
  kmp_uint32 gtid;
  volatile kmp_uint32 tid;

  std::atomic<bool> running = false;

  SharedPointer<Team> currentTeam;

  Mutex tasksMutex;
  etl::optional<kmp_int32> requestedNumThreads;
};
}; // namespace kmp
