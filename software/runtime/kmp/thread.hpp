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
  Thread(const Thread &other);

  void run();
  void wakeUp();
  bool isRunning() const;

  void pushTask(const Task &task);
  etl::optional<etl::reference_wrapper<const Task>> getCurrentTask();

  void pushTeam(SharedPointer<Team> team);
  void popTeam();

  SharedPointer<Team> getCurrentTeam();

  kmp_uint32 getGtid() const;
  kmp_uint32 getTid();

  void requestNumThreads(kmp_int32 numThreads);
  void forkCall(const SharedPointer<Microtask> &microtask);

  void copyPrivate(ident_t *loc, kmp_int32 gtid, size_t cpy_size,
                   void *cpy_data, void (*cpy_func)(void *, void *),
                   kmp_int32 didit);

public:
  etl::list<Task, 10> tasks;

protected:
  kmp_uint32 gtid;

private:
  std::atomic<bool> running = false;

  Mutex teamsMutex;
  etl::stack<SharedPointer<Team>, 10> teams;

  Mutex tasksMutex;
  etl::optional<kmp_int32> requestedNumThreads;
};
}; // namespace kmp
