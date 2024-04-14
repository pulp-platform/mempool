#include "kmp.hpp"
#include "printf.h"
#include <atomic>
#include <memory>
#include <mutex>

extern "C" {
#include "runtime.h"
}

namespace kmp {

namespace runtime {

etl::vector<kmp::Thread, NUM_CORES> threads(NUM_CORES);

void printError(const etl::exception &e) {
  printf("%s %s %d\n", e.what(), e.file_name(), e.line_number());
};

void init() {
  printf("Initializing runtime\n");

  etl::error_handler::set_callback<printError>();

  for (kmp_int32 i = 0; i < NUM_CORES; i++) {
    threads[i].coreId = i;
  }
};

void runThread(kmp_int32 core_id) { threads[core_id].run(); };

} // namespace runtime

Task::Task(const Microtask &microtask, Barrier &barrier)
    : microtask(microtask), barrier(etl::ref(barrier)){};

void Task::barrierWait() const { barrier.get().wait(); };

void Task::run() {
  microtask.run();
  barrierWait();
};

Microtask::Microtask(kmpc_micro fn, va_list args, kmp_int32 argc) : fn(fn) {
  if (argc > 15) {
    printf("Unsupported number of microtask arguments, max is 15 and %d were "
           "passed\n",
           argc);
    return;
  }

  void *arg = nullptr;
  for (kmp_int32 i = 0; i < argc; i++) {
    arg = va_arg(args, void *);
    this->args.push_back(arg);
  }
};

void Microtask::run() {
  kmp_int32 gtid = mempool_get_core_id();
  kmp_int32 tid = gtid; // TODO: Change this

  // There seems to not be a better way to do this without custom passes or ASM
  switch (args.size()) {
  default:
    printf("Unsupported number of microtask arguments, max is 15 and %d were "
           "passed\n",
           args.size());
    return;
  case 0:
    fn(&gtid, &tid);
    break;
  case 1:
    fn(&gtid, &tid, args[0]);
    break;
  case 2:
    fn(&gtid, &tid, args[0], args[1]);
    break;
  case 3:
    fn(&gtid, &tid, args[0], args[1], args[2]);
    break;
  case 4:
    fn(&gtid, &tid, args[0], args[1], args[2], args[3]);
    break;
  case 5:
    fn(&gtid, &tid, args[0], args[1], args[2], args[3], args[4]);
    break;
  case 6:
    fn(&gtid, &tid, args[0], args[1], args[2], args[3], args[4], args[5]);
    break;
  case 7:
    fn(&gtid, &tid, args[0], args[1], args[2], args[3], args[4], args[5],
       args[6]);
    break;
  case 8:
    fn(&gtid, &tid, args[0], args[1], args[2], args[3], args[4], args[5],
       args[6], args[7]);
    break;
  case 9:
    fn(&gtid, &tid, args[0], args[1], args[2], args[3], args[4], args[5],
       args[6], args[7], args[8]);
    break;
  case 10:
    fn(&gtid, &tid, args[0], args[1], args[2], args[3], args[4], args[5],
       args[6], args[7], args[8], args[9]);
    break;
  case 11:
    fn(&gtid, &tid, args[0], args[1], args[2], args[3], args[4], args[5],
       args[6], args[7], args[8], args[9], args[10]);
    break;
  case 12:
    fn(&gtid, &tid, args[0], args[1], args[2], args[3], args[4], args[5],
       args[6], args[7], args[8], args[9], args[10], args[11]);
    break;
  case 13:
    fn(&gtid, &tid, args[0], args[1], args[2], args[3], args[4], args[5],
       args[6], args[7], args[8], args[9], args[10], args[11], args[12]);
    break;
  case 14:
    fn(&gtid, &tid, args[0], args[1], args[2], args[3], args[4], args[5],
       args[6], args[7], args[8], args[9], args[10], args[11], args[12],
       args[13]);
    break;
  case 15:
    fn(&gtid, &tid, args[0], args[1], args[2], args[3], args[4], args[5],
       args[6], args[7], args[8], args[9], args[10], args[11], args[12],
       args[13], args[14]);
    break;
  }
};

Thread::Thread(const Thread &other){};

void Thread::run() {
  while (1) {
    while (!running) {
      mempool_wfi();
    }

    tasksLock.lock();
    if (tasks.size() > 0) {
      Task &task = tasks.front();
      tasksLock.unlock();

      task.run();

      tasksLock.lock();
      tasks.pop_front();
      tasksLock.unlock();
    } else {
      running = false;
      tasksLock.unlock();
    }
  }
};

void Thread::wakeUp() {
  if (running) {
    return;
  } else {
    running = true;
    wake_up(coreId);
  }
};

void Thread::pushTask(const Task &task) {
  std::lock_guard<Mutex> lock(tasksLock);

  tasks.push_back(task);
};

etl::optional<etl::reference_wrapper<const Task>> Thread::getCurrentTask() {
  std::lock_guard<Mutex> lock(tasksLock);

  if (tasks.size() > 0) {
    return etl::cref(tasks.front());
  } else {
    return etl::nullopt;
  }
};

} // namespace kmp
