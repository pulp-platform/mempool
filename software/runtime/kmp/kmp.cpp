#include "kmp.hpp"
#include "printf.h"
#include <memory>

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
};

void runThread(kmp_int32 core_id) { threads[core_id].run(); };

} // namespace runtime

Task::Task(Microtask &microtask) : microtask(microtask){};

Task::Task(Microtask &microtask, Barrier &barrier)
    : microtask(microtask), barrier(etl::ref(barrier)){};

void Task::run() {
  microtask.run();

  if (barrier) {
    barrier->get().wait();
  }
};

Microtask::Microtask(kmpc_micro fn, va_list args) : fn(fn) {
  void *arg;
  while ((arg = va_arg(args, void *)) != NULL) {
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

void Thread::run() {
  while (1) {
    mempool_wfi();
    if (tasks.size() > 0) {
      Task task = tasks.front();
      tasks.pop_front();
      task.run();
    }
  }
};

} // namespace kmp
