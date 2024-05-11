#include "kmp/task.hpp"
#include "kmp/runtime.hpp"

extern "C" {
#include "runtime.h"
}

namespace kmp {
Task::Task(const SharedPointer<Microtask> &microtask) : microtask(microtask){};

void Task::run() const { microtask->run(); };

Microtask::Microtask(kmpc_micro fn, va_list args, kmp_int32 argc)
    : fn(fn), argc(argc) {
  this->args = new void *[argc];

  if (argc > 15) {
    printf("Unsupported number of microtask arguments, max is 15 and %d were "
           "passed\n",
           argc);
    return;
  }

  void *arg = nullptr;
  for (kmp_int32 i = 0; i < argc; i++) {
    arg = va_arg(args, void *);
    this->args[i] = arg;
  }
};

Microtask::Microtask(Microtask &&other)
    : fn(other.fn), args(other.args), argc(other.argc) {
  other.args = nullptr;
  other.argc = 0;
};

Microtask &Microtask::operator=(Microtask &&other) {
  if (this != &other) {
    fn = other.fn;
    args = other.args;
    argc = other.argc;
    other.args = nullptr;
    other.argc = 0;
  }
  return *this;
};

Microtask::~Microtask() {
  if (args != nullptr) {
    delete[] args;
  }
};

void Microtask::run() const {
  kmp_int32 gtid = mempool_get_core_id();
  kmp_int32 tid = runtime::getCurrentThread().getTid();

  // There seems to not be a better way to do this without custom passes or ASM
  switch (argc) {
  default:
    printf("Unsupported number of microtask arguments, max is 15 and %d were "
           "passed\n",
           argc);
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

} // namespace kmp
