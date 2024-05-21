#include "kmp/task.hpp"
#include "kmp/runtime.hpp"
#include "printf.h"

extern "C" {
#include "runtime.h"
}

namespace kmp {
Microtask::Microtask(kmpc_micro func, va_list args, kmp_int32 argc)
    : func(func), args(nullptr), argc(argc) {

  assert(argc <= MAX_ARGS && "Unsupported number of microtask arguments");

  if (argc > MAX_ARGS) {
    printf("Unsupported number of microtask arguments, max is %d and %d were "
           "passed\n",
           MAX_ARGS, argc);
    return;
  }

  this->args = new void *[argc];

  DEBUG_PRINT("Microtask constructor, args: %p\n", this->args);

  void *arg = nullptr;
  for (kmp_int32 i = 0; i < argc; i++) {
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-vararg)
    arg = va_arg(args, void *);
    // NOLINTNEXTLINE(cppcoreguidelines-pro-bounds-pointer-arithmetic)
    this->args[i] = arg;
  }
};

Microtask::Microtask(Microtask &&other) noexcept
    : func(other.func), args(other.args), argc(other.argc) {
  other.args = nullptr;
  other.argc = 0;
};

Microtask &Microtask::operator=(Microtask &&other) noexcept {
  if (this != &other) {
    func = other.func;
    args = other.args;
    argc = other.argc;
    other.args = nullptr;
    other.argc = 0;
  }
  return *this;
};

Microtask::~Microtask() {
  delete[] args;
};

void Microtask::run() const {
  kmp_int32 gtid = static_cast<kmp_int32>(mempool_get_core_id());
  kmp_int32 tid = static_cast<kmp_int32>(runtime::getCurrentThread().getTid());

  assert(argc <= MAX_ARGS && "Unsupported number of microtask arguments");

  // There seems to not be a better way to do this without custom passes or ASM
  switch (argc) {
  default:
    printf("Unsupported number of microtask arguments, max is %d and %d were "
           "passed\n",
           MAX_ARGS, argc);
    return;

  // NOLINTBEGIN(cppcoreguidelines-pro-bounds-pointer-arithmetic,*-magic-numbers)
  case 0:
    func(&gtid, &tid);
    break;
  case 1:
    func(&gtid, &tid, args[0]);
    break;
  case 2:
    func(&gtid, &tid, args[0], args[1]);
    break;
  case 3:
    func(&gtid, &tid, args[0], args[1], args[2]);
    break;
  case 4:
    func(&gtid, &tid, args[0], args[1], args[2], args[3]);
    break;
  case 5:
    func(&gtid, &tid, args[0], args[1], args[2], args[3], args[4]);
    break;
  case 6:
    func(&gtid, &tid, args[0], args[1], args[2], args[3], args[4], args[5]);
    break;
  case 7:
    func(&gtid, &tid, args[0], args[1], args[2], args[3], args[4], args[5],
         args[6]);
    break;
  case 8:
    func(&gtid, &tid, args[0], args[1], args[2], args[3], args[4], args[5],
         args[6], args[7]);
    break;
  case 9:
    func(&gtid, &tid, args[0], args[1], args[2], args[3], args[4], args[5],
         args[6], args[7], args[8]);
    break;
  case 10:
    func(&gtid, &tid, args[0], args[1], args[2], args[3], args[4], args[5],
         args[6], args[7], args[8], args[9]);
    break;
  case 11:
    func(&gtid, &tid, args[0], args[1], args[2], args[3], args[4], args[5],
         args[6], args[7], args[8], args[9], args[10]);
    break;
  case 12:
    func(&gtid, &tid, args[0], args[1], args[2], args[3], args[4], args[5],
         args[6], args[7], args[8], args[9], args[10], args[11]);
    break;
  case 13:
    func(&gtid, &tid, args[0], args[1], args[2], args[3], args[4], args[5],
         args[6], args[7], args[8], args[9], args[10], args[11], args[12]);
    break;
  case 14:
    func(&gtid, &tid, args[0], args[1], args[2], args[3], args[4], args[5],
         args[6], args[7], args[8], args[9], args[10], args[11], args[12],
         args[13]);
    break;
  case 15:
    func(&gtid, &tid, args[0], args[1], args[2], args[3], args[4], args[5],
         args[6], args[7], args[8], args[9], args[10], args[11], args[12],
         args[13], args[14]);
    break;
  }
  // NOLINTEND(cppcoreguidelines-pro-bounds-pointer-arithmetic,*-magic-numbers)
};

} // namespace kmp
