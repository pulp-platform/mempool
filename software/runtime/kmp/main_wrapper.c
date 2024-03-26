#include "printf.h"

int __real_main();

int __wrap_main() {
  printf("Wrapper main");
  return __real_main();
}
