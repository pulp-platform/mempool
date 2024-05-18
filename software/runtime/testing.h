// Inspired by https://jera.com/techinfo/jtns/jtn002

#pragma once

#include "printf.h"

#define MAX_TESTS 20

typedef struct {
  const char *name;
  void (*func)(char const **out_error_message);
} test_t;

test_t tests[MAX_TESTS]; // NOLINT

int tests_run = 0;    // NOLINT(*-global-variables)
int tests_failed = 0; // NOLINT(*-global-variables)
int num_tests = 0;    // NOLINT(*-global-variables)

// NOLINTNEXTLINE
#define STRINGIFY(x) #x
// NOLINTNEXTLINE
#define TOSTRING(x) STRINGIFY(x)
#define LINE_STRING TOSTRING(__LINE__)

// NOLINTNEXTLINE
#define ASSERT_TRUE(condition, error_message)                                  \
  do {                                                                         \
    if (!(condition)) {                                                        \
      *out_error_message = (error_message);                                    \
      return;                                                                  \
    }                                                                          \
  } while (0)

// NOLINTNEXTLINE
#define ASSERT_EQ(left, right)                                                 \
  do {                                                                         \
    if (!((left) == (right))) {                                                \
      *out_error_message =                                                     \
          #left " is not equal to " #right ", " __FILE__ ":" LINE_STRING;      \
      return;                                                                  \
    }                                                                          \
  } while (0)

// NOLINTNEXTLINE
#define ASSERT_NEQ(left, right)                                                \
  do {                                                                         \
    if (!((left) != (right))) {                                                \
      *out_error_message =                                                     \
          #left " is equal to " #right ", " __FILE__ ":" LINE_STRING;          \
      return;                                                                  \
    }                                                                          \
  } while (0)

// NOLINTNEXTLINE
#define EXPECT_TRUE(condition, error_message)                                  \
  do {                                                                         \
    if (!(condition))                                                          \
      printf("\t[CHECK FAILED]: %s, %s:%d\n", (error_message), __FILE__,       \
             __LINE__);                                                        \
  } while (0)

// NOLINTNEXTLINE
#define RUN_TEST(test)                                                         \
  do {                                                                         \
    printf("\n[RUNNING]: %s \n", (test).name);                                 \
    const char *message = NULL;                                                \
    ((test).func)(&message);                                                   \
    tests_run++;                                                               \
    if (message != NULL) {                                                     \
      tests_failed++;                                                          \
      printf("\t[ASSERTION FAILED]: %s\n", message);                           \
      printf("[FAIL]: %s\n", (test).name);                                     \
    } else {                                                                   \
      printf("[SUCCESS]: %s\n", (test).name);                                  \
    }                                                                          \
  } while (0)

// NOLINTNEXTLINE
#define RUN_ALL_TESTS()                                                        \
  do {                                                                         \
    for (int i = 0; i < num_tests; i++) {                                      \
      RUN_TEST(tests[i]);                                                      \
    }                                                                          \
  } while (0)

// NOLINTNEXTLINE
#define PRINT_TEST_RESULTS()                                                   \
  do {                                                                         \
    printf("Ran %d tests\n", tests_run);                                       \
    printf("Failed %d tests\n", tests_failed);                                 \
  } while (0)

// NOLINTNEXTLINE
#define TEST(testname)                                                         \
  void testname(char const **out_error_message);                               \
  __attribute__((constructor)) void add_##testname##_to_array(void) {          \
    if (num_tests < MAX_TESTS) {                                               \
      tests[num_tests].name = #testname;                                       \
      tests[num_tests].func = testname;                                        \
      num_tests++;                                                             \
    } else {                                                                   \
      printf("Too many tests added, max is %s\n", MAX_TESTS);                  \
    }                                                                          \
  }                                                                            \
  void testname(char const **out_error_message)
