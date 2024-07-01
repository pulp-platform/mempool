# Copyright 2024 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import os
import re
import fnmatch
import runner

DIR = os.path.dirname(os.path.realpath(__file__))
SOFTWARE_DIR = os.path.join(DIR, "../")
TESTS_DIR = os.path.join(SOFTWARE_DIR, "tests")
BIN_DIR = os.path.join(DIR, "../bin")
TESTS_BIN_DIR = os.path.join(BIN_DIR, "tests")

RED = "\033[91m"
GREEN = "\033[92m"
YELLOW = "\033[93m"
RESET = "\033[0m"


def parse_line(line, stats):
    running_re = re.compile(r"\[RUNNING\]:\s+(.*)")
    success_re = re.compile(r"\[SUCCESS\]:\s+(.*)")
    fail_re = re.compile(r"\[FAIL\]:\s+(.*)")
    failures_re = re.compile(r"\[\w+ FAILED\]:\s+(.*)")

    if m := running_re.search(line):
        stats["num_tests"] += 1
        print(f"{YELLOW}[RUNNING]{RESET}: {m.group(1)}")
    elif m := success_re.search(line):
        print(f"{GREEN}[SUCCESS]{RESET}: {m.group(1)}")
        stats["num_success"] += 1
    elif m := fail_re.search(line):
        print(f"{RED}[FAIL]{RESET}: {m.group(1)}")
    elif m := failures_re.search(line):
        print(f"   {RED}[FAIL]{RESET}: {m.group(1)}")


def print_results(stats):
    color = (GREEN if stats["num_success"] > 0 and
             stats["num_success"] == stats["num_tests"] else RED)
    print(
        f'{color}'
        f'[RESULT]{RESET}: '
        f'{stats["num_success"]}/{stats["num_tests"]} tests passed'
    )


def main():
    parser = runner.get_arg_parser()
    parser.add_argument(
        "tests", type=str, nargs="+", help="Tests to run (glob matching)"
    )
    parser.add_argument(
        "-r",
        "--repetitions",
        type=int,
        default=10,
        help="Test repetitions (not all tests use this)",
    )

    args = parser.parse_args()

    matching_tests = []
    for test in args.tests:
        for root, dirs, _ in os.walk(TESTS_DIR):
            for d in dirs:
                full_path = os.path.relpath(os.path.join(root, d), TESTS_DIR)
                if fnmatch.fnmatch(full_path, test):
                    matching_tests.append(full_path)

    if not matching_tests:
        print("No tests found matching the pattern")
        return

    print(f"Running tests: {matching_tests}")

    env = os.environ
    env["REPETITIONS"] = str(args.repetitions)

    for test in sorted(set(matching_tests)):
        print()

        testpath = os.path.join(TESTS_DIR, test)

        if args.compiler and not runner.compile(testpath, args, env):
            continue

        if not os.path.exists(os.path.join(TESTS_BIN_DIR, test)):
            print(f"Test {test} not found")
            continue

        stats = {"num_tests": 0, "num_success": 0}

        res, reason, out = runner.run(
            test, args, env,
            lambda line: parse_line(line, stats))

        if not res:
            print(f"{RED}[FAIL]{RESET}: {reason}")
            stats["num_tests"] = "?"

        print_results(stats)


if __name__ == "__main__":
    main()
