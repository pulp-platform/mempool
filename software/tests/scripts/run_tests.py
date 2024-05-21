import argparse
import os
import subprocess
import threading
import fnmatch
import re
import queue
import time

DIR = os.path.dirname(os.path.realpath(__file__))
HARDWARE_DIR = os.path.join(DIR, '../../../hardware')
SOFTWARE_DIR = os.path.join(DIR, '../../../software')
TESTS_DIR = os.path.join(SOFTWARE_DIR, 'tests')
BIN_DIR = os.path.join(DIR, '../../bin')
TESTS_BIN_DIR = os.path.join(BIN_DIR, 'tests')

RED = "\033[91m"
GREEN = "\033[92m"
YELLOW = "\033[93m"
RESET = "\033[0m"


def kill_timeout(p):
    print(f'{RED}[FAIL]{RESET}: Timeout')
    p.terminate()


def enqueue_output(out, queue):
    for line in iter(out.readline, ''):
        queue.put(line)


def compile_test(test, args):
    if not os.path.exists(os.path.join(TESTS_DIR, test)):
        print(f'Test {test} not found')
        return False

    env = os.environ
    env["COMPILER"] = args.compiler
    env["config"] = args.config

    if not args.debug:
        env["NDEBUG"] = "1"

    dir, testname = os.path.split(test)

    print(f"Compiling {test}")
    comp = subprocess.run(
        ["make", "-C", os.path.join(TESTS_DIR, dir), testname],
        env=env, capture_output=True)

    if comp.returncode != 0:
        print(f"Failed to compile {test}")
        if args.verbose:
            print(comp.stdout.decode('utf-8'))
            print(comp.stderr.decode('utf-8'))
        return False

    return True


def parse_line(line, stats):
    running_re = re.compile(r'\[RUNNING\]:\s+(.*)')
    success_re = re.compile(r'\[SUCCESS\]:\s+(.*)')
    fail_re = re.compile(r'\[FAIL\]:\s+(.*)')
    failures_re = re.compile(r'\[\w+ FAILED\]:\s+(.*)')

    if m := running_re.search(line):
        stats["num_tests"] += 1
        print(f'{YELLOW}[RUNNING]{RESET}: {m.group(1)}')
    elif m := success_re.search(line):
        print(f'{GREEN}[SUCCESS]{RESET}: {m.group(1)}')
        stats["num_success"] += 1
    elif m := fail_re.search(line):
        print(f'{RED}[FAIL]{RESET}: {m.group(1)}')
    elif m := failures_re.search(line):
        print(f'   {RED}[FAIL]{RESET}: {m.group(1)}')


def print_results(stats):
    print(f'{GREEN if stats["num_success"] > 0 and stats["num_success"] == stats["num_tests"] else RED}'
          f'[RESULT]{RESET}: {stats["num_success"]}/{stats["num_tests"]} tests passed')


def run_test(test, args):
    env = os.environ
    env["app"] = test
    env["config"] = args.config

    output = ''
    timer = None

    print(f"Running {test}")

    stats = {'num_tests': 0, 'num_success': 0}

    try:
        # https://stackoverflow.com/a/76624958
        with subprocess.Popen(["make", "-C", HARDWARE_DIR, args.simulator],
                              env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              text=True, bufsize=1,
                              errors='replace') as p:

            # Start a timer to kill the process if it takes too long
            timer = threading.Timer(args.timeout, kill_timeout, [p])
            timer.start()

            stdout_queue = queue.Queue()
            stderr_queue = queue.Queue()

            stdout_thread = threading.Thread(target=enqueue_output,
                                             args=(p.stdout, stdout_queue))
            stderr_thread = threading.Thread(target=enqueue_output,
                                             args=(p.stderr, stderr_queue))

            stdout_thread.daemon = True
            stderr_thread.daemon = True

            stdout_thread.start()
            stderr_thread.start()

            while True:
                time.sleep(0.1)

                while not stdout_queue.empty() or not stderr_queue.empty():
                    try:
                        stdout_line = stdout_queue.get_nowait()
                    except queue.Empty:
                        stdout_line = None

                    try:
                        stderr_line = stderr_queue.get_nowait()
                    except queue.Empty:
                        stderr_line = None

                    for line in [stdout_line, stderr_line]:
                        if line:
                            output += line
                            parse_line(line, stats)

                            if args.verbose:
                                print(line, end='')

                            if ('Error 117') in line:
                                print(f'{RED}[FAIL]{RESET}: Banshee called '
                                      'the police, most likely a deadlock '
                                      '(all threads called wfi)')
                                p.terminate()
                                return False

                            if ('Stackoverflow' in line):
                                print(f'{RED}[FAIL]{RESET}: Stackoverflow')
                                p.terminate()
                                return False

                            if (args.simulator == "banshee"
                                    and "Program done" in line):
                                p.terminate()
                                break

                if (p.poll() is not None and stdout_queue.empty()
                        and stderr_queue.empty()):
                    break

            if p.returncode is not None and p.returncode > 0:
                print(
                    f'{RED}[FAIL]{RESET}: Non-zero return code {p.returncode}')
                return False

    except Exception as e:
        print(e)
        return False

    finally:
        if timer:
            timer.cancel()
        print_results(stats)


def main():
    parser = argparse.ArgumentParser(description='Run test')
    parser.add_argument('tests', type=str, nargs='+',
                        help='Tests to run (glob matching)')
    parser.add_argument('-t', '--timeout', type=int,
                        default=180, help='Timeout in seconds')
    parser.add_argument('-s', '--simulator', type=str,
                        default='verilator', help='Simulator to use')
    parser.add_argument('-c', '--config', type=str,
                        default='minpool-no-xpulp', help='Mempool configuration')
    parser.add_argument('--compiler', type=str, choices=["gcc", "llvm"],
                        help='Compile test before running')
    parser.add_argument('--verbose', action='store_true', default=False,
                        help='Print verbose output')
    parser.add_argument('--debug', action='store_true', default=False,
                        help='Compile in debug mode')

    args = parser.parse_args()

    matching_tests = []
    for test in args.tests:
        for root, dirs, files in os.walk(TESTS_DIR):
            for d in dirs:
                full_path = os.path.relpath(os.path.join(root, d), TESTS_DIR)
                if fnmatch.fnmatch(full_path, test):
                    matching_tests.append(full_path)

    if not matching_tests:
        print("No tests found matching the pattern")
        return

    print(f"Running tests: {matching_tests}")

    for test in sorted(set(matching_tests)):

        if args.simulator == 'verilator':
            args.simulator = 'verilate'

        print()

        if (args.compiler
                and not compile_test(test, args)):
            continue

        if not os.path.exists(os.path.join(TESTS_BIN_DIR, test)):
            print(f'Test {test} not found')
            continue

        run_test(test, args)


if __name__ == '__main__':
    main()
