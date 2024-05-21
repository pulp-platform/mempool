import subprocess
import os
import re
import pandas as pd
import threading
import queue
import time
from pprint import pp

HARDWARE_DIR = "../hardware"
APPS_DIR = "../software/apps"
KMP_APPS_DIR = APPS_DIR + "/kmp"
OMP_APPS_DIR = APPS_DIR + "/omp"
UART_REGEX = re.compile(r"\[UART\] ((?!.*\bresult\b).*): (\d+)", re.IGNORECASE)
GIT_COMMIT_HASH = subprocess.check_output(
    ["git", "describe", "--always", "--dirty"]).strip().decode("utf-8")
OUTPUT = f"results/{GIT_COMMIT_HASH}/results.csv"

results = pd.DataFrame(columns=["app", "name", "compiler", "cycles"])


def kill_timeout(p):
    print('Timeout')
    p.terminate()


def enqueue_output(out, queue):
    for line in iter(out.readline, ''):
        queue.put(line)


def compileAll(dir, compiler, config="minpool-no-xpulp"):
    env = os.environ
    env["COMPILER"] = compiler
    env["NDEBUG"] = "1"
    env["config"] = config
    subprocess.run(["make", "-C", dir, "all"], env=env)


def run_benchmark(app, simulator, config):
    env = os.environ
    env["app"] = app
    env["config"] = config

    output = ''
    timer = None

    print(f"Running {app}")

    try:
        # https://stackoverflow.com/a/76624958
        with subprocess.Popen(["make", "-C", HARDWARE_DIR, simulator],
                              env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              text=True, bufsize=1,
                              errors='replace') as p:

            # Start a timer to kill the process if it takes too long
            timer = threading.Timer(120, kill_timeout, [p])
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
                time.sleep(1)

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

                            if True:
                                print(line, end='')

                            if ('Stackoverflow' in line):
                                print("Stackoverflow")
                                p.terminate()
                                return False

                            if (simulator == "banshee" and "Program done" in line):
                                p.terminate()
                                break

                if (p.poll() is not None and stdout_queue.empty()
                        and stderr_queue.empty()):
                    break

            if p.returncode is not None and p.returncode > 0:
                print(f'Non-zero return code {p.returncode}')
                return False

    except Exception as e:
        print(e)
        return False

    finally:
        if timer:
            timer.cancel()

    return output


def runAll(dir, compiler, simulator="verilate", config="minpool-no-xpulp"):
    global results

    env = os.environ
    env["config"] = config

    for app in os.listdir(dir):
        if (os.path.isfile(os.path.join(dir, app)) or app.startswith(".")
                or "benchmark" not in app):
            continue

        print(f"Running {app}")

        app_dir = f"{os.path.basename(dir)}/{app}"

        output = ""

        output = run_benchmark(app_dir, simulator, config)
        if not output:
            continue

        matches = UART_REGEX.findall(output)
        for match in matches:
            results = pd.concat([results, pd.DataFrame([{"app": app, "name":
                                                         match[0], "compiler":
                                                         compiler, "cycles":
                                                         int(match[1])}])])

        pp(results)
        print()
        results.to_csv(OUTPUT, index=False)


def main():
    os.makedirs(f'results/{GIT_COMMIT_HASH}', exist_ok=True)

    compileAll(KMP_APPS_DIR, "llvm")
    runAll(KMP_APPS_DIR, "llvm")

    compileAll(OMP_APPS_DIR, "gcc")
    runAll(OMP_APPS_DIR, "gcc")


if __name__ == '__main__':
    main()
