import subprocess
import os
import re
import pandas as pd
from pprint import pp

HARDWARE_DIR="../../hardware"
APPS_DIR="../apps"
KMP_APPS_DIR=APPS_DIR + "/kmp"
OMP_APPS_DIR=APPS_DIR + "/omp"
OUTPUT="results.csv"
UART_REGEX=re.compile(r"\[UART\] ((?!.*\bresult\b).*): (\d+)", re.IGNORECASE)

results = pd.DataFrame(columns=["app", "name", "compiler", "cycles"])

def compileAll(dir, compiler, config="minpool-no-xpulp"):
    env = os.environ
    env["COMPILER"] = compiler
    env["NDEBUG"] = "1"
    env["config"] = config
    subprocess.run(["make", "-C", dir, "all"], env=env)


def runAll(dir, compiler, simulator="verilate", config="minpool-no-xpulp"):
    global results

    env = os.environ
    env["config"] = config

    for app in os.listdir(dir):
        if os.path.isfile(os.path.join(dir, app)) or app.startswith("."):
            continue

        print(f"Running {app}")

        env["app"] = f"{os.path.basename(dir)}/{app}"

        try:
            output = subprocess.run(["make", "-C", HARDWARE_DIR, simulator],
                                     env=env, capture_output=True, text=True,
                                     timeout=500)

        except subprocess.TimeoutExpired as e:
            print("Timeout")
            print(e.stdout.decode())
            print()
            continue

        matches = UART_REGEX.findall(output.stdout)
        for match in matches:
            results = pd.concat([results, pd.DataFrame([{"app": app, "name":
                                                         match[0], "compiler":
                                                         compiler, "cycles":
                                                         int(match[1])}])])


            pp(results)
            print()
            results.to_csv(OUTPUT, index=False)


def main():
    compileAll(KMP_APPS_DIR, "llvm")
    runAll(KMP_APPS_DIR, "llvm")

    compileAll(OMP_APPS_DIR, "gcc")
    runAll(OMP_APPS_DIR, "gcc")

if __name__ == '__main__':
    main()
