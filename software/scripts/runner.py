# Copyright 2024 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import os
import subprocess
import threading
import fnmatch
import re
import queue
import time
import signal

DIR = os.path.dirname(os.path.realpath(__file__))
HARDWARE_DIR = os.path.join(DIR, "../../hardware")


# https://stackoverflow.com/a/4791612
def kill_proc(proc):
    os.killpg(os.getpgid(proc.pid), signal.SIGKILL)


def enqueue_output(out, queue):
    try:
        for line in iter(out.readline, ""):
            queue.put(line)
    except Exception as e:
        print(e)
        pass


def compile(prog, args, env_extra):
    if not os.path.exists(prog):
        print(f"{prog} not found")
        return False

    env = os.environ
    env["config"] = args.config
    env["COMPILER"] = args.compiler
    env |= env_extra if env_extra else {}

    if not args.debug:
        env["NDEBUG"] = "1"

    dir, progname = os.path.split(prog)

    print(f"Compiling {progname}")
    comp = subprocess.run(
        ["make", "-C",  dir, progname],
        env=env,
        capture_output=True,
    )

    if comp.returncode != 0:
        print(f"Failed to compile {progname}")
        if args.verbose:
            print(comp.stdout.decode("utf-8"))
            print(comp.stderr.decode("utf-8"))
        return False

    return True


def run(prog, args, env_extra, line_callback):
    if args.simulator == "verilator":
        args.simulator = "verilate"

    env = os.environ
    env["config"] = args.config
    env["app"] = prog
    env |= env_extra if env_extra else {}

    output = ""
    timer = None

    print(f"Running {prog}")

    try:
        # https://stackoverflow.com/a/76624958
        proc = subprocess.Popen(
            ["make", "-C", HARDWARE_DIR, args.simulator],
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
            errors="replace",
            preexec_fn=os.setsid
        )

        # Start a timer to kill the process if it takes too long
        if args.timeout > 0:
            timer = threading.Timer(args.timeout, kill_proc, [proc])
            timer.start()

        stdout_queue = queue.Queue()
        stderr_queue = queue.Queue()

        stdout_thread = threading.Thread(
            target=enqueue_output, args=(proc.stdout, stdout_queue)
        )
        stderr_thread = threading.Thread(
            target=enqueue_output, args=(proc.stderr, stderr_queue)
        )

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
                        line_callback(line)

                        if args.verbose:
                            print(line, end="")

                        if ("Error 117") in line:
                            reason = ("Banshee called "
                                      "the police, most likely a deadlock "
                                      "(all threads called wfi)")
                            kill_proc(proc)
                            return (False, reason)

                        if "Stackoverflow" in line:
                            kill_proc(proc)
                            return (False, "Stackoverflow")

                        if (args.simulator == "banshee" and
                                "Program done" in line):
                            kill_proc(proc)
                            break

            if (
                proc.poll() is not None
                and stdout_queue.empty()
                and stderr_queue.empty()
            ):
                break

        if proc.returncode is not None and proc.returncode > 0:
            return (False, "Non-zero return code")
        elif timer is not None and not timer.is_alive():
            return (False, "Timeout")
        else:
            return (True, output)

    except Exception as e:
        return (False, str(e))

    finally:
        if proc.poll() is None:
            kill_proc(proc)
        if timer:
            timer.cancel()


def get_arg_parser():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "-t",
        "--timeout",
        type=int,
        default=180,
        help="Timeout in seconds (set to 0 to disable)",
    )
    parser.add_argument(
        "-s", "--simulator", type=str, default="verilator",
        help="Simulator to use"
    )
    parser.add_argument(
        "-c",
        "--config",
        type=str,
        default="minpool-no-xpulp",
        help="Mempool configuration",
    )
    parser.add_argument(
        "--compiler",
        type=str,
        choices=["gcc", "llvm"],
        help="Compiler",
    )
    parser.add_argument(
        "--verbose", action="store_true", default=False,
        help="Print verbose output"
    )
    parser.add_argument(
        "--debug", action="store_true", default=False,
        help="Compile in debug mode"
    )

    return parser
