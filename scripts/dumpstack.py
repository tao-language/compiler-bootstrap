#!/usr/bin/env python3
"""Sample Erlang stack traces of a running Gleam program to debug hangs.

`gleam run` / `gleam test` really run:

    erl -pa <ebins...> -eval '<name>@@main:run(<module>)' -noshell -extra <args>

where <module> is the project name (run) or <name>_test (test). Instead of
relying on gleam to launch the VM, this script builds the project and runs
the compiled beams directly, injecting a sampling stack profiler via:

    -s samplestack start     (spawns the sampler, scripts/samplestack.erl)
    -s dumpstack_main start  (runs the program's main, generated wrapper)

The sampler prints one line per non-idle process per tick (deduped: a line
is only repeated when the set of stacks changes), plus a short histogram of
the most common top frames. Samples are written to a log file, flushed line
by line, because the VM is terminated with SIGKILL at the end, which would
lose anything still buffered in a stdout pipe. The VM is also run with a
per-process heap cap (+hmax) so a runaway allocation cannot exhaust the
machine's memory.

Usage:
  python scripts/dumpstack.py [--delay=S] [--duration=S] [--sampling-rate=N] [--test] -- [args...]

Examples:
  python scripts/dumpstack.py -- run lib/prelude/v0.0.1/result.tao
  python scripts/dumpstack.py --sampling-rate=10 -- test lib/prelude/v0.0.1/result.tao
  python scripts/dumpstack.py --delay=1.5 --test
"""

import argparse
import glob
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)

# Line the sampler writes when it is about to start sampling.
START_MARKER = "sampler: sampling for"

# Per-process heap cap for the target VM, in words (8 bytes each): 16 GiB.
# The hang we debug grows a data structure without bound, which would
# otherwise let the VM exhaust the machine's memory before we kill it.
# Capping the heap makes the runaway process die (with a heap_limit error)
# instead, while the sampler captures its stack first.
HEAP_CAP_WORDS = 16 * 1024 ** 3 // 8


def beam_pids():
    """Return the pids of all running beam.smp processes (as a set)."""
    try:
        r = subprocess.run(["ps", "-axo", "pid=,command="],
                           capture_output=True, text=True)
    except OSError:
        return set()
    pids = set()
    for line in r.stdout.splitlines():
        parts = line.strip().split(None, 1)
        if len(parts) == 2 and "beam.smp" in parts[1]:
            try:
                pids.add(int(parts[0]))
            except ValueError:
                pass
    return pids


def parse_args(argv):
    ap = argparse.ArgumentParser(
        description="Sampling stack profiler for debugging Gleam/BEAM hangs.",
        epilog="everything after `--` is passed to the target program",
    )
    ap.add_argument("--delay", type=float, default=0.0,
                    help="start sampling after this many seconds (default 0)")
    ap.add_argument("--duration", type=float, default=2.0,
                    help="how long to sample for, in seconds (default 2)")
    ap.add_argument("--sampling-rate", type=int, default=30,
                    help="samples per second (default 30)")
    ap.add_argument("--test", action="store_true",
                    help="run the project's test suite (gleam test) instead "
                         "of `gleam run`")
    ap.add_argument("rest", nargs=argparse.REMAINDER,
                    help="arguments after `--`")
    args = ap.parse_args(argv)
    rest = list(args.rest)
    if rest and rest[0] == "--":
        rest = rest[1:]
    return args, rest


def project_name():
    with open(os.path.join(ROOT, "gleam.toml")) as f:
        m = re.search(r'^\s*name\s*=\s*["\']([^"\']+)["\']', f.read(), re.M)
    if not m:
        sys.exit("error: could not find name = \"...\" in gleam.toml")
    return m.group(1)


def compile_erl(erlc, src, tmp):
    r = subprocess.run([erlc, "-o", tmp, src], capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit("error: failed to compile %s:\n%s%s"
                 % (os.path.basename(src), r.stdout, r.stderr))
    if not os.path.exists(os.path.join(tmp, os.path.basename(src[:-4]) + ".beam")):
        sys.exit("error: no beam produced for %s" % src)


def stream_stdout(proc, stop):
    """Stream the target's stdout (program output) to the terminal."""
    for line in proc.stdout:
        if stop.is_set():
            break
        sys.stdout.write(line)
        sys.stdout.flush()


def print_line(line):
    sys.stdout.write(line + "\n")
    sys.stdout.flush()


class LogTailer:
    """Tail the sampler's log file, printing complete lines to stdout.

    A line could in theory be observed mid-write; only emit up to the last
    newline and carry the rest over.
    """

    def __init__(self, path, stop, on_line):
        self.path = path
        self.stop = stop
        self.on_line = on_line

    def run(self):
        with open(self.path, "r", errors="replace") as f:
            buf = ""
            while not self.stop.is_set():
                chunk = f.read(65536)
                if chunk:
                    buf += chunk
                    while "\n" in buf:
                        line, buf = buf.split("\n", 1)
                        self.on_line(line)
                else:
                    time.sleep(0.02)
            if buf:
                self.on_line(buf)


def main():
    args, rest = parse_args(sys.argv[1:])
    if args.sampling_rate < 1:
        sys.exit("error: --sampling-rate must be >= 1")
    if args.duration <= 0:
        sys.exit("error: --duration must be > 0")
    if args.delay < 0:
        sys.exit("error: --delay must be >= 0")
    if not args.test and not rest:
        sys.exit("error: nothing to run; pass e.g. `-- test lib/foo.tao` "
                 "or use --test")

    name = project_name()
    module = name + "_test" if args.test else name

    tmp = tempfile.mkdtemp(prefix="dumpstack-")
    try:
        print("[dumpstack] building project...")
        if subprocess.run(["gleam", "build"], cwd=ROOT).returncode != 0:
            sys.exit("error: gleam build failed")

        erlc = shutil.which("erlc") or "erlc"
        compile_erl(erlc, os.path.join(HERE, "samplestack.erl"), tmp)

        # Wrapper that runs the program's main. (-s bundles its arguments
        # into a single list, so we can't pass the module atom directly.)
        wrapper = os.path.join(tmp, "dumpstack_main.erl")
        with open(wrapper, "w") as f:
            f.write("-module(dumpstack_main).\n"
                    "-export([start/0]).\n"
                    "start() -> %s@@main:run(%s).\n" % (name, module))
        compile_erl(erlc, wrapper, tmp)

        # -s modules run in command line order during boot, so the sampler
        # starts before the program does.
        ebin_dirs = sorted(glob.glob(os.path.join(ROOT, "build", "dev",
                                                  "erlang", "*", "ebin")))
        if not ebin_dirs:
            sys.exit("error: no ebin dirs found under build/dev/erlang")
        cmd = (["erl", "-smp",
                "-hmax", str(HEAP_CAP_WORDS)]
               + [a for d in ebin_dirs for a in ("-pa", d)]
               + ["-pa", tmp]
               + ["-s", "samplestack", "start",
                  "-s", "dumpstack_main", "start",
                  "-noshell"])
        if rest:
            cmd += ["--"] + rest

        # Sampler output goes to this file (flushed line by line) so it
        # survives the SIGKILL; the program's own output goes to stdout.
        # It must exist before the VM starts (append mode does not create).
        log_path = os.path.join(tmp, "samples.log")
        open(log_path, "w").close()

        delay_ms = int(args.delay * 1000)
        dur_ms = int(args.duration * 1000)
        interval_ms = max(1, round(1000 / args.sampling_rate))
        env = dict(os.environ)
        env["DUMPSTACK_DELAY_MS"] = str(delay_ms)
        env["DUMPSTACK_DURATION_MS"] = str(dur_ms)
        env["DUMPSTACK_INTERVAL_MS"] = str(interval_ms)
        env["DUMPSTACK_LOG"] = log_path

        print("[dumpstack] running module %s with: %s"
              % (module, " ".join(rest)))
        before_beams = beam_pids()
        target = subprocess.Popen(
            cmd, cwd=ROOT, env=env,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            start_new_session=True, universal_newlines=True, bufsize=1)

        stop = threading.Event()
        sampling_started = threading.Event()
        n_samplers = [0]
        summarized = set()

        def on_log_line(line):
            print_line(line)
            if START_MARKER in line:
                sampling_started.set()
            m = re.search(r"\[sampler \d+ of (\d+)\]$", line)
            if m:
                n_samplers[0] = int(m.group(1))
            m = re.search(r"^sampler\[(\d+)\]:", line)
            if m:
                summarized.add(int(m.group(1)))

        t_log = threading.Thread(
            target=LogTailer(log_path, stop, on_log_line).run, daemon=True)
        t_log.start()
        t_out = threading.Thread(
            target=stream_stdout, args=(target, stop), daemon=True)
        t_out.start()

        # Wait for the sampler to start (or the target to die on its own),
        # then let the sample window elapse, plus a margin so the sampler
        # can write its summary before we kill the VM.
        deadline = time.time() + 30
        while time.time() < deadline:
            if sampling_started.is_set() or target.poll() is not None:
                break
            time.sleep(0.1)

        if sampling_started.is_set():
            # Let the sample window elapse (plus a margin so the sampler
            # can write its summary), but stop waiting if the target dies.
            window_end = time.time() + args.delay + args.duration + 2
            while target.poll() is None and time.time() < window_end:
                time.sleep(0.2)

        # Erlang processes MUST be terminated with SIGKILL or a beam.smp
        # process is leaked.
        killed = False
        if target.poll() is None:
            killed = True
            try:
                os.killpg(target.pid, signal.SIGKILL)
            except (ProcessLookupError, PermissionError):
                target.kill()
        rc = target.wait()
        stop.set()
        t_log.join(timeout=2)
        t_out.join(timeout=2)

        # Defensive sweep: kill any beam.smp that appeared during the run
        # (our VM should already be dead; anything new is a leak).
        leaked = sorted(pid for pid in beam_pids() if pid not in before_beams)
        for pid in leaked:
            try:
                os.kill(pid, signal.SIGKILL)
            except (ProcessLookupError, PermissionError):
                pass

        print("[dumpstack] "
              + ("target still running, killed with SIGKILL (hang confirmed?)"
                 if killed
                 else "target exited on its own with status %s" % rc))
        if leaked:
            print("[dumpstack] WARNING: killed leaked beam.smp process(es): %s"
                  % ", ".join(map(str, leaked)))
        else:
            print("[dumpstack] no beam.smp leaks")

        # Only meaningful when we killed the VM: if it exited on its own
        # (fast run), the samplers simply never finished their window.
        missing = [i for i in range(n_samplers[0]) if i not in summarized]
        if killed and missing:
            print("[dumpstack] note: sampler(s) %s never finished: a "
                  "scheduler may have been lost to a non-preemptable "
                  "native loop, so the processes in their share are "
                  "invisible in the ticks above"
                  % ", ".join(map(str, missing)))
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


if __name__ == "__main__":
    main()
