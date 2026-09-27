#!/usr/bin/env python3
"""Stack-dump a hanging compiler run on the BEAM.

Two complementary samplers run while the CLI executes:

1. In-VM tracers (scripts/stackdump.erl): two processes busy-poll the
   target and sample it every --iters poll iterations (NOT by time:
   erlang:monotonic_time is broken in this Erlang build), logging its
   current function, reduction delta and heap size:
     [#2 tr1] {core@unify,retry_deferred,3} | red+12345678 heap=9011 msq=0
   current_function is the top Erlang frame; a process stuck inside one
   long C call shows the MFA of the function that made the C call.
   The tracers busy-poll, so the period is workload-dependent (~1s at
   the default 300000 iters) and the target runs somewhat slower than
   unsampled.

2. Native sampler (macOS `sample`): for the last --sample-secs of the
   budget, `sample` records native call stacks of all beam threads,
   showing the C function the target is stuck in (GC, make_internal_hash,
   iolist, ...). The full report is saved to --native and a per-thread
   summary is printed at the end.

Reading the result:
  - in-VM: constant MFA + flat heap -> tight loop; growing heap -> blow-up
  - native: 100% in one C function (e.g. make_internal_hash) -> the BEAM
    function below it (JIT frames show as ??? in <unknown binary>) is the
    caller; e.g. erts_maps_put means the hot code builds big maps each
    iteration. JIT-compiled BEAM code has no symbols in `sample` output.

Exit codes: 9 = in-VM tracers halted the VM after --max samples (hang
observed), 0 = command finished on its own, 1 = target crashed,
137 = wall-clock budget expired and the VM was killed.

Examples:
  scripts/stackdump.py -- debug-file --add=prelude lib/prelude/v0.0.1/result.tao
  scripts/stackdump.py -- debug-src '<tao source>' --add=prelude
  scripts/stackdump.py -- test lib/prelude/v0.0.1/result.tao
  # Dump a `gleam test` hang (the Gleam test suite, not the Tao `test` CLI):
  scripts/stackdump.py --test --
"""

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EBIN_ROOT = os.path.join(ROOT, "build", "dev", "erlang")
ERL_SAMPLER = os.path.join(ROOT, "scripts", "stackdump.erl")
MAIN_CALL = "'cli@entrypoint':entrypoint"
TEST_CALL = "compiler_bootstrap_test:main"
SAMPLE_SECS_DEFAULT = 3


def erl_bin(s: str) -> str:
    """Render a Python string as an Erlang binary literal."""
    if all(c.isprintable() and ord(c) < 128 for c in s):
        esc = s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n").replace("\t", "\\t")
        return f'<<"{esc}">>'
    return "<" + ",".join(str(b) for b in s.encode()) + ">"


def build_launcher(tmp: str, cli_args: list[str], test: bool, iters: int,
                   maxn: int, log: str) -> str:
    # The launcher: a compiled beam that starts the tracers on itself, then
    # runs the entrypoint (the main CLI, or the test target for --test).
    # Neither returns on normal paths, so the halt below only covers odd
    # returns. CLI args are embedded as literals: the erl -eval path routes
    # calls with arguments through a broken erlang:apply in this build.
    if test:
        # eunit runs the test functions in anonymous spawned task
        # processes, so the tracers scan for the hottest process.
        target = "scan"
        main_call = f"{TEST_CALL}()"
    else:
        # the launcher runs the whole CLI itself, so it is the target.
        target = "self()"
        bins = ", ".join(erl_bin(a) for a in cli_args)
        main_call = f"{MAIN_CALL}([{bins}])"
    src = f"""-module(sd_run).
-export([go/0]).
go() ->
  stackdump:start(self(), {target}, {iters}, {maxn}, <<"{log}">>),
  {main_call},
  erlang:halt(0).
"""
    path = os.path.join(tmp, "sd_run.erl")
    with open(path, "w") as f:
        f.write(src)
    return path


def ebin_dirs() -> list[str]:
    dirs = []
    for dirpath, dirnames, _ in os.walk(EBIN_ROOT):
        if "ebin" in dirnames and os.path.isdir(os.path.join(dirpath, "ebin")):
            dirs.append(os.path.join(dirpath, "ebin"))
    return sorted(dirs)


def native_summary(path: str) -> None:
    """Print per-thread top frames, skipping idle threads."""
    idle_re = re.compile(r"cond_wait|psynch|__select|semaphore|kevent|read\s*\(")
    thread = None
    frames: list[str] = []
    idle = False
    beamed = False

    def flush() -> None:
        nonlocal thread, frames, idle, beamed
        if thread and not idle and beamed:
            print(thread, file=sys.stderr)
            for line in frames:
                print(line, file=sys.stderr)
        thread, frames, idle, beamed = None, [], False, False

    with open(path) as f:
        for line in f:
            s = line.rstrip("\n")
            if re.match(r"^\s*[0-9]+ Thread_", s):
                flush()
                thread = s
                continue
            if thread is not None and len(frames) < 8:
                frames.append(s)
                if idle_re.search(s):
                    idle = True
                if "(in beam.smp)" in s:
                    beamed = True
    flush()


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--iters", type=int, default=300_000,
                    help="in-VM sample period in poll iterations (default 300000, ~1s of wall "
                         "time; the tracers busy-poll, so the period is workload-dependent - "
                         "lower it for a finer spin rate)")
    ap.add_argument("--max", type=int, default=300,
                    help="halt the VM after N in-VM samples (default 300)")
    ap.add_argument("--budget", type=int, default=40,
                    help="wall-clock limit in seconds, then native-sample and kill (default 40)")
    ap.add_argument("--sample-secs", type=int, default=SAMPLE_SECS_DEFAULT,
                    help="native sampling duration at the end of the budget (default 3)")
    ap.add_argument("--native", default="/tmp/stackdump-native.txt",
                    help="where to save the full native sample report")
    ap.add_argument("--test", action="store_true",
                    help="run the test target entrypoint (gleam test) instead of the main CLI")
    ap.add_argument("--no-build", action="store_true", help="skip `gleam build`")
    ap.add_argument("cli_args", nargs="*",
                    help="CLI args for the program under test (after --)")
    args = ap.parse_args()

    if not args.test and not args.cli_args:
        ap.error("no CLI args after -- (or use --test)")

    os.chdir(ROOT)
    if not args.no_build:
        r = subprocess.run(["gleam", "build"], capture_output=True, text=True)
        if r.returncode != 0:
            print(r.stdout + r.stderr, file=sys.stderr)
            return 1

    tmp = tempfile.mkdtemp(prefix="stackdump.")
    log = os.path.join(tmp, "samples.log")
    erl_err = os.path.join(tmp, "erl.err")

    launcher = build_launcher(tmp, args.cli_args, args.test, args.iters, args.max, log)
    r = subprocess.run(["erlc", "-o", tmp, launcher, ERL_SAMPLER],
                       capture_output=True, text=True)
    if r.returncode != 0:
        print(r.stderr, file=sys.stderr)
        shutil.rmtree(tmp, ignore_errors=True)
        return 1

    # This Erlang build ignores colon-separated -pa lists, so pass one -pa
    # flag per directory, and use absolute paths. -eval only gets the
    # 0-arity sd_run:go/0: calls with args route through a broken
    # erlang:apply in this build.
    pa_args: list[str] = []
    for d in [tmp] + ebin_dirs():
        pa_args += ["-pa", d]

    erl = shutil.which("erl") or "erl"
    cmd = [erl, "-noshell", f"-name", f"sd_{os.getpid()}", *pa_args,
           "-eval", "sd_run:go()"]

    # The VM's stdout (program output, test dots, phase traces) is passed
    # through; the report (in-VM samples, error log, native summary) goes
    # to stderr so both streams stay separate.
    with open(erl_err, "wb") as errf:
        proc = subprocess.Popen(cmd, stderr=errf)

    # If the VM is still alive when the budget expires, native-sample it
    # for --sample-secs and then kill it.
    end = time.monotonic() + args.budget
    sampler: subprocess.Popen | None = None
    native_sampled = False
    while proc.poll() is None and time.monotonic() < end:
        if not native_sampled and end - time.monotonic() <= args.sample_secs:
            native_sampled = True
            if shutil.which("sample"):
                with open(args.native, "wb") as nf:
                    sampler = subprocess.Popen(
                        ["sample", str(proc.pid), str(args.sample_secs)],
                        stdout=nf, stderr=subprocess.DEVNULL)
            else:
                print("stackdump: `sample` not found (macOS only); skipping native sampling",
                      file=sys.stderr)
        time.sleep(0.2)
    if proc.poll() is None:
        proc.kill()
    code = proc.wait()
    if code < 0:  # killed by a signal; use the shell 128+signum convention
        code = 128 + (-code)
    if sampler is not None:
        sampler.wait()

    # Stale crash dumps confuse later runs; check mtime if one reappears.
    for d in [ROOT] + ebin_dirs():
        p = os.path.join(d, "erl_crash.dump")
        if os.path.exists(p):
            os.remove(p)

    print("--- stackdump: in-vm samples ---", file=sys.stderr)
    try:
        with open(log) as f:
            sys.stderr.write(f.read())
    except OSError:
        pass
    with open(erl_err) as f:
        errlog = f.read()
    if errlog.strip():
        print("--- stackdump: erlang error log ---", file=sys.stderr)
        sys.stderr.write(errlog)
    if native_sampled and sampler is not None and os.path.exists(args.native):
        print(f"--- stackdump: native sample ({args.native}) ---", file=sys.stderr)
        try:
            native_summary(args.native)
            print(f"(full report: {args.native})", file=sys.stderr)
        except OSError:
            pass
    if code in (124, 137):
        print(f"stackdump: budget of {args.budget}s expired", file=sys.stderr)

    shutil.rmtree(tmp, ignore_errors=True)
    return code


if __name__ == "__main__":
    sys.exit(main())
