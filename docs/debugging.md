# Debugging hangs (and other misbehaviour) in compiler-bootstrap

`scripts/dumpstack.py` is the primary tool for debugging hangs. It is a
**sampling stack profiler** for the BEAM: it builds the project, launches the
same VM that `gleam run` / `gleam test` would (with the compiled beams
directly), injects three in-VM sampler processes at boot, and prints stack
traces of all busy processes to stdout as it samples. After the sample window
the VM is terminated with SIGKILL (mandatory for Erlang — anything else
leaks a `beam.smp` process).

## Usage

```sh
python scripts/dumpstack.py [--delay=S] [--duration=S] [--sampling-rate=N] [--test] -- [cli-args...]
```

| flag | default | meaning |
|---|---|---|
| `--delay=S` | `0` | wait S seconds after VM start before sampling begins |
| `--duration=S` | `2` | sample for S seconds |
| `--sampling-rate=N` | `30` | samples per second (higher = finer, slower, more overhead) |
| `--test` | — | run the test suite (`compiler_bootstrap_test`) instead of `gleam run` |

Everything after `--` is passed to the program exactly as `gleam run -- ...`
would pass it.

```sh
# The current hang repro (result.tao e2e test)
timeout -k 9 20 python scripts/dumpstack.py -- test lib/prelude/v0.0.1/result.tao

# A command that works — you should see the test output, exit status 0
timeout -k 9 15 python scripts/dumpstack.py -- test lib/prelude/v0.0.1/option.tao

# The whole test suite (the result.tao e2e test hangs it)
timeout -k 9 20 python scripts/dumpstack.py --duration=3 --test

# The hang starts after ~1s of work: skip the startup phase
timeout -k 9 20 python scripts/dumpstack.py --delay=1 --duration=3 -- test lib/prelude/v0.0.1/result.tao
```

Always keep the `timeout -k 9 N` wrapper: it protects against the script
itself misbehaving. The script already kills the VM and sweeps for stray
`beam.smp` processes, and prints a leak report at the end.

Exit code is `0` whenever the tool itself completed (whether or not the
target hung) and `1` on tool errors (build failure, bad flags, ...). The
hang verdict comes from the printed line `target still running, killed with
SIGKILL (hang confirmed?)`, not from the exit code.

## Example output (the result.tao hang)

```
[dumpstack] building project...
[dumpstack] running module compiler_bootstrap with: test lib/prelude/v0.0.1/result.tao
sampler: sampling for 2.00 s at 30.30 Hz (delay 0.00 s) [sampler 0 of 3]
sampler: sampling for 2.00 s at 30.30 Hz (delay 0.00 s) [sampler 1 of 3]
sampler: sampling for 2.00 s at 30.30 Hz (delay 0.00 s) [sampler 2 of 3]
t=0.1s [s0] <0.0.0> (main) depth=1  init/boot_loop/2
t=0.1s [s1] <0.50.0> depth=4  code_server/handle_loader/4 <- code_server/run_loader/4 <- ...
t=0.11s [s1] <0.50.0> depth=7  prim_file/read_file/1 <- erl_prim_loader/read_file/1 <- ...
t=0.17s [s1] (sample timed out: a process in this share blocks process_info, probably stuck in native code)
sampler[0]: 61 samples (60 identical ticks suppressed), top frames across 0 non-idle stacks
sampler[2]: 61 samples (60 identical ticks suppressed), top frames across 0 non-idle stacks
sampler[1]: 41 samples (0 identical ticks suppressed), top frames across 3 non-idle stacks
     3  code_server/handle_loader/4
[dumpstack] target still running, killed with SIGKILL (hang confirmed?)
[dumpstack] no beam.smp leaks
```

In a `--test` run the transition can be caught on a program stack instead:

```
t=1.47s [s1] <0.111.0> depth=8  gleam@list/-key_find/2-anonymous-0-/2 <- gleam@list/find_map/2 <- core@unwrap/unwrap_neut/4 <- core@unify/unify/3
t=1.66s [s1] (sample timed out: a process in this share blocks process_info, probably stuck in native code)
```

## Reading the output

- **Tick line** `t=<s>s [sN] <pid> (main)? depth=D  MFA <- MFA <- MFA <- MFA`
  — the top 4 stack frames of a busy process, top frame first. `t=` is
  relative to the *start of sampling* (i.e. after `--delay`). `(main)` marks
  the VM's main process `<0.0.0>` (the program runs in a process it spawns;
  main just sits in `init/boot_loop` while boot is in progress).
- **`[s0..s2]`** — which of the three samplers reported the line. Pids are
  partitioned round-robin over the samplers, so lines from different samplers
  can appear out of chronological order.
- **`(all processes idle)`** — that sampler's share contains only
  message-waiting processes at that tick.
- **Lines are deduped**: a tick is printed only when the set of busy stacks
  *changed*. The `(N identical ticks suppressed)` count in each summary says
  how many ticks looked the same. So a steady-state infinite loop shows as
  one line plus a big suppressed count — that is the expected shape.
- **`(sample timed out: ...)`** — one of the processes in that share is
  stuck in a way that makes `process_info` block (a non-preemptable native
  loop holding the process lock). The sampler survives and skips that share
  for the rest of the window. **The last tick line you saw for that pid is
  the closest you can get to the hang point.**
- **`sampler[N]: ... top frames`** — per-sampler histogram of top frames
  across the window. If a sampler's summary is missing, print at the end
  flags it: that sampler's scheduler was probably lost to a non-preemptable
  native loop, and the pids in its share are invisible.
- **`no beam.smp leaks`** / `WARNING: killed leaked ...` — the post-run
  sweep. If you ever see a leaked `beam.smp` consuming memory, kill it:
  `pkill -9 -f beam.smp`.

## Workflows

### Reproduce and locate a hang

Run the repro with the defaults. Read the tick lines top to bottom: the
program's work appears as a pid (stable across ticks) walking through
compiler modules (`tao@parse`, `core@unify`, `code_server`, ...). The hang
point is **the last stack that pid shows before it goes silent or its share
prints the timeout line**. For the result.tao repro that last readable
frame has been `core@unify/unify/3` (via `core@unwrap/unwrap_neut/4`).

### The hang starts later in the run

Use `--delay` to skip startup and the phases you already understand, and
`--duration` to widen the window. Example: the suite reaches the hang after
~1s: `python scripts/dumpstack.py --delay=1 --duration=3 --test`.

### Catch the transition into the stuck state

The busy→stuck transition can happen within ~50 ms, and once the process is
stuck its stack is unreadable (see timeout line). A higher
`--sampling-rate` (e.g. `--sampling-rate=100`) increases the odds of landing
a tick inside the short window where the stack is still readable. The cost
is more CPU (the overhead of sampling is expected and documented, but 100 Hz
is noticeably heavier than 30 Hz).

### Profile a slow (but terminating) run

Runs that finish on their own work the same way: the window is simply cut
short by the program's exit (`target exited on its own with status N`). Use
a `--duration` covering the slow phase and read the per-sampler top-frames
histograms to see where the time went.

## What the tool does under the hood (short)

1. `gleam build`, then compile `scripts/samplestack.erl` and a one-line
   wrapper that calls `<name>@@main:run(<module>)` (the same entry point
   `gleam run` uses; `<name>_test` for `--test`).
2. Launch `erl -smp -hmax <16 GiB in words> -pa <ebins> -s samplestack start
   -s dumpstack_main start -noshell -- <args>`. The `-s` modules run in
   command-line order during boot, so the samplers start before the program.
3. Samplers write to a log file (one flushed line at a time, so everything
   survives the final SIGKILL); the script tails it to stdout alongside the
   program's own stdout.
4. After `delay + duration` (plus a 2 s margin for the summaries), the
   process group is killed with **SIGKILL**, and any `beam.smp` that
   appeared during the run is killed and reported.

Design constraints worth knowing:

- **Three samplers, not one.** A process stuck in a non-preemptable native
  loop (JIT-compiled code or a NIF) loses its scheduler forever, and
  `process_info` on that process blocks. Redundant samplers with disjoint pid
  shares plus a per-tick timeout mean at least some samplers always survive
  and report, and a pathological process can't freeze the tool.
- **`+hmax` (16 GiB per process).** The hang grows a map without bound;
  without the cap the VM can exhaust the machine's memory (a ~90 GB
  `beam.smp` was observed). With the cap, the runaway process dies of
  `heap_limit` instead. A legitimate process genuinely needing > 16 GiB of
  heap would be killed too — change `HEAP_CAP_WORDS` in `scripts/dumpstack.py`.
- **Sampling overhead is real and expected**: each sampler pegs one core for
  the window (busy-wait, deliberately not `timer:sleep` — timers were
  observed to stop firing during the real hang), plus the per-tick
  `process_info` sweeps.
- **Waiting processes are invisible** (except main), since a hung *loop* is
  a busy process. A process blocked in a NIF shows up via its share's
  timeout line rather than a stack.

## Housekeeping

- Never run a `gleam run` / `gleam test` that might hang without
  `timeout -k 9 N` (or via this script, which handles it).
- After a run there should be no stray `beam.smp` (the script reports).
  Gleam's own compiler server (a few MB, spawned by `gleam build`) is
  persistent by design and is *not* a leak.
- If `erl_crash.dump` appears in the repo root (VM boot failure), delete it
  before the next run: `rm -f erl_crash.dump`.
