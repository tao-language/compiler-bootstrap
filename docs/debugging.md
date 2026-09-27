# Debugging hangs (and other misbehaviour) in compiler-bootstrap

`scripts/stackdump.py` is the primary tool for debugging hangs. It wraps the
target command (the main CLI or the `gleam test` suite) in a launcher beam
that starts two in-VM sampler processes, enforces a wall-clock budget from
Python, and native-samples the BEAM with macOS `sample` near the end of the
budget. Full report goes to **stderr**; the program's own stdout passes
through.

## The two samplers

1. **In-VM tracers** (`scripts/stackdump.erl`). Two processes busy-poll and,
   every `--iters` poll iterations, log one line per tracer:
   ```
   [#42 tr1] {gleam@dict,has_key,2} <0.10.0> | red+38211 heap=86071 msq=0
   ```
   - `current_function` is the top Erlang frame; a process stuck inside one
     long C call shows the MFA of the function that made the C call.
   - `red+DELTA` = reductions since the previous sample (work per period).
   - `heap` = `total_heap_size`.
   - Sampling is by **iteration count, not time**: `erlang:monotonic_time`
     runs at an arbitrary rate in this Erlang build (see
     docs/erlang-gotchas.md), so time-based deadlines never fire.
   - The tracers busy-poll, so they slow the target down (~6× for the test
     suite) and the sample period is load-dependent.
   - **CLI mode** samples the launcher pid directly (it runs the whole CLI).
   - **Test mode** (`--test`): eunit runs test functions in *anonymous*
     spawned task processes, so the tracers scan all VM processes every
     period and report the one with the biggest reduction delta — the
     infinite loop always dominates. The spin is in an eunit task pid like
     `<0.12x.0>`.
2. **Native sampler** (macOS `sample`, last `--sample-secs` of the budget).
   Records native stacks of all beam threads; a per-thread summary is
   printed at the end, the full report is saved to `--native`
   (default `/tmp/stackdump-native.txt`). JIT-compiled BEAM frames show as
   `??? (in <unknown binary>)`; the C frames below them
   (`erts_maps_put`, `make_internal_hash`, `erl_gc_*`, …) identify the
   problem.

## Usage

```sh
# CLI hang (the current repro: prelude result.tao with its tests active)
timeout -k 9 60 scripts/stackdump.py --budget 40 --max 500 \
  -- debug-file --add=prelude lib/prelude/v0.0.1/result.tao

# Any other CLI command
timeout -k 9 60 scripts/stackdump.py -- debug-src '<tao source>' --add=prelude

# gleam test hang (the e2e prelude test in test/tao/examples_test.gleam)
timeout -k 9 120 scripts/stackdump.py --budget 90 --max 600 --no-build --test
```

Flags: `--iters N` (sample period in poll iterations, default 300000; lower
for a finer period), `--max N` (halt the VM after N in-VM samples, default
300), `--budget SECS` (wall-clock limit, default 40), `--sample-secs`
(default 3), `--native PATH`, `--test`, `--no-build` (skip `gleam build`).

## Exit codes

| code | meaning |
|---|---|
| 0 | the command finished on its own (no hang) |
| 9 | the in-VM tracers halted the VM after `--max` samples (hang was being sampled) |
| 1 | the target (launcher) crashed or exited first |
| 137 | wall-clock budget expired; Python killed the VM (after native-sampling it) |

A hang is **confirmed** by: 137 or 9 **plus** (a) in-VM samples showing one
pid with a large, roughly constant `red+` and a **flat** heap, and/or (b)
the native sample showing ~100% of one thread in one C function.

## Reading the results

- **Constant MFA (or a small oscillating set) + constant `red+` + flat heap**
  → tight infinite loop. The MFA is where the top of the loop is; the native
  C frame is where the time actually goes (e.g. 100% `make_internal_hash`
  under `erts_maps_put` = the loop hashes huge terms every iteration).
- **Growing heap** → blow-up (non-terminating construction), not a loop.
- **`msq` (message queue) growing** → a process is stuck producing messages
  nobody consumes.
- In test mode the *spin process pid is stable* across samples
  (e.g. `<0.125.0>` for the whole hang) while other pids churn — follow the
  pid with the big `red+`.

### Practical notes (learned while debugging the `compile.tests` hang)

- In test mode the hang **onset is at a roughly fixed sample number**
  (~490, since both suite progress and sampling are reduction-based), while
  the wall-clock time to reach it varies a lot with machine load (45s–240s+
  observed). Size `--budget` for the slow case; `--max` just needs to
  exceed the onset sample number if you want the VM halted *inside* the
  hang (exit 9) rather than by the budget (exit 137 — also a success).
- The busy-poll tracers slow the suite ~6×; a plain `gleam test` run that
  hangs at ~10s needs a ~60–120s budget under tracers.
- `gleam test` runs *all* tests — the hang is reached via the e2e
  `examples_prelude_test` which loads the prelude with its tests active.
- After every run: `pkill -9 -f beam.smp` (kill strays) and
  `rm -f erl_crash.dump` in the repo root and ebin dirs (stale dumps
  confuse later runs).
- Never run a `gleam run`/`gleam test` that might hang without
  `timeout -k 9 N`.

## The bug currently being debugged

Infinite loop in phase `compile.tests` (type-checking of test statements),
reproduced with `lib/prelude/v0.0.1/result.tao` tests active. Trigger:
**multiple call-sites of an implicitly-quantified function** (even one
implicit param + two tests). Pinned (commented-out) tests:
`test/tao/implicit_args_test.gleam`
(`two_identical_tests_terminate_test`, `two_different_tests_terminate_test`,
`multi_implicit_two_tests_terminate_test`). A related non-hanging crash:
the BAD2 shape crashes the de-Bruijn assert at `src/core/quote.gleam:136`
(index −6). Signature under stackdump: CLI flat heap 86071, test-mode flat
heap 53194, native 100% `make_internal_hash` ← `erts_maps_put`. Full
root-cause analysis with fix suggestions:
docs/compile-tests-hang-analysis.md. Broken-BIF table:
docs/erlang-gotchas.md.
