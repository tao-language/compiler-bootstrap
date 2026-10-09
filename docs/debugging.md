# Debugging the Tao/Core compiler

A guide to debugging this compiler: hangs, slow type-checking, and "what value
did a hole get solved with" questions. Pick the tool by what you need:

| you want to... | use |
|---|---|
| Bisection: which phase / which hole / which value, while the compile still **finishes** (seconds) | `gleam run -- debug-src "<source>" --add=prelude` — add `--trace-solves` for the live hole-solve trace |
| Debug a single Tao expression instead of a whole module | `gleam run -- debug-expr "<expr>" --add=prelude` |
| Debug a whole `.tao` module exactly as it is loaded | `gleam run -- debug-file <path> --add=prelude` |
| Debug a raw Core term | `gleam run -- debug-core "<term>"` |
| Locate a **hang** — the run no longer terminates, so the pipeline tools above can't return | `scripts/dumpstack.py` (native-level BEAM stack profiler) |
| Inspect a pathological value that `format.value` crashes on | `echo`-bracketing + a one-level "sketch" printer (see the *Tracing pathological values* section) |

Two tools cover most work. **`debug-src --trace-solves`** is the workhorse
while the program still terminates: it runs the full pipeline on inline source
with per-phase timing, a full hole-substitution dump, and a live trace of every
hole solve — you can watch exactly which hole gets solved with which value (see
the *The `debug-src` pipeline tools* section). **`dumpstack.py`** takes over
once it stops terminating (below): it samples native BEAM stacks of the hung
process. A common session flow is to bisect with `debug-src` until the run gets
slow or hangs, then hand off to `dumpstack.py`.

## dumpstack.py (the hang tool)

`scripts/dumpstack.py` is a **sampling stack profiler** for the BEAM: it builds
the project, launches the same VM that `gleam run` / `gleam test` would (with
the compiled beams directly), injects three in-VM sampler processes at boot,
and prints stack traces of all busy processes to stdout as it samples. After
the sample window the VM is terminated with SIGKILL (mandatory for Erlang —
anything else leaks a `beam.smp` process).

**IMPORTANT**: Do not truncate the dumpstack output the first time you run it, it can be long but it's all important. You can truncate it in later runs once you know what you're looking for.

## Usage

```sh
python scripts/dumpstack.py [--delay=S] [--duration=S] [--sampling-rate=N] [--test] [--no-native] -- [cli-args...]
```

| flag | default | meaning |
|---|---|---|
| `--delay=S` | `0` | wait S seconds after VM start before sampling begins |
| `--duration=S` | `2` | sample for S seconds |
| `--sampling-rate=N` | `30` | samples per second (higher = finer, slower, more overhead) |
| `--test` | — | run the test suite (`compiler_bootstrap_test`) instead of `gleam run` |
| `--no-native` | off | skip the macOS `sample(8)` native stack dump taken right before the SIGKILL. On by default **only when the target hangs** (adds ~2 s); never runs when the target exits on its own.

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
t=0.14s [s1] (sample timed out: a process in this share blocks process_info, probably stuck in native code)
sampler[2]: 61 samples (60 identical ticks suppressed), top frames across 0 non-idle stacks
sampler[1]: 62 samples (0 identical ticks suppressed), top frames across 18 non-idle stacks
    10  prim_file/read_file/1
     4  code_server/handle_loader/4
sampler[1]: last seen per pid (most recent first):
  <0.95.0>  t=0.12s  depth=8  gleam@list/-key_find/2-anonymous-0-/2 <- gleam@list/find_map/2 <- tao@define/type_stmt_data/5 <- tao@define/type_stmt/5
  <0.50.0>  t=0.12s  depth=7  prim_file/read_file/1 <- erl_prim_loader/read_file/1 <- ...
sampler[0]: 96 samples (88 identical ticks suppressed), top frames across 2 non-idle stacks
sampler[0]: last seen per pid (most recent first):
  <0.0.0>  t=2.00s  depth=1  init/boot_loop/2
[dumpstack] native (C-level) sample of pid 79259, last 2s before kill:
  erts_sched_1: + 1700 ???  (in <unknown binary>)  [0x10a072d04]
  erts_sched_2: + 1700 ???  (in <unknown binary>)  [0x109d029fc]
  ... (one line per thread; the 12 scheduler threads are all pegged) ...
  make_internal_hash  (in beam.smp)        1700
  read  (in libsystem_kernel.dylib)        1700
[dumpstack] full native report: /var/folders/.../T/dumpstack-native-XXXX.txt
[dumpstack] target still running, killed with SIGKILL (hang confirmed?)
[dumpstack] no beam.smp leaks
```

The native `sample(8)` section is the C-level view: every `erts_sched_N`
thread parked in `??? (in <unknown binary>)` is a scheduler stuck in
JIT-compiled (unsymbolicated) code, and the `make_internal_hash (in
beam.smp)` line in the "Sort by top of stack" summary names the C function
the stuck Erlang loop compiled down to. This is what the in-VM sampler
cannot see (its own `process_info` blocks on the stuck process). Use
`--no-native` to skip it; the full report is always saved to the named file.

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
- **`sampler[N]: last seen per pid (most recent first):`** — one line per
  busy pid the sampler ever saw, in the form
  `<pid>  t=<lastT>s  depth=D  MFA <- MFA <- MFA <- MFA`, sorted so the most
  recently active pid is first. Pids are never removed, so a pid that goes
  silent or stuck keeps its *last known* stack here. This is the fastest way
  to the answer: **the top entry of the share that printed the timeout line
  is the stuck pid's last readable stack.** (Each sampler only covers its own
  pid share, so the three sections together cover all pids.)
- **`[dumpstack] native (C-level) sample of pid ...`** — the `sample(8)`
  report taken in the ~2 s before the SIGKILL (hang path only, on by
  default). One line per OS thread: the top native frame. A scheduler thread
  parked in `??? (in <unknown binary>)` is stuck in JIT-compiled code;
  the `Sort by top of stack` lines that follow name the C function the stuck
  loop compiled down to (e.g. `make_internal_hash (in beam.smp)`). Skip with
  `--no-native`. The full report is saved to the printed path.
- **`no beam.smp leaks`** / `WARNING: killed leaked ...` — the post-run
  sweep. If you ever see a leaked `beam.smp` consuming memory, kill it:
  `pkill -9 -f beam.smp`.

## Interpreting the native sample

The `sample(8)` section (the C-level view, "Sort by top of stack") names the C
function the stuck Erlang loop compiled down to. In this compiler the recurring
signatures:

- **`make_internal_hash (in beam.smp)`** — the loop is computing a **term
  hash**, i.e. doing a structural `==` / `=/=` (or a `map`/`set`/`dict` /
  `list.key_find` over *values*) on a **large or growing term**. This is the
  most common "hang" in this codebase and it is **not a recursion bug** — it is
  one or many expensive comparisons. Audit the hot path for `==` / `list.contains`
  / `list.key_find` over a `List` of `Value`s, or `==` on a `TypeDef` (the
  `tdef1 == tdef2` case in `unify`). A term built up by repeated `eval` of a
  cyclic module record gets larger every round, so the hash grows too — see the
  *Common hang signatures* section.
- **`make_external_term` / `erlang_term_to_binary`** — serializing a huge term
  (e.g. `format.value` / `quote` on a pathological value).
- **`erlang_gc` / `erlang_small_alloc`** — allocation churn; the loop is
  building terms faster than expected (usually a growing list or map).
- **`??? (in <unknown binary>)` with no named C function** — JIT-compiled
  Erlang with no symbol; fall back to the in-VM sampler's last tick line for
  that pid to name the Gleam frame.

The native frame tells you the *class* of the stuck op (hashing vs serializing
vs looping), not *which* Gleam function — pair it with the in-VM sampler's last
readable tick line (the `MFA <- MFA` stack) to name the Gleam frame.

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
stuck its stack is unreadable (see timeout line). Two mechanisms sharpen it:

- **Burst on transition (built in, no flag).** When a previously-idle pid
  suddenly appears busy, that sampler automatically raises its rate ~6× for
  200 ms (e.g. 30 Hz → ~180 Hz) to maximize the chance of landing a tick
  while the stack is still readable. You'll see a short run of closely-spaced
  `t=` values after a transition. No action needed.
- **Higher base rate.** `--sampling-rate=100` raises the steady-state rate
  too. The cost is more CPU (the overhead of sampling is expected and
documented, but 100 Hz is noticeably heavier than 30 Hz).

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
4. After `delay + duration` (plus a 2 s margin for the summaries), if the
   target is *still running* (the hang path) the script runs macOS
   `sample(8)` on the VM for ~2 s to capture the native C-level stacks (this
   reads through mach task ports, so it works even though `process_info`
   blocks on the stuck process), then kills the process group with
   **SIGKILL**. If the target exited on its own, no `sample(8)` is run. Any
   `beam.smp` that appeared during the run is killed and reported.

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
- **Fast runs (program exits before the window ends) produce no summary.**
  When the program finishes and exits on its own before `--duration` elapses,
  `init:stop()` begins tearing the VM down and `init`'s `kill_all_pids`
  reaps the samplers (observed at ~0.75 s) well before the window deadline,
  so the end-of-window summaries (histogram + last-seen) are never written.
  This is expected, not a bug — the tick lines up to the program's exit are
  still valid. To get summaries from a fast run, use a `--duration` that ends
  *before* the program exits. (See the "Known limitation — fast case" block
  in `scripts/samplestack.erl` for the full investigation notes, including
  the suspected JIT/C-wedge cause of the early sampler silence.)

## Housekeeping

- Never run a `gleam run` / `gleam test` that might hang without
  `timeout -k 9 N` (or via this script, which handles it).
- After a run there should be no stray `beam.smp` (the script reports).
  Gleam's own compiler server (a few MB, spawned by `gleam build`) is
  persistent by design and is *not* a leak.
- If `erl_crash.dump` appears in the repo root (VM boot failure), delete it
  before the next run: `rm -f erl_crash.dump`.

## The `debug-src` pipeline tools

`debug-src` runs **inline source** through the full pipeline (the prelude
compiled in, like a real module) — no writing `/tmp/*.tao` files. It is by far
the fastest way to bisection a type-checking / unification problem: it runs in
well under a second and prints a lot. `debug-expr` is the same for a single
expression, `debug-file` for a whole loaded module, `debug-core` for a raw Core
term.

```sh
# From a file (the B/A/C hang shapes from docs/plan.md):
gleam run -- debug-src "$(cat /tmp/taoscratch/B_two_params_two_tests.tao)" --add=prelude
# Inline:
gleam run -- debug-src 'type Rst(a, e) { | OkX(a) | ErrX(e) } ...' --add=prelude --trace-solves
```

`--add=prelude` (or `--add=prelude:0.0.1`) loads the prelude package; the hang
shapes only reproduce **with** it. `--add` is repeatable; `--path` adds extra
package search dirs (default `lib`).

Output, top to bottom:
- `source: "..." packages: [#("prelude", None)]` — **confirm the prelude
  actually loaded** (`packages:` non-empty); an empty `packages:` means you are
  not debugging the real repro.
- `define.types: Nms holes=M`, `define.values: Nms holes=M` — per-phase timing
  + running hole counter.
- `// subst=N holes=M deferred=K` — the substitution-table size and the
  **deferred-constraint queue** at the end of the module compile. A large or
  *growing* `deferred=` across retries signals undecidable constraints.
- One line per solved hole: `h131 (envlen=19): #Rst({...})` — the hole's
  **solution, displayed against its captured solve env** (so `$N` indices are
  valid). This is the single most useful line for "what did hole 131 get solved
  with?" A solution that is a whole **module record** (a `Rcd` with many
  fields) on a *type-parameter* hole is the corruption signature from
  `docs/plan.md`.
- `resolve.context: Nms`, any build errors, then the test re-check
  (`compile.tests`) and its `term:` / `✓` / `✗` results.

**`--trace-solves`** interleaves, live, three kinds of event as unification
runs (including inside `compile.tests`, where the B-shape corruption happens):
- `SOLVE h131 <- Rcd[Bool_and_or]` — hole 131 just got solved with a value of
  that sketch (`Rcd[...]` = a record, `LitT`, `Ctr`, `For`, ...; `""`-named
  fields print as `*`). A `SOLVE hN <- Rcd[<module>]` on a tdef value-hole is
  the corruption.
- `MERGE h131 value=... existing=...` — a hole met twice (defensive merge).
- `BUDGET used=N/limit` — how much of the unification work budget one top-level
  `unify` consumed. `used` near (or above) the limit means that unification hit
  the rewrite budget (see *Tuning a threshold*).

Because `debug-src` *finishes* (it is bounded), you can grep its output — unlike
a hang, which you can only sample. Prefer it until the run is slow enough to
need `dumpstack.py`.

## Common hang signatures in this compiler

The recurring shape of a hang here: a **type-parameter value-hole gets solved
with a module record** (a `Rcd` carrying every definition of a module, with
captured environments that reference the record itself). Unifying against such a
record re-expands it forever — `unify`/`unify_rcd`/`eval` descend, `eval`
re-introduces the module record at a deeper level, and the term grows without
bound. Two distinct failure modes:

- **Slow drain (not a tight loop).** Each step re-hashes an ever-larger term,
  so a *bounded* amount of work takes many seconds. `dumpstack`'s native sample
  shows `make_internal_hash`; the budget value oscillates in a narrow band or
  drains very slowly. This is what the `result.tao`/B-shape hang was.
- **Genuine non-termination.** A mutual recursion (`unify` ↔ `unify_rcd` ↔
  `unify_gadt` ↔ `eval`) with no step budget at all — the budget value stays
  constant (or the op is non-budgeted) while the step count climbs.

**Safety nets that turn these into errors instead of hangs** (all in
`src/core/`, added for the `result.tao` bug — see `docs/plan.md`):
- **Unification work budget** — `unify_budget_limit` in `core/unify.gleam`. A
  single top-level `unify`/`unify_rcd` carries a work counter in
  `Context.budget`; past the limit it raises `UnificationNotTerminating`
  instead of recursing.
- **Occurs-check depth bound** — `occurs_depth_limit` in `core/occurs.gleam`;
  a self-referential solution deepens the check one level per `eval` round, so
  the bound returns `True` (→ `InfiniteType`) instead of looping.
- **Deferred-queue cap** — `deferred_queue_limit` in `core/unify.gleam`;
  a pathological type re-defers forever, so the cap bounds the queue.

If you raise any of these to fix a false positive, re-run the slowest *legit*
input *and* the B-shape hang repro (`scripts/shape_matrix.sh`) — the two bounds
are in tension (see *Tuning a threshold*).

## Tracing pathological values

`format.value` (and `format.term`) can **crash** on pathological values — the
B-shape corruption produced values with stale `NVar` de Bruijn levels, and
`format.value` → `quote_neut_rec` hit `assert index >= 0`. So "just print the
value" is not always possible. Techniques that survive:

- **One-level "sketch" printer.** A cycle-safe printer that names only the top
  constructor and never descends (the `solve_sketch` fn in `core/unify.gleam`
  is the reference: `Rcd` → `Rcd[field_names]`, neutrals → `NVar`/`NHole`/
  `NApp`/...). Use it to *label* values in a trace without re-triggering the
  descent.
- **`echo`-bracketing.** Wrap the suspect op with entry/done markers to build a
  timeline of what runs before the hang, e.g.
  `let _ = echo "STEP budget=" <> int.to_string(ctx.budget)`. `echo` **returns
  the echoed value** and prints two lines (value + dimmed source location), so
  grep for the quoted value. See *Gleam instrumentation gotchas*.
- **Bounded inspectors.** To answer "does hole N's solution mention itself"
  without looping, walk the solution with an explicit depth bound and a `seen`
  set of hole ids (the `unwrap_seen` pattern in `core/unwrap.gleam`), and report
  `True`/`False` at the bound rather than recursing forever.

## Tuning a threshold (budget, depth cap, ...)

When a fix is "add a budget/cap that errors instead of hangs," the value is a
knife-edge between two regimes:
- **Too low** → legitimate unifications error (false positive). Measure the
  *max* steps a legit unification needs — and measure it on the **slowest legit
  input** (here, `check lib/prelude/v0.0.1` over the whole multi-module dir, not
  a single file; the dir needs more steps than any one file).
- **Too high** → a pathological descent reaches the region where each step is
  expensive (growing-term hash) before the budget drains, so it hangs instead
  of erroring. Measure the **hang onset** from above (raise the limit until the
  repro hangs; the onset is just below that).

Pick a value with margin on **both** sides. In this compiler the two are close
enough to matter: the prelude dir needs ~155 steps, the B-shape hang onset is
~350, and `unify_budget_limit` was set to 250. When in doubt, bias toward the
hang side (a false-positive error is recoverable; a hang is not).

## Gleam instrumentation gotchas

Tracing is done with ad-hoc `echo` in the source (remove before committing). The
traps, all hit in the sessions that fixed the `result.tao` bug:

- **`echo` is an expression that returns its value.** As a statement, bind it:
  `let _ = echo "..."`. Inside a `case` branch with a mixed return type, wrap
  the branch in a block that ends in the real value.
- **No semicolons.** A block is newline-separated; `{ let _ = echo "..."; Nil }`
  is a syntax error — use a newline.
- **A `case` used only for side effects** needs each branch to produce the
  enclosing expression's type; the usual form is
  `case cond { True -> { let _ = echo "..."; Nil } False -> Nil }` (with the
  inner newline, not a semicolon).
- **No parenthesized subexpressions** like `1 * (2 + 3)` — add a `let`.
- **Qualified stdlib calls that don't exist** (e.g. `gleam/int.to_string` is
  not a thing) — import the module (`import gleam/int`) and call `int.to_string`.
- **`panic as "a" <> b` parses as `(panic as "a") <> b`** — a type error.
  Parenthesize: `panic as ("a" <> b)`.
- **Line numbers in crash traces don't always match the source** — the
  `result.tao` display crash was reported at `error.gleam:88` but the real
  `assert` was in `quote.gleam` via `format.value`. Trust the *innermost* frame.
- **`@external(erlang, "erlang", "system_time") fn now_ns() -> Int`** is the
  cheap way to time a block (`let t0 = now_ns() ... now_ns() - t0`); use it to
  find which op is slow before assuming it's the recursion.

## Build environment gotchas

- **`build/` holds the compiled Erlang deps, not just project output.** Never
  `rm -rf build` casually: a from-scratch rebuild re-compiles the rebar3 deps
  (via `gflambe → eflambe → meck`), and **meck 0.9.2 fails under OTP 27+** —
  its `prod` profile sets `warnings_as_errors` and OTP 27+ deprecates the old
  `catch` expression. After any clean build, run `scripts/fix-meck.sh` (adds
  `nowarn_deprecated_catch` to the extracted `build/packages/meck/rebar.config`),
  then `gleam build` again.
- **`scripts/warnings.sh`** prints a categorized table of all build warnings
  (kind + location + per-kind counts) — use it to track the `todo`-reduction
  work.
