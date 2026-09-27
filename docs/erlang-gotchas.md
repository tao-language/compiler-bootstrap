# Erlang gotchas (homebrew 29.0.6, this machine)

All entries verified with isolated probes. This build is heavily stripped
(missing modules, broken BIFs) and has scheduling/timer pathologies that make
the usual debugging tools unreliable. Prefer external tooling
(`scripts/stackdump.py` uses macOS `sample` plus iteration-count-based in-VM
tracers; see docs/debugging.md) over in-VM introspection.

## Broken / missing BIFs and modules

| Tool | Result |
|---|---|
| `erlang:process_display(Pid, stack)` — all forms | `badarg` (`badopt`) |
| `erlang:trace(Pid, true, [call, return_to])` | returns success, emits **zero** events for a busy loop |
| `erlang:trace(Pid, true, [call], [Mfa])` (arity 4) | `undef` |
| `erlang:trace(Pid, true, ['receive'])` | **works** (atom must be quoted) |
| `dbg:*` | `undef` (module absent) |
| `erlang:trace_info(Pid, [Items])` | `badarg` — use the full-dict form `process_info(Pid)` + `lists:keyfind/3` (NOT `proplists:get_value/2`: it raises on non-tuple entries) |
| `erlang:process_info(Pid, Item)` / `process_info(Pid, [Items])` | **work** (single item and list form both return the usual `{Item, Value}` / list) — an earlier note claimed `badarg`; re-verified 2026-09-27 |
| `erlang:process_info/1` on a timer-blocked process | returns the atom `undefined` (NOT `[]`); `[]` means dead pid; a proper dict for executing / plain-`receive`-blocked processes. Filter with `is_list/1` before touching the result |
| `erlang:flush/0`, `code:module_info/1` | `undef` / `badarg` |
| `erlang:erlang_crashdump/0` | `undef` |
| `erlang:system_info(command_line)`, `os:argv/0`, `code:which_all/1` | `badarg` / `undef` |
| `erl -eval` calling `some@module:fun/...` | routes through a broken `erlang:apply` → `badarg`. Start entry points from a **compiled beam** instead. |
| `erlang:spawn(Fun, Args)` via `erl -eval` | `badarg` — use `spawn(Mod, Fun, Args)` |
| `erl -pa a:b` (colon-separated list) | silently ignored — pass one `-pa` per directory |

Works: full `erlang:process_info(Pid)` dict (incl. `current_function`,
`reductions`, `total_heap_size`, `message_queue_len`), `erlang:monitor/2`,
`erlang:halt/1`, `timer:sleep/1`, `io:format/2`, `proplists`,
`file:open/write/close`, `code:ensure_loaded/1`, `erlang:monitor`/DOWN
messages, `erlang:process_info(Pid, Item)`.

Note: `file:write(Fd, Term)` with a non-list Term returns `{error,badarg}`
**silently** (no crash) — strings/binaries only. And iolists containing
multi-MB terms are **truncated mid-line silently** — keep logged terms small.

Note: `io:format`'s `~b` requires a non-negative integer; booleans are atoms
and raise `badarg` (stock behavior, but easy to hit: use `~p` for `true`/`false`).

## Scheduling and timer pathologies (the big ones)

- **`receive ... after N` timers silently never fire** while a sibling
  process is busy or doing heavy io, for arbitrary N (tested 250ms–1000ms).
  With an idle/sleeping parent the same timers fire on time. Do not build
  periodic tracers on `receive after`.
- **`erlang:monotonic_time/1` (and `system_time`/`os:timestamp`) run at an
  arbitrary rate** — observed at 3% of real time, 1.6× fast, even backwards.
  Nothing time-based works: no `receive after` timers while a sibling is
  busy, no time-based polling. `scripts/stackdump.py` therefore samples by
  *iteration count* (busy-poll recursion counter) and enforces the wall-clock
  budget from Python.
- Even busy-poll tracers **get starved** under some workloads (heavy single
  `io:format` of multi-MB strings, heavy allocation), sometimes after a few
  samples. Treat in-VM sampling as best-effort only.
- A process stuck in a C call (e.g. `make_internal_hash` on a huge key list)
  can freeze every other timer in the VM — the whole VM appears hung with one
  core at 100% and no progress anywhere.

Consequences: to find where a hang is, use `scripts/stackdump.py`, which
native-samples the beam with macOS `sample` (external, immune to all of the
above) and additionally runs best-effort in-VM tracers that sample current
function / reductions / heap by iteration count. It handles both the CLI
(`gleam run -- ...`) and `gleam test` (the eunit task processes are
anonymous, so scan mode reports the hottest process). See
docs/debugging.md.

## Erlang syntax quirks (this erlc)

- Clause separators are `;`. Newline-only clause separation is a syntax error
  ("syntax error before: [") — different from stock OTP, do not "fix" it.
  Two *top-level* clauses of the same function separated by a bare newline
  fail with "function already defined" — add `;` between top-level clauses.
  A trailing `;` after the last expression in a case branch is a syntax error.
- `case`/`if` cannot appear in subexpression position when a branch doesn't
  bind the target variable ("unsafe in case").
- Guard `when N > 0` on a clause can mis-compile ("function already
  defined"); prefer `case N > 0 of ... end` in the body.
- `case` in `erl -eval` expressions fails (`illegal_expr`); evaluate from a
  compiled beam.
- `-module(x)` must match the file basename; `erlc` errors otherwise.
- `end` cannot be used as an atom name in some positions.

## Crash dumps

- Erlang-level fatal errors (e.g. `undef` during boot) **do** write
  `erl_crash.dump`; `kill -SEGV` does **not** (handler stripped).
- The dump's `=proc:<pid>` section has `Current call: Mod:Fun/N` and
  `Program counter: 0x... (Mod:Fun/N + offset)` for every process, but only
  the top frame — no full BEAM stack.
- Stale dumps appear at the repo root and inside ebin dirs after failed
  runs; `rm -f erl_crash.dump` before and after runs and check mtimes.

## Gleam → Erlang naming

Module `cli/entrypoint` → Erlang `'cli@entrypoint'` (beam `cli@entrypoint.beam`).
Gleam `String` = binary: CLI args embedded in launcher beams must be
`<<"...">>` literals. The package main is `'compiler_bootstrap@@main'`;
`pub fn main/0` is not exported. The `gleam test` entry point is
`compiler_bootstrap_test:main/0` (gleeunit; the test beam exports neither
`run/0` nor any `@@main` variant). Compiler-core beams of interest:
`core@unify`, `core@infer`, `core@eval`, `core@quote`, `core@resolve`,
`tao@define`, `tao@compile`, `tao@tests`, `tao@load` — under
`build/dev/erlang/compiler_bootstrap/ebin/`.

## BEAM JIT

Hot functions are JIT-compiled; in `sample` output their frames appear as
`??? (in <unknown binary>) [0x...]`. The C frames below them
(`erts_maps_put`, `make_internal_hash`, `erl_gc_*`, ...) are still
resolvable and usually identify the problem (e.g. "hot code builds huge maps
every iteration").
