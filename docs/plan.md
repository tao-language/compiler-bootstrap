# Plan: principled module loading, imports, and debug traces

> **TRANSIENT FILE — do not commit.** This is a working plan for a rapidly
> evolving WIP. Delete it once every task below is done and verified.
> Re-derive the "confirmed/suspected" sections if the code has moved on.

---

## 0. Background (read this first)

Tao compiles to Core; types are values. A **library/package** is a directory
under `lib/` (e.g. `lib/prelude/v0.0.1/`), a **version** is a subdirectory, and
a **module** is a `.tao` file. Module names are strings that always start with
`/`.

The high-level questions this plan addresses:

1. Can a library import modules **within itself** and from **other
   dependencies**? (Yes — see §1, but the real CLI can only see the prelude.)
2. Is the current prelude inclusion **sound and principled**? (Resolution is
   sound; naming/loading is ad-hoc.)
3. Should **versions be part of the path**? (Keep them in the *file path*; they
   are *not* the root cause of the de-dup pain.)

### The mechanism (how it works today)

- **Import resolution** is generic and sound: `declare.imports`
  (`src/tao/declare.gleam`) looks up an `import path *`'s `path` in the loaded
  module list and flattens the target's public names into the importer. No
  prelude special-casing here.
- **Import paths** are normalized to start with `/` in the parser
  (`src/tao/parse.gleam:import_path`), so `import prelude/bool` → `/prelude/bool`.
- **Loading** assigns module names via **four inconsistent code paths** (this is
  the ad-hoc part):

  | Path | Function | Name produced for `lib/prelude/v0.0.1/bool.tao` |
  |---|---|---|
  | check/run/test | `common.load_modules` | `/lib/prelude/v0.0.1/bool` |
  | `debug-file --root` | `load.directory` | `/bool` |
  | package load | `load.package` | `/prelude/bool` |
  | `debug-file` target | `load.module` | `/lib/prelude/v0.0.1/bool` |

- **Implicit prelude import** (`load.implicit_prelude_imports`): an AST rewrite
  that appends `import <prelude-module> *` (all sharing alias `/__prelude__`) to
  every non-prelude module, making `+`, `Bool`, `Option`, … global.
- **Prelude de-dup** (`common.prelude_copies` + `prelude_package_name` + the
  filter in `common.compile`): replaces a prelude file loaded *by path* with its
  *package* copy, and drops the duplicate. Hardcodes the `lib/prelude/` prefix.

### Key insights

- **Module identity is version-independent** (`/prelude/bool`); **file layout is
  versioned** (`lib/prelude/v0.0.1/bool.tao`). This split is *correct* (matches
  Go/Rust/Nix: version is a build-time resolution concern, not part of the
  import path). **Keep the version in the file path.**
- The de-dup pain comes from **bypassing package resolution** (raw-path naming),
  **not** from the version being in the path. If loading were uniform
  (always `/package/<relpath>`, version resolved+stripped), there would be no
  mismatch and no `prelude_copies`.
- The **import resolver is fine**; the **naming/loading layer** is the thing to
  fix. Unifying naming + driving loading from a dependency manifest deletes the
  prelude-specific de-dup and makes library imports work for `check`/`run`/`test`.
- The **prelude is special-cased by string name in 3 places**
  (`common.with_prelude`, `load.implicit_prelude_imports`,
  `common.prelude_copies`/`prelude_package_name`). It should just be an
  always-present dependency.

### Confirmed (measured)

- Intra-package import resolves: `foo/b.tao` `import foo/a` →
  `/foo/b : a → import /foo/a`.
- Cross-package import resolves: `bar/c.tao` `import foo/a` →
  `/bar/c : a → import /foo/a`. (Both via `debug-expr --add=foo --add=bar`.)
- `tao check <a package file that imports a non-prelude package>` **crashes**
  with `runtime error: todo — "error: module not found"` (only the prelude is
  loaded as a package by `common.load`).
- `tao check lib/prelude/v0.0.1/bool.tao` exits 0 (the de-dup works).
- With **two** prelude version dirs present, `load.find_version` picks the
  newest and the module is still named `/prelude/bool` (version-independent).
  Only one version is loaded (newest-wins).
- `debug-file --root=lib/prelude/v0.0.1 lib/prelude/v0.0.1/bool.tao` loads the
  **same file three times**: `/lib/prelude/v0.0.1/bool`, `/bool`,
  `/prelude/bool`. **No de-dup** on this path (only `common.load` has it).
- `bool`, `option`, and `result` **all export `_or`**; the implicit import
  flattens all three into every module's global scope.
- ~~`src/tao/declare.gleam:77-80` has debug leftovers: `echo path`, `echo …`,
  `todo as "error: module not found"` — a missing import is a **crash**, not a
  reported error.~~ **Fixed in Task 1:** now produces an accumulated
  `SyntaxError` instead of crashing.
- `debug-expr`'s `holes_summary` (`src/cli/debug_expr.gleam`) hits an assert in
  `core/quote`→`core/format.value` when formatting some hole values (unrelated
  to imports; obscures `debug-expr` output).
- Disabling `prelude_copies` (probe) still let `check` on prelude files pass —
  the de-dup is a **cleanup**, not a strict correctness requirement in the simple
  cases.
- `check --trace=modules` on a prelude file shows the module list and import
  edges (explicit `bool`/`option` aliases within the prelude). On a non-prelude
  file, the implicit `/__prelude__` edges to all 8 prelude modules are visible.

### Suspected (not directly measured)

- Which `_or` wins the global collision is **filesystem directory-listing order**
  dependent (`fs.list_recursive` order → `implicit_prelude_imports` order). Not
  measured which of bool/option/result wins; masked in practice because `_or` is
  only reached via the type-dispatching `or` overload.
- **Multi-version coexistence** is unsupported: inferred from `find_version`
  picking a single version; not tested with two versions *simultaneously used* by
  different importers.
- `ImportSome` name resolution at desugar time relies on **module records being
  bound by their path name** (`src/tao/desugar.gleam`); inferred, not traced
  end-to-end.
- Whether `check`/`run`/`test` would load a full dependency closure correctly —
  not implemented yet, so not measured.

### Key file map

| File | Role |
|---|---|
| `src/tao/load.gleam` | `module`, `module_list`, `directory`, `package`, `package_list`, `find_version`, `implicit_prelude_imports`, `file` |
| `src/cli/common.gleam` | `with_prelude`, `load`, `prelude_copies`, `prelude_package_name`, `compile`, `expand_paths`, `normalize` |
| `src/tao/declare.gleam` | `modules`, `module_defs`, `statement`, `imports`, `exports`, `is_public_name` |
| `src/tao/compile.gleam` | `modules` (the pipeline: declare→define×2→resolve), `tests` |
| `src/tao/desugar.gleam` | `module`, `expr`, `statement` (import → module-record field access) |
| `src/tao/parse.gleam` | `import_`, `import_path`, `import_alias`, `import_name` |
| `src/cli/entrypoint.gleam` | CLI arg parsing for all commands |
| `src/cli/{check,run,run_tests,debug_expr,debug_file,debug_src}.gleam` | the commands |
| `src/core/context.gleam` | `Context` — has the `trace_solves: Bool` pattern to follow |
| `lib/prelude/v0.0.1/` | the prelude (bool, option, result, operators/*) |

### Gotchas (Gleam / workflow)

- `gleam test` has **no `--filter`**; it runs all tests.
- No `if`/`else` (match on `True`/`False`), no loops (recursion), no `Any`.
- **No parenthesized subexpressions** like `1 * (2 + 3)` — introduce a `let`.
- Stdlib is thin; before using a function, prove it with a one-liner (drop a
  scratch `src/apitest.gleam`, build, delete).
- `echo #("label", value)` to instrument.
- **`timeout -k 9 N`** on every `gleam run`/`gleam test` (a hung BEAM ignores
  SIGTERM). `gleam run` < 1s → timeout 2; `gleam build`/`gleam test` ~2s →
  timeout 5. **Never** 30s. `pkill -9 -f beam.smp` for stale 100%-CPU procs.
- Some tests **pin current behavior**; a failing test may need loosening if the
  new semantics are correct.
- Ignore `build/`; do **not** look in `examples/tao/tour/` (outdated/broken).
- `gleam run -- debug-file <f>` / `debug-expr "<e>"` for pipeline debugging.

---

## Task status checklist

| # | Task | Status |
|---|---|---|
| 1 | `--trace=` CLI flag + module-name-resolution trace | done |
| 2 | One loader, one naming rule | done |
| 3 | `tao.toml` dependency manifest | not-started |
| 4 | Prelude always present (as a dependency) | not-started |
| 5 | Relative imports | not-started |

Suggested order: **1 → 2 → 3 → 4 → 5**. Task 1 is independent tooling that
helps verify the rest. Task 2 is the foundation; 3/4/5 build on it.

---

## Task 1 — `--trace=` CLI flag + module-name-resolution trace

**Goal.** Add a repeatable `--trace=<kind>` flag to `check`/`run`/`test` (the
real commands, not just `debug-*`) that, for `kind=modules`, dumps the **final
module-name list** and the **resolved import edges**. Design it to be
**scalable** to more kinds (solved holes, unification, …) without adding new
commands — the long-term direction is "pass debug flags" instead of maintaining
`debug-file`/`debug-expr`/`debug-src`. Only `modules` is in scope now.

**Why in `check`/`run`/`test`.** These all funnel through `common.compile` →
`tao/compile.modules`, so one emission point covers all three.

**Design.**

1. New type (put it in `src/tao/trace.gleam`, or next to `Context`):
   ```gleam
   pub type TraceKind {
     TraceModules   // in scope now
     // TraceSolves  // future: targeted solved holes
     // TraceUnify   // future: unification steps
   }
   ```
2. Thread the enabled kinds. Follow the existing `Context.trace_solves: Bool`
   pattern (`src/core/context.gleam`): add `trace: List(TraceKind)` (default `[]`)
   to `Context`. (Optional end-state: fold `trace_solves` into
   `trace` as a `TraceSolves` kind so `debug-src --trace=solves` replaces
   `--trace-solves`; do this only if trivial, else defer.)
3. Emit the trace in **`tao/compile.modules`** (`src/tao/compile.gleam`), right
   after `declare.modules(mods)`, when `TraceModules ∈ ctx.trace`. It has both
   `mods` (loaded modules, post `implicit_prelude_imports`) and `defs` (the
   resolved import structure), so it can print both the name list and the edges.
   - Name list: `list.map(mods, fn(m) { m.0 })`.
   - Import edges: for each module's def list, collect the `path` of each
     `Import` stmt → `module → imported_path` (include the alias to show implicit
     vs explicit, e.g. `/__prelude__`).
   - Add a small `pub fn module_trace(mods, defs) -> Nil` in `tao/trace.gleam`
     (or `declare.gleam`) so it's reusable and unit-testable.
4. CLI: in `src/cli/entrypoint.gleam`, parse `--trace=<kind>` (repeatable) for
   `check`, `run`, `test` and pass the `List(TraceKind)` down through
   `common.load`/`common.compile` (thread it into the `Context` built in
   `common.compile`). Map `"modules" -> TraceModules`, unknown kind → error.
   Update the `help` text.

**Acceptance.**
- `gleam run -- check --trace=modules lib/prelude/v0.0.1/bool.tao` prints the
  module list (incl. `/prelude/bool`, …) and import edges (incl. the implicit
  `/__prelude__` edges and `prelude/operators/and → /prelude/bool`).
- Without `--trace=modules`, output is unchanged.
- A unit test pins the shape of `module_trace` output for a tiny 2-module graph.

**Notes.**
- The implicit prelude imports are already in the AST by the time
  `compile.modules` runs (`common.compile` calls `implicit_prelude_imports`
  first), so they show up for free.
- Keep IO out of `declare.*` if possible; `tao/compile.modules` is the cleanest
  single choke point for the real commands. The `debug-*` commands call
  `declare.modules` directly for per-phase output; they can adopt `module_trace`
  later as part of consolidating `debug-*` into flags (out of scope now).
- **Also fix while here (tiny, high value):** replace the `echo`/`todo`
  leftovers in `src/tao/declare.gleam:77-80` with a proper "module not found"
  diagnostic (an accumulated `e.Error`, not a crash). This is what made
  `tao check <package file>` die with a `todo` in §1.

---

## Task 2 — One loader, one naming rule

**Goal.** Make module naming **uniform and version-independent**: every module
is loaded as `/package/<relpath>` (version resolved and stripped), and there is
**no separate raw-path naming** for files that belong to a package. This deletes
`prelude_copies`/`prelude_package_name`/the `compile` filter and the
triple-naming seen in `debug-file --root`.

**Target invariants.**
- A file's module name depends only on **which package it belongs to + its path
  within the package**, never on *how it was selected* (by path, by directory,
  by package).
- Top-level scripts (files not in any package) get a well-defined name (e.g.
  keep `/` + normalized path, or a reserved `/main`-style name). Document the
  rule.
- The prelude is loaded exactly like any other package.

**Approach.**
1. Introduce a single loader, e.g.
   `load.project(paths: List(String), deps: List(#(String, Option(String)))) ->
   #(List(Module), List(Error))` that:
   - resolves each dep to a concrete dir (reuse `load.package`/`find_version`),
   - loads every package module as `/package/<relpath>`,
   - loads the **selected** top-level files (the CLI `paths`) and, for each,
     checks whether it lies inside a known package dir; if so it is *the same
     module* (dedupe by canonical name) rather than a new raw-path module.
2. Rework `src/tao/load.gleam` so `module`/`directory`/`package` share one
   naming helper. `directory`'s relative naming (`/bool`) should only be used
   *inside* a package loader (to build `/package/bool`), not as a standalone
   module name.
3. Rework `src/cli/common.gleam`:
   - `load` returns the unified module set; **delete** `prelude_copies`,
     `prelude_package_name`, and the duplicate-dropping filter in `compile`.
   - `compile` becomes "compile the unified set" (implicit prelude import stays
     for now; Task 4 rethinks it).
4. Rework the `debug-*` commands to use the unified loader (they currently call
   `load.module`/`load.directory`/`load.package_list` directly and are the source
   of the triple-naming).

**Acceptance.**
- `debug-file --root=lib/prelude/v0.0.1 lib/prelude/v0.0.1/bool.tao` shows
  `/prelude/bool` **once**, not three names.
- `tao check lib/prelude/v0.0.1/bool.tao` still exits 0 (now without the de-dup).
- A scratch `foo`/`bar` package pair (see §1 probes) still resolves intra- and
  cross-package imports when the packages are loaded.
- No `lib/prelude/` string is hardcoded anywhere in `src/` (grep to confirm).

**Notes / risks.**
- This is the largest task; it touches every command's loading. Do it in one
  session but change one command's loading at a time and run the full
  `gleam test` after each.
- `common.expand_paths`/`normalize` (CLI path → file list) stays; what changes is
  how those files get *named* once loaded.
- Pin the "file inside a package ⇒ canonical package name" rule with a unit test
  (e.g. loading `lib/prelude/v0.0.1/bool.tao` by path yields `/prelude/bool`).
- Beware the `import_path` parser already prepends `/`; keep module-name and
  import-path conventions aligned (`/package/<relpath>`).

---

## Task 3 — `tao.toml` dependency manifest

**Goal.** Add a per-package / per-project manifest so the **dependency closure**
is explicit data, not "prelude + whatever `--add` says". For now it holds
**library dependencies and versions** only; design it to grow other fields.

**Scope (minimal).**
- A `tao.toml` (name it consistently; confirm against any existing convention)
  with at least:
  ```toml
  name = "foo"
  version = "0.0.1"
  dependencies = [
    { name = "prelude" },           # version optional → latest
    { name = "bar", version = "0.0.1" },
  ]
  ```
- A loader that reads it (the project already depends on TOML-capable libs via
  Gleam; check what's available — `gleam.toml`/`manifest.toml` are for the
  *Gleam* build, **not** Tao; don't conflate them). If no TOML parser is a dep,
  either add one or use a simpler format — decide and record the choice here.
- Wire it into Task 2's `load.project`: the project's `tao.toml` (and each dep's)
  determines the dependency set, so `check`/`run`/`test` compile the real
  closure. `--add`/`--path` become overrides/extra roots on top of the manifest.

**Acceptance.**
- A scratch project with a `tao.toml` listing `foo` (which lists `prelude`)
  type-checks via `tao check` **without** `--add` (prelude + `foo` auto-loaded).
- The manifest parser has unit tests (parse a sample, missing version → latest,
  unknown field tolerated/ignored for forward-compat).

**Notes.**
- Keep the schema open: reserve a place for future fields (e.g. `default-exports`,
  `implicit-imports`, path overrides) without parsing them yet.
- This is what finally makes intra-/cross-library imports work for the real CLI
  (Task 1's crash on a package file becomes a clean type-check).

---

## Task 4 — Prelude always present (as a dependency)

**Goal.** The prelude is **always** available and implicitly imported, expressed
as "the prelude is an always-present dependency" rather than name-matched
special cases.

**Approach.**
1. With Task 3's manifest, ensure the prelude is **unconditionally** in the
   dependency set (auto-added if absent), so `common.with_prelude`'s job is
   subsumed by the manifest/loader. Keep `with_prelude` only as a thin
   compatibility shim or delete it.
2. Keep the **implicit-import feature** (global stdlib names) — it's wanted — but
   re-derive "is this module the prelude?" from package identity (the manifest /
   canonical name) instead of the `lib/prelude/` string prefix.
3. **Address the global name collision** (`bool`/`option`/`result` all export
   `_or`): either (a) guarantee prelude export names are unique, (b) namespace
   the implicit import so collisions are detected/reported, or (c) document and
   pin the resolution rule. Prefer (a) if the underscore names are meant to be
   internal (they're reached via the `or`/`and` overloads). Record the decision.

**Acceptance.**
- `tao check` on a file using `+`/`Bool` works with **no** `--add` and no
  `tao.toml` (prelude auto-present).
- No `prelude` string-literal special-casing remains outside the loader/manifest
  (grep).
- The `_or` collision is resolved deterministically (test pins which is visible,
  or proves it's unreachable).

---

## Task 5 — Relative imports

**Goal.** Allow imports **relative to the importing module's package**, e.g.
inside the prelude `import ./bool` (or `import bool`) resolves to
`/prelude/bool`. This is a source-level convenience; resolution is still by
canonical name.

**Approach.**
1. Extend the parser (`src/tao/parse.gleam:import_path`) to accept a relative
   form (leading `./`, or a bare name meaning "same package"). Keep the existing
   absolute form (`prelude/bool`) working.
2. Resolve relative → canonical **at load/declare time**, using the importing
   module's package prefix: `./bool` in `/prelude/operators/and` →
   `/prelude/bool`. This needs the importer's package to be known, which Task 2's
   canonical naming provides.
3. Update `declare.imports`/`desugar` so a relative import desugars to the
   canonical path before module-record lookup.

**Acceptance.**
- The prelude's `operators/and.tao` can be rewritten to `import ../bool` (or
  `import bool`) and still type-checks (pin with a test).
- Absolute imports still work unchanged.
- A relative import that escapes the package (`../../x`) has a defined behavior
  (allowed within the dep closure, or a clear error) — decide and pin.

**Notes.**
- Depends on Task 2 (canonical `/package/<relpath>` naming) so the relative→
  canonical rewrite is well-defined.
- Keep it minimal: relative *within a package* is the main win; cross-package
  relative paths can be a later extension.

---

## Cross-cutting cleanup (fold into the task above that touches the file)

- ~~`src/tao/declare.gleam:77-80`: replace `echo`/`todo` with a real
  "module not found" error. (Task 1.)~~ **Done.**
- `src/cli/debug_expr.gleam` `holes_summary` assert in `quote`/`format.value`:
  make it not crash on un-quotable hole values. (Nice-to-have; improves probing.)
- ~~Remove now-dead code after Task 2: `prelude_copies`, `prelude_package_name`,
  the `compile` duplicate filter, and any `load` path that no longer has a
  caller.~~ **Done.** (`prelude_copies`, `prelude_package_name`, and
  `load_modules` deleted from `common.gleam`; the `compile` filter removed.
  `load.module`/`load.module_list`/`load.directory` remain as `pub` API but
  have no internal callers.)

## Lessons learned (Task 1)

- **Gleam has no multiple spreads in a list literal:** `[a, ..b, ..c]` is
  illegal; use `list.append(list.append([a], b), c)` or intermediate `let`s.
- **Gleam has no duplicate imports:** `import foo` and `import foo.{Bar}` in the
  same file is an error; merge into `import foo.{type Bar}`.
- **`Context` constructor must be imported explicitly:** `import
  core/context.{type Context, Context}` — the type and the constructor are
  separate imports.
- **Build output is very noisy** (30+ pre-existing `todo` warnings). A
  `scripts/build.sh` that filters to `grep "^error"` would speed up iteration.
- **The `declare.modules` API change** (returning `#(List, List(Error))`)
  rippled to 6 call sites. A smaller change (e.g. a separate
  `modules_with_errors` function) would have been less invasive, but the tuple
  return is more principled and the old crash-free API is the only one that
  should exist going forward.

## Lessons learned (Task 2)

- **Parameter names shadow function names:** naming a pattern variable `file`
  shadows the `file/1` function in the same module. Use a distinct name like
  `path` for the local variable.
- **Case arms with multiple expressions need `{}`:** `[_v, ..rest] ->\n  let x = ...\n  expr` is a syntax error; wrap in `{ let x = ...; expr }`.
- **The unified loader is a drop-in replacement:** `load.project(paths, files,
  packages)` subsumes the old `load_modules` + `package_list` + `prelude_copies`
  trio. The dedup is by canonical name, so a file inside a package directory is
  automatically identified with its package module.
- **`debug-file` needed `filepath` and `utils/fs` imports** after switching to
  the unified loader (for `filepath.join` and `fs.list_recursive`).

## Verification checklist (run before marking a task done)

- `timeout -k 9 5 gleam test` (all tests; no `--filter`), no need to run `gleam build` separately, `gleam test` builds automatically.
- Re-run the §1 probes: intra-/cross-package import; `check` on a prelude file;
  `debug-file --root` single-naming; two-version newest-wins.
- Grep for leftover `lib/prelude/` string special-casing and `todo`/`echo` in
  `src/`.
