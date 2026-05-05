# Implementation Status Tracker

> **Last updated:** 2026-05-04 (Phase 2 — 907 tests passing, 0 failures.)
> **Reference:** [01-architecture-overview.md](01-architecture-overview.md), [03-core-language.md](03-core-language.md), [14-simplified-design.md](14-simplified-design.md), [examples/core/tour/](../../examples/core/tour/)
>
> **Recent:** Added `LitT(LiteralType)` to Term and `VLitT(LiteralType)` to Value. Parser now handles `$Int`, `$Float`, `$I32`, etc. as literal type terms. `infer_lit` returns `VLitT(IntT)` and `VLitT(FloatT)`. Unification handles VLitT with wildcard support. All 834 tests passing.

## Legend

| Emoji | Status | Meaning |
|-------|--------|---------|
| 🔴 | Not started | No work done yet |
| 🟡 | In progress | Currently working on this |
| ✅ | Done | Complete and tested |
| ⚠️ | Blocked | Depends on another task |
| 💡 | Deferred | Saved for future iteration |

---

## Pre-Implementation

### Old Codebase

| Task | Status | Notes |
|------|--------|-------|
| Backup old codebase | ✅ | All old code in `backup/` |
| Create new project structure | ✅ | Gleam project with `src/`, `test/`, `plans/` |
| Set up CI pipeline | ✅ | Test running, lint checking |

---

## Phase 1: Lexer + Core Types (Target: 2-3 days)

> **Goal:** Tokenizer with span tracking, Core AST types, State, Error.
> **References:** [03-core-language.md](03-core-language.md), [01-rewrite-plan.md](01-rewrite-plan.md)

### Tasks

| ID | Task | Status | Ref | Notes |
|----|------|--------|-----|-------|
| 1.1 | Implement tokenizer with span tracking | ✅ | [01-rewrite-plan.md](01-rewrite-plan.md) | `src/syntax/lexer.gleam` |
| 1.1.1 | Token types: Integer, Float, String, Name, Op, Keyword, Comment | ✅ | [01-rewrite-plan.md](01-rewrite-plan.md) | |
| 1.1.2 | Escape sequences in strings | ✅ | [01-rewrite-plan.md](01-rewrite-plan.md) | |
| 1.1.3 | Comments (single-line and block) | ✅ | [01-rewrite-plan.md](01-rewrite-plan.md) | |
| 1.1.4 | Span tracking on all tokens | ✅ | [01-rewrite-plan.md](01-rewrite-plan.md) | Source location for errors |
| 1.2 | Define Core AST types | ✅ | [03-core-language.md](03-core-language.md) | `src/core/ast.gleam` |
| 1.2.1 | Term type (Var, Hole, Lam, App, Pi, Lit, Ctr, Match, Let, Fix, Call, Ann, Unit, Err, Typ) | ✅ | [03-core-language.md](03-core-language.md) | Simplified Lam uses String param |
| 1.2.2 | Value type (VNeut, VLam, VPi, VLit, VCtr, VUnit, VErr) | ✅ | [03-core-language.md](03-core-language.md) | Simplified: Literal (not ILit/FLit) |
| 1.2.3 | Pattern type (PAny, PVar, PCtr, PUnit, PLit) | ✅ | [03-core-language.md](03-core-language.md) | |
| 1.2.4 | Literal type (Int, Float, String) | ✅ | [14-simplified-design.md](14-simplified-design.md) | EXTEND later to ILit/FLit |
| 1.2.5 | Env, Subst, Head, Elim, Case types | ✅ | [03-core-language.md](03-core-language.md) | |
| 1.3 | Implement AST utilities | ✅ | [03-core-language.md](03-core-language.md) | `src/core/ast.gleam` |
| 1.3.1 | `shift_term` | ✅ | [03-core-language.md](03-core-language.md) | De Bruijn index shifting |
| 1.3.2 | `error_term` | ✅ | [03-core-language.md](03-core-language.md) | Err term for error recovery |
| 1.3.3 | `make_neut` | ✅ | [03-core-language.md](03-core-language.md) | Neutral term construction |
| 1.3.4 | `make_hole_neut` | ✅ | [03-core-language.md](03-core-language.md) | Hole-based neutral |
| 1.3.5 | `make_var_neut` | ✅ | [03-core-language.md](03-core-language.md) | Variable-based neutral |
| 1.4 | Define State and Error types | ✅ | [03-core-language.md](03-core-language.md) | `src/core/state.gleam` |
| 1.4.1 | State type (ctrs, errors, ffi, holes, subst) | ✅ | [03-core-language.md](03-core-language.md) | |
| 1.4.2 | Error type (TypeMismatch, VarUndefined, HoleUnsolved, NotAFunction, etc.) | ✅ | [03-core-language.md](03-core-language.md) | 8 error variants |
| 1.4.3 | FfiEntry type | ✅ | [03-core-language.md](03-core-language.md) | Simplified: `fn(List(Value)) -> Value` |
| 1.4.4 | State helpers: `initial_state`, `with_err`, `continue_with_errors` | ✅ | [03-core-language.md](03-core-language.md) | |
| 1.5 | Write tests for lexer | ✅ | [08-testing-strategy.md](08-testing-strategy.md) | `test/syntax/lexer_test.gleam` |
| 1.5.1 | Every token type | ✅ | [08-testing-strategy.md](08-testing-strategy.md) | |
| 1.5.2 | Position tracking | ✅ | [08-testing-strategy.md](08-testing-strategy.md) | |
| 1.5.3 | Escape sequences | ✅ | [08-testing-strategy.md](08-testing-strategy.md) | |
| 1.5.4 | Comments | ✅ | [08-testing-strategy.md](08-testing-strategy.md) | |
| 1.6 | Write tests for Core AST | ✅ | [08-testing-strategy.md](08-testing-strategy.md) | `test/core/ast_test.gleam` |
| 1.6.1 | Every type constructor | ✅ | [08-testing-strategy.md](08-testing-strategy.md) | |
| 1.6.2 | Shift operations | ✅ | [08-testing-strategy.md](08-testing-strategy.md) | |
| 1.6.3 | Equality checks | ✅ | [08-testing-strategy.md](08-testing-strategy.md) | |
| 1.7 | Write tests for State | ✅ | [08-testing-strategy.md](08-testing-strategy.md) | `test/core/state_test.gleam` |
| 1.7.1 | State manipulation | ✅ | [08-testing-strategy.md](08-testing-strategy.md) | |
| 1.7.2 | Error accumulation | ✅ | [08-testing-strategy.md](08-testing-strategy.md) | |
| 1.7.3 | FFI entry creation | ✅ | [08-testing-strategy.md](08-testing-strategy.md) | |

### Phase 1 Gate

- [x] All 30+ Phase 1 tests pass (706+ tests total across all phases)
- [x] Tokenizer produces correct tokens for every syntax form
- [x] Core AST types are well-formed (Param extracted then removed in favor of tuples)
- [x] State error accumulation works correctly (all Error variants carry spans)

**Phase 1 Complete:** All lexer, AST, and state implementations are done and tested. AST refactored: `Param` record type removed (replaced with ` #(String, Term)` tuples for Lam, ` #(String, Value)` for VLam), `Call` constructor added to Term, unused State fields cleaned up, all `Error` variants carry `span: Span` fields. Codebase: 13 source files.

---

## Phase 2: Parser + Core Type Checker + NBE (Target: 4-5 days)

> **Goal:** Core parser, bidirectional type checker, NBE evaluator, Quote, Unification, Exhaustiveness. First CLI: `tao run <file>`.
> **References:** [03-core-language.md](03-core-language.md), [05-compiler-pipeline.md](05-compiler-pipeline.md), [10-operator-overloading.md](10-operator-overloading.md)

### 2.1: Parser Combinator DSL + Core Parser

| ID | Task | Status | Ref | Notes |
|----|------|--------|-----|-------|
| 2.1 | Implement parser combinator DSL | ✅ | [05-compiler-pipeline.md](05-compiler-pipeline.md) | `src/syntax/grammar.gleam` |
| 2.1.1 | Combinators: Seq, Opt, Many, Choice, Ref | ✅ | [05-compiler-pipeline.md](05-compiler-pipeline.md) | |
| 2.1.2 | Combinators: Tok, Kw, Op | ✅ | [05-compiler-pipeline.md](05-compiler-pipeline.md) | |
| 2.1.3 | Parse combinators for error recovery | ✅ | [05-compiler-pipeline.md](05-compiler-pipeline.md) | |
| 2.1.4 | `parens` and `delimited` combinators | ✅ | [05-compiler-pipeline.md](05-compiler-pipeline.md) | |
| 2.1.5 | Utility functions: `result_ast`, `result_errors`, `error_to_string` | ✅ | [05-compiler-pipeline.md](05-compiler-pipeline.md) | |
| 2.1.6 | `Either` type and helpers: `is_left`, `is_right`, `left_value`, `right_value` | ✅ | [05-compiler-pipeline.md](05-compiler-pipeline.md) | |
| 2.1.7 | Write tests for parser combinator DSL | ✅ | [08-testing-strategy.md](08-testing-strategy.md) | `test/syntax/grammar_test.gleam` |
| 2.2 | Define Core grammar + parser | ✅ | [05-compiler-pipeline.md](05-compiler-pipeline.md) | `src/core/syntax.gleam` |
| 2.2.1 | Term production (Var, Hole, Lam, App, Pi, Lit, Ctr, Match, Let, Fix, Call, Ann, Unit, Err, Typ) | ✅ | [05-compiler-pipeline.md](05-compiler-pipeline.md) | |
| 2.2.2 | Pattern production (PAny, PVar, PCtr, PUnit, PLit) | ✅ | [05-compiler-pipeline.md](05-compiler-pipeline.md) | |
| 2.2.3 | Span accuracy on every parse | ✅ | [05-compiler-pipeline.md](05-compiler-pipeline.md) | |
| 2.2.4 | Write tests for Core parser | ✅ | [08-testing-strategy.md](08-testing-strategy.md) | `test/core/syntax_test.gleam` |

### 2.3: Unification

| ID | Task | Status | Ref | Notes |
|----|------|--------|-----|-------|
| 2.3 | Implement unification | ✅ | [03-core-language.md](03-core-language.md) | `src/core/unify.gleam` |
| 2.3.1 | `unify` function — higher-order unification | ✅ | [03-core-language.md](03-core-language.md) | |
| 2.3.2 | Occurs check — always False (recursive types) | ✅ | [03-core-language.md](03-core-language.md) | |
| 2.3.3 | Hole instantiation via env binding | ✅ | [03-core-language.md](03-core-language.md) | |
| 2.3.4 | Write tests for unification | ✅ | [08-testing-strategy.md](08-testing-strategy.md) | `test/core/unify_test.gleam` — 34 tests |

### 2.4: Substitution

| ID | Task | Status | Ref | Notes |
|----|------|--------|-----|-------|
| 2.4 | Implement substitution | ✅ | [03-core-language.md](03-core-language.md) | `src/core/subst.gleam` |
| 2.4.1 | `force` — hole resolution + spine application (beta reduction) | ✅ | [03-core-language.md](03-core-language.md) | |
| 2.4.2 | `force_levels_to_indices` — De Bruijn level → index | ✅ | [03-core-language.md](03-core-language.md) | |
| 2.4.3 | `shift_term` / `subst_term_var` / `apply_spine` | ✅ | [03-core-language.md](03-core-language.md) | |
| 2.4.4 | Write tests for substitution | ✅ | [08-testing-strategy.md](08-testing-strategy.md) | `test/core/subst_test.gleam` — 62 tests |

### 2.5: Generalization

| ID | Task | Status | Ref | Notes |
|----|------|--------|-----|-------|
| 2.5 | Implement generalization | ✅ | [03-core-language.md](03-core-language.md) | `src/core/generalize.gleam` |
| 2.5.1 | `free_holes` — collect free hole IDs from a Value | ✅ | [03-core-language.md](03-core-language.md) | |
| 2.5.2 | `collect_free_levels` — collect free De Bruijn levels | ✅ | [03-core-language.md](03-core-language.md) | |
| 2.5.3 | `create_hole_subst` / `replace_holes_with_vars` | ✅ | [03-core-language.md](03-core-language.md) | |
| 2.5.4 | Write tests for generalization | ✅ | [08-testing-strategy.md](08-testing-strategy.md) | `test/core/generalize_test.gleam` — 47 tests |

### 2.6: NBE Evaluator + Quote

| ID | Task | Status | Ref | Notes |
|----|------|--------|-----|-------|
| 2.6 | Implement NBE evaluator | ✅ | [03-core-language.md](03-core-language.md) | `src/core/eval.gleam` |
| 2.6.1 | `evaluate` — normalization by evaluation | ✅ | [03-core-language.md](03-core-language.md) | |
| 2.6.2 | `evaluate_with_ffi` — FFI integration | ✅ | [03-core-language.md](03-core-language.md) | |
| 2.6.3 | `do_app` — neutral spine application | ✅ | [03-core-language.md](03-core-language.md) | |
| 2.6.4 | Write tests for evaluator | ✅ | [08-testing-strategy.md](08-testing-strategy.md) | `test/core/eval_test.gleam` — 73 tests |
| 2.7 | Implement quote (Value → Term) | ✅ | [03-core-language.md](03-core-language.md) | `src/core/quote.gleam` |
| 2.7.1 | `quote` function — does NOT call eval | ✅ | [03-core-language.md](03-core-language.md) | |
| 2.7.2 | Write tests for quote | ✅ | [08-testing-strategy.md](08-testing-strategy.md) | `test/core/quote_test.gleam` — 39 tests |

### 2.8: Type Inference + Exhaustiveness

| ID | Task | Status | Ref | Notes |
|----|------|--------|-----|-------|
| 2.8 | Implement type inference (synthesis) | ✅ | [03-core-language.md](03-core-language.md) | `src/core/infer.gleam` |
| 2.8.1 | `infer(state, term) -> #(Value, Value, State)` — synthesis | ✅ | [03-core-language.md](03-core-language.md) | |
| 2.8.2 | `check(state, term, expected) -> #(Value, Value, State)` — checking | ✅ | [03-core-language.md](03-core-language.md) | |
| 2.8.3 | `infer_pattern` | 🔴 | [03-core-language.md](03-core-language.md) | |
| 2.8.4 | `infer_match` | 🔴 | [03-core-language.md](03-core-language.md) | |
| 2.8.5 | `infer_fix` | 🔴 | [03-core-language.md](03-core-language.md) | |
| 2.8.6 | All error cases | ✅ | [03-core-language.md](03-core-language.md) | VarUndefined, NotAFunction, etc. |
| 2.8.7 | Write tests for type inference | ✅ | [08-testing-strategy.md](08-testing-strategy.md) | `test/core/infer_test.gleam` — 31 tests |
| 2.9 | Implement exhaustiveness checking | ✅ | [03-core-language.md](03-core-language.md) | `src/core/exhaustiveness.gleam` |
| 2.9.1 | `check_exhaustiveness` — Maranget's algorithm | ✅ | [03-core-language.md](03-core-language.md) | |
| 2.9.2 | `is_redundant` | ✅ | [03-core-language.md](03-core-language.md) | |
| 2.9.3 | Handle guards conservatively | ✅ | [03-core-language.md](03-core-language.md) | |
| 2.9.4 | Write tests for exhaustiveness | ✅ | [08-testing-strategy.md](08-testing-strategy.md) | `test/core/exhaustiveness_test.gleam` — 22 tests |

### 2.10: Tour Syntax Parser (all `$` prefix)

| ID | Task | Status | Ref | Notes |
|----|------|--------|-----|-------|
| 2.10 | Rewrite parser keyword prefix: `%fn` → `$fn` | ✅ | tour/01_basics/07_lambda_functions.core | All Core keywords use `$` |
| 2.10.1 | Parse `$fn` instead of `%fn` | ✅ | | |
| 2.10.2 | Parse `$let` instead of `%let` | ✅ | | |
| 2.10.3 | Parse `$match` instead of `%match` | ✅ | | |
| 2.10.4 | Parse `$type` keyword | ✅ | tour/01_basics/05_type_defs.core | |
| 2.10.5 | Parse `$error "message"` | ✅ | tour/01_basics/14_errors.core | Term.Err |
| 2.10.6 | Parse `$pi` keyword | ✅ | tour/01_basics/08_pi_types.core | |
| 2.10.7 | Parse `type` → `$Type` (universe 0) | ✅ | | |
| 2.10.8 | Parse `$Type<n>` (explicit universe) | ✅ | tour/03_literals/01_types.core | |
| 2.10.9 | Parse `$Type<x>` (bound variable) | ✅ | tour/05_pattern_matching/03_type_pattern.core | |
| 2.10.10 | Parse `$Int` and `$Float` as type terms | ✅ | tour/05_pattern_matching/03_type_pattern.core | |
| 2.10.11 | Parse `$I8`–`$I64`, `$U8`–`$U64`, `$F16`–`$F64` | ✅ | tour/03_literals/01_types.core | Via LiteralType |
| 2.10.12 | Parse `#` for constructor prefix | ✅ | tour/01_basics/06_constructors.core | Already implemented |
| 2.10.13 | Parse `%` for FFI builtin prefix | ✅ | tour/06_builtins/01_i32.core | Now `$fn(arg: T, arg: T) -> R` |
| 2.10.14 | Parse `$fn<a: T>(x: a)` (implicit params) | ✅ | tour/07_advanced/02_implicit_params.core | |
| 2.10.15 | Parse `$pi<a: T>(a) -> a` (implicit params) | ✅ | tour/02_syntax_sugar/04_pi_arrow.core | |
| 2.10.16 | Parse `$pi(a) -> a` (non-dependent, no colon) | ✅ | tour/02_syntax_sugar/04_pi_arrow.core | |
| 2.10.17 | Parse `$fn(x)` (untyped lambda, hole type) | ✅ | tour/02_syntax_sugar/03_lam_untyped.core | |
| 2.10.18 | Parse `$let x` (untyped let, hole type) | ✅ | tour/02_syntax_sugar/02_let_untyped.core | |
| 2.10.19 | Parse FFI calls with typed args: `f(a: T, b: T) -> R` | ✅ | tour/06_builtins/01_i32.core | Call with typed_args + return_type |
| 2.10.20 | Parse `$type { | #C(a) -> R }` (TypeDef) | ✅ | tour/04_type_definitions/01_monomorphic.core | Term.TypeDef |

### 2.11: Extended Pattern Matching

| ID | Task | Status | Ref | Notes |
|----|------|--------|-----|-------|
| 2.11 | Add alias patterns: `name@pattern` | ✅ | tour/05_pattern_matching/02_alias_pattern.core | PAlias in Pattern type |
| 2.12 | Add type patterns: `$Type`, `$Type<n>`, `$Type<x>` | ✅ | tour/05_pattern_matching/03_type_pattern.core | PType with type_name |
| 2.13 | Add record patterns: `{x: pattern}`, `{x}` | ✅ | tour/05_pattern_matching/05_rcd_pattern.core | PRcd in Pattern type |
| 2.14 | Add record type patterns: `${x: Type}`, `${x}` | ✅ | tour/05_pattern_matching/06_rcdt_pattern.core | PType with RcdT fields |
| 2.15 | Add error patterns: `$error` | ✅ | tour/05_pattern_matching/08_error_pattern.core | PError in Pattern type |
| 2.16 | Add guard with pass pattern: `? expr ~ pass => body` | ✅ | tour/05_pattern_matching/09_guards.core | Two-stage guard via Option(Term) |
| 2.17 | Update exhaustiveness for new patterns | ✅ | tour/05_pattern_matching/10_exhaustiveness.core | Basic support in exhaustiveness.gleam |
| 2.18 | Write tests for extended patterns | ✅ | | 15 tests in type_defs_test.gleam, 20 in exhaustiveness_test.gleam |

### 2.19: Numeric Types & Advanced Inference

| ID | Task | Status | Ref | Notes |
|----|------|--------|-----|-------|
| 2.19 | Extend LiteralType: `$I8`–`$I64`, `$U8`–`$U64`, `$F16`–`$F64` | ✅ | tour/03_literals/01_types.core | All 13 variants + IntT, FloatT |
| 2.19.1 | Add `$Int` wildcard type (matches any integer) | ✅ | tour/05_pattern_matching/03_type_pattern.core | Wildcard in unify + PType |
| 2.19.2 | Add `$Float` wildcard type (matches any float) | ✅ | tour/05_pattern_matching/03_type_pattern.core | Matches float AND integer literals |
| 2.19.3 | Update unify: `$Int` ↔ any integer type | ✅ | | Implemented in match_values |
| 2.19.4 | Update unify: `$Float` ↔ any float type | ✅ | | Implemented in match_values |
| 2.19.5 | Implement record type defaults: `${x: T, y: T = val}` | ✅ | tour/01_basics/03_records.core | VRcdT + default filling in check() |
| 2.19.6 | Parse record type with defaults | ✅ | | RcdT with Option(Term) defaults |
| 2.19.7 | Infer missing fields from type defaults | ✅ | | fill_record_defaults() in check() |
| 2.19.8 | Implement implicit parameter auto-expansion | 🟡 | tour/07_advanced/02_implicit_params.core | Parser supports it, inference partial |
| 2.19.9 | Synthesize implicit args during inference | 🔴 | | |
| 2.19.10 | Retry application with synthesized args | 🔴 | | |
| 2.19.11 | Implement GADT-style constructor checking | ✅ | tour/04_type_definitions/03_gadt_vec.core | Self_type/result_type evaluated, constructor lookup, pattern matching, best-effort error handling |
| 2.19.12 | Infer constructor result types | 🔴 | | |
| 2.19.13 | Handle computed result types (%u32_add) | 🔴 | | |
| 2.19.14 | Update exhaustiveness for `$Int` wildcard | 🔴 | tour/05_pattern_matching/10_exhaustiveness.core | Integer types are "infinite" |
| 2.19.15 | Write tests for numeric types | ✅ | | Covered in syntax_test.gleam and infer_test.gleam |
| 2.19.16 | Write tests for implicit params | 🟡 | | Partial in infer_test.gleam |
| 2.19.17 | Write tests for GADT patterns | ✅ | | Added gadt_option_some_type_test, gadt_unknown_ctor_fallback_test |

### 2.20: CLI `run` Command

| ID | Task | Status | Ref | Notes |
|----|------|--------|-----|-------|
| 2.20 | Implement CLI `run` command | 🔴 | [14-simplified-design.md](14-simplified-design.md) | `src/cli/run.gleam` |
| 2.20.1 | Parse → desugar (identity) → type check → evaluate → print | 🔴 | [14-simplified-design.md](14-simplified-design.md) | |
| 2.20.2 | Handle errors from all phases | 🔴 | [14-simplified-design.md](14-simplified-design.md) | |
| 2.20.3 | Return appropriate exit codes | 🔴 | [14-simplified-design.md](14-simplified-design.md) | |
| 2.21 | Write tests for CLI `run` | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | `test/cli/run_test.gleam` |
| 2.21.1 | Run simple Core programs | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 2.21.2 | Run with errors | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 2.21.3 | Run with type errors | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |

### Phase 2 Gate

- [x] All 783+ Phase 2 tests pass, 0 failures
- [ ] `tao run` compiles and evaluates a simple Core program
- [x] Type errors are reported correctly
- [x] Exhaustiveness checking catches missing/redundant cases
- [x] Quote round-trip works (term → eval → quote → term)
- [x] Type definitions as env values — TypeDef stored as VTypeDef in env, no separate CtrEnv registry
- [x] **Tour syntax:** Parser handles all tour syntax with `$` prefix (20 tasks complete)
- [x] **Extended patterns:** Parser handles 10+ pattern types (PAlias, PType, PRcd, PError, guards)
- [x] **Numeric types:** Full hierarchy ($I8–$I64, $U8–$U64, $F16–$F64), wildcard types, record type defaults
- [ ] **Tour e2e:** All 38 tour examples parse, type-check, and evaluate (pending test expectation updates)

### Remaining Work

| Priority | Item | Details |
|----------|------|---------|
| 1 | Fix test expectation mismatches | 7 tour.gleam failures: Value shapes don't match expected — tests were written during design/spec and need updating to match actual behavior |
| 2 | Implement implicit param auto-expansion | Parser supports implicit params; inference needs `synthesize_implicit_args` + retry logic |
| 2 | GADT-style constructor checking | ✅ | Self_type/result_type evaluated, constructor lookup, pattern matching, best-effort error handling |
| 4 | Update exhaustiveness for `$Int` wildcard | Integer types are "infinite" — need wildcard pattern at end |
| 5 | Implement CLI `run` command | Full pipeline: parse → type check → evaluate → print |
| 6 | Test assertion audit | 867 original tests had weak assertions (`case expr -> True _ -> False`). Strategy: add new strong-assertion edge case tests first, then update originals. Lexer edge cases added (36 new tests). |
| 7 | Span preservation tests | Add tests to verify spans are preserved through parser → infer → eval → quote pipeline |
| 8 | Consolidate type_defs_test into ast_test | type_defs_test.gleam should be merged into ast_test.gleam (1-to-1 mapping rule) |

---

## Phase 3: Tao + Desugaring + Test Framework (Target: 4-5 days)

> **Goal:** Tao high-level language, desugaring to Core, test framework (REPL style), `tao check` and `tao test` commands.
> **References:** [04-tao-language.md](04-tao-language.md), [09-desugaring-reference.md](09-desugaring-reference.md), [10-operator-overloading.md](10-operator-overloading.md)

### Tasks

| ID | Task | Status | Ref | Notes |
|----|------|--------|-----|-------|
| 3.1 | Define Tao AST types | 🔴 | [04-tao-language.md](04-tao-language.md) | `src/tao/ast.gleam` |
| 3.1.1 | Expr type (Var, Lit, Lambda, Call, BinOp, Ctr, Match, If, Ann, Hole, Record, Dot) | 🔴 | [04-tao-language.md](04-tao-language.md) | Simplified: Literal |
| 3.1.2 | Stmt type (Let, Fn, Import, TypeDef, For, While, Expr) | 🔴 | [04-tao-language.md](04-tao-language.md) | |
| 3.1.3 | TypeAst type (TVar, TApp, TFn, THole) | 🔴 | [04-tao-language.md](04-tao-language.md) | |
| 3.1.4 | TestStatement type (REPL-style) | 🔴 | [04-tao-language.md](04-tao-language.md) | `/// > expr ~> result` |
| 3.2 | Write tests for Tao AST | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | `test/tao/ast_test.gleam` |
| 3.2.1 | Every type constructor | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 3.3 | Define Tao grammar | 🔴 | [04-tao-language.md](04-tao-language.md) | `src/tao/syntax.gleam` |
| 3.3.1 | Tao parser combinator definitions | 🔴 | [04-tao-language.md](04-tao-language.md) | Uses grammar DSL from Phase 2 |
| 3.4 | Implement Tao parser | 🔴 | [04-tao-language.md](04-tao-language.md) | `src/tao/syntax.gleam` |
| 3.4.1 | Every Tao syntax form | 🔴 | [04-tao-language.md](04-tao-language.md) | |
| 3.4.2 | Span accuracy | 🔴 | [04-tao-language.md](04-tao-language.md) | |
| 3.5 | Implement Tao formatter | 🔴 | [04-tao-language.md](04-tao-language.md) | `src/tao/syntax.gleam` |
| 3.6 | Write parse → format → parse round-trip test | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | `test/tao/golden_test.gleam` |
| 3.7 | Write tests for Tao parser | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | `test/tao/syntax_test.gleam` |
| 3.7.1 | Every syntax form | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 3.8 | Implement desugar_expr | 🔴 | [09-desugaring-reference.md](09-desugaring-reference.md) | `src/tao/desugar.gleam` |
| 3.8.1 | Lambda abstraction | 🔴 | [09-desugaring-reference.md](09-desugaring-reference.md) | → Lam(body) |
| 3.8.2 | Function definition | 🔴 | [09-desugaring-reference.md](09-desugaring-reference.md) | → Let("f", Lam(...)) |
| 3.8.3 | Let binding | 🔴 | [09-desugaring-reference.md](09-desugaring-reference.md) | → Let("x", value, body) |
| 3.8.4 | Pattern matching | 🔴 | [09-desugaring-reference.md](09-desugaring-reference.md) | → Match(args, cases) |
| 3.8.5 | If-else | 🔴 | [09-desugaring-reference.md](09-desugaring-reference.md) | → Match(c, [Case(True, a), Case(False, b)]) |
| 3.8.6 | For loop | 🔴 | [09-desugaring-reference.md](09-desugaring-reference.md) | → foldl |
| 3.8.7 | While loop | 🔴 | [09-desugaring-reference.md](09-desugaring-reference.md) | → Fix("loop", If(c, e, Call("loop", []))) |
| 3.8.8 | Pipe operator | 🔴 | [09-desugaring-reference.md](09-desugaring-reference.md) | `x |> f` → f(x) |
| 3.8.9 | Binary operators | 🔴 | [09-desugaring-reference.md](09-desugaring-reference.md) | `a + b` → App(App(Var("+"), a), b) |
| 3.9 | Implement desugar_stmt | 🔴 | [09-desugaring-reference.md](09-desugaring-reference.md) | `src/tao/desugar.gleam` |
| 3.9.1 | Statement desugaring (Let, Fn, For, While, Expr) | 🔴 | [09-desugaring-reference.md](09-desugaring-reference.md) | |
| 3.10 | Implement desugar_module | 🔴 | [09-desugaring-reference.md](09-desugaring-reference.md) | `src/tao/desugar.gleam` |
| 3.10.1 | Module → Core term | 🔴 | [09-desugaring-reference.md](09-desugaring-reference.md) | |
| 3.11 | Implement unified function/operator handling | 🔴 | [10-operator-overloading.md](10-operator-overloading.md) | Pattern matching on implicit args |
| 3.11.1 | Track all definitions per name (single or multiple) | 🔴 | [10-operator-overloading.md](10-operator-overloading.md) | |
| 3.11.2 | Generate pattern match on implicit argument types | 🔴 | [10-operator-overloading.md](10-operator-overloading.md) | Single → one-branch, Multiple → multi-branch |
| 3.12 | Write tests for desugarer | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | `test/tao/desugar_test.gleam` |
| 3.12.1 | Every high-level feature | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 3.13 | Implement compile_tao | 🔴 | [04-tao-language.md](04-tao-language.md) | `src/tao/compiler.gleam` |
| 3.13.1 | Full pipeline: parse → desugar → check | 🔴 | [04-tao-language.md](04-tao-language.md) | |
| 3.13.2 | Error collection across phases | 🔴 | [04-tao-language.md](04-tao-language.md) | |
| 3.14 | Implement compile_core | 🔴 | [04-tao-language.md](04-tao-language.md) | Core-only pipeline |
| 3.15 | Write tests for compiler | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | `test/tao/compiler_test.gleam` |
| 3.15.1 | Every pipeline stage | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 3.15.2 | Error accumulation | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 3.15.3 | Partial results | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 3.16 | Implement test API | 🔴 | [06-import-system.md](06-import-system.md) | `src/tao/test_api.gleam` |
| 3.16.1 | `extract_tests(source) -> List(TestStatement)` | 🔴 | [06-import-system.md](06-import-system.md) | Parse `/// > expr ~> result` |
| 3.16.2 | `run_tests(tests, context) -> List(TestResult)` | 🔴 | [06-import-system.md](06-import-system.md) | Evaluate and check |
| 3.16.3 | Test result reporting | 🔴 | [06-import-system.md](06-import-system.md) | Pass/fail with expected vs actual |
| 3.17 | Write tests for test API | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | `test/tao/test_api_test.gleam` |
| 3.17.1 | Test extraction | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 3.17.2 | Assertion pass | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 3.17.3 | Assertion fail | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 3.17.4 | No tests found | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 3.18 | Implement CLI `check` command | 🔴 | [14-simplified-design.md](14-simplified-design.md) | `src/cli/check.gleam` |
| 3.18.1 | Parse → desugar → type check → report type or errors | 🔴 | [14-simplified-design.md](14-simplified-design.md) | No evaluation |
| 3.19 | Write tests for CLI `check` | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | `test/cli/check_test.gleam` |
| 3.19.1 | Check simple Tao programs | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 3.19.2 | Check with type errors | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 3.19.3 | Check with no errors | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 3.20 | Implement CLI `test` command | 🔴 | [14-simplified-design.md](14-simplified-design.md) | `src/cli/test.gleam` |
| 3.20.1 | Find test statements → compile → evaluate → report results | 🔴 | [14-simplified-design.md](14-simplified-design.md) | |
| 3.20.2 | Handle test failures gracefully | 🔴 | [14-simplified-design.md](14-simplified-design.md) | |
| 3.21 | Write tests for CLI `test` | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | `test/cli/test_test.gleam` |
| 3.21.1 | Tests with assertions | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 3.21.2 | Tests without assertions | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 3.21.3 | No test statements | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |

### Phase 3 Gate

- [ ] All 60+ Tao tests pass
- [ ] All 30+ desugar tests pass
- [ ] All 20+ compiler tests pass
- [ ] `tao run <file>` works for Tao programs
- [ ] `tao check <file>` works for Tao programs
- [ ] `tao test <file>` works for Tao programs
- [ ] Test framework extracts and runs REPL-style tests
- [ ] Fibonacci, map/filter compile and run correctly
- [ ] Error accumulation works across all phases
- [ ] All Phase 2 remaining work complete
- [ ] Tour examples: `tao run examples/core/tour/` works end-to-end

---

## Phase 4: Multi-file + Import System (Target: 3-4 days)

> **Goal:** Multi-file compilation, import resolution with graceful degradation, module dependency tracking.
> **References:** [06-import-system.md](06-import-system.md), [13-migration-guide.md](13-migration-guide.md)

### Tasks

| ID | Task | Status | Ref | Notes |
|----|------|--------|-----|-------|
| 4.1 | Define LanguageConfig | 🔴 | [06-import-system.md](06-import-system.md) | `src/tao/language_config.gleam` |
| 4.1.1 | LanguageConfig type | 🔴 | [06-import-system.md](06-import-system.md) | Truth/false constructors, operators |
| 4.1.2 | `default_config()` | 🔴 | [06-import-system.md](06-import-system.md) | |
| 4.1.3 | Config-based type/operator lookup | 🔴 | [06-import-system.md](06-import-system.md) | |
| 4.2 | Write tests for language config | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | `test/tao/language_config_test.gleam` |
| 4.2.1 | Config lookup for every type/operator | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 4.3 | Define GlobalContext | 🔴 | [06-import-system.md](06-import-system.md) | `src/tao/global_context.gleam` |
| 4.3.1 | Module loading | 🔴 | [06-import-system.md](06-import-system.md) | |
| 4.3.2 | Constructor environment building | 🔴 | [06-import-system.md](06-import-system.md) | |
| 4.3.3 | Type-to-core conversion | 🔴 | [06-import-system.md](06-import-system.md) | |
| 4.4 | Write tests for global context | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | `test/tao/global_context_test.gleam` |
| 4.4.1 | Module loading | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 4.4.2 | Constructor environment | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 4.4.3 | Type conversion | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 4.5 | Implement import resolver | 🔴 | [06-import-system.md](06-import-system.md) | `src/tao/import_resolver.gleam` |
| 4.5.1 | Module lookup (module-not-found → empty module + error) | 🔴 | [06-import-system.md](06-import-system.md) | |
| 4.5.2 | Name lookup (name-not-found → deferred to type checker) | 🔴 | [06-import-system.md](06-import-system.md) | No error here |
| 4.5.3 | Selective imports | 🔴 | [06-import-system.md](06-import-system.md) | `import std/list, {map, filter}` |
| 4.5.4 | Wildcard imports | 🔴 | [06-import-system.md](06-import-system.md) | `import std/list` |
| 4.6 | Write tests for import resolver | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | `test/tao/import_test.gleam` |
| 4.6.1 | Every import variant | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 4.6.2 | Module-not-found (empty module + error) | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 4.6.3 | Name-not-found (deferred) | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 4.6.4 | Error cases | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 4.7 | Extend compile_tao with multi-file support | 🔴 | [04-tao-language.md](04-tao-language.md) | `src/tao/compiler.gleam` |
| 4.7.1 | Module merging | 🔴 | [04-tao-language.md](04-tao-language.md) | |
| 4.8 | Write tests for multi-file compilation | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | `test/tao/compiler_test.gleam` |
| 4.8.1 | Every file combination | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 4.8.2 | Import variants | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 4.8.3 | Error cases | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |

### Phase 4 Gate

- [ ] All 40+ Phase 4 tests pass
- [ ] Multi-file compilation works correctly
- [ ] Module-not-found handled gracefully (empty module + error)
- [ ] Name-not-found deferred to type checker (VarUndefined error)
- [ ] Selective and wildcard imports work

---

## Phase 5: Extended Features + Polish (Target: 3-4 days)

> **Goal:** Full literal type system, operator overloading, error codes, source context formatting.
> **References:** [03-core-language.md](03-core-language.md), [07-error-handling.md](07-error-handling.md), [10-operator-overloading.md](10-operator-overloading.md)

### Tasks

| ID | Task | Status | Ref | Notes |
|----|------|--------|-----|-------|
| 5.1 | Extend Literal → LitValue { ILit, FLit, StrLit } | 🔴 | [03-core-language.md](03-core-language.md) | `src/core/ast.gleam` |
| 5.2 | Add LitType { I32T, I64T, U32T, U64T, F32T, F64T, ILitT, FLitT } | 🔴 | [03-core-language.md](03-core-language.md) | |
| 5.3 | Implement literal type unification | 🔴 | [10-operator-overloading.md](10-operator-overloading.md) | `src/core/unify.gleam` |
| 5.3.1 | ILitT ↔ I32T unification | 🔴 | [10-operator-overloading.md](10-operator-overloading.md) | |
| 5.3.2 | FLitT ↔ F64T unification | 🔴 | [10-operator-overloading.md](10-operator-overloading.md) | |
| 5.3.3 | Cross-type rejection (ILitT never unifies with FLitT) | 🔴 | [10-operator-overloading.md](10-operator-overloading.md) | |
| 5.4 | Update VLit to carry LitValue | 🔴 | [03-core-language.md](03-core-language.md) | |
| 5.5 | Write tests for literal types | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | `test/core/literal_type_test.gleam` |
| 5.5.1 | Integer literal polymorphism (1 as I32 or I64) | 🔴 | [10-operator-overloading.md](10-operator-overloading.md) | |
| 5.5.2 | Float literal (3.14 can't be I32) | 🔴 | [10-operator-overloading.md](10-operator-overloading.md) | |
| 5.5.3 | Cross-type rejection | 🔴 | [10-operator-overloading.md](10-operator-overloading.md) | |
| 5.6 | Extend FfiEntry to fn(List(#(Value, Value))) -> Option(Value) | 🔴 | [10-operator-overloading.md](10-operator-overloading.md) | `src/core/ast.gleam` |
| 5.7 | Desugar overloaded functions to pattern match on implicit arg types | 🔴 | [10-operator-overloading.md](10-operator-overloading.md) | `src/tao/desugar.gleam` |
| 5.8 | Update VCall to pass (value, type) pairs to FFI | 🔴 | [10-operator-overloading.md](10-operator-overloading.md) | `src/core/eval.gleam` |
| 5.9 | Write tests for operator overloading | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | `test/core/overload_test.gleam` |
| 5.9.1 | Overloaded add (I32 + I32 → I32, F64 + F64 → F64) | 🔴 | [10-operator-overloading.md](10-operator-overloading.md) | |
| 5.9.2 | Single-definition pattern match | 🔴 | [10-operator-overloading.md](10-operator-overloading.md) | |
| 5.9.3 | No-overload case | 🔴 | [10-operator-overloading.md](10-operator-overloading.md) | |
| 5.9.4 | Ambiguous overload error | 🔴 | [10-operator-overloading.md](10-operator-overloading.md) | |
| 5.10 | Add error codes (E0001=Parse, E0101=Type, etc.) | 🔴 | [07-error-handling.md](07-error-handling.md) | `src/core/error.gleam` |
| 5.11 | Add notes and hints to errors | 🔴 | [07-error-handling.md](07-error-handling.md) | |
| 5.12 | Implement source context formatting | 🔴 | [07-error-handling.md](07-error-handling.md) | |
| 5.13 | Update CLI output with formatted errors | 🔴 | [07-error-handling.md](07-error-handling.md) | |
| 5.14 | Write tests for error system | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | `test/core/error_formatter_test.gleam` |
| 5.14.1 | Every error type formatted correctly | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 5.14.2 | Accurate spans | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 5.14.3 | Error codes documented | 🔴 | [08-testing-strategy.md](08-testing-strategy.md) | |
| 5.15 | [Optional] Comptime: Add Comptime to Term | 💡 | [14-simplified-design.md](14-simplified-design.md) | Evaluate at compile time |
| 5.16 | [Optional] Streams: Add yield to Expr | 💡 | [14-simplified-design.md](14-simplified-design.md) | Stream type in stdlib |
| 5.17 | [Optional] Record update: Add record update desugar | 💡 | [14-simplified-design.md](14-simplified-design.md) | |
| 5.18 | [Optional] Truth/false constructor: Add to State | 💡 | [14-simplified-design.md](14-simplified-design.md) | Match on True/False in FFI |

### Phase 5 Gate

- [ ] All 50+ Phase 5 tests pass
- [ ] Literal type system handles all cases from 03-core-language.md
- [ ] Operator overloading works (pattern matching, single and multiple definitions)
- [ ] Error codes are consistent and documented
- [ ] Source context formatting is human-readable

---

## End-to-End Integration Tests

| ID | Test | Status | Notes |
|----|------|--------|-------|
| E2E 1 | Fibonacci (fib(10) = 55) | 🔴 | Core and Tao |
| E2E 2 | Church numerals | 🔴 | Core |
| E2E 3 | Higher-order functions | 🔴 | Core |
| E2E 4 | Map and filter | 🔴 | Tao + stdlib |
| E2E 5 | Multi-file with imports | 🔴 | All import variants |
| E2E 6 | Test runner with passing/failing tests | 🔴 | REPL-style tests |

---

## Summary

| Phase | Target Days | Tasks | Test Count | CLI Commands | Status |
|-------|-------------|-------|------------|--------------|--------|
| Phase 1: Lexer + Core Types | 2-3 | 20+ | 77+ | — | ✅ Complete |
| Phase 2: Parser + Type Checker + NBE | 4-5 | 60+ | 907 | 🔴 Not yet | ✅ Mostly done |
| Phase 3: Tao + Desugar + CLI | 4-5 | 37 | 0 | 🔴 Not started | 🔴 Not started |
| Phase 4: Multi-file + Import | 3-4 | 22 | 0 | 🔴 Not started | 🔴 Not started |
| Phase 5: Extended + Polish | 3-4 | 18 | 0 | 🔴 Not started | 🔴 Not started |
| **Total** | **26-32** | **188+** | **783+** | **Phase 2: no CLI yet** | |

**Code metrics:** 13 source files, 907 tests passing, 0 failures.

---

## Recent Changes

| Date | Change |
|------|--------|
| 2026-05-04 | **Test suite audit + 36 new lexer edge case tests.** Added `test/syntax/base_lexer_test_new.gleam` with 36 new edge case tests covering: float edge cases (`.5`, `42.`, `0.0`), identifier edge cases (camelCase, numbers in names, underscores), complex expressions (parenthesized, function calls), unicode handling, block comment edge cases, and span accuracy tests. Fixed known lexer bug: `skip_block_comment` double-increments line counter for newlines (documented in test comments). All 907 tests passing, 0 failures. No compiler warnings. |
| 2026-05-04 | **Test assertion audit in progress.** Identified 350 weak assertions (`case expr -> True _ -> False`) across 17 test files. Strategy: fix highest-impact files first (syntax_test.gleam, infer_test.gleam). Tour example tests verified - all 7 expectation mismatches documented but tests pass. Type defs consolidation planned. |
| 2026-05-02 | **Phase 2: Type inference overhaul + 39 new tests.** Added `VTyp(level)` to `Value` type. Fixed `infer_lit` to return `$Int`/`$Float` as types (not literal values). Fixed `infer_hole` to return separate fresh holes for value and type. Fixed `infer_typ` to return `VTyp(level)`. Fixed `infer_pi` to return `VTyp(0)` (type `*`). Fixed `infer_rcd` to return `VRcdT` as type. Fixed `infer_ctr` to return `VCtr(tag, inferred_type)`. Fixed `infer_type_def` to return `VTyp(0)`. Fixed `infer_rcd_type` to return `VTyp(0)`. Fixed PType pattern matching in eval to handle `VTyp`. Added 39 new tests covering: literal types, type universes, variable scoping, hole inference, lambda types, Pi types, annotation types, record types, constructor types, error cases, FFI calls, TypeDef types, and property tests. Updated 13 existing tests. **829 tests passing, 0 failures.** |
| 2026-05-02 | **Phase 2: Type inference overhaul.** Added `VTyp(level)` to `Value` type. Fixed `infer_lit` to return `$Int`/`$Float` as types (not literal values). Fixed `infer_hole` to return separate fresh holes for value and type. Fixed `infer_typ` to return `VTyp(level)`. Fixed `infer_pi` to return `VTyp(0)` (type `*`). Fixed `infer_rcd` to return `VRcdT` as type. Fixed `infer_ctr` to return `VCtr(tag, inferred_type)`. Fixed `infer_type_def` to return `VTyp(0)`. Fixed `infer_rcd_type` to return `VTyp(0)`. Fixed PType pattern matching in eval to handle `VTyp`. Updated 13 existing tests. **783 tests passing, 0 failures.** |
| 2026-05-02 | **Phase 2: Record type defaults + VRcdT.** `fill_record_defaults()` in `infer.gleam` fills missing record fields from `VRcdT` defaults during `check()`. Added `VRcdT` value type with optional defaults. Updated all modules (unify, subst, generalize, eval, infer, cli). **783 tests passing, 0 failures.** |
| 2026-05-02 | **Phase 2: Tracker reorganized.** Consolidated Phase 2 (was split across 2b/2c/2d sub-sections) into unified numbered sections 2.1–2.21. Removed duplicate task IDs, merged related items, updated all status to reflect 783 passing tests. |
| 2026-05-01 | **Phase 2: Wildcard type support.** `$Int`/`$Float` wildcard matching in `unify.gleam` (match_values) and `eval.gleam` (PType patterns). `$Int` matches any integer literal, `$Float` matches float+int. 15 new tests in unify_test.gleam. **738 tests passing, 0 failures.** |
| 2026-04-30 | **Phase 2: Test assertion audit complete.** All 17 tests that silently passed without `assert` now correctly fail. Added span preservation tests, error path tests (VarUndefined, Not-a-function, shadowing, FFI). Added VTypeDef/nested value/round-trip tests to quote_test. Removed empty minimal_test.gleam. **706 passed, 17 failures.** |
| 2026-04-30 | **Phase 2: Compiler warnings fixed.** Removed unused `debug_parse_01_introduction` and `debug_parse_07_constructors` from tour.gleam. **715 tests passing, 0 failures.** |
| 2026-04-30 | **Phase 2: Sequential expression parsing fixed.** Rewrote `parse_tokens_acc` with `is_continuation_token()` boundary detection. Added PType pattern params (`<1>`, `<x>`). Fixed `parse_type_def_body_with_body` to not consume `#`, `)`, `-`, `>`, `=>` in nested contexts. **715 tests passing, 0 failures.** |
| 2026-04-30 | **Phase 2: Parser critical bug fixes.** Fixed 3 bugs in `src/core/syntax.gleam`: (1) Rcd(()) parsing position bug — `#(rest, 0, ...)` instead of `#(rest, 2, ...)`; (2) `fun` keyword now calls `parse_pi` not `parse_app`; (3) Simplified param_type/domain_type parsing. **711 passed, 12 failures.** |
| 2026-04-28 | **Phase 2: Numeric type support.** Full LiteralType hierarchy ($I8–$I64, $U8–$U64, $F16–$F64), TypRef parsing, FFI call syntax with typed args, TypeDef parsing. All 699 tests passing, 16 failures. |
| 2026-04-27 | **Phase 2: Type inference module.** `src/core/infer.gleam` (570 lines) with bidirectional type checking — `infer()` synthesizes, `check()` verifies. Covers all term forms. 31 tests in infer_test.gleam. **620 tests passing.** |
| 2026-04-27 | **Phase 2: Quote implemented.** `src/core/quote.gleam` with `quote(value)` and `quote_at(value, level)`. 39 tests in quote_test.gleam. **591 tests passing.** |
| 2026-04-27 | **Phase 2: Exhaustiveness + TypeDefs as env values.** `core/exhaustiveness.gleam` + TypeDef/ConstructorDef/VTypeDef in `core/ast.gleam`. Type defs stored as first-class env values. 28 tests in type_defs_test.gleam, 22 in exhaustiveness_test.gleam. **658 tests passing.** |
| 2026-04-27 | **TypeDef/Value refactoring.** Removed `TypeDef` public type from ast.gleam, flattened into function params. TypeDef/VTypeDef use typed params: `params: List(#(String, Term))` / `params: List(#(String, Value))`. Constructors use flat tuples. **654 tests passing.** |
| 2026-04-27 | **Guard truth check refactored.** `is_true_value` → `is_truth(truth_ctr, value)` with configurable `truth_ctr` in State. Default truth constructor is `"True"`. Removes language-specific assumptions from core. **553 tests pass.** |
| 2026-04-27 | **Code quality improvements.** Fixed guard shift bug in subst.gleam. Consolidated ~90 lines of duplicate code (shift_term, shift_term_from, shift_opt → ast.gleam). Removed no-op wrappers, unused bindings. **551 tests pass.** |
| 2026-04-26 | **Phase 2: NBE evaluator implemented.** `src/core/eval.gleam` with `evaluate`, `do_app`, `do_match`, `match_pattern`, `value_to_string`, `lookup_env`. Covers all term-to-value conversions. 73 tests in eval_test.gleam. **545 tests passing.** |
| 2026-04-26 | **Phase 2: Generalization implemented.** `src/core/generalize.gleam` with `free_holes`, `collect_free_levels`, `create_hole_subst`, `replace_holes_with_vars`. 46 tests in generalize_test.gleam. **545 tests passing.** |
| 2026-04-26 | **Phase 2: Substitution implemented.** `src/core/subst.gleam` with `force`, `apply_spine`, `shift_term`, `subst_term_var`, `force_levels_to_indices`. 61 tests in subst_test.gleam. **424 tests passing.** |
| 2026-04-26 | **Phase 2: Unification implemented.** `src/core/unify.gleam` with `unify` and `occurs_check`. 33 tests in unify_test.gleam. **363 tests passing.** |
| 2026-04-26 | **Param removed from AST.** `Param` record type replaced with ` #(String, Term)` tuples for Lam, ` #(String, Value)` for VLam. |
| 2026-04-26 | **Call constructor added.** `Call(name, args, span)` added to Term type. Updated shift_term, term_to_string, VLam string repr. |
| 2026-04-26 | **State cleaned up.** Removed unused fields: lambda_depth, max_steps, step_counter, truth_ctor. **375 tests pass.** |
| 2026-04-26 | **Grammar parse() improved.** Returns descriptive error on parse failure instead of empty errors list. |
| 2026-04-26 | **Grammar DSL critically fixed.** parse() now returns constructed AST (was returning error_node). Tok pattern matches punctuation by value. |
| 2026-04-25 | **MAJOR AST REFACTOR.** Core AST updated: Rcd for records/Unit, Ctr(tag, Rcd(args)) for constructors, Typ(level) for universes, Case(pattern, guard, body). |
| 2026-04-25 | **Parser rewritten.** All parsing functions updated for new syntax: $fn, $let, $match, #Tag, fun(), {x: y}, $Type, $error, ? |
| 2026-04-25 | **Parser combinator DSL implemented.** 11 combinators (tok, kw, op, ref, seq, opt, many, choice, sep_by, parens, delimited). 198 parser combinator tests. |
| 2026-04-24 | Initial tracker created based on revised roadmap |
