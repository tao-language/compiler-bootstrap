# Comprehensive Analysis: Cleanup & Simplification

## Executive Summary

The codebase is a working prototype with a clear three-layer architecture (Syntax → Core → Tao). However, it suffers from **7 categories of issues** that prevent it from being a clean, maintainable prototype. This analysis prioritizes fixes by impact and effort, always preferring simplicity and readability over complexity.

**Current State:**
- ✅ 14 source files, 10 test files, 30 tests passing
- ❌ 90+ compiler warnings
- ❌ Multiple architectural mismatches with the design plan
- ❌ Placeholder code mixed with real logic
- ❌ De Bruijn index/level confusion in evaluator

---

## Category 1: Critical - De Bruijn Index/Level Confusion

### Problem
The evaluator (`core/eval.gleam`) fundamentally misunderstands the relationship between De Bruijn indices (syntax) and De Bruijn levels (semantics):

**Current code:**
```gleam
// eval.gleam line 56-60
fn eval_var(state: State, idx: Int) -> Result(Value, String) {
  case env_to_list(state), idx {
    [val], 0 -> Ok(val)
    [_, ..rest], n -> eval_var(state, n - 1)
    _, _ -> Error("Variable not found")
  }
}
```

**Issues:**
1. `env_to_list` returns an empty list — it's a no-op placeholder
2. The function treats `idx` as a De Bruijn **level** (0 = innermost), but `Term.Var` uses indices (0 = closest binder above)
3. There's no environment passed to `eval_var`, so it can't actually look up variable values
4. `eval_app` on line 72 discards the argument value: `eval_term(state, body)` instead of `eval_term(new_state, body)` with `env` extended

**Impact:** The evaluator **never actually evaluates function application correctly**. Lambdas always reduce to `IntVal(0)` because the body is evaluated in the wrong environment.

### Fix (Low effort, high impact)
```gleam
// New signature: evaluator receives an environment of values (De Bruijn levels)
pub fn eval(env: List(Value), term: Term) -> Result(Value, String) {
  eval_term(env, term)
}

fn eval_term(env: List(Value), term: Term) -> Result(Value, String) {
  case term {
    Var(_, idx) -> eval_var(env, idx)
    Lam(param, body) -> Ok(Closure(param: param, body: body, env: env))
    App(fun, arg) -> {
      case eval_term(env, fun) {
        Ok(Closure(p, b, Closure_env)) -> {
          case eval_term(env, arg) {
            Ok(arg_val) -> eval_term([arg_val, ..Closure_env], b)
            Error(e) -> Error(e)
          }
        }
        Ok(_) -> Error("Not a function")
        Error(e) -> Error(e)
      }
    }
    // ... rest unchanged
  }
}

fn eval_var(env: List(Value), idx: Int) -> Result(Value, String) {
  case env_drop_to(env, idx) {
    [val] -> Ok(val)
    _ -> Error("Variable not found")
  }
}

fn env_drop_to(env: List(Value), idx: Int) -> List(Value) {
  case env, idx {
    _, 0 -> env
    [_, ..rest], _ -> env_drop_to(rest, idx - 1)
    _ -> []
  }
}
```

**Why this works:** De Bruijn **levels** are absolute: `Var(0)` always means the innermost binder. The evaluator works with levels directly — no translation needed. The environment is a simple list where index 0 is the innermost binding.

---

## Category 2: Critical - Broken Application Evaluation

### Problem
`eval_app` (line 72-76) never passes the evaluated argument to the body:
```gleam
fn eval_app(state: State, fun: Value, arg_val: Value) -> Result(Value, String) {
  case fun {
    Closure(_, body, _) -> eval_term(state, body)  // arg_val discarded!
    _ -> Error("Not a function")
  }
}
```

The argument value is evaluated and passed as a parameter, but then **never used**. The body is evaluated in the current state without the argument bound.

### Fix
This is fixed by the De Bruijn fix above — when the lambda body is evaluated, it should be in an environment that includes the argument value.

---

## Category 3: Critical - Type Checker is a No-Op

### Problem
`core/infer.gleam` has `check_term` that just calls `infer_term` without unifying types:
```gleam
pub fn check_term(state: State, term: Term, expected: Type) -> Result(State, String) {
  case infer_term(state, term) {
    Ok(st) -> {
      // TODO: Implement full type checking
      Ok(st)  // Always succeeds
    }
    Error(e) -> Error(e)
  }
}
```

Also, `infer_intlit`, `infer_floatlit`, `infer_stringlit`, `infer_ctr` all just return `Ok(state)` without producing any type. The type checker **never detects type errors**.

### Fix (Aligns with design plan)
The design plan specifies bidirectional checking with `infer` (synthesize) and `check` (verify). For the prototype:
```gleam
/// Infer type - returns a fresh hole ID that will be resolved by unification
pub fn infer_term(state: State, term: Term) -> Result(#(State, Type), String) {
  case term {
    Var(name, _) -> infer_var(state, name)
    Lam(param, body) -> infer_lam(state, param, body)
    App(fun, arg) -> infer_app(state, fun, arg)
    Lit(LInt(_)) -> Ok(#(state, TVar(-1)))  // Synthesize type hole
    Lit(LFloat(_)) -> Ok(#(state, TVar(-1)))
    Lit(LString(_)) -> Ok(#(state, TVar(-1)))
    Ctr(_, _) -> infer_ctr(state)
    Match(scr, cases) -> infer_match(state, scr, cases)
    Hole(id) -> Ok(#(state, TVar(id)))
    Err(message) -> Error(message)
  }
}

/// Check term against expected type
pub fn check_term(state: State, term: Term, expected: Type) -> Result(#(State, Type), String) {
  case infer_term(state, term) {
    Ok(#(st, inferred)) -> unify.type_unify(st, inferred, expected)
    Error(e) -> Error(e)
  }
}
```

**Key insight:** Instead of storing types in the environment, use **holes** with negative IDs for synthesized types. The unifier resolves them. This matches the design plan's approach.

---

## Category 4: Critical - Desugarer Produces Invalid Terms

### Problem
Multiple desugarer functions produce placeholder/incorrect output:

**desugar_match** (line 120-127):
```gleam
fn desugar_match(arg, cases, env) -> Result(#(Term, List(#(String, Type))), String) {
  case desugar_expr(arg, env) {
    Ok(#(arg_term, new_env)) -> {
      // Placeholder: ignores actual cases, returns dummy match
      Ok(#(Match(scrutinee: arg_term, cases: [
        Case(pattern: PatVar("_"), body: Lit(LInt(0))
      ]), new_env))
    }
    Error(e) -> Error(e)
  }
}
```

**desugar_binop** (line 85-102):
```gleam
fn desugar_binop(left, op, right, env) -> Result(#(Term, ...), String) {
  // Bug: uses Var(func_name, 0) but func_name is not in env
  Ok(#(App(
    fun: Var(name: func_name, index: 0),
    arg: App(fun: Var(name: func_name, index: 0), arg: right_term),
  ), final_env))
}
```
This produces `+ + 1` instead of `+(+ left right)`.

**desugar_record** (line 228-240):
```gleam
fn desugar_record(fields, env) -> Result(#(Term, ...), String) {
  // Bug: ignores field_terms, always returns dummy
  Ok(#(Ctr(tag: "record", args: [Lit(LInt(0))]), env))
}
```

**desugar_dot** (line 243-249):
```gleam
fn desugar_dot(record, field, env) -> Result(#(Term, ...), String) {
  // Bug: discards desugared record, returns Var(field, 0)
  Ok(#(Var(name: field, index: 0), new_env))
}
```

### Fix
Implement each function properly:

```gleam
fn desugar_match(arg, cases, env) -> Result(#(Term, List(#(String, Type))), String) {
  case desugar_expr(arg, env) {
    Ok(#(arg_term, new_env)) -> {
      case list.map_try(cases, fn(c) {
        case desugar_clause(c, new_env) {
          Ok(clause) -> Ok(clause)
          Error(e) -> Error(e)
        }
      }) {
        Ok(case_list) -> Ok(#(Match(scrutinee: arg_term, cases: case_list), new_env))
        Error(e) -> Error(e)
      }
    }
    Error(e) -> Error(e)
  }
}

fn desugar_binop(left, op, right, env) -> Result(#(Term, ...), String) {
  case desugar_expr(left, env) {
    Ok(#(left_term, new_env)) ->
      case desugar_expr(right, new_env) {
        Ok(#(right_term, final_env)) -> {
          // + a b  →  (λ+) (+ a b)  where (+) is looked up in env
          case env_index(final_env, binop_to_func_name(op), 0) {
            Ok(idx) -> Ok(#(
              App(
                fun: Var(name: binop_to_func_name(op), index: idx),
                arg: App(fun: Var(name: binop_to_func_name(op), index: idx), arg: right_term),
              ),
              final_env
            ))
            Error(e) -> Error(e)
          }
        }
        Error(e) -> Error(e)
      }
    Error(e) -> Error(e)
  }
}
```

---

## Category 5: Important - Type System Inconsistencies

### Problem
`core/ast.gleam` has **two different Literal types**:

```gleam
pub type Literal {
  LInt(value: Int)
  LFloat(value: Float)
  LString(value: String)
}
```

But `tao/ast.gleam` has:
```gleam
pub type Literal {
  IntLit(value: Int)
  FloatLit(value: Float)
  StringLit(value: String)
}
```

This duplication serves no purpose — both are simple value containers. The design plan explicitly states:
> **Generic Literals**: Start with single `Int`, `Float`, and `String` types

### Fix (Aligns with design plan)
Remove `tao/ast.gleam`'s `Literal` type entirely. Use `core/ast.Literal` everywhere:

```gleam
// In tao/ast.gleam, remove:
// pub type Literal { IntLit... FloatLit... StringLit... }

// In tao/desugar.gleam, replace term_from_literal:
fn term_from_literal(lit: core.ast.Literal) -> Term {
  case lit {
    core.ast.LInt(n) -> Lit(value: core.ast.LInt(n))
    core.ast.LFloat(n) -> Lit(value: core.ast.LFloat(n))
    core.ast.LString(s) -> Lit(value: core.ast.LString(s))
  }
}
```

Or better yet, add the literal constructors directly to `tao/ast.gleam`:
```gleam
pub type Literal {
  LInt(value: Int)
  LFloat(value: Float)
  LString(value: String)
}
```

This eliminates the `term_from_literal` wrapper entirely.

---

## Category 6: Important - State Management is Broken

### Problem
`state.gleam` has `new_state` and `push_binding` that return `State` but don't update all fields:

```gleam
pub fn push_binding(state: State, name: String, typ: Type) -> State {
  State(..state, env: Env(
    bindings: [ #(name, typ), ..state.env.bindings ],
    ffi: state.env.ffi,
  ))
}
```

This is correct, but `infer.gleam` doesn't use it:
```gleam
fn infer_lam(state, param, body) -> Result(State, String) {
  let new_state = state.State(
    env: state.State(..state).env,  // ❌ Doesn't add param binding!
    errors: state.State(..state).errors,
    hole_bindings: state.State(..state).hole_bindings,
  )
  // ...
}
```

Also, `state.gleam` has `env_to_list` in `eval.gleam` which returns `[]`:
```gleam
fn env_to_list(state: state.State) -> List(Value) {
  []  // ❌ Never actually converts environment
}
```

### Fix (Aligns with design plan)
The design plan specifies a simpler `State`:
```gleam
pub type State {
  State(
    env: Env,
    errors: List(TypeError),
    hole_bindings: List(#(HoleId, Type)),
  )
}
```

This is already the case. The fix is to actually use the environment in the evaluator and type checker:

```gleam
// In infer.gleam, fix infer_lam:
fn infer_lam(state: State, param: String, body: Term) -> Result(#(State, Type), String) {
  let new_state = state.push_binding(param, TVar(-1))  // Synthesize type hole for param
  case infer_term(new_state, body) {
    Ok(#(body_st, body_type)) -> {
      // The type is Π(param: hole_type).body_type
      let pi_type = TPi(param: param, arg: TVar(-1), body: body_type)
      Ok(#(body_st, pi_type))
    }
    Error(e) -> Error(e)
  }
}
```

---

## Category 7: Important - Formatter is Incomplete

### Problem
`grammar.gleam` has a `format_flat` function that ignores `Nest` and `Group`:
```gleam
pub fn format_flat(doc: Doc) -> String {
  case doc {
    Nest(n, inner) -> format_flat(inner)  // ❌ Ignores indentation
    Group(inner) -> format_flat(inner)    // ❌ Always flattens
    // ...
  }
}
```

The design plan says:
> **No fancy error formatting** — Basic error messages with spans are sufficient for a prototype

### Decision
For the prototype, **remove the formatter entirely**. It adds ~150 lines of code that does nothing useful. Add it later when the core loop works.

```gleam
// Remove from grammar.gleam:
// - All Doc type constructors except Text
// - empty(), text(), line(), space(), hardline()
// - concat(), append(), group(), nest()
// - join(), space_sep(), comma_sep()
// - parens(), braces(), brackets()
// - format_flat(), format_doc()

// Keep only the parser combinators
```

---

## Category 8: Cleanup - Naming Inconsistencies

### Problem
Inconsistent naming across the codebase:

| File | Type | Issue |
|------|------|-------|
| `core/ast.gleam` | `Type.TVar(id)` | Uses numeric ID, not name |
| `tao/ast.gleam` | `TypeAst.TVar(name)` | Uses string name |
| `core/eval.gleam` | `Value.Closure(param, body, env)` | `env` is List(Value) |
| `core/infer.gleam` | `infer_term` returns `State` | Should return `#(State, Type)` |
| `tao/desugar.gleam` | `env_index` | Should be `lookup_env` |

### Fix (Aligns with design plan)
```gleam
// Standardize on:
// - core/ast.Type.TVar(name: String)  // variable by name, resolved by type checker
// - core/state.Env.bindings: List(#(String, Type))  // name → type
// - core/ast.Term.Var(index: Int)  // De Bruijn index only (no name needed)

// This eliminates the need for name in Term.Var, simplifying substitution
```

But for the prototype, **keep the current naming** and add TODO comments. Renaming now would require touching 10+ files.

---

## Category 9: Cleanup - Unused Code

### Problem
Several modules are essentially no-ops:

| Module | Status | Action |
|--------|--------|--------|
| `core/generalize.gleam` | **Missing** (not in repo) | Create stub or remove from plan |
| `core/subst.gleam` | **Missing** | Create stub or remove from plan |
| `core/error.gleam` | **Missing** | Create stub or remove from plan |
| `core/ast_string.gleam` | **Missing** | Create stub or remove from plan |
| `tao/test_parser.gleam` | **Missing** | Merge into test_api |
| `tao/test_reporter.gleam` | **Missing** | Merge into test_api |
| `tao/test_filter.gleam` | **Missing** | Merge into test_api |
| `syntax/source_snippet.gleam` | **Missing** | Merge into grammar |
| `syntax/error_formatter.gleam` | **Missing** | Merge into grammar |
| `tao/import_ast.gleam` | **Missing** | Merge into import_resolver |

The design plan specifies these should be merged or removed. Currently they don't exist, which is correct for the prototype.

### Fix
**Leave them removed.** The design plan explicitly cuts these. Add them back only when needed.

---

## Category 10: Cleanup - Excessive Warnings

### Problem
90+ compiler warnings from unused imports, unused variables, and pattern matching issues.

### Quick Wins (Low effort)

**1. Remove unused imports from `compiler.gleam`:**
```gleam
// Before:
import core/ast.{type Term, type Value, Var, Lam, App, Lit, Ctr, Match, Hole, Err, 
                 IntVal, FloatVal, StringVal, Closure, CtrVal, LitVal, HoleVal, ErrVal, 
                 LInt, LFloat, LString}

// After (only keep what's used):
import core/ast.{type Term, type Value, Lit, Hole, Err, LInt, LFloat, LString,
                 IntVal, FloatVal, StringVal, Closure, CtrVal, LitVal, HoleVal, ErrVal}
```

**2. Fix unused variables in `desugar.gleam`:**
```gleam
// Before:
fn desugar_lambda(params, body, env) -> Result(#(Term, List(#(String, Type))), String) {
  case params {
    [param] -> {
      let param_env = list.append(env, [ #(param.name, TVar(0)) ])
      // param.name is used, but param.type_ is not
      // ...
    }
  }
}

// After (rename to avoid warning):
fn desugar_lambda(params, body, env) -> Result(#(Term, List(#(String, Type))), String) {
  case params {
    #[param, ..] -> {
      let param_env = list.append(env, [ #(param.name, TVar(0)) ])
      // ...
    }
  }
}
```

**3. Remove `gleam/list` and `gleam/int` from `infer.gleam` (unused):**
```gleam
// Remove these imports - they're not used
import gleam/list  // ❌ unused
import gleam/int   // ❌ unused
```

Wait, `gleam/int` **is** used in `type_to_string`. Let me check:
```gleam
"Int" <> int.to_string(id)
```
So `gleam/int` is used. `gleam/list` is not used.

---

## Prioritized Action Plan

### Phase 1: Fix Core Correctness (2-3 days)

| Task | Effort | Impact |
|------|--------|--------|
| Fix `eval.gleam` De Bruijn levels | 2h | **Critical** — evaluator works |
| Fix `eval_app` argument passing | 1h | **Critical** — function application works |
| Fix `env_to_list` or remove it | 15m | **Critical** — no more empty env |
| Fix `check_term` unification | 2h | **Critical** — type errors detected |
| Fix `infer_term` return type | 1h | **Critical** — types are produced |
| Fix `desugar_match` | 1h | **Important** — matches work |
| Fix `desugar_binop` | 1h | **Important** — operators work |
| Fix `desugar_record` | 30m | **Important** — records work |
| Fix `desugar_dot` | 30m | **Important** — field access works |

**Total: ~9.5 hours**

### Phase 2: Align with Design Plan (1-2 days)

| Task | Effort | Impact |
|------|--------|--------|
| Remove formatter from `grammar.gleam` | 30m | **Cleanup** — less code |
| Remove `tao/ast.Literal` duplication | 30m | **Cleanup** — single source of truth |
| Remove unused imports (compiler, infer) | 30m | **Cleanup** — fewer warnings |
| Add TODO comments to placeholder code | 1h | **Maintainability** — clear roadmap |
| Create stub files for missing modules | 30m | **Completeness** — matches design plan |

**Total: ~4 hours**

### Phase 3: Improve Tests (1-2 days)

| Task | Effort | Impact |
|------|--------|--------|
| Add evaluator tests (lambda, app, NBE) | 2h | **Core** — verifies NBE |
| Add type checker tests (Pi, App, unification) | 2h | **Core** — verifies type safety |
| Add desugarer tests (match, binop, record) | 1h | **Tao** — verifies desugaring |
| Add compiler integration tests | 2h | **End-to-end** — verifies full pipeline |
| Fix existing tests to match new APIs | 1h | **Tests** — all tests pass |

**Total: ~8 hours**

### Phase 4: Polish (1 day)

| Task | Effort | Impact |
|------|--------|--------|
| Fix remaining warnings | 2h | **Quality** — clean build |
| Standardize naming (where easy) | 2h | **Readability** — consistent style |
| Add documentation to public APIs | 1h | **Maintainability** — self-documenting |
| Performance profiling | 1h | **Optimization** — find bottlenecks |

**Total: ~6 hours**

---

## Expected Results After Cleanup

| Metric | Before | After |
|--------|--------|-------|
| Compiler errors | 0 | 0 |
| Compiler warnings | 90+ | <10 |
| Working evaluator | ❌ | ✅ (NBE) |
| Working type checker | ❌ | ✅ (bidirectional) |
| Working desugarer | ⚠️ (partial) | ✅ (all features) |
| Test count | 30 | ~100 |
| Lines of dead code | ~200 | ~50 |

---

## Principles for Implementation

1. **One small change at a time** — Each commit should fix one issue and have passing tests.
2. **Write tests first** — When fixing a bug, write a failing test, then fix the code.
3. **Don't refactor while fixing** — If you need to refactor to fix a bug, do it in a separate commit.
4. **Align with the design plan** — The simplified design is the source of truth.
5. **Prefer simple over clever** — A straightforward implementation that works is better than a clever one that doesn't.
6. **Document decisions** — Add TODO comments for known issues so they don't get forgotten.

---

## What NOT to Do

1. **Don't add a visitor pattern** — The design plan explicitly cuts this.
2. **Don't add error codes** — Descriptive messages are sufficient for a prototype.
3. **Don't add golden tests** — Focus on correctness tests first.
4. **Don't add comptime** — It adds significant complexity.
5. **Don't add streams/generators** — Can be a library later.
6. **Don't split Int/Float into I32/I64/F32/F64** — Start with generic types.
7. **Don't add fancy error formatting** — Basic messages with spans are enough.
8. **Don't add color output** — Not essential for a prototype.

---

## Summary

The codebase is a **working skeleton** with the right architecture but broken internals. The priority is:

1. **Fix the evaluator** so that `eval(Closure, arg)` actually applies the argument
2. **Fix the type checker** so that it produces and checks types
3. **Fix the desugarer** so that all Tao features compile correctly
4. **Clean up** unused code, warnings, and naming inconsistencies
5. **Add tests** to verify the fixes

Once these are done, the prototype will have a **working core loop**: write Tao code → parse → desugar → type check → evaluate → see output.
