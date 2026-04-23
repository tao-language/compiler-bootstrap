# Comprehensive Analysis: Making Core Fully Language-Agnostic

## Executive Summary

The compiler has a clear three-layer architecture (Syntax → Core → Tao), but **Core still contains significant language-specific concerns** that belong in Tao. Additionally, there are several structural issues across the codebase that affect maintainability. This document identifies all issues and proposes concrete fixes.

---

## Part 1: Core Language-Specific Assumptions

### Issue 1.1: Hardcoded Boolean Truth Constructor

**Location:** `core/eval.gleam:19`
```gleam
pub fn eval(ffi: state.FFI, env: ast.Env, term: ast.Term) -> ast.Value {
  eval_with_ctor(ffi, env, term, "True")
}
```

**Problem:** `eval/3` hardcodes `"True"` as the truth constructor. The `eval_with_ctor` variant exists but isn't used by default. This means any language with a different truth constructor (e.g., `"yes"`, `"True'"`) can't use Core's default `eval`.

**Impact:** Every language layer must duplicate or modify eval logic if it doesn't use `"True"`.

**Fix:** Make truth constructor configurable at the `State` level, with `State` defaulting to `"True"`. The main `eval/3` should derive it from `state.truth_ctor`:

```gleam
pub fn eval(ffi: state.FFI, env: ast.Env, term: ast.Term, state: state.State) -> ast.Value {
  eval_with_ctor(ffi, env, term, state.truth_ctor)
}
```

Or better: store `ffi` with its truth constructor so eval can access it.

---

### Issue 1.2: Hardcoded Literal Types in Core

**Location:** `core/ast.gleam:1-18`
```gleam
pub type Literal {
  I32(value: Int)
  I64(value: Int)
  U32(value: Int)
  U64(value: Int)
  F32(value: Float)
  F64(value: Float)
  IntLit(value: Int)
  FloatLit(value: Float)
}

pub type LiteralType {
  I32T
  I64T
  U32T
  U64T
  F32T
  F64T
  ILitT
  FLitT
}
```

**Problem:** Core has **8 literal types baked into its AST**. A different language might want different types (e.g., `BigInt`, `Rational`, or no numeric types at all). The type checker's `typeof_lit/1` function has a hard 8-way match.

**Impact:** Core cannot support arbitrary literal types. Adding a new type requires modifying Core source code.

**Fix:** Move literal types to `LanguageConfig` in Tao:

```gleam
// In language_config.gleam:
pub type LiteralType {
  LiteralType(name: String, tag: String)
}

pub type LanguageConfig {
  LanguageConfig(
    // ...
    literal_types: List(#(String, LiteralType)),  // e.g., #("I32", #("I32", "literal"))
    // ...
  )
}
```

Core should accept `Literal` and `LiteralType` as opaque string tags, with interpretation deferred to the language layer.

---

### Issue 1.3: FFI Builtins Hardcoded in Tao, Not Extensible

**Location:** `tao/ffi.gleam`
```gleam
pub fn tao_ffis() -> state.FFI {
  [
    #("add", state.Builtin(ffi_add, [])),
    #("sub", state.Builtin(ffi_sub, [])),
    // ... 10 fixed builtins
  ]
}
```

**Problem:** FFI is defined as a **fixed list** of builtin functions. There's no mechanism for a language layer to add or remove builtins. While the FFI is in Tao (correct), the builtins are hardcoded as a fixed list rather than being configurable.

**Fix:** Make FFI extensible. Allow languages to compose FFI lists:

```gleam
pub fn tao_ffis(extra: List(#(String, state.Builtin))) -> state.FFI {
  base_ffis() ++ extra
}

fn base_ffis() -> state.FFI {
  [...]
}
```

---

### Issue 1.4: State Defaults Assume Tao

**Location:** `core/state.gleam`
```gleam
pub const initial_state = State(
  truth_ctor: "True",  // Hardcoded for Tao
  ffi: [],              // FFI populated by language layer (good)
)
```

**Problem:** `initial_state` defaults to `"True"` as the truth constructor. This is a **language-specific default** in Core.

**Fix:** Remove the default. Let the language layer set it:

```gleam
pub const initial_state = State(
  truth_ctor: "",  // Empty string — language layer must set
  ffi: [],
)
```

Or better: don't provide `initial_state` at all. Create it from the language config.

---

### Issue 1.5: `is_true_value` Helper in Core

**Location:** `core/ast.gleam:315-319`
```gleam
pub fn is_true_value(value: Value, truth_ctor: String) -> Bool {
  case value {
    VCtrValue(VCtr(tag, _)) if tag == truth_ctor -> True
    _ -> False
  }
}
```

**Problem:** This is a language-specific utility function. Core shouldn't export language-aware helpers.

**Fix:** Move this to Tao's eval or desugar module, where the truth constructor is known from config.

---

### Issue 1.6: Bool Logic in FFI Returns Hardcoded Constructor Names

**Location:** `tao/ffi.gleam:117-120`
```gleam
fn bool_to_value(b: Bool) -> ast.Value {
  case b {
    True -> ast.VCtrValue(ast.VCtr("True", ast.VUnit))
    False -> ast.VCtrValue(ast.VCtr("False", ast.VUnit))
  }
}
```

**Problem:** Comparison operators return `"True"` and `"False"` constructors, which are language-specific names.

**Fix:** Accept the truth/false constructor names as parameters, or read from config.

---

## Part 2: Structural & Code Quality Issues

### Issue 2.1: Massive Code Duplication Across Subsitution Modules

**Pattern:** Three separate `subst_term_with_*` and `subst_value_with_*` functions exist:

| Function | Module | Purpose |
|----------|--------|---------|
| `subst_term_with_implicit_vars` | `subst.gleam` | Replace implicit param indices |
| `subst_value_with_implicit_vars` | `subst.gleam` | Same for values |
| `subst_value_with_hole_vars` | `generalize.gleam` | Replace hole → HVar |
| `subst_term_with_hole_vars` | `generalize.gleam` | Same for terms |

**Problem:** Each function has **nearly identical structure** — a term/value traversal that case-matches on every constructor. This is the same pattern repeated 6 times across 2 files with slight variations.

**Fix:** Create a generic substitution framework:

```gleam
// core/subst.gleam
pub type SubstRule {
  SubstRule(
    on_hole: fn(Int, Span) -> Option(Term),
    on_hvar: fn(Int) -> Option(Value),
    on_hvar_val: fn(Int) -> Option(Term),
  )
}

pub fn subst_term(term: Term, rule: SubstRule) -> Term {
  // Generic traversal
}
```

This reduces 6 implementations → 1 generic + 6 simple rules.

---

### Issue 2.2: Duplicate `shift_hvar_term` / `shift_hvar` / `shift_hvar_loop` Duplication

**Problem:** Core has multiple nearly-identical shift functions:

1. `shift_term/2` in `ast.gleam` — shifts De Bruijn indices
2. `shift_hvar_term/3` in `infer.gleam` — shifts HVar indices relative to offset
3. `shift_hvar/2` in `infer.gleam` — shifts HVar indices in values

These have overlapping concerns and differ in subtle ways.

**Fix:** Consolidate into a single `shift` module:

```gleam
// core/shift.gleam
pub fn shift_term(term: Term, shift: Int) -> Term
pub fn shift_term_relative(term: Term, shift: Int, offset: Int) -> Term
pub fn shift_value(value: Value, shift: Int) -> Value
pub fn shift_value_relative(value: Value, shift: Int, offset: Int) -> Value
```

---

### Issue 2.3: Massive Function Bodies with Deep Nesting

**Location:** `core/infer.gleam` — entire file
**Location:** `tao/desugar.gleam` — entire file

**Problem:** Many functions in `infer.gleam` are 50-100 lines with deeply nested pattern matching. For example, `infer_lam/5` (lines 172-264) is a single monolithic function.

**Fix:** Extract sub-steps into named helper functions:

```gleam
// Before: infer_lam does everything
fn infer_lam(...) -> #(Value, Type, State) {
  // 90 lines of mixed: implicit holes, domain eval, body inference,
  // generalization, implicit param handling, quoting, VPi construction
}

// After: clear steps
fn infer_lam(...) -> #(Value, Type, State) {
  let s = setup_implicit_params(implicit, s)
  let domain_val = eval_domain(param_ty_term, s)
  let s = increment_level(s)
  let s = increment_lambda_depth(s)
  let #(body_val, body_ty, s) = infer_body(body, s)
  let s = decrement_lambda_depth(s)
  let s = decrement_level(s)
  generalize_holes_and_build_result(...)
}
```

---

### Issue 2.4: Error Handling Is Inconsistent

**Pattern:** Three different error propagation styles coexist:

1. **State.errors list** (used by type checker) — accumulates errors
2. **VErr sentinel values** (used by evaluator) — propagates errors through computation
3. **Result types** (used by compiler) — early termination

**Problem:** The type checker and evaluator mix these paradigms. For example, `infer/1` returns `VErr` values when errors occur, but also accumulates errors in `State.errors`. This makes it unclear whether an error has been handled.

**Fix:** Use a consistent approach:
- **Type checking:** State.errors accumulation only (no VErr sentinels in return values)
- **Evaluation:** VErr sentinels only (don't accumulate errors in state)
- **Compiler:** Result types for parse/compile errors

---

### Issue 2.5: `eval` Calls Inside Type Checker

**Location:** `core/infer.gleam` — multiple places call `eval.eval`
```gleam
// Inside infer/1:
let arg_val = eval.eval(s.ffi, env, arg)
let ret_ty_val = eval.eval(s.ffi, env, ctr.ret_ty)

// Inside check/1:
let ty_val = eval.eval(s.ffi, get_env(s), ann_ty)
```

**Problem:** The type checker calls the evaluator during type inference/checking. This violates the abstraction: the type checker should operate on syntax (Terms), not evaluate them. Evaluation during type checking can cause:
- Non-termination if a term is not normalizable
- Performance issues (evaluating during type checking is redundant)
- Subtle bugs when evaluated values differ from expected syntactic behavior

**Fix:** Only evaluate type annotations that are **explicitly annotated** (Ann nodes), not during inference. Use a separate normalization pass if needed.

---

### Issue 2.6: `infer_call` Has Incomplete Logic

**Location:** `core/infer.gleam:423-456`
```gleam
fn infer_call(
  s: state.State,
  name: String,
  typed_args: List(#(ast.Term, ast.Term)),
  ret: ast.Term,
  span: Span,
) -> #(ast.Value, ast.Type, state.State) {
  // ...
  case list.key_find(s.ffi, name) {
    Ok(state.Builtin(impl, _)) -> {
      case impl(arg_vals) {
        Some(result_val) -> {
          // Derive actual result type from the value
          let actual_result_ty = case result_val {
            ast.VCtrValue(ctr) -> {
              case list.key_find(s.ctrs, ctr.tag) {
                Ok(c) -> eval.eval(s.ffi, get_env(s), c.ret_ty)
                Error(Nil) -> value_type(arg_vals, arg_tys)
              }
            }
            ast.VLit(v) -> typeof_lit(v)
            ast.VLitT(lit_ty) -> ast.VLitT(lit_ty)
            ast.VUnit -> ast.VTyp(0)
            _ -> value_type(arg_vals, arg_tys)
          }
          #(result_val, actual_result_ty, s)
        }
        None -> {
          let #(result_ty_hole, s) = new_hole(s)
          #(ast.VCall(name: name, args: arg_vals, ret: expected_result_ty), result_ty_hole, s)
        }
      }
    }
    Error(Nil) -> {
      #(ast.VCall(name: name, args: arg_vals, ret: expected_result_ty), expected_result_ty, s)
    }
  }
}
```

**Problem:** The inferred type is **derived from the runtime value** rather than being computed from the function's type signature. This means:
- Type errors from FFI calls are not caught
- The return type depends on evaluation order
- Two equivalent FFI calls might produce different types

**Fix:** FFI should have explicit type signatures in the FFI registry:

```gleam
pub type Builtin {
  Builtin(
    impl: fn(List(ast.Value)) -> Option(ast.Value),
    args_types: List(ast.Type),
    ret_type: ast.Type,
    required_permissions: List(Permission),
  )
}
```

---

### Issue 2.7: Redundant `type_to_string` / `value_to_string` in Error Formatter

**Location:** `core/error_formatter.gleam`
```gleam
fn type_to_string(ty: ast.Type) -> String { ... }
fn value_to_string(val: ast.Value) -> String { ... }
fn literal_from_value(lit: ast.Literal) -> String { ... }
fn literal_type_to_string(lit: ast.LiteralType) -> String { ... }
fn pattern_to_string(pattern: ast.Pattern) -> String { ... }
fn literal_to_string(lit: ast.Literal) -> String { ... }
fn float_to_string(f: Float) -> String { ... }
fn head_to_string(head: ast.Head) -> String { ... }
```

**Problem:** The file already has `core/ast_string.gleam` for these utilities, but `error_formatter.gleam` duplicates much of the logic.

**Fix:** Import and use `core/ast_string` consistently.

---

### Issue 2.8: `infer_match` Doesn't Use `truth_ctor` from State

**Location:** `core/infer.gleam:339-371`
```gleam
pub fn infer_match(
  s: state.State,
  arg: ast.Term,
  motive: ast.Term,
  cases: List(ast.Case),
  span: Span,
) -> #(ast.Value, ast.Type, state.State) {
  // ...
  // The guard evaluation uses hardcoded "True" truth constructor
  // But it should use s.truth_ctor
}
```

**Problem:** Match guard evaluation calls `eval_with_ctor` from `infer_match` but doesn't pass `s.truth_ctor`. Guards will only work if the truth constructor is `"True"`.

**Fix:** Pass `s.truth_ctor` to the evaluation functions used in match guards.

---

### Issue 2.9: `check` Function Has Duplicate Logic with `infer`

**Location:** `core/infer.gleam:1261-1336` (check function)

**Problem:** The `check` function duplicates much of the logic from `infer`. For example, both handle `Fix` and `Lam` nodes separately with nearly identical code paths.

**Fix:** Refactor to use a shared pattern:

```gleam
fn check(
  s: State,
  term: Term,
  expected_ty: Type,
  ty_span: Span,
) -> #(Value, State) {
  case term {
    // Check-specific cases (Lam with Pi, Lit coercion, etc.)
    _ -> {
      // Default: infer, then unify
      let #(val, ty, s2) = infer(s, term)
      unify_result(s2, ty, expected_ty, get_span(term), ty_span)
    }
  }
}
```

---

## Part 3: Tao-Specific Issues

### Issue 3.1: Implicit Prelude Imports Are Implicitly Conditional

**Location:** `tao/desugar.gleam:228-239`
```gleam
let has_type_defs = has_type_definitions(module.body)
let prelude_imports = case has_type_defs {
  True -> []
  False -> create_implicit_prelude_imports(dc.global, module.span)
}
```

**Problem:** Modules that define their own types get NO prelude imports. This means `type Foo = Bar` won't have access to Prelude types like `String`, `Int`, etc. The logic is inconsistent — why should defining a type prevent importing prelude?

**Fix:** Always include prelude imports. If a module defines its own `Bool`, it will shadow the prelude's `Bool` (which is correct). Don't skip prelude imports.

---

### Issue 3.2: `merge_prelude_ctr_env` Scans Dict by Path Prefix

**Location:** `tao/desugar.gleam:441-460`
```gleam
fn get_prelude_module_paths(global: GlobalContext) -> List(String) {
  case global.modules |> dict.to_list() {
    [] -> []
    [pair, ..rest] -> {
      let #(path, _) = pair
      case string.starts_with(path, "prelude/") {
        True -> [path, ..get_prelude_module_paths_loop(rest)]
        False -> get_prelude_module_paths_loop(rest)
      }
    }
  }
}
```

**Problem:** This iterates through ALL modules looking for `"prelude/"` prefix. If modules are not stored in order, this is O(n) every time.

**Fix:** Store prelude modules separately in `GlobalContext`:

```gleam
pub type GlobalContext {
  GlobalContext(
    modules: Dict(String, ModuleRef),
    prelude_modules: List(String),  // Fast lookup
    current_module: Option(String),
  )
}
```

---

### Issue 3.3: `exprs_to_stmts` Is Duplicated in Two Files

**Locations:** `tao/global_context.gleam:313-367` and `tao/compiler.gleam:147-219`

**Problem:** These two functions are nearly identical but in different files. They differ slightly (compiler has more cases), but the overlap is significant.

**Fix:** Create a shared utility module or move both into one file.

---

### Issue 3.4: `get_expr_span` Is Duplicated

**Locations:** `tao/global_context.gleam:243-259` and `tao/compiler.gleam:131-146`

**Problem:** Two identical functions.

**Fix:** Extract to shared utility.

---

### Issue 3.5: No Separation Between Import Resolution and Desugaring

**Problem:** `desugar_import` (in desugar.gleam) directly accesses the global context to:
1. Look up imported modules
2. Extract function bodies
3. Create module records

This couples import resolution tightly to desugaring.

**Fix:** Separate concerns:
1. **Import resolution:** Resolve `import foo as *` → actual module path
2. **Desugaring:** Use resolved imports to generate Core terms

---

## Part 4: Recommendations Priority

### P0: Critical (Breaking correctness if wrong)

| # | Issue | Impact |
|---|-------|--------|
| 1.6 | `bool_to_value` hardcodes `"True"/"False"` | FFI returns wrong constructors for non-Tao languages |
| 1.1 | `eval` hardcodes `"True"` truth constructor | Match guards won't work for non-default truth constructors |
| 2.5 | `eval` called during type checking | Potential non-termination, performance issues |
| 2.6 | `infer_call` derives types from runtime values | Type errors not caught, non-deterministic types |

### P1: High (Significant maintainability issues)

| # | Issue | Impact |
|---|-------|--------|
| 1.2 | Literal types hardcoded in Core AST | Cannot support new types without modifying Core |
| 2.1 | Tripled substitution code | Bug fixes must be applied 3× |
| 2.2 | Multiple shift implementations | Inconsistent behavior between shifts |
| 1.5 | `is_true_value` in Core | Language-specific logic in abstraction layer |

### P2: Medium (Code quality improvements)

| # | Issue | Impact |
|---|-------|--------|
| 2.3 | Massive function bodies | Hard to read, hard to test |
| 2.4 | Inconsistent error handling | Confusing to debug |
| 2.8 | `truth_ctor` not used in match | Guard evaluation broken for non-Tao |
| 3.1 | Conditional prelude imports | Inconsistent module behavior |

### P3: Low (Cleanups)

| # | Issue | Impact |
|---|-------|--------|
| 2.7 | Duplicate string utilities | Wasted LOC |
| 2.9 | Duplicate `check`/`infer` logic | Maintenance overhead |
| 3.3 | Duplicate `exprs_to_stmts` | DRY violation |
| 3.4 | Duplicate `get_expr_span` | DRY violation |

---

## Part 5: Refactoring Roadmap

### Phase 1: Make Core Truly Language-Agnostic (P0 + P1 items)

```
1. Extract truth_ctor from State → make eval/eval_with_ctor the only public API
2. Move bool_to_value to Tao (accept truth/false constructors as params)
3. Move is_true_value from core/ast to Tao
4. Add explicit type signatures to FFI registry
5. Remove eval calls from type checker (or limit to explicit annotations only)
6. Parameterize literal types in Core via language config
```

### Phase 2: Eliminate Duplication (P1 + P2 items)

```
1. Create core/shift.gleam with unified shift operations
2. Create core/subst_rule.gleam with generic substitution framework
3. Consolidate error string utilities into core/ast_string
4. Extract shared exprs_to_stmts and get_expr_span to tao/shared
5. Add prelude_modules list to GlobalContext for O(1) lookup
```

### Phase 3: Simplify Core Logic (P2 items)

```
1. Break up infer_lam/5 into named sub-steps
2. Break up infer/1 into pattern + dispatch structure
3. Extract match guard evaluation to a separate function
4. Clean up check/infer duplication with shared dispatch
```

### Phase 4: Separate Tao Concerns (P3 items)

```
1. Separate import resolution from desugaring
2. Consolidate prelude import logic
3. Fix conditional prelude import behavior
4. Remove dead/unused code paths
```

---

## Appendix: Files That Need Changes

| File | Changes |
|------|---------|
| `core/eval.gleam` | Remove hardcoded `"True"` default; accept truth_ctor from State |
| `core/ast.gleam` | Move `is_true_value` to Tao; consider making literal types extensible |
| `core/state.gleam` | Remove hardcoded `truth_ctor: "True"` default |
| `core/infer.gleam` | Remove eval calls during type checking; use `s.truth_ctor` in match |
| `core/subst.gleam` | Refactor with generic substitution framework |
| `tao/ffi.gleam` | Parameterize `bool_to_value`; make FFI extensible |
| `tao/language_config.gleam` | Add literal_types, truth_constructor, bool_constructors |
| `tao/desugar.gleam` | Remove conditional prelude imports; use truth_ctor from config |
| `tao/global_context.gleam` | Add prelude_modules list; consolidate shared utilities |
| `tao/compiler.gleam` | Remove duplicate `exprs_to_stmts` / `get_expr_span` |
