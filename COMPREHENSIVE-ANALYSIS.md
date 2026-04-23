# Comprehensive Analysis: Hardcoded Assumptions, Dummy Spans, and Architecture Issues

## Executive Summary

The codebase is well-structured with a clear separation between Core (language-agnostic) and Tao (language-specific). The prelude loading mechanism via `with_prelude()` is correctly designed. However, there are **four categories of issues** that need addressing:

| Category | Severity | Count | Files Affected |
|----------|----------|-------|----------------|
| Dummy spans (line/col = 0) | Medium-High | ~95 occurrences | 10 files |
| Hardcoded truth constructor ("True") | Medium | 6 locations | 3 files |
| Hardcoded literal type defaults | Low (by design) | N/A | 2 files |
| FFI type hardcoding | Medium | 20+ type signatures | 1 file |

---

## 1. DUMMY SPANS (Critical)

### What was found
**142 total** occurrences of `Span("...", 0, 0, 0, 0)` in non-test source files. This violates the requirement that "the compiler should NOT have any hardcoded assumptions like dummy spans."

### Breakdown by location

#### src/tao/syntax.gleam — 50 occurrences
The parser creates fake spans when fallback/error paths are taken. Many token matchers default to `Int(0, Span("error", 0, 0, 0, 0))` when patterns don't match.

**Examples:**
```gleam
// Line 395
let default_span = Span("error", 0, 0, 0, 0)

// Line 723-724
[] -> Int(0, Span("program", 0, 0, 0, 0))
_ -> Block(stmts, Span("program", 0, 0, 0, 0))

// Lines 1578, 1586, 1741, etc.
Ctr("Or", patterns, Span("or", 0, 0, 0, 0))
```

**Root cause:** The parser combinator fallback expressions (`_ -> Int(0, Span("error", 0, 0, 0, 0))`) create error AST nodes with invalid spans. These spans are later used for error reporting.

**Fix strategy:** Replace dummy spans with the actual token's span. Since the parser uses real token spans, we can propagate them:
```gleam
_ -> Int(0, current_token_span)  // instead of Span("error", 0, 0, 0, 0)
```

#### src/tao/global_context.gleam — 14 occurrences
The type-to-core conversion functions create dummy spans in `type_ast_to_core`:
```gleam
TVar(name) -> core_ast.Ctr(name, core_ast.Unit(Span("unit", 0, 0, 0, 0)), Span("type", 0, 0, 0, 0))
TApp(name, _args) -> core_ast.Ctr(name, core_ast.Unit(Span("unit", 0, 0, 0, 0)), Span("tapp", 0, 0, 0, 0))
```

And in constructor environment extraction:
```gleam
arg_ty: core_ast.Typ(0, Span("unit", 0, 0, 0, 0))
ret_ty: core_ast.Typ(0, Span("type", 0, 0, 0, 0))
```

**Fix strategy:** `type_ast_to_core` receives a `TypeAst` which already has span information attached in the original source. However, the current signature doesn't propagate the original span. Add a `span: Span` parameter to `type_ast_to_core` and pass it through. For constructor extraction, pass the constructor/declaration span into `tao_type_to_core_ctrs`.

#### src/tao/desugar.gleam — 7 occurrences
Placeholder spans in `build_type_applications`, `build_fn_type`, and hole creation:
```gleam
#[CoreHole(-1, Span("fn", 0, 0, 0, 0)), dc)  // line 1773
#[CoreHole(-1, Span("record", 0, 0, 0, 0)), dc)  // line 1776
#[CoreHole(-1, Span("tuple", 0, 0, 0, 0)), dc)  // line 1779
#[CoreHole(-1, Span("_", 0, 0, 0, 0)), dc)  // line 1782
```

And in type definition processing:
```gleam
arg_ty: core_ast.Typ(0, Span("unit", 0, 0, 0, 0)),  // line 1334
ret_ty: core_ast.Typ(0, Span("type", 0, 0, 0, 0)),   // line 1335
```

**Fix strategy:** The desugarer has access to spans from the source expressions. Propagate the expression span through the desugaring pipeline. For type definitions, pass the original `StmtType` span into `tao_type_to_core_ctrs`.

#### src/compiler_bootstrap.gleam — 2 occurrences
Both in the `run_core` and `run_tao` functions:
```gleam
let span = Span("", 0, 0, 0, 0)  // line 667
let span = Span("", 0, 0, 0, 0)  // line 789
```

Used for `quote()` calls. Since we're quoting an already-evaluated term (not source code), a file path is needed. Pass `file.path` instead of `""`.

**Fix strategy:** Replace with `Span(file.path, 0, 0, 0, 0)`. The columns will still be 0 (since we don't have column info from evaluation), but at least the file path is correct.

#### src/tao/test_api.gleam — 2 occurrences
In `format_type` and `value_to_string`:
```gleam
let span = Span("", 0, 0, 0, 0)  // lines 697, 756
```

Same as compiler_bootstrap — these are for formatting values, not source code.

**Fix strategy:** Pass `file` or `"test"` as the file path.

#### src/tao/import_resolver.gleam — 4 occurrences
```gleam
DirectoryNotFound(dir_path, Span("unknown", 0, 0, 0, 0))  // lines 261-266
Span("unknown", 0, 0, 0, 0)  // line 364
```

**Fix strategy:** Propagate the actual module/import path into the span.

#### src/core/syntax.gleam — 15 occurrences
All in error recovery paths when the parser fails:
```gleam
Err("Parse error: " <> msg, grammar.Span("", 0, 0, 0, 0))
```

**Fix strategy:** When parsing fails, use the remaining input span as a placeholder. Even better, pass through the span from the parser's error result.

#### src/core/infer.gleam — 2 occurrences
In `infer_pattern` for PCtr error cases:
```gleam
let s = check_type(s, expected_ty, ctr_ret_ty, Span("", 0, 0, 0, 0), Span("", 0, 0, 0, 0))
let s = state.State(..s, errors: [state.CtrUndefined(tag, Span("", 0, 0, 0, 0)), ..s.errors])
```

**Fix strategy:** These span the pattern and the undefined constructor. Pass the pattern's span to both calls.

#### src/syntax/error_reporter.gleam — 1 occurrence
```gleam
grammar.Span("", 0, 0, 0, 0)  // line 559
```

In `get_term_span` helper.

**Fix strategy:** This function exists to extract a span from any Core term. The real fix is to ensure all terms have real spans from the start (see fixes above). This function can then traverse the term tree to find the innermost real span.

#### src/tao/test_parser.gleam — 1 occurrence
```gleam
span: Span("unknown", 0, 0, 0, 0),  // line 794
```

**Fix strategy:** Pass the test annotation's line position.

---

## 2. HARDCODED TRUTH CONSTRUCTOR ("True")

### What was found
The truth constructor is used in `eval` to determine if a match guard evaluates to true:
```gleam
case guard_val, ast.is_true_value(guard_val, truth_ctor)
```

### Locations with hardcoded "True"

| File | Line | Context |
|------|------|---------|
| `src/core/eval.gleam` | 22 | `eval` defaults to `eval_with_ctor(ffi, env, term, "True")` |
| `src/core/eval.gleam` | 309 | `do_call` defaults to `"True"` |
| `src/core/state.gleam` | 134 | `initial_state` has `truth_ctor: "True"` |
| `src/tao/ffi.gleam` | 162, 166, 170, 174, 178, 182 | Comparison FFI passes `"True", "False"` to `dispatch_cmp` |
| `src/tao/language_config.gleam` | 130 | `default_config()` has `truth_constructor: "True"` |
| `src/tao/language_config.gleam` | 131 | `default_config()` has `false_constructor: "False"` |

### Analysis

**The language_config approach is correct.** Tao's `language_config.gleam` provides a `LanguageConfig` record that contains the truth constructor, and the desugarer reads from `dc.config.truth_constructor`. This means the desugarer is **not** hardcoded.

**The problem is in the evaluation layer.** The `eval` function in `core/eval.gleam` defaults to "True" and there's no way to pass a custom truth constructor from the compiler_bootstrap layer. The `eval` calls in `compiler_bootstrap.gleam` (run_tao, run_core) call `eval(ffi, env, term)` which hardcodes "True".

Similarly, `ffi.gleam` comparison operations (eq, neq, lt, gt, lte, gte) hardcode `"True"` and `"False"` as the truth/false constructor names. This is **partially** OK since these are Tao-specific FFI operations — but it should read from a config or be parameterized.

### Fix strategy

**Option A: Pass truth constructor through eval chain (Recommended)**

Add a `truth_ctor: String` parameter to `tao_ffis()` and pass it through evaluation:
```gleam
pub fn tao_ffis() -> state.FFI {
  let cfg = lang_config.default_config()
  [
    #("add", state.Builtin(impl: ffi_add, ...)),
    ...
    #("eq", state.Builtin(
      impl: fn(args) -> Option(ast.Value) {
        dispatch_cmp(args, int_op_eq, float_op_eq, cfg.truth_constructor, cfg.false_constructor)
      },
      ...
    )),
  ]
}
```

Or better: make the FFI struct carry the truth constructor, and use it in `eval` and `do_call`.

**Option B: Read from State (simpler)**

The `State` already has a `truth_ctor` field. Pass the state to `eval`:
```gleam
pub fn eval(s: state.State, term: ast.Term) -> ast.Value {
  eval_with_ctor(s.ffi, [], term, s.truth_ctor)
}
```

This is the cleaner approach because the state already tracks the truth constructor. The callers in `compiler_bootstrap.gleam` would need to initialize the state with `initial_state_with(tao_ffis(), "True")` instead of `initial_state`.

---

## 3. FFI TYPE HARDCODING

### What was found
In `src/tao/ffi.gleam`, all FFI builtin definitions use hardcoded types:
```gleam
#("eq", state.Builtin(
  impl: ffi_eq,
  arg_types: [ast.VLitT(ast.I32T), ast.VLitT(ast.I32T)],
  ret_type: ast.VTyp(0),  // Bool type
  required_permissions: [],
)),
```

All comparison operators use `ast.VTyp(0)` as the return type (assuming Bool). All arithmetic operators use `ast.VLitT(ast.I32T)` for both args and return.

### Why this is a problem

1. **`ast.VTyp(0)` for Bool**: This is a generic type at level 0. It works because unification treats `VTyp(n)` uniformly, but it's not semantically correct — it should reference the Bool type.

2. **`I32T` for all arithmetic**: Tao's language_config already has overloaded int/float types (`IntLit`/`FloatLit`). The FFI should accept overloaded types so that `1 + 2.5` works via type coercion.

3. **Missing overloaded types**: The FFI should accept `ast.VLitT(ast.IntLit)` for the return type, matching what the desugarer produces for numeric literals.

### Fix strategy

**Change FFI type signatures to use overloaded types:**
```gleam
pub fn tao_ffis() -> state.FFI {
  let cfg = lang_config.default_config()
  [
    #("add", state.Builtin(
      impl: ffi_add,
      arg_types: [ast.VLitT(ast.IntLit), ast.VLitT(ast.IntLit)],
      ret_type: ast.VLitT(ast.IntLit),
      required_permissions: [],
    )),
    #("eq", state.Builtin(
      impl: ffi_eq,
      arg_types: [ast.VLitT(ast.IntLit), ast.VLitT(ast.IntLit)],
      ret_type: cfg.bool_type,  // Needs to be a Core term, not just a string
      required_permissions: [],
    )),
  ]
}
```

The Bool type reference is more problematic because `ast.VTyp(0)` is a Core-level type, while the Bool `type` is defined in the prelude. The FFI layer should accept a `core_ast.Term` for the return type, which the caller passes in.

---

## 4. DESUGARER HARDCODED I32

### What was found
In `src/tao/desugar.gleam` line 2834:
```gleam
CoreBuiltinType(name, span) -> {
  case name {
    "I32" -> core_ast.LitT(typ: core_ast.I32T, span: span)
    "I64" -> core_ast.LitT(typ: core_ast.I64T, span: span)
    ...
  }
}
```

This `CoreBuiltinType` branch is hit when desugaring type annotations. It maps type names to Core's literal types.

### Fix strategy

This should read from `lang_config` instead of a hardcoded case:
```gleam
CoreBuiltinType(name, span) -> {
  case lang_config.lookup_primitive_type(dc.config.primitive_types, name) {
    Some(lt) -> core_ast.LitT(typ: lt, span: span)
    None -> core_ast.Hole(id: -1, span: span)
  }
}
```

---

## 5. DUPLICATE CODE

### What was found

#### compiler_bootstrap.gleam — run_tao and run_core are nearly identical
`run_core` (lines 620-695) and `run_tao` (lines 698-795) share ~60 lines of nearly identical logic:
- Type checking
- FFI evaluation
- Force + quote
- Format + output

**Fix strategy:** Extract a shared `run_and_evaluate` helper that takes the FFI and the term:
```gleam
fn run_and_evaluate(ffi: state.FFI, term: core_ast.Term, type_state: state.State, 
                    file: File, verbose: Bool, has_errors: Bool) -> Result(Nil, Error) {
  // ... shared evaluation logic
}
```

#### global_context.gleam — duplicate comment
Lines 491-492:
```gleam
/// Register a single prelude module from lib/prelude/.
/// Register a single prelude module from lib/prelude/.
```

**Fix strategy:** Remove the duplicate comment line.

---

## 6. PRELUDE LOADING (Already Correct)

### What was found

The prelude loading mechanism is **correctly designed**:

1. `with_prelude()` in `global_context.gleam` scans `lib/prelude/` for `.tao` files.
2. Each file is parsed and registered with the "prelude/" prefix.
3. `create_implicit_prelude_imports()` in `desugar.gleam` creates wildcard imports for all prelude modules.
4. `merge_prelude_ctr_env()` merges constructor environments from prelude modules.

### Small improvements

1. **Hardcoded `"prelude/"` prefix in desugar.gleam** (lines 935, 940, 955): The desugarer checks for `string.starts_with(path, "prelude/")` to identify prelude modules. This is acceptable because it's a naming convention, but it should be extracted to a constant in `global_context.gleam`.

2. **Hardcoded `"lib/prelude"` path in `import_resolver.gleam`** (line 142):
```gleam
string.contains(file_path, "lib/prelude") || string.starts_with(file_path, "prelude")
```
This is acceptable as a file-level check but should be a constant.

---

## 7. ADDITIONAL ISSUES

### 7.1 Initial state not carrying FFI

In `compiler_bootstrap.gleam`, the check commands use:
```gleam
let #(_type_result, _type_annotation, final_state) = infer(initial_state, parse_result.ast)
```

But `initial_state` has `ffi: []` (empty). The type checker needs FFI for `%call` operations. For Tao files, `initial_state` is used but FFI is only added later in `run_tao`:
```gleam
let ffi = tao_ffis()
let value = eval(ffi, env, term)
```

**Fix:** Use `initial_state_with(tao_ffis(), "True")` for Tao type checking, not `initial_state`.

### 7.2 Desugarer does not pass FFI to type checker

In `check_tao` and `run_tao` in `compiler_bootstrap.gleam`, the type checker is called with `initial_state` which has no FFI:
```gleam
let #(term, _dc) = desugar_module(module, ctx)
let #(result, _, state) = infer(initial_state, term)
```

But `term` may contain `%call` operations that need FFI during inference.

**Fix:** Merge FFI into initial state before calling `infer`:
```gleam
let state_with_ffi = initial_state_with(tao_ffis(), "True")
let #(result, _, state) = infer(state_with_ffi, term)
```

### 7.3 `exprs_to_stmts` duplication

Both `compiler_bootstrap.gleam` and `tao/test_api.gleam` define their own `exprs_to_stmts` functions that convert parsed Tao expressions to statements. They are nearly identical.

**Fix:** Move to `tao/ast.gleam` or `tao/syntax.gleam` as a shared utility.

### 7.4 `get_expr_span` duplication

Both `compiler_bootstrap.gleam` and `tao/compiler.gleam` define their own `get_expr_span_from_syntax` / `get_expr_span` functions that pattern-match all TaoExpr variants to extract spans. These are identical.

**Fix:** Move to `tao/syntax.gleam` as `get_expr_span: Expr -> Span`.

---

## 8. SUMMARY TABLE

| Issue | Severity | Effort | Files | Fixability |
|-------|----------|--------|-------|------------|
| Dummy spans | High | Medium | 10 | Direct — propagate real spans |
| Truth constructor default | Medium | Low | 2 | Direct — use `State.truth_ctor` |
| FFI type hardcoding | Medium | Medium | 1 | Direct — use overloaded types + config |
| I32 hardcoded in desugarer | Low | Low | 1 | Direct — use `lang_config` |
| Duplicate code | Low | Low | 3 | Direct — extract shared functions |
| Initial state missing FFI | Medium | Low | 1 | Direct — use `initial_state_with` |
| Expr-to-stmt duplication | Low | Low | 2 | Direct — extract shared function |

---

## 9. RECOMMENDED PRIORITY ORDER

### Phase 1: Critical correctness (blocking real error spans)
1. Fix `compiler_bootstrap.gleam` — replace `Span("", 0, 0, 0, 0)` with real file paths
2. Fix `tao/test_api.gleam` — replace `Span("", 0, 0, 0, 0)` with real file paths  
3. Fix `src/tao/global_context.gleam` — `type_ast_to_core` to accept and propagate spans
4. Use `initial_state_with(tao_ffis(), "True")` instead of `initial_state` for Tao compilation

### Phase 2: Language-agnostic eval
5. Pass `State.truth_ctor` through `eval` chain instead of hardcoding "True"
6. Update `ffi.gleam` comparison dispatchers to use config-based truth/false constructors

### Phase 3: FFI type correctness
7. Replace `ast.VTyp(0)` return types in comparison FFI with actual Bool type
8. Replace `ast.VLitT(ast.I32T)` with `ast.VLitT(ast.IntLit)` for overloaded arithmetic
9. Fix `desugar.gleam` `CoreBuiltinType` to use `lang_config`

### Phase 4: Code cleanup
10. Extract shared functions (`exprs_to_stmts`, `get_expr_span`, `run_and_evaluate`)
11. Remove duplicate comment in `global_context.gleam`
12. Fix remaining dummy spans in parser fallbacks

---

## 10. ARCHITECTURE ASSESSMENT

### What works well
- **Core is language-agnostic:** Core has no knowledge of Tao-specific types, functions, or constructors. The `Term`, `Value`, `Pattern`, and `State` types are all generic.
- **Prelude loading is dynamic:** `with_prelude()` scans `lib/prelude/` at runtime. No hardcoded module names in the compiler.
- **Desugarer uses config:** `lang_config.LanguageConfig` is passed through `DesugarContext` and used for operator names, constructor names, and primitive types.
- **Error accumulation:** Both Core and Tao accumulate errors in `State.errors`, never stopping on the first error.
- **Bidirectional type checking:** Clean separation between `infer` (synthesize) and `check` (verify).

### What could be improved
- **State carries truth_ctor but it's not used:** The `State` has a `truth_ctor` field but `eval` ignores it, using a hardcoded "True" instead. This is a missed opportunity for clean architecture.
- **FFI is Tao-specific but could be abstracted:** `tao_ffis()` creates Tao-specific builtins. The FFI interface in Core (`state.FFI`) is generic, but the implementation layer (`tao/ffi.gleam`) could be more abstract.
- **Literal types in Core:** Core defines `I32T`, `I64T`, `U32T`, `U64T`, `F32T`, `F64T`, `ILitT`, `FLitT` — these are language-agnostic primitive types, which is fine. But the desugarer hardcodes the mapping from Tao type names to Core literal types. This should come from `lang_config`.
