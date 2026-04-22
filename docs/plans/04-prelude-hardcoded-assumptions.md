# Comprehensive Analysis: Hardcoded Assumptions in Compiler

**Date:** 2026-04-21

## Overview

This document identifies all hardcoded assumptions in the compiler codebase, categorizes them by severity and type, and provides a prioritized plan for remediation. The goal is to ensure:

1. **Core is language-agnostic** — no assumptions about specific types, constructors, functions, or operators
2. **The compiler has no prelude knowledge** — no hardcoded module names, types, constructors, or functions
3. **Prelude is loaded dynamically** from `lib/prelude/*.tao` files

---

## Categorization of Hardcoded Assumptions

### Category A: Safe / Intentional (No Fix Needed)

These are acceptable hardcoded values that are either:

- **Language-agnostic primitives** (integer/float types in Core)
- **Configurable defaults** that can be overridden
- **Implementation details** specific to Core's internal representation

| File | Line(s) | Assumption | Reason |
|------|---------|-----------|--------|
| `core/ast.gleam` | All | `I32`, `I64`, `U32`, `U64`, `F32`, `F64` literal types | Core language primitives — part of the Core type system itself |
| `core/eval.gleam` | 18, 306 | `"True"` truth constructor | Default fallback; `eval_with_ctor` accepts configurable truth ctor |
| `core/state.gleam` | 88 | `truth_ctor: "True"` default | Configurable via state; set by language layer |
| `core/ast_string.gleam` | 25-32 | `I32T` → `"I32"`, etc. | Internal type-to-string mapping for Core AST |
| `core/error_formatter.gleam` | 564-569 | `I32T` → `"Int"` | Error display formatting |
| `core/syntax.gleam` | 1000-1005 | `%I32`, `%I64`, `%F32`, `%F64`, `%U32`, `%U64` | Core language parser syntax — these are literal keywords of Core |

---

### Category B: Compiler Should Not Have — REMOVE FROM COMPILER

These assumptions live in the **Tao compiler** and should either be removed or delegated to the language layer.

#### B1: Hardcoded Primitive Type Names in Desugarer

**File:** `src/tao/desugar.gleam`

**Lines 1744-1749:**
```gleam
"I32" -> #(CoreBuiltinType(name, Span(name, 0, 0, 0, 0)), dc)
"I64" -> #(CoreBuiltinType(name, Span(name, 0, 0, 0, 0)), dc)
"U32" -> #(CoreBuiltinType(name, Span(name, 0, 0, 0, 0)), dc)
"U64" -> #(CoreBuiltinType(name, Span(name, 0, 0, 0, 0)), dc)
"F32" -> #(CoreBuiltinType(name, Span(name, 0, 0, 0, 0)), dc)
"F64" -> #(CoreBuiltinType(name, Span(name, 0, 0, 0, 0)), dc)
```

**Line 2794-2800 (in `core_term_to_term_loop`):**
```gleam
"I32" -> core_ast.LitT(typ: core_ast.I32T, span: span)
"I64" -> core_ast.LitT(typ: core_ast.I64T, span: span)
"U32" -> core_ast.LitT(typ: core_ast.U32T, span: span)
"U64" -> core_ast.LitT(typ: core_ast.U64T, span: span)
"F32" -> core_ast.LitT(typ: core_ast.F32T, span: span)
"F64" -> core_ast.LitT(typ: core_ast.F64T, span: span)
```

**Problem:** The Tao desugarer has knowledge of Core's internal primitive types (`I32T`, `I64T`, etc.). If we were to change these type names or add new ones, the desugarer would need to be updated.

**Fix:** Make the type-to-core-type mapping configurable via a `PrimitiveTypes` config passed through the desugarer context, or better: keep these as the **language-agnostic primitives that all languages share** (like in a standard library), not hardcoded in the compiler.

---

#### B2: Hardcoded Binary/Unary Operator Names

**File:** `src/tao/desugar.gleam`

**Lines 1993-2016:**
```gleam
fn binop_to_name(op: BinOperator) -> String {
  case op {
    OpAdd -> "add"
    OpSub -> "sub"
    OpMul -> "mul"
    OpDiv -> "div"
    OpMod -> "mod"
    OpEq -> "eq"
    OpNeq -> "neq"
    OpLt -> "lt"
    OpGt -> "gt"
    OpLte -> "lte"
    OpGte -> "gte"
    OpAnd -> "and"
    OpOr -> "or"
    OpConcat -> "concat"
    OpPipe -> "pipe"
  }
}

fn unaryop_to_name(op: UnaryOperator) -> String {
  case op {
    OpNegate -> "negate"
    OpNot -> "not"
  }
}
```

**Lines 2007-2031 (in `desugar_binop`):**
```gleam
"and" | "or" -> {
  let app1 = CoreApp(CoreVar(op_name, span), core_left, span)
  #(CoreApp(app1, core_right, span), dc2)
}
_ -> {
  let core_call = CoreCall(op_name, [core_left, core_right], span)
  #(
    case op_name {
      "eq" | "neq" | "lt" | "lte" | "gt" | "gte" -> {
        CoreAnn(core_call, CoreCtr("Bool", CoreUnit(span), span), span)
      }
      _ -> core_call
    },
    dc2,
  )
}
```

**Lines 2047-2063 (in `desugar_unaryop`):**
```gleam
"not" -> {
  #(CoreApp(CoreVar(op_name, span), core_expr, span), dc1)
}
_ -> {
  #(CoreCall(op_name, [core_expr], span), dc1)
}
```

**Problems:**

1. **Operator-to-name mapping is hardcoded** — if we want to change operator names, we must modify the compiler.
2. **Boolean operators (`and`, `or`) are treated specially** — calling them as `CoreApp` (user-defined functions) instead of `CoreCall` (FFI builtins). This is actually a good pattern but the specific names are hardcoded.
3. **`not` is treated specially** — same pattern, but hardcoded name.
4. **`"Bool"` constructor is hardcoded** in the type annotation for comparison operators.
5. **Arithmetic operators (`add`, `sub`, `mul`, `div`) are treated as FFI builtins** via `CoreCall`.
6. **Comparison operators get `CoreAnn(..., CoreCtr("Bool", ...))`** — assumes the result type is `"Bool"`.

**Fix:**

- Extract operator name mappings to a **configurable table** that the language layer provides.
- The Boolean type name (`"Bool"`) should come from the **constructor environment** or be a **configurable default**.
- Keep the pattern of distinguishing between FFI builtins (arithmetic) and user-defined functions (boolean) but make the operator categories configurable.

---

#### B3: Hardcoded Constructor Names for Control Flow

**File:** `src/tao/desugar.gleam`

**Line 1529 (`desugar_while`):**
```gleam
let true_clause = CoreCase(
  pattern: core_ast.PCtr("True", core_ast.PUnit),
  body: body_with_rec,
  guard: None,
  span: span,
)
```

**Line 1535-1540 (`desugar_while`):**
```gleam
let default_clause = CoreCase(
  pattern: core_ast.PAny,
  body: CoreRcd([], span),
  guard: None,
  span: span,
)
```

**Problem:** `while` loop desugaring hardcodes `"True"` as the truth constructor. While `eval_with_ctor` accepts a configurable truth constructor, the desugarer itself doesn't have access to it.

**Fix:** The desugarer should either:
1. Accept the truth constructor name as a parameter from the compiler context, or
2. Look it up from the constructor environment (if `"True"` is registered), or
3. Default to `"True"` but be documented as a configurable convention.

---

#### B4: Hardcoded List Constructors

**File:** `src/tao/desugar.gleam`

Multiple lines reference `"Nil"` and `"Cons"` constructors:
- Lines 1418, 1435, 1457, 1479: `for` loop desugaring
- Lines 2369-2410: list pattern desugaring
- Lines 2460, 2466: list expression desugaring

**Problem:** The desugarer assumes lists are represented as `Cons`/`Nil` constructors. If we wanted to represent lists differently (e.g., as a built-in type), we'd need to change the desugarer.

**Fix:** Accept list constructor names as configurable parameters in the desugarer context, or make them part of a "language configuration" record.

---

#### B5: Hardcoded `"Bool"` Constructor Type

**File:** `src/tao/desugar.gleam`

**Line 2031:**
```gleam
CoreAnn(core_call, CoreCtr("Bool", CoreUnit(span), span), span)
```

**Problem:** The result type of comparison operators is hardcoded to `"Bool"`. This should come from the constructor environment.

**Fix:** Look up `"Bool"` in the constructor environment (`dc.ctrs`) and use that name, or default to `"Bool"` only if it's not found (but still not hardcode the type annotation generation).

---

### Category C: Prelude Loading — Currently Correct, But Verify

#### C1: Prelude Loading via `with_prelude()`

**File:** `src/tao/global_context.gleam`

**Lines 276-310:**
```gleam
pub fn register_prelude_from_path(ctx: GlobalContext, path: String) -> GlobalContext {
  let prelude_path = "prelude/" <> path
  let file_path = "lib/prelude/" <> path <> ".tao"
  // ...
}

pub fn with_prelude(ctx: GlobalContext) -> GlobalContext {
  case simplifile.read_directory("lib/prelude") {
    Ok(files) -> {
      let prelude_files = list.filter(files, fn(f) {
        string.ends_with(f, ".tao") && !string.ends_with(f, ".test.tao")
      })
      // ...
    }
  }
}
```

**Status:** ✅ **CORRECT** — The prelude is loaded dynamically by scanning `lib/prelude/` for `.tao` files. No hardcoded module names.

**Caveat:** The `"prelude/"` prefix in `register_prelude_from_path` is hardcoded. While this is a reasonable convention, it means all prelude modules will always be prefixed with `"prelude/"`. This is acceptable as a convention, not a language assumption.

---

#### C2: Prelude Detection in Import Resolver

**File:** `src/tao/import_resolver.gleam`

**Lines 141-142:**
```gleam
string.contains(file_path, "lib/prelude") || string.starts_with(file_path, "prelude")
```

**Lines 218-220:**
```gleam
case string.starts_with(path, "prelude") {
  True -> project_root <> "/lib/" <> path
```

**Problem:** Import resolver has hardcoded `"prelude"` path detection logic.

**Fix:** This is acceptable for the import resolution mechanism — it's how the file system is organized, not a language assumption. However, the path `"lib/prelude"` should be configurable.

---

#### C3: Prelude Module Detection

**File:** `src/tao/global_context.gleam`

**Line 187:**
```gleam
string.starts_with(module_path, "prelude")
```

**Status:** ✅ **ACCEPTABLE** — This is used to detect prelude modules for the implicit import mechanism. The prefix `"prelude"` is a convention, not a hardcoded assumption about specific types/constructors.

---

### Category D: FFI Layer — Correctly Separated

#### D1: Tao FFI Operations

**File:** `src/tao/ffi.gleam`

**Lines 12-22:**
```gleam
pub fn tao_ffis() -> state.FFI {
  [
    #("add", state.Builtin(ffi_add, [])),
    #("sub", state.Builtin(ffi_sub, [])),
    // ... etc.
  ]
}
```

**Line 168-169:**
```gleam
True -> ast.VCtrValue(ast.VCtr("True", ast.VUnit))
False -> ast.VCtrValue(ast.VCtr("False", ast.VUnit))
```

**Problem:** 
1. FFI operations are defined in the **Tao FFI layer** (correctly separated from Core) — ✅ good.
2. The `bool_to_value` function hardcodes `"True"` and `"False"` constructors.

**Fix:** The `bool_to_value` function should accept the truth/false constructor names as parameters, or look them up from the constructor environment.

---

### Category E: Core Language — Intentionally Fixed

The Core language has fixed primitives (`I32T`, `I64T`, etc.) because Core **is** a specific language with specific types. This is acceptable. What should be language-agnostic is the **language layer** (Tao) that compiles to Core, not Core itself.

---

## Priority Matrix

| Priority | Issue | File | Impact |
|----------|-------|------|--------|
| **P0** | Boolean type hardcoded in desugar_binop | `desugar.gleam:2031` | High — prevents removing Bool assumption |
| **P0** | Truth constructor hardcoded in desugar_while | `desugar.gleam:1529` | High — prevents configurable truth ctor |
| **P0** | Bool/True hardcoded in tao FFI | `ffi.gleam:168-169` | High — bool_to_value needs configurable ctors |
| **P1** | Operator name mappings hardcoded | `desugar.gleam:1993-2063` | Medium — could be configurable table |
| **P1** | Primitive type names in desugarer | `desugar.gleam:1744-1749, 2794-2800` | Medium — should be configurable |
| **P1** | Nil/Cons hardcoded in desugarer | `desugar.gleam:1418-2466` | Medium — list representation assumptions |
| **P2** | Prelude path prefix hardcoded | `global_context.gleam:278` | Low — convention, not assumption |
| **P2** | Prelude detection in import_resolver | `import_resolver.gleam:141-142` | Low — filesystem organization |

---

## Detailed Fix Plan

### Fix 1: Extract Truth Constructor as Configuration (P0)

**Create a new type for language configuration:**

```gleam
pub type LanguageConfig {
  LanguageConfig(
    truth_constructor: String,      // e.g., "True"
    false_constructor: String,      // e.g., "False"
    bool_type: String,              // e.g., "Bool"
    list_cons: String,              // e.g., "Cons"
    list_nil: String,              // e.g., "Nil"
    operator_map: Dict(String, String),  // symbol -> function name
    ffi_ops: List(String),          // which operators use FFI
  )
}
```

**Apply to:**
1. `DesugarContext` — add `config: LanguageConfig` field
2. `DesugarContext` functions — use config for truth ctor, bool type, list constructors
3. `tao_ffis()` — accept truth/false constructors from config
4. `desugar_while`, `desugar_if` — use config for truth constructor

### Fix 2: Extract Operator Mapping (P1)

**Create a configurable operator mapping:**

```gleam
pub type OperatorMapping {
  OperatorMapping(
    /// Binary operators: symbol -> function name
    binary: Dict(String, String),
    /// Unary operators: symbol -> function name  
    unary: Dict(String, String),
    /// Which binary operators are FFI builtins vs user-defined
    ffi_binary: Set(String),
    /// Which unary operators are FFI builtins vs user-defined
    ffi_unary: Set(String),
  )
}
```

**For Tao default:**
```gleam
fn tao_operator_mapping() -> OperatorMapping {
  OperatorMapping(
    binary: dict.from_list([
      #("+", "add"),
      #("-", "sub"),
      // ... all operators
    ]),
    unary: dict.from_list([
      #("-", "negate"),
      #("not", "not"),
    ]),
    ffi_binary: set.from_list(["add", "sub", "mul", "div", "eq", "neq", "lt", "gt", "lte", "gte"]),
    ffi_unary: set.from_list(["negate"]),
  )
}
```

### Fix 3: Remove Hardcoded Bool from desugar_binop (P0)

**Replace:**
```gleam
"eq" | "neq" | "lt" | "lte" | "gt" | "gte" -> {
  CoreAnn(core_call, CoreCtr("Bool", CoreUnit(span), span), span)
}
```

**With:**
```gleam
case list.key_find(ctrs, "Bool") {
  Ok(_) -> CoreAnn(core_call, CoreCtr("Bool", CoreUnit(span), span), span)
  Error(_) -> {
    // Fallback: look up from global context or use a hole
    core_call
  }
}
```

### Fix 4: Make tao_ffis() Accept Configurable Constructors (P0)

**Change:**
```gleam
fn bool_to_value(b: Bool) -> ast.Value
```

**To:**
```gleam
fn bool_to_value(b: Bool, truth_ctor: String, false_ctor: String) -> ast.Value
```

### Fix 5: Extract Nil/Cons from Desugarer (P1)

**Add to `DesugarContext`:**
```gleam
list_cons: String,
list_nil: String,
```

**Replace all hardcoded `"Cons"` and `"Nil"` references** with `dc.list_cons` and `dc.list_nil`.

### Fix 6: Make Primitive Types Configurable (P1)

**Create a primitive type registry:**
```gleam
pub type PrimitiveTypes {
  PrimitiveTypes(
    types: List(#(String, core_ast.LiteralType)),
  )
}
```

**For Tao default:**
```gleam
fn tao_primitive_types() -> PrimitiveTypes {
  PrimitiveTypes([
    #("I32", core_ast.I32T),
    #("I64", core_ast.I64T),
    #("U32", core_ast.U32T),
    #("U64", core_ast.U64T),
    #("F32", core_ast.F32T),
    #("F64", core_ast.F64T),
  ])
}
```

---

## Summary: What's Already Correct

1. ✅ **Prelude loading** — `with_prelude()` scans `lib/prelude/` dynamically
2. ✅ **No hardcoded prelude types** — types are loaded from `.tao` files
3. ✅ **No hardcoded prelude module names** — modules discovered via filesystem scan
4. ✅ **Constructor environment merging** — prelude ctors properly merged into desugarer context
5. ✅ **FFI separation** — Tao FFI is in `src/tao/ffi.gleam`, not in Core
6. ✅ **Core State.ffi is empty by default** — populated by language layer

## Summary: What Needs Fixing

1. ⚠️ **Boolean type hardcoding** — `"Bool"` hardcoded in `desugar_binop`
2. ⚠️ **Truth constructor hardcoding** — `"True"` hardcoded in `desugar_while`, `ffi.gleam`
3. ⚠️ **Operator name mappings** — hardcoded `binop_to_name`, `unaryop_to_name`
4. ⚠️ **List constructors** — `"Cons"`, `"Nil"` hardcoded in desugarer
5. ⚠️ **Primitive type names** — hardcoded in `desugar_type_ast` and `core_term_to_term_loop`

## Recommendations

1. **Create a `LanguageConfig` record** that all language layers (Tao, future languages) pass through
2. **Move operator mappings** to the language layer
3. **Keep Core primitives fixed** — they are the compilation target
4. **The desugarer should be parameterized** on the language config
5. **Prelude loading is already correct** — no changes needed there
