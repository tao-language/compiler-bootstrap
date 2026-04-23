# Migration Guide: Old Architecture → New Architecture

## Key Changes Summary

This document maps old components to new components and explains the rationale for each change.

## Directory Structure Changes

| Old | New | Notes |
|-----|-----|-------|
| `src/syntax/grammar.gleam` | `src/syntax/grammar.gleam` | Simplified DSL, better error recovery |
| `src/syntax/lexer.gleam` | `src/syntax/lexer.gleam` | Same, no changes |
| `src/syntax/formatter.gleam` | `src/syntax/formatter.gleam` | Same, no changes |
| `src/syntax/error_reporter.gleam` | `src/syntax/error_reporter.gleam` | Unified with source_snippet |
| `src/syntax/source_snippet.gleam` | `src/syntax/source_snippet.gleam` | Moved into error_reporter |
| `src/core/ast.gleam` | `src/core/ast.gleam` | Simplified, no duplicate Literal types |
| `src/core/infer.gleam` | `src/core/infer.gleam` | Cleaner error handling |
| `src/core/eval.gleam` | `src/core/eval.gleam` | Pass truth_ctor through explicitly |
| `src/core/quote.gleam` | `src/core/quote.gleam` | NO EVAL (critical invariant) |
| `src/core/unify.gleam` | `src/core/unify.gleam` | Literal type overloading |
| `src/core/subst.gleam` | `src/core/subst.gleam` | Same, no changes |
| `src/core/generalize.gleam` | `src/core/generalize.gleam` | Same, no changes |
| `src/core/exhaustiveness.gleam` | `src/core/exhaustiveness.gleam` | Same, no changes |
| `src/core/error_formatter.gleam` | `src/core/error_formatter.gleam` | Better diagnostics |
| `src/core/state.gleam` | `src/core/state.gleam` | Single comprehensive state |
| `src/core/list_utils.gleam` | `src/core/list_utils.gleam` | Same, no changes |
| `src/core/ast_string.gleam` | `src/core/ast_string.gleam` | Same, no changes |
| `src/core/color.gleam` | `src/core/color.gleam` | Same, no changes |
| `src/core/visitor.gleam` | `src/core/visitor.gleam` | Same, no changes |
| `src/tao/ast.gleam` | `src/tao/ast.gleam` | Simplified, removed legacy types |
| `src/tao/lexer.gleam` | `src/tao/lexer.gleam` | Extends base lexer |
| `src/tao/syntax.gleam` | `src/tao/syntax.gleam` | Uses grammar library |
| `src/tao/desugar.gleam` | `src/tao/desugar.gleam` | No CoreTerm duplication |
| `src/tao/compiler.gleam` | `src/tao/compiler.gleam` | Unified pipeline |
| `src/tao/global_context.gleam` | `src/tao/global_context.gleam` | Cleaner module resolution |
| `src/tao/import_resolver.gleam` | `src/tao/import_resolver.gleam` | Same, no changes |
| `src/tao/import_ast.gleam` | `src/tao/import_ast.gleam` | Same, no changes |
| `src/tao/ffi.gleam` | `src/tao/ffi.gleam` | Pass truth_ctor through |
| `src/tao/language_config.gleam` | `src/tao/language_config.gleam` | Same, no changes |
| `src/tao/test_api.gleam` | `src/tao/test_api.gleam` | Same, no changes |
| `src/tao/test_parser.gleam` | `src/tao/test_parser.gleam` | Same, no changes |
| `src/tao/test_reporter.gleam` | `src/tao/test_reporter.gleam` | Same, no changes |
| `src/tao/test_filter.gleam` | `src/tao/test_filter.gleam` | Same, no changes |
| `src/tao/infer_utils.gleam` | `src/core/infer_utils.gleam` | Moved to core |
| `src/compiler_bootstrap.gleam` | `src/compiler_bootstrap.gleam` | Simplified pipeline |

## Architecture Improvements

### 1. No Duplicate Types Between Core and Tao

**Problem:** Old code had `Literal` in both `core/ast.gleam` and `tao/ast.gleam`. The desugarer converted between them.

**Solution:** Single `Literal` type in `core/ast.gleam`. Tao parser produces `core/Literal` directly. No conversion needed.

### 2. Unified Error Handling

**Problem:** Old code scattered errors across multiple mechanisms (State.errors, exceptions, panic).

**Solution:** Every function returns `(result, errors)` tuple. Errors accumulate explicitly through the pipeline.

### 3. No CoreTerm Duplication

**Problem:** Old `desugar.gleam` had its own `CoreTerm` type separate from `core/ast.Term`. After desugaring, a second conversion was needed.

**Solution:** Desugarer produces `core/ast.Term` directly. No intermediate type.

### 4. Explicit Truth Constructor

**Problem:** Old code hardcoded `"True"` and `"False"` in multiple places (eval, ffi, state).

**Solution:** Truth constructor is passed through `State` explicitly. FFI entries read from config.

### 5. Accurate Spans

**Problem:** Old code used `Span("error", 0, 0, 0, 0)` in ~142 places for error recovery.

**Solution:** Parser creates spans from actual lexer tokens. For synthesized nodes, `span_dummy()` is used but type checker propagates spans from child nodes.

### 6. Language-Agnostic Core

**Problem:** Old `core/ast.gleam` had Tao-specific FFI entries and configuration.

**Solution:** Core is truly language-agnostic. No Tao-specific types, no Tao-specific FFI. Tao passes resolved `CtrEnv` and `List(FfiEntry)` to Core.

## Type System Improvements

### Literal Type Resolution

**Old:** Literal type resolution was implicit in unification.

**New:** Explicit `ILitT` and `FLitT` types that unify with any concrete literal type. Clear separation between untyped literals (from parser) and typed values (from evaluator).

### Hole ID Convention

**Old:** Mixed positive/negative ID conventions.

**New:** Consistent convention:
- Negative IDs: synthesis holes (infer)
- Positive IDs: verification holes (check)

### State Type

**Old:** Scattered state across multiple records.

**New:** Single `State` record containing everything:
```gleam
pub type State {
  State(
    ctrs: CtrEnv,
    truth_ctor: String,
    false_ctor: String,
    holes: List(#(Int, Value)),
    subst: Subst,
    errors: List(Error),
    ffi: List(FfiEntry),
    step_limit: Int,
  )
}
```

## Desugaring Improvements

### For-Loop Desugaring

**Old:** Complex nested desugaring with separate iterator module.

**New:** Direct desugaring to Core `fix` + `match`:
```gleam
for x in collection { e }
→ let loop = fix \_ -> match next(collection) {
  | Some(x) -> e; loop ()
  | None -> ()
}
loop ()
```

### Mutable Variable Desugaring

**Old:** Tracked mutability in separate state.

**New:** Each "mutation" creates a new binding with unique name:
```tao
mut x = 0
x = x + 1
```
```gleam
let x_0 = 0
let x_1 = +(x_0, 1)
```

### Operator Desugaring

**Old:** Operator desugaring was mixed into parser.

**New:** Operators are desugared in the grammar library. The parser produces AST nodes for operators, which are then converted to function calls during desugaring.

## Testing Improvements

### Golden Tests

**Old:** No golden tests.

**New:** Round-trip tests for every phase:
- Parse → Format → Parse (AST equality)
- Term → Eval → Quote → Term (structural equality)

### Test Categories

**Old:** Mixed test categories.

**New:** Explicit test categories:
1. Unit tests (every function, example-based)
2. Golden tests (round-trip invariants)
3. Integration tests (pipeline stages)
4. End-to-end tests (complete programs)

## Error Handling Improvements

### Error Codes

**Old:** No error codes.

**New:** Systematic error codes:
- E0001-E0003: Parse errors
- E0101-E0111: Type errors
- E0201-E0203: Pattern errors
- E0301-E0303: Import errors
- E0501: Comptime errors

### Source Context

**Old:** Basic error messages.

**New:** Full source context with:
- Line numbers and column positions
- Caret pointers (^) highlighting the error
- Secondary spans with labels
- Notes and hints

## What Stays the Same

The following components remain **unchanged** in the rewrite:

1. **De Bruijn indices for syntax** — Term uses indices (0 = closest binder)
2. **De Bruijn levels for semantics** — Value uses levels (0 = innermost binder)
3. **Bidirectional type checking** — infer (synthesis) and check (verification)
4. **Normalization by evaluation** — NBE with neutral spine representation
5. **Maranget-style exhaustiveness checking** — Conservative guard handling
6. **Hole convention** — Negative = synthesis, positive = verification
7. **Quote does not evaluate** — Critical invariant preserved
8. **Module system** — Imports desugar to let bindings

## What's New

1. **Visitor pattern** — Generic AST traversal to reduce duplication
2. **Grammar-based formatting** — Precedence defined once in grammar, reused by formatter
3. **Error accumulation at every phase** — No early exits, no panic on errors
4. **Language-agnostic Core** — Zero Tao-specific assumptions
5. **No CoreTerm duplication** — Desugarer produces core/ast.Term directly
6. **Explicit truth constructor** — Passed through State, not hardcoded
7. **Systematic error codes** — Every error has a unique code
8. **Source context in errors** — Full diagnostic with line numbers and pointers
9. **Golden tests** — Round-trip invariants for every phase

## Migration Checklist

- [ ] Move existing code to `old/` directory
- [ ] Create new directory structure
- [ ] Implement grammar library (Phase 1)
- [ ] Implement core language (Phase 2)
- [ ] Implement Tao language (Phase 3)
- [ ] Implement module system (Phase 4)
- [ ] Implement error handling (Phase 5)
- [ ] Implement high-level features (Phase 6)
- [ ] Write end-to-end tests (Phase 7)
- [ ] Verify all 700+ existing tests pass
- [ ] Verify all examples work
- [ ] Verify no import cycles
- [ ] Verify no hardcoded assumptions
