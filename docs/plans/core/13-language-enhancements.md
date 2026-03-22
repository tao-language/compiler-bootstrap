# Core Language Enhancement Plan

> **Goal**: Enable real-world programs (fibonacci, dependent types, etc.)
> **Status**: 📋 Planned
> **Date**: March 2025

---

## Overview

This plan outlines the implementation of features needed to write real-world programs in the core language, including recursion, named functions, and data type definitions.

---

## Current Limitations

1. **No let-bindings** - Cannot define named functions or values
2. **No recursion** - Requires fixpoint combinator or let-rec
3. **No data type definitions** - Constructors must be predefined
4. **Limited pattern matching** - Match expressions work but are verbose

---

## Implementation Phases

### Phase 1: Let-Bindings ✅

**Goal**: Add let-bindings for named values and functions

**Syntax**:
```
let x = 42 in x
let id = x -> x in id(42)
```

**Implementation**:
- [ ] Add `Let` constructor to `Term` and `NamedTerm`
- [ ] Add grammar rule for `let` expressions
- [ ] Add formatter for `let` expressions
- [ ] Add type checking for `let` bindings
- [ ] Add evaluation for `let` bindings
- [ ] Add examples: `examples/core/terms/11_let_binding.core.tao`
- [ ] Add tests: `test/core/syntax_test.gleam`

**Error Cases**:
- [ ] `examples/core/errors/syntax_errors/08_unclosed_let.core.tao`
- [ ] `examples/core/errors/type_errors/04_let_type_mismatch.core.tao`

---

### Phase 2: Recursive Let (let-rec) ✅

**Goal**: Add recursive let-bindings for recursion

**Syntax**:
```
let rec fib = n -> %match n ~ $Type {
  | 0 -> 1
  | 1 -> 1
  | _ -> fib(n - 1) + fib(n - 2)
} in fib(10)
```

**Implementation**:
- [ ] Extend `Let` constructor with recursive flag
- [ ] Update grammar for `let rec`
- [ ] Update type checking for recursive bindings
- [ ] Update evaluation for recursive bindings
- [ ] Add examples: `examples/core/programs/01_fibonacci.core.tao`

**Error Cases**:
- [ ] `examples/core/errors/type_errors/05_recursive_type.core.tao`

---

### Phase 3: Data Type Definitions ✅

**Goal**: Add data type definitions for constructors

**Syntax**:
```
data Option(a) = #Some(a) | #None
data List(a) = #Cons(a, List(a)) | #Nil
```

**Implementation**:
- [ ] Add `DataDef` type for data type definitions
- [ ] Add grammar rule for `data` declarations
- [ ] Add type checking for data types
- [ ] Register constructors in type checker state
- [ ] Add examples: `examples/core/programs/02_option.core.tao`

**Error Cases**:
- [ ] `examples/core/errors/type_errors/06_undefined_constructor.core.tao`
- [ ] `examples/core/errors/type_errors/07_duplicate_constructor.core.tao`

---

### Phase 4: Pattern Matching Enhancements ✅

**Goal**: Improve pattern matching syntax and exhaustiveness

**Syntax**:
```
%match opt ~ $Type {
  | #Some(x) -> x
  | #None -> 0
}
```

**Implementation**:
- [ ] Fix match expression type checking (motive inference)
- [ ] Implement exhaustiveness checking
- [ ] Add redundant pattern detection
- [ ] Add examples: `examples/core/programs/03_match_option.core.tao`

**Error Cases**:
- [ ] `examples/core/errors/exhaustiveness_checks/01_missing_case.core.tao`
- [ ] `examples/core/errors/exhaustiveness_checks/02_redundant_case.core.tao`

---

### Phase 5: Real-World Programs ✅

**Goal**: Create comprehensive example programs

**Programs**:
- [ ] Fibonacci with recursion
- [ ] Option type with pattern matching
- [ ] List operations (map, filter, fold)
- [ ] Church numerals
- [ ] Boolean logic
- [ ] Vector with dependent types (length-indexed)

---

## Testing Strategy

### Unit Tests
- Each new construct gets syntax tests
- Type checking tests for each error case
- Evaluation tests for runtime behavior

### Integration Tests
- End-to-end tests for complete programs
- Round-trip tests (parse → format → parse)

### Error Tests
- Each error type has example files
- Tests verify error messages and locations

---

## Success Criteria

- ✅ All 344+ existing tests continue to pass
- ✅ New features have comprehensive tests
- ✅ Example programs compile and run correctly
- ✅ Error messages are clear and actionable
- ✅ Documentation is complete and accurate

---

## Timeline

| Phase | Estimated Effort | Dependencies |
|-------|-----------------|--------------|
| Phase 1: Let-bindings | 2-3 hours | None |
| Phase 2: Recursive let | 3-4 hours | Phase 1 |
| Phase 3: Data types | 4-6 hours | Phase 2 |
| Phase 4: Pattern matching | 4-6 hours | Phase 3 |
| Phase 5: Programs | 4-8 hours | Phase 4 |

**Total**: 17-27 hours

---

## Related Documents

- [Core Language Overview](../../docs/plans/core/01-overview.md)
- [Error Reporting Plan](../../docs/plans/error-reporting/01-overview.md)
- [CLI Integration Plan](../../docs/plans/cli/01-overview.md)
