# Production Ready Compiler Plan

> **Goal**: Transform the compiler bootstrap into a production-ready compiler and runtime
> **Status**: 🚧 In Progress - Error reporting infrastructure complete
> **Date**: March 2025

---

## Overview

This document outlines the work needed to transform the compiler bootstrap from a working prototype into a production-ready compiler and runtime system.

---

## Current Status

### ✅ Complete and Working

**Syntax Library:**
- ✅ Lexer with full token support (`%match`, `%call`, `%comptime`, `?` for guards)
- ✅ Grammar DSL with parser/formatter generation
- ✅ Document algebra formatter
- ✅ Source location tracking
- ✅ Error recovery in parser (never panics - returns error AST nodes)
- ✅ Variable patterns in match expressions
- ✅ Source snippet formatter for error display

**Core Language:**
- ✅ All 14 Term variants implemented (including `Err` for error recovery)
- ✅ Two-pass parsing with proper variable shadowing
- ✅ Pattern syntax (wildcards, variables, as-patterns, constructors)
- ✅ Records with fields
- ✅ ASCII syntax (`->`, `$Type`, `#Constructor`, `%match`, `%call`, `%comptime`)
- ✅ Error AST nodes (`Term.Err`, `NamedTerm.NErr`) for graceful error recovery
- ✅ 401 tests passing - ALL TESTS PASS

**CLI:**
- ✅ Command-line argument parsing with `argv`
- ✅ File I/O with `simplifile`
- ✅ `check` and `run` commands
- ✅ Verbose and debug modes
- ✅ Type checker integration (`core.infer`)
- ✅ Evaluator integration (`core.eval` + `core.quote`)
- ✅ Error reporting infrastructure (source snippets ready)
- ✅ Parser never panics on invalid input

**Examples:**
- ✅ 10 working core examples
- ✅ 7 syntax error examples
- ✅ 2 syntax recovery examples

**Error Reporting:**
- ✅ Source snippet formatter (`syntax/source_snippet.gleam`)
- ✅ Enhanced parse error types with spans (`ParseErrorWithSpan`)
- ✅ Error reporter module (`syntax/error_reporter.gleam`)
- ✅ Error AST nodes for graceful recovery
- 📋 Source snippet display in CLI (infrastructure ready, integration pending)

### 📋 Pending (Production Readiness)

**Critical Issues:**
1. ✅ Match expression parsing - FIXED (added variable patterns)
2. ✅ Type checker integrated with CLI
3. ✅ Evaluator integrated with CLI
4. ✅ Parser never panics - returns error AST nodes
5. ✅ All 401 tests passing - FIXED pattern matching bug (`[..]` → `[_, ..]`)
6. ⏳ Source snippet display integration in CLI
7. ⏳ Exhaustiveness checking in CLI

**Enhancement Areas:**
- 📋 Multi-span error display (e.g., type mismatches)
- 📋 Error codes for all error types (E0001, E0101, etc.)
- 📋 Suggestions/hints for common errors
- 📋 JSON error output format
- 📋 Color terminal support
- 📋 FFI and comptime full support
- 📋 Performance optimizations

---

## Critical Issues (Must Fix)

### 1. Fix Match Expression Parsing

**Problem**: Match expressions fail to parse with "Parse failed" error.

**Current Status**: The `Match` grammar rule exists but parsing fails.

**Root Cause**: Likely issue with `Cases` rule or pattern parsing in match context.

**Fix Required**:
- [ ] Debug match expression parsing
- [ ] Fix `Cases` grammar rule
- [ ] Fix `Pattern` grammar rule for match context
- [ ] Add match expression tests
- [ ] Verify round-trip: parse → format → parse

**Files to Update**:
- `src/core/syntax.gleam` - Fix grammar rules
- `test/core/syntax_test.gleam` - Add match tests
- `examples/core/` - Add working match examples
- `examples/core/errors/exhaustiveness_checks/` - Add exhaustiveness examples

**Estimated Effort**: 2-4 hours

---

### 2. Integrate Type Checker with CLI

**Problem**: CLI only performs parsing, not type checking.

**Current Status**: `core/core.gleam` has full type checker implementation, but CLI doesn't use it.

**Fix Required**:
- [ ] Import `core/core` in `compiler_bootstrap.gleam`
- [ ] Wire up `core.infer()` in `check_core()` function
- [ ] Format and display type errors with source locations
- [ ] Add type error examples to `examples/core/errors/type_errors/`
- [ ] Test type error reporting

**Files to Update**:
- `src/compiler_bootstrap.gleam` - Add type checking integration
- `examples/core/errors/type_errors/README.md` - Update with working examples
- `docs/plans/core/` - Update implementation status

**Estimated Effort**: 4-6 hours

---

### 3. Implement Exhaustiveness Checking

**Problem**: Pattern match coverage checking not integrated.

**Current Status**: Maranget's algorithm is implemented in `core/core.gleam` but not called.

**Fix Required**:
- [ ] Call exhaustiveness checker after type checking
- [ ] Format and display coverage errors
- [ ] Add missing case examples
- [ ] Add redundant case examples
- [ ] Test exhaustiveness checking

**Files to Update**:
- `src/compiler_bootstrap.gleam` - Add exhaustiveness checking
- `examples/core/errors/exhaustiveness_checks/` - Add working examples

**Estimated Effort**: 3-5 hours

---

### 4. Implement Proper Exit Codes

**Problem**: CLI always exits with 0, even on errors.

**Current Status**: Exit codes defined in types but not used.

**Fix Required**:
- [ ] Use `gleam/io` exit functions (or FFI if needed)
- [ ] Exit 0 on success
- [ ] Exit 1 on parse/type errors
- [ ] Exit 2 on runtime errors
- [ ] Exit 3 on file not found
- [ ] Exit 4 on invalid arguments

**Files to Update**:
- `src/compiler_bootstrap.gleam` - Add exit codes

**Estimated Effort**: 1-2 hours

---

### 5. Improve Error Message Formatting

**Problem**: Error messages lack source snippets and context.

**Current Status**: Basic error messages with position info only.

**Fix Required**:
- [ ] Add source snippet formatting (like Rust compiler)
- [ ] Show line numbers and column pointers
- [ ] Add context lines (before/after error)
- [ ] Add helpful hints/suggestions
- [ ] Colorize output (if terminal supports it)

**Example Output**:
```
error: Type mismatch
  ┌─ examples/bad.core.tao:3:5
  │
3 │ (x : $I32) -> x
  │     ^^^^^ Expected $Type, got $I32
  │
  = hint: Try using $Type instead
```

**Files to Update**:
- `src/compiler_bootstrap.gleam` - Add error reporter module
- `src/syntax/grammar.gleam` - Enhance `ParseError` with more context

**Estimated Effort**: 4-8 hours

---

## Enhancement Areas (Should Have)

### 6. Runtime Evaluation Integration

**Goal**: Full evaluation of core expressions in `run` command.

**Current Status**: `run` command only formats and prints, doesn't evaluate.

**Work Required**:
- [ ] Wire up `core.eval()` in `run_core()` function
- [ ] Format and display evaluation results
- [ ] Handle runtime errors (division by zero, etc.)
- [ ] Add evaluation examples

**Estimated Effort**: 3-5 hours

---

### 7. FFI and Comptime Support

**Goal**: Full support for foreign function calls and compile-time evaluation.

**Current Status**: FFI and comptime terms exist but not fully integrated.

**Work Required**:
- [ ] Fix comptime parsing (currently broken)
- [ ] Implement FFI call evaluation
- [ ] Add comptime examples
- [ ] Add FFI examples

**Estimated Effort**: 6-10 hours

---

### 8. Performance Optimizations

**Goal**: Reasonable performance for large files.

**Current Status**: No performance testing done.

**Work Required**:
- [ ] Benchmark parsing performance
- [ ] Benchmark type checking performance
- [ ] Optimize hot paths
- [ ] Add performance regression tests

**Estimated Effort**: 4-8 hours

---

### 9. Documentation and Examples

**Goal**: Comprehensive documentation for users and developers.

**Current Status**: Basic documentation exists but incomplete.

**Work Required**:
- [ ] User guide (getting started, tutorial)
- [ ] Language reference (complete syntax and semantics)
- [ ] CLI reference (all commands and options)
- [ ] API documentation (for library users)
- [ ] More examples (real-world use cases)
- [ ] Migration guide (for Tao language)

**Estimated Effort**: 8-16 hours

---

## Nice to Have (Could Have)

### 10. Watch Mode

**Goal**: Automatically re-check files on changes.

**Work Required**:
- [ ] Add `--watch` flag
- [ ] File system watching
- [ ] Incremental re-checking
- [ ] Clear screen on re-run

**Estimated Effort**: 4-6 hours

---

### 11. REPL

**Goal**: Interactive read-eval-print loop.

**Work Required**:
- [ ] Line editing support
- [ ] History
- [ ] Type display
- [ ] Context management

**Estimated Effort**: 8-12 hours

---

### 12. Output File Generation

**Goal**: Compile to executable or bytecode.

**Work Required**:
- [ ] Add `--output` flag
- [ ] Code generation (Erlang or JavaScript)
- [ ] Linking support
- [ ] Optimization passes

**Estimated Effort**: 20-40 hours

---

## Implementation Priority

### Phase 1: Critical Fixes (Week 1-2)
1. Fix match expression parsing
2. Integrate type checker with CLI
3. Implement proper exit codes

### Phase 2: Error Handling (Week 2-3)
4. Improve error message formatting
5. Implement exhaustiveness checking

### Phase 3: Runtime (Week 3-4)
6. Runtime evaluation integration
7. FFI and comptime support

### Phase 4: Polish (Week 4-6)
8. Performance optimizations
9. Documentation and examples

### Phase 5: Advanced Features (Future)
10. Watch mode
11. REPL
12. Output file generation

---

## Success Criteria

A production-ready compiler should:

- [ ] Parse all valid core programs without errors
- [ ] Reject all invalid programs with clear error messages
- [ ] Type check programs correctly
- [ ] Report all errors (not just the first one)
- [ ] Provide helpful error messages with source locations
- [ ] Exit with appropriate exit codes
- [ ] Handle large files efficiently
- [ ] Have comprehensive documentation
- [ ] Have a good set of examples

---

## Related Documents

- **[01-overview.md](../core/01-overview.md)** - Core language overview
- **[02-syntax.md](../core/02-syntax.md)** - Syntax specification
- **[05-cli.md](../cli/01-overview.md)** - CLI documentation
- **[../grammar/01-overview.md](../grammar/01-overview.md)** - Grammar system overview

---

## References

- [Core Syntax](../../src/core/syntax.gleam)
- [Core Evaluator](../../src/core/core.gleam)
- [CLI Implementation](../../src/compiler_bootstrap.gleam)
- [Examples](../../examples/core/)
