# Implementation Roadmap

## Overview

This roadmap breaks the rewrite into **5 phases**, each producing a working increment. The MVP CLI (run/check/test) is delivered in Phase 3. All remaining features are added incrementally.

## Quick Reference: What's Built When

```
Phase 1  → Lexer + Core types         → No runnable code
Phase 2  → Parser + Type Checker + NBE → `tao run <file>` works
Phase 3  → Tao + Desugar + Test API   → `tao run`, `tao check`, `tao test` all work
Phase 4  → Multi-file + Import        → Full compilation
Phase 5  → Extended Features + Polish → Full design
```

## Phase 1: Lexer + Core Types (2-3 days)

### Goals
- Tokenizer with span tracking
- Core AST types (Term, Value, Pattern, Literal, State, Error, FfiEntry)
- Basic utilities (shift, error_term, make_neut)

### Tasks

#### 1.1 Lexer (src/syntax/lexer.gleam)
- Implement tokenizer with span tracking
- Support all token types: Integer, Float, String, Name, Op, Keyword, Comment
- Handle escape sequences in strings
- Handle comments (single-line and block)

**Tests:** tokenization of every token type, position tracking, escape sequences, comments, empty input

#### 1.2 Core AST (src/core/ast.gleam)
- Define Term, Value, Pattern, Case, Head, Elim types
- Define Literal { Int, Float, String }, Env, Subst types
- Implement shift_term, error_term, make_neut, make_hole_neut, make_var_neut

**Tests:** every type constructor, shift operations, equality checks

#### 1.3 State (src/core/state.gleam)
- Define State, FfiEntry, Error types
- Implement initial_state, with_err, continue_with_errors

**Tests:** state manipulation, error accumulation, FFI entry creation

### Phase 1 Testing Criteria
- ✅ All 30+ lexer tests pass
- ✅ All 20+ AST tests pass
- ✅ State error accumulation works correctly

## Phase 2: Parser + Core Type Checker + Run CLI (4-5 days)

### Goals
- Core parser + formatter
- Bidirectional type inference/checking
- Normalization by evaluation
- Quote (Value → Term)
- Unification + substitution + generalization
- Exhaustiveness checking
- **CLI `run` command works**

### Tasks

#### 2.1 Grammar DSL + Core Parser (src/syntax/grammar.gleam, src/core/syntax.gleam)
- Implement parser combinator DSL (Seq, Opt, Many, Choice, Ref, Tok, Kw, Op)
- Define Core grammar
- Implement Core parser
- Implement Core formatter (optional, for debugging)

**Tests:** every combinator, Core syntax form, span accuracy

#### 2.2 Unification (src/core/unify.gleam)
- Implement unify function
- Implement occurs check
- Implement hole instantiation (positive/negative IDs)

**Tests:** every type pair, occurs check, hole instantiation

#### 2.3 Substitution (src/core/subst.gleam)
- Implement force (evaluate through substitution)
- Implement force_levels_to_indices (value → term)
- Implement shift_term (already in ast)

**Tests:** force on every value type, level-to-index conversion, shift operations

#### 2.4 Generalization (src/core/generalize.gleam)
- Implement generalize (quantify holes)

**Tests:** generalization of every type form

#### 2.5 Evaluation (src/core/eval.gleam)
- Implement evaluate (NBE)
- Implement evaluate_with_ffi
- Implement do_app (neutral spine application)

**Tests:** every value form, FFI calls, neutral spine

#### 2.6 Quote (src/core/quote.gleam)
- Implement quote (Value → Term)
- Verify quote does NOT call eval (critical invariant)

**Tests:** every value form, quote ≠ eval, nested lambda quoting

#### 2.7 Type Inference (src/core/infer.gleam)
- Implement infer (synthesis) — returns #(Term, Value, State)
- Implement check (verification) — returns #(Term, Value, State)
- Implement infer_pattern
- Implement infer_match
- Implement infer_fix
- Implement all error cases

**Tests:** every term form, every error case, type mismatch accumulation

#### 2.8 Exhaustiveness (src/core/exhaustiveness.gleam)
- Implement check_exhaustiveness (Maranget's algorithm)
- Implement is_redundant
- Handle guards conservatively

**Tests:** every pattern combination, redundant cases, missing cases

#### 2.9 CLI Run Command (src/cli/run.gleam)
- Implement run mode: parse → desugar (identity) → type check → evaluate → print
- Handle errors from all phases
- Return appropriate exit codes

**Tests:** run simple Core programs, run with errors, run with type errors

### Phase 2 Testing Criteria
- ✅ All 80+ core tests pass
- ✅ Every function has example-based tests
- ✅ `tao run` compiles and evaluates a simple Core program
- ✅ Type errors are reported correctly
- ✅ Exhaustiveness checking catches missing/redundant cases
- ✅ Quote round-trip works (term → eval → quote → term)

## Phase 3: Tao + Desugaring + Test Framework (4-5 days)

### Goals
- Tao high-level language
- Desugaring to Core
- **CLI `check` and `test` commands work**
- Test framework with REPL-style tests

### Tasks

#### 3.1 Tao AST (src/tao/ast.gleam)
- Define Expr, Stmt, Pattern, TypeAst types
- Define Literal, BinOp, UnaryOp, RecordField, MatchClause types
- Define Param, Constructor, ConstructorField types

**Tests:** every type constructor, structural equality

#### 3.2 Tao Syntax (src/tao/syntax.gleam)
- Define Tao grammar (using grammar DSL from Phase 2)
- Implement Tao parser
- Implement Tao formatter
- Implement parse → format → parse round-trip

**Tests:** every Tao syntax form, span accuracy, round-trip

#### 3.3 Desugar (src/tao/desugar.gleam)
- Implement desugar_expr (every Tao expression → Core term)
- Implement desugar_stmt (every Tao statement → Core term)
- Implement desugar_module (module → Core term)
- Implement unified function/operator handling:
  - Track all definitions per name (single or multiple)
  - Always generate pattern match on implicit argument types
  - Single definition → one-branch match; multiple → multi-branch match

**Desugar tests:** every high-level feature:
- Lambda abstraction
- Function definition
- Let binding
- Pattern matching
- If-else
- For loop
- While loop
- Pipe operator
- Binary operators (a + b → "+"(a, b))

#### 3.4 Compiler Pipeline (src/tao/compiler.gleam)
- Implement compile_tao (full pipeline: parse → desugar → check)
- Implement compile_core (Core only pipeline)
- Implement error collection across phases

**Tests:** every pipeline stage, error accumulation, partial results

#### 3.5 Test Framework (src/tao/test_api.gleam)
- Implement REPL-style test extraction from `/// > expr ~> result` comments
- Implement test execution with assertion checking
- Implement test result reporting

**Tests:** test extraction, assertion pass, assertion fail, no tests found

#### 3.6 CLI Check Command (src/cli/check.gleam)
- Implement check mode: parse → desugar → type check → report type or errors
- Don't evaluate — only type check

**Tests:** check simple Tao programs, check with type errors, check with no errors

#### 3.7 CLI Test Command (src/cli/test.gleam)
- Implement test mode: find test statements → compile → evaluate → report results
- Handle test failures gracefully

**Tests:** tests with assertions, tests without assertions, no test statements

### Phase 3 Testing Criteria
- ✅ All 60+ Tao tests pass
- ✅ All 30+ desugar tests pass
- ✅ All 20+ compiler tests pass
- ✅ **`tao run <file>` works** for Tao programs
- ✅ **`tao check <file>` works** for Tao programs
- ✅ **`tao test <file>` works** for Tao programs
- ✅ Test framework extracts and runs REPL-style tests
- ✅ Fibonacci, map/filter compile and run correctly
- ✅ Error accumulation works across all phases

## Phase 4: Multi-file + Import System (3-4 days)

### Goals
- Multi-file compilation
- Import resolution with graceful degradation
- Module dependency tracking

### Tasks

#### 4.1 Language Config (src/tao/language_config.gleam)
- Define LanguageConfig type
- Implement default_config()
- Implement config-based type/operator lookup
- Track truth/false constructor names

**Tests:** config lookup for every type/operator

#### 4.2 Global Context (src/tao/global_context.gleam)
- Define GlobalContext type
- Implement module loading
- Implement constructor environment building
- Implement type-to-core conversion

**Tests:** module loading, constructor environment, type conversion

#### 4.3 Import Resolver (src/tao/import_resolver.gleam)
- Implement import resolution (module lookup, name lookup)
- Implement graceful degradation:
  - **module-not-found** → empty module + error to state
  - **name-not-found** → defer to type checker (no error here)
- Implement selective and wildcard imports

**Tests:** every import variant, module-not-found (empty + error), name-not-found (deferred), error cases

#### 4.4 Multi-file Compilation (src/tao/compiler.gleam)
- Extend compile_tao with multi-file support
- Implement module merging

**Tests:** every file combination, import variants, error cases

### Phase 4 Testing Criteria
- ✅ All 40+ import tests pass
- ✅ Multi-file compilation works correctly
- ✅ Module-not-found handled gracefully (empty module + error)
- ✅ Name-not-found deferred to type checker (VarUndefined error)
- ✅ Selective and wildcard imports work

## Phase 5: Extended Features + Polish (3-4 days)

### Goals
- Full literal type system (ILit/FLit, I32T/I64T/etc.)
- Operator overloading via pattern matching
- Better error messages with codes and source context
- Optional: Comptime, Streams, Record update

### Tasks

#### 5.1 Literal Types (src/core/ast.gleam, src/core/unify.gleam)
- Extend Literal → LitValue { ILit, FLit, StrLit }
- Add LitType { I32T, I64T, U32T, U64T, F32T, F64T, ILitT, FLitT }
- Implement literal type unification (ILitT ↔ I32T, FLitT ↔ F64T, etc.)
- Update VLit to carry LitValue

**Tests:** integer literal polymorphism (1 as I32 or I64), float literal (3.14 can't be I32), cross-type rejection

#### 5.2 Operator Overloading (src/core/ast.gleam, src/core/infer.gleam)
- Extend FfiEntry to take fn(List(#(Value, Value))) -> Option(Value)
- Desugar overloaded functions to pattern match on implicit argument types
- Update VCall to pass (value, type) pairs to FFI

**Tests:** overloaded add (I32 + I32 → I32, F64 + F64 → F64), single-definition pattern match, no-overload case, ambiguous overload error

#### 5.3 Error System (src/core/error.gleam, src/cli/*.gleam)
- Add error codes (E0001=Parse syntax, E0101=Type mismatch, etc.)
- Add notes and hints to errors
- Implement source context formatting
- Update CLI output with formatted errors

**Tests:** every error type formatted correctly, accurate spans, error codes documented

#### 5.4 Extended Features (as needed)
- Comptime: Add Comptime to Term, evaluate at compile time
- Streams: Add yield to Expr, Stream type in stdlib
- Record update: Add record update desugar
- Truth/false constructor: Add to State, match on True/False in FFI

### Phase 5 Testing Criteria
- ✅ All 50+ extended feature tests pass
- ✅ Literal type system handles all cases from 03-core-language.md
- ✅ Operator overloading works (pattern matching, single and multiple definitions)
- ✅ Error codes are consistent and documented
- ✅ Source context formatting is human-readable

## Summary

| Phase | Days | Features | CLI Commands | Test Count |
|-------|------|----------|-------------|------------|
| 1: Lexer + Core Types | 2-3 | Tokenizer, Core AST, State, Error | — | 30+ |
| 2: Parser + Core + **Run** | 4-5 | Parser, type checker, NBE, Quote, CLI | `run` ✅ | 80+ |
| 3: Tao + **Check + Test** | 4-5 | Tao parser, desugarer, test framework | `run`, `check`, `test` ✅ | 110+ |
| 4: Multi-file + Import | 3-4 | Import system, module loading | `run`, `check`, `test` ✅ | 40+ |
| 5: Extended + Polish | 3-4 | Literal types, overloading, errors | `run`, `check`, `test` ✅ | 50+ |
| **Total** | **16-21** | **Complete language** | **Full CLI** | **~310** |

## Risk Mitigation

| Risk | Mitigation |
|------|-----------|
| Grammar DSL is too complex | Build incrementally, test each combinator |
| Core type checking is buggy | Start with simple terms, gradually add complexity |
| Desugaring is error-prone | Write desugar tests for each feature independently |
| Import resolution is inconsistent | Always: module-not-found → empty module + error, name-not-found → deferred to type checker |
| Error accumulation is incomplete | Test every error path explicitly |
| Performance is poor | Profile early, optimize NBE step limit |

## Success Criteria

1. ✅ All existing examples still work (fibonacci, Church numerals, higher-order functions)
2. ✅ `tao run`, `tao check`, `tao test` all work from Phase 3 onwards
3. ✅ No circular imports (modules desugared independently)
4. ✅ No hardcoded assumptions (dummy spans, truth constructors, etc.)
5. ✅ Every function has example-based tests
6. ✅ Error accumulation works correctly at every phase
7. ✅ Parser, formatter, type checker, evaluator all recover from errors
8. ✅ Multi-file compilation works correctly (Phase 4)
9. ✅ Import system handles all variants (selective, wildcard); module-not-found → empty module + error; name-not-found deferred to type checker
10. ✅ Operator overloading via pattern matching on implicit parameters (Phase 5)
