# Implementation Roadmap

## Overview

This roadmap breaks the rewrite into **7 phases**, each producing a working, testable increment. The MVP is delivered in Phase 3, and all remaining features are added incrementally.

## Phase 0: Setup and Migration (1-2 days)

### Goals
- Create the new directory structure
- Back up the existing codebase
- Set up build configuration

### Tasks
1. Create `plans/rewrite/` directory (done ✓)
2. Create new directory structure under `src/` and `test/`
3. Move existing code to `old/` directory
4. Update `gleam.toml` for new structure
5. Create basic project structure files

### Deliverables
- `old/` directory contains the complete existing codebase
- New directory structure is set up
- `gleam test` passes (empty test suite)

## Phase 1: Grammar Library (3-4 days)

### Goals
- Language-agnostic grammar library that both Core and Tao use
- Robust tokenizer
- Parser combinator DSL
- Document algebra and layout algorithm
- Parse error accumulation

### Tasks

#### 1.1 Lexer (src/syntax/lexer.gleam)
- Implement tokenizer with span tracking
- Support all token types: Integer, Float, String, Name, Op, Keyword, Comment
- Handle escape sequences in strings
- Handle comments (single-line and block)
- Handle Unicode

**Tests:** tokenization of every token type, position tracking, escape sequences, comments, empty input

#### 1.2 Grammar DSL (src/syntax/grammar.gleam)
- Implement pattern types: Token, Keyword, Op, Ref, Seq, Opt, Many, Choice, Parens, Delimited
- Implement operator types: Prefix, Postfix, Infix
- Implement parser combinator functions: alt, ref, seq, opt, many, choice, sep1, delimited
- Implement grammar definition API: rule, left_assoc_rule, right_assoc_rule
- Implement parse error types and accumulation

**Tests:** every combinator, error accumulation, span accuracy, empty input

#### 1.3 Formatter (src/syntax/formatter.gleam)
- Implement document algebra: Empty, Text, Line, HardLine, Group, Nest, Concat
- Implement layout algorithms: render, format_to_string
- Implement layout helpers: join, space_sep, comma_sep, parens, braces, brackets
- Implement grammar-guided formatting: format_binop_with_grammar

**Tests:** document operations, layout decisions, precedence-based wrapping, empty docs

#### 1.4 Error Reporter (src/syntax/error_reporter.gleam)
- Implement parse error formatting with source context
- Implement span highlighting
- Implement note and hint formatting

**Tests:** error formatting for every parse error type, span accuracy

### Phase 1 Testing Criteria
- ✅ All 100+ lexer tests pass
- ✅ All 50+ grammar combinator tests pass
- ✅ All 20+ formatter tests pass
- ✅ Golden tests (parse → format → parse) pass for both Core and Tao
- ✅ Error accumulation works correctly for all error types

## Phase 2: Core Language (5-7 days)

### Goals
- Language-agnostic core language implementation
- Bidirectional type inference/checking
- Normalization by evaluation
- Quote (Value → Term)
- Unification and substitution
- Generalization
- Exhaustiveness checking

### Tasks

#### 2.1 Core AST (src/core/ast.gleam)
- Define Term, Value, Pattern, Case, Head, Elim types
- Define LitValue, LitType, CtrDef, CtrEnv types
- Define Env, Context, Subst types
- Implement shift_term, error_term, make_neut, make_hole_neut, make_var_neut

**Tests:** every type constructor, shift operations, equality checks

#### 2.2 Core Syntax (src/core/syntax.gleam)
- Define Core grammar (using grammar library)
- Implement Core parser
- Implement Core formatter
- Implement parse → format → parse round-trip

**Tests:** every Core syntax form, span accuracy, round-trip

#### 2.3 State (src/core/state.gleam)
- Define State, FfiEntry, Error types
- Implement initial_state, with_err, continue_with_errors
- Implement error accumulation utilities

**Tests:** state manipulation, error accumulation, FFI entry creation

#### 2.4 Unification (src/core/unify.gleam)
- Implement unify function
- Implement occurs check
- Implement literal type unification (ILitT, FLitT)
- Implement hole instantiation (positive/negative IDs)

**Tests:** every type pair, occurs check, literal type resolution, hole instantiation

#### 2.5 Substitution (src/core/subst.gleam)
- Implement force (evaluate through substitution)
- Implement force_levels_to_indices (value → term)
- Implement shift_term (already in ast)

**Tests:** force on every value type, level-to-index conversion, shift operations

#### 2.6 Generalization (src/core/generalize.gleam)
- Implement generalize (quantify holes)
- Handle implicit parameters

**Tests:** generalization of every type form, implicit param handling

#### 2.7 Evaluation (src/core/eval.gleam)
- Implement evaluate (NBE)
- Implement evaluate_with_ffi
- Implement do_app (neutral spine application)
- Implement neutral spine evaluation

**Tests:** every value form, step limit, FFI calls, neutral spine

#### 2.8 Quote (src/core/quote.gleam)
- Implement quote (Value → Term)
- Implement quote_with_env
- Verify quote does NOT call eval (critical invariant)

**Tests:** every value form, quote ≠ eval, nested lambda quoting

#### 2.9 Type Inference (src/core/infer.gleam)
- Implement infer (synthesis)
- Implement check (verification)
- Implement infer_pattern
- Implement infer_match
- Implement infer_fix
- Implement infer_comptime
- Implement all error cases

**Tests:** every term form, every error case, type mismatch accumulation

#### 2.10 Exhaustiveness (src/core/exhaustiveness.gleam)
- Implement check_exhaustiveness (Maranget's algorithm)
- Implement is_redundant
- Handle guards conservatively

**Tests:** every pattern combination, redundant cases, missing cases, guards

### Phase 2 Testing Criteria
- ✅ All 200+ core unit tests pass
- ✅ Every function has example-based tests
- ✅ Golden tests (term → eval → quote → term) pass
- ✅ Round-trip (parse → format → parse) passes
- ✅ Church numerals work correctly
- ✅ Exhaustiveness checking catches all missing/redundant cases

## Phase 3: Tao Language MVP (5-7 days)

### Goals
- Tao high-level language
- Desugaring to Core
- Basic compilation pipeline
- Test framework

### Tasks

#### 3.1 Tao AST (src/tao/ast.gleam)
- Define Expr, Stmt, Pattern, TypeAst types
- Define Literal, BinOp, UnaryOp, RecordField, MatchClause types
- Define Param, Constructor, ConstructorField types
- Define ImportItem, ImportName types
- Implement span helpers: span_from_expr, span_from_pattern, span_from_stmt

**Tests:** every type constructor, span helpers, structural equality

#### 3.2 Tao Lexer (src/tao/lexer.gleam)
- Extend base lexer with Tao-specific tokens
- Support Tao keywords: fn, let, mut, in, match, case, type, of, import, as, test, run, comptime, if, else, for, while, loop, break, continue, return, yield

**Tests:** every Tao keyword, operator, and literal type

#### 3.3 Tao Syntax (src/tao/syntax.gleam)
- Define Tao grammar (using grammar library)
- Implement Tao parser
- Implement Tao formatter
- Implement parse → format → parse round-trip

**Tests:** every Tao syntax form, span accuracy, round-trip

#### 3.4 Desugar (src/tao/desugar.gleam)
- Implement desugar_expr (every Tao expression → Core term)
- Implement desugar_stmt (every Tao statement → Core term)
- Implement desugar_module (module → Core term)
- Implement loop context tracking (break/continue)

**Desugar tests:** every high-level feature:
- Lambda abstraction
- Function definition
- Let binding
- Pattern matching
- If-else
- For loop
- While loop
- Loop (infinite)
- Break/continue
- Yield/generator
- Mutable variables
- Record update
- Pipe operator
- Result bind
- Comptime block
- Run statement
- Test statement

#### 3.5 Compiler Pipeline (src/tao/compiler.gleam)
- Implement compile_tao (full pipeline)
- Implement compile_core (Core only pipeline)
- Implement error collection across phases

**Tests:** every pipeline stage, error accumulation, partial results

#### 3.6 Test API (src/tao/test_api.gleam)
- Implement test framework
- Implement expect assertions
- Implement test execution

**Tests:** test framework basic operations, assertion failures

### Phase 3 Testing Criteria
- ✅ All 100+ Tao unit tests pass
- ✅ All 50+ desugar tests pass
- ✅ All 30+ compiler tests pass
- ✅ MVP can compile a complete Tao program (fibonacci, map/filter)
- ✅ Test framework works correctly
- ✅ Error accumulation works across all phases

## Phase 4: Module System (3-4 days)

### Goals
- Multi-file compilation
- Import resolution
- Module dependency tracking
- Circular import detection

### Tasks

#### 4.1 Language Config (src/tao/language_config.gleam)
- Define LanguageConfig type
- Implement default_config()
- Implement config-based type/operator lookup

**Tests:** config lookup for every type/operator

#### 4.2 Global Context (src/tao/global_context.gleam)
- Define GlobalContext type
- Implement module loading
- Implement constructor environment building
- Implement type-to-core conversion

**Tests:** module loading, constructor environment, type conversion

#### 4.3 Import Resolver (src/tao/import_resolver.gleam)
- Implement import resolution (module lookup, name lookup)
- Implement graceful degradation: module-not-found → empty module + error, name-not-found → deferred to type checker
- Implement selective and wildcard imports

**Tests:** every import variant, module-not-found, name-not-found (deferred), error cases

#### 4.4 Multi-file Compilation (src/tao/compiler.gleam)
- Extend compile_tao with multi-file support
- Implement module merging

**Tests:** every file combination, import variants, error cases

### Phase 4 Testing Criteria
- ✅ All 40+ import tests pass
- ✅ Multi-file compilation works correctly
- ✅ Module-not-found handled gracefully (empty module + error)
- ✅ Name-not-found deferred to type checker
- ✅ Selective and wildcard imports work

## Phase 5: Error Handling & Diagnostics (2-3 days)

### Goals
- Comprehensive error reporting
- Source context formatting
- Error code system

### Tasks

#### 5.1 Error Formatter (src/core/error_formatter.gleam)
- Implement format_diagnostic for every TypeError
- Implement source span highlighting
- Implement note and hint formatting

**Tests:** every error type formatted correctly, span accuracy

#### 5.2 Error Reporter (src/syntax/error_reporter.gleam)
- Implement parse error formatting
- Implement import error formatting

**Tests:** every error type formatted correctly

#### 5.3 Tao Error Reporter (src/tao/error_reporter.gleam)
- Implement Tao-specific error formatting
- Integrate with Core error formatter

**Tests:** every Tao error type formatted correctly

### Phase 5 Testing Criteria
- ✅ All 50+ error formatting tests pass
- ✅ Every error has accurate spans
- ✅ Error output is human-readable with source context
- ✅ All 30+ error codes are documented

## Phase 6: High-Level Features (3-4 days)

### Goals
- All remaining high-level features
- Generator/Stream support
- Record update syntax
- Optional chaining

### Tasks

#### 6.1 Generator Support
- Implement Stream type in stdlib
- Implement yield desugaring
- Implement Stream helpers (map, filter, fold)

**Tests:** Stream creation, Stream operations, yield desugaring

#### 6.2 Record Update
- Implement record update syntax desugaring
- Implement partial record update

**Tests:** complete record update, partial record update

#### 6.3 Optional Chaining
- Implement optional chaining desugaring
- Implement Result.unwrap and Error handling

**Tests:** optional chaining, Result handling

#### 6.4 Performance Optimizations
- Implement NBE optimizations (step limit)
- Implement term normalization during type checking
- Implement caching for repeated evaluations

**Tests:** performance benchmarks, step limit behavior

### Phase 6 Testing Criteria
- ✅ All 60+ high-level feature tests pass
- ✅ Generators work correctly
- ✅ Record update works correctly
- ✅ Optional chaining works correctly
- ✅ Performance is acceptable

## Phase 7: Integration & Polish (2-3 days)

### Goals
- End-to-end tests
- Documentation
- CLI improvements
- Final cleanup

### Tasks

#### 7.1 End-to-End Tests
- Implement e2e_test.gleam
- Test complete Tao programs (fib, map/filter, generators)
- Test Core programs from examples

**Tests:** every example program

#### 7.2 Documentation
- Update README.md
- Document new architecture
- Add usage examples

#### 7.3 CLI Improvements
- Improve error output formatting
- Add --list flag for tests
- Add --filter flag for test names

#### 7.4 Final Cleanup
- Remove duplicate code
- Verify all tests pass
- Verify no import cycles
- Verify no hardcoded assumptions

### Phase 7 Testing Criteria
- ✅ All 500+ tests pass
- ✅ All examples work correctly
- ✅ No import cycles
- ✅ No hardcoded assumptions (dummy spans, truth constructors, etc.)
- ✅ CLI is user-friendly
- ✅ Documentation is complete

## Summary

| Phase | Days | Features | Test Count |
|-------|------|----------|------------|
| 0: Setup | 1-2 | Directory structure, backup | 0 |
| 1: Grammar | 3-4 | Lexer, parser, formatter | 170+ |
| 2: Core | 5-7 | Type checking, evaluation, quoting | 200+ |
| 3: Tao MVP | 5-7 | Desugaring, compilation, tests | 180+ |
| 4: Modules | 3-4 | Import system, multi-file | 40+ |
| 5: Errors | 2-3 | Error reporting, diagnostics | 50+ |
| 6: Features | 3-4 | Generators, record update, optional chaining | 60+ |
| 7: Polish | 2-3 | E2E tests, docs, CLI | 50+ |
| **Total** | **24-34** | **Complete language** | **~750** |

## Risk Mitigation

| Risk | Mitigation |
|------|-----------|
| Grammar library is too complex | Build incrementally, test each combinator |
| Core type checking is buggy | Start with simple terms, gradually add complexity |
| Desugaring is error-prone | Write desugar tests for each feature independently |
| Import resolution is inconsistent | Always: module-not-found → empty module + error, name-not-found → deferred to type checker |
| Error accumulation is incomplete | Test every error path explicitly |
| Performance is poor | Profile early, optimize NBE step limit |

## Success Criteria

1. ✅ All existing examples still work (fibonacci, Church numerals, higher-order functions)
2. ✅ All existing tests pass (700+ tests)
3. ✅ No import cycles
4. ✅ No hardcoded assumptions
5. ✅ Every function has example-based tests
6. ✅ Error accumulation works correctly at every phase
7. ✅ Parser, formatter, type checker, evaluator all recover from errors
8. ✅ Multi-file compilation works correctly
9. ✅ Import system handles all variants (selective, wildcard); module-not-found → empty module + error; name-not-found deferred to type checker
10. ✅ High-level features desugar correctly to Core
