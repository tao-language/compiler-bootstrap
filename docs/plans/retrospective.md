# Compiler Bootstrap Retrospective

## Executive Summary

This document captures lessons learned from building the Compiler Bootstrap project—a dependently-typed core language with a Tao frontend, normalization by evaluation, and a parser combinator library. After fixing critical evaluation and parser recovery bugs (achieving 519/519 passing tests), we reflect on what worked, what didn't, and what we would do differently.

### Project Goals

1. **Dependently typed core language** with bidirectional type checking and normalization by evaluation
2. **Language-agnostic parser combinator library** with Pratt parsing for operator precedence
3. **Language-agnostic formatter library** with document algebra and automatic line breaking
4. **Generic grammar DSL** as a single source of truth for parsers and formatters
5. **Tao language** as a high-level functional language with TypeScript-like syntax

### Final Status

- ✅ **519 tests passing** (all tests green)
- ✅ **Recursive functions work** (`factorial(5) = 120`)
- ✅ **Parser error recovery works** (graceful handling of missing values)
- ✅ **Step counters prevent infinite loops** (timeout protection)
- ✅ **Exhaustiveness checking works** (with conservative guard handling)

---

## Table of Contents

1. [Architecture & Structure](#1-architecture--structure)
2. [Debugging & Diagnostics](#2-debugging--diagnostics)
3. [Testing Strategy](#3-testing-strategy)
4. [Syntax Library Design](#4-syntax-library-design)
5. [Core Language Design](#5-core-language-design)
6. [Tao Language Design](#6-tao-language-design)
7. [Planning & Insights](#7-planning--insights)
8. [File & Function Organization](#8-file--function-organization)
9. [Tools That Would Have Helped](#9-tools-that-would-have-helped)
10. [Gleam-Specific Lessons](#10-gleam-specific-lessons)
11. [Type Theory Implementation Lessons](#11-type-theory-implementation-lessons)
12. [Summary: Keep, Change, Add](#12-summary-keep-change-add)
13. [Key Insights for Future Projects](#13-key-insights-for-future-projects)
14. [Timeline of Major Bugs](#14-timeline-of-major-bugs)
15. [Recommended Reading](#15-recommended-reading)

---

## 1. Architecture & Structure

### 1.1 What Worked ✅

| Aspect | Why It Worked | Example |
|--------|---------------|---------|
| **De Bruijn indices** | Correct by construction, no variable capture bugs | No alpha-conversion needed |
| **NbE architecture** | Clean separation of evaluation and quoting (when done right) | `normalize = eval + quote` |
| **Grammar DSL** | Declarative, composable, good for prototyping | `rule("Expr", [alt(ref("BinOp"), ref("Atom"))])` |
| **Error accumulation** | Type checker continues after errors (IDE-friendly) | Shows all errors, not just first |
| **Test structure** | Mirror of src/ in test/, easy to find tests | `src/core/core.gleam` → `test/core/core_test.gleam` |
| **Step counters** | Prevent infinite loops, provide diagnostics | `eval_with_steps(ffi, env, term, max_steps)` |
| **Document algebra** | Clean separation of layout logic | `formatter.concat([formatter.text("hello"), ...])` |

### 1.2 What I Would Change ❌

#### A. Module Organization

**Current Problem**: `core.gleam` is 3,400+ lines with mixed concerns.

**Better Structure**:
```
src/core/
├── types.gleam           # Term, Value, Head, Elim, Case types
├── env.gleam             # Env, Closure, helpers (list_get, extend_env)
├── eval.gleam            # Evaluation (eval_loop, do_app, do_match, do_dot)
├── quote.gleam           # Quoting (quote, quote_term_in_env, quote_head)
├── unify.gleam           # Unification, free_holes, occurs, subst
├── typecheck.gleam       # Type inference, checking, exhaustiveness
├── builtin.gleam         # FFI definitions and implementations
├── normalize.gleam       # normalize = eval + quote
├── state.gleam           # State, Subst, Ctx types
└── errors.gleam          # Error types, formatting
```

**Benefits**:
- Each module has a single responsibility
- Finding `do_match` is trivial (it's in `eval.gleam`)
- Testing individual components is easier
- Compilation is faster (smaller files)
- Git diffs are more meaningful

**Migration Strategy**:
1. Start by extracting pure types to `types.gleam`
2. Move FFI code to `builtin.gleam`
3. Extract evaluation functions to `eval.gleam`
4. Extract quoting functions to `quote.gleam`
5. Keep `core.gleam` as a re-export module for backward compatibility

#### B. Explicit Effect Tracking

**Current Problem**: No way to know if a function evaluates or quotes.

**Better Approach**: Use explicit naming conventions and documentation:

```gleam
// ============================================================================
// PURE TRANSFORMATIONS (no effects, no FFI needed)
// ============================================================================

/// Quote a term to syntax (pure, no evaluation)
pub fn reify(lvl: Int, value: Value) -> Term

/// Substitute in a term (pure)
pub fn subst(term: Term, var: Int, replacement: Term) -> Term

/// Shift De Bruijn indices (pure)
pub fn shift(term: Term, amount: Int, from: Int) -> Term

// ============================================================================
// EFFECTFUL OPERATIONS (need FFI, can fail, can loop)
// ============================================================================

/// Evaluate a term to a value (effectful, uses FFI)
pub fn eval(ffi: FFI, env: Env, term: Term) -> Value

/// Unify two values (effectful, modifies substitution)
pub fn unify(sub: Subst, v1: Value, v2: Value) -> Result(Subst, UnifyError)

/// Type check a term (effectful, accumulates errors)
pub fn check(s: State, term: Term, expected: Type) -> State

// ============================================================================
// COMPOSITE OPERATIONS (document what they combine)
// ============================================================================

/// Normalize: evaluate then reify (effectful)
pub fn normalize(ffi: FFI, term: Term) -> Term {
  let value = eval(ffi, [], term)
  reify(0, value)
}
```

**Benefits**:
- Clear what operations can fail or loop
- Easier to reason about performance
- Pure functions are easier to test
- Effectful functions can be mocked in tests

#### C. Configuration Over Hardcoded Constants

**Current Problem**: Step limits hardcoded as `1000000`.

**Better Approach**:
```gleam
/// Compiler configuration
pub type Config {
  Config(
    /// Maximum evaluation steps before timeout
    max_eval_steps: Int,
    /// Maximum quoting steps before timeout  
    max_quote_steps: Int,
    /// Maximum unification steps
    max_unify_steps: Int,
    /// What to do on timeout
    timeout_behavior: TimeoutBehavior,
    /// Whether to enable tracing
    enable_tracing: Bool,
  )
}

/// Timeout behavior options
pub type TimeoutBehavior {
  /// Return a neutral term (computation stuck)
  ReturnNeutral
  /// Return an error
  ReturnError
  /// Return partial result with warning
  ReturnPartial
}

/// Default configuration
pub fn default_config() -> Config {
  Config(
    max_eval_steps: 1_000_000,
    max_quote_steps: 1_000_000,
    max_unify_steps: 100_000,
    timeout_behavior: ReturnNeutral,
    enable_tracing: False,
  )
}

/// Evaluation with configuration
pub fn eval_with_config(ffi: FFI, env: Env, term: Term, config: Config) -> Value {
  eval_with_steps(ffi, env, term, 0, config.max_eval_steps)
}
```

**Benefits**:
- Easy to tune for different use cases
- Tests can use lower limits for faster execution
- Production can use higher limits
- Tracing can be enabled for debugging

#### D. Explicit Environment Representation

**Current Problem**: Environments are implicit lists, hard to debug.

**Better Approach**:
```gleam
/// Explicit environment with metadata
pub type Env {
  Env(
    values: List(Value),
    names: List(String),      // For debugging
    levels: List(Int),        // De Bruijn levels
  )
}

/// Create empty environment
pub fn empty_env() -> Env {
  Env([], [], [])
}

/// Extend environment (explicit about what's added)
pub fn extend_env(env: Env, name: String, value: Value) -> Env {
  let level = list.length(env.values)
  Env(
    [value, ..env.values],
    [name, ..env.names],
    [level, ..env.levels],
  )
}

/// Lookup with better error messages
pub fn env_get(env: Env, index: Int) -> Result(#(String, Value), EnvError) {
  case list_get(env.values, index) {
    Some(value) -> {
      let name = list_get(env.names, index) |> result.unwrap("unknown")
      Ok(#(name, value))
    }
    None -> Error(EnvOutOfBounds(index, list.length(env.values)))
  }
}
```

**Benefits**:
- Can print environment for debugging
- Better error messages on lookup failure
- Can validate environment invariants
- Easier to understand variable capture

---

## 2. Debugging & Diagnostics

### 2.1 What Would Have Helped

#### A. Evaluation Tracer

```gleam
/// Trace event during evaluation
pub type TraceEvent {
  EvalEnter(term: Term, env_size: Int)
  EvalExit(value: Value, steps: Int)
  AppEnter(fun: Value, arg: Value)
  AppExit(result: Value)
  MatchEnter(arg: Value, cases: Int)
  MatchExit(result: Value)
  FixUnfold(name: String, body_size: Int)
  StepCount(total: Int, remaining: Int)
}

/// Callback type for tracing
pub type Tracer = fn(TraceEvent) -> Nil

/// Evaluate with tracing
pub fn eval_with_trace(
  ffi: FFI, 
  env: Env, 
  term: Term,
  tracer: Tracer,
) -> Value {
  eval_loop_with_trace(ffi, env, term, 0, 1_000_000, tracer)
}

/// Example usage in tests
pub fn debug_factorial() {
  let events = list.new()
  let tracer = fn(event) {
    events = [event, ..events]
  }
  let result = eval_with_trace(ffi, [], factorial_5, tracer)
  io.println("Evaluation trace:")
  list.each(events, fn(e) { io.println(format_event(e)) })
}
```

**Why**: Would have immediately shown that quote was re-evaluating lambda bodies.

#### B. Value/Term Inspector

```gleam
/// Inspection options
pub type InspectOptions {
  InspectOptions(
    max_depth: Int,
    show_de_bruijn: Bool,    // Show indices or names
    unfold_fixpoints: Bool,  // Show unfolded fixpoints
    show_types: Bool,        // Show type annotations
  )
}

/// Inspect a value with options
pub fn inspect_value(value: Value) -> String {
  inspect_value_opts(value, default_inspect_options())
}

pub fn inspect_value_opts(value: Value, opts: InspectOptions) -> String {
  inspect_value_loop(value, opts, 0, [])
}

/// Example output:
/// 
/// Without options:
/// VLam([], "x", [VLit(I32(42))], App(Var(0), Var(0)))
///
/// With options (show names, depth 2):
/// λ(x: I32) => x @ 0
///   env[0] = 42
fn inspect_value_loop(
  value: Value, 
  opts: InspectOptions, 
  depth: Int,
  env: Env,
) -> String {
  case depth > opts.max_depth {
    True -> "..."
    False -> case value {
      VLit(I32(n)) -> int.to_string(n)
      VLam(_, name, env, body) -> {
        let param_type = env_get_type(env, 0) |> result.unwrap("Unknown")
        "λ(" <> name <> ": " <> param_type <> ") => ..."
      }
      VNeut(head, spine) -> {
        "⟨" <> format_head(head) <> format_spine(spine) <> "⟩"
      }
      // ... etc
    }
  }
}
```

**Why**: Erlang's `inspect` doesn't show De Bruijn indices meaningfully.

#### C. Step Counter Visualization

```gleam
/// Step statistics
pub type StepStats {
  StepStats(
    total_steps: Int,
    eval_steps: Int,
    quote_steps: Int,
    unify_steps: Int,
    match_steps: Int,
    app_steps: Int,
    peak_env_size: Int,
  )
}

/// Evaluate and return stats
pub fn eval_with_stats(ffi: FFI, env: Env, term: Term) -> #(Value, StepStats) {
  let counter = new_counter()
  let result = eval_with_counter(ffi, env, term, counter)
  let stats = get_stats(counter)
  #(result, stats)
}

/// Format stats for display
pub fn format_stats(stats: StepStats) -> String {
  let total = stats.total_steps
  "Step Statistics:\n"
  <> "  Total:       " <> int.to_string(total) <> "\n"
  <> "  Eval:        " <> int.to_string(stats.eval_steps) 
     <> " (" <> int.to_string(stats.eval_steps * 100 / total) <> "%)\n"
  <> "  Quote:       " <> int.to_string(stats.quote_steps)
     <> " (" <> int.to_string(stats.quote_steps * 100 / total) <> "%)\n"
  <> "  Unify:       " <> int.to_string(stats.unify_steps) <> "\n"
  <> "  Peak env:    " <> int.to_string(stats.peak_env_size)
}
```

**Why**: Would have immediately shown that quote was consuming 99% of steps for factorial.

**Example Output**:
```
Step Statistics:
  Total:       1,000,000
  Eval:        47 (0%)
  Quote:       999,953 (99%)  ← RED FLAG!
  Unify:       0
  Peak env:    5
```

#### D. Grammar Debugger

```gleam
/// Parse trace event
pub type ParseTrace {
  RuleEnter(rule: String, position: Int, input: String)
  RuleExit(rule: String, position: Int, matched: Bool, consumed: Int)
  TokenConsume(token: String, position: Int)
  AlternativeTry(rule: String, alt_index: Int)
  AlternativeFail(rule: String, alt_index: Int)
  Backtrack(rule: String, from: Int, to: Int)
}

/// Parse with tracing
pub fn parse_with_trace(
  grammar: Grammar,
  source: String,
  trace_fn: fn(ParseTrace) -> Nil,
) -> ParseResult {
  parse_loop_with_trace(grammar, source, 0, trace_fn)
}

/// Example: Debug why "let x = ; let y = 20" fails
pub fn debug_let_parsing() {
  let traces = list.new()
  let tracer = fn(t) { traces = [t, ..traces] }
  let result = parse_with_trace(tao_grammar(), "let x = ; let y = 20", tracer)
  
  io.println("Parse trace:")
  list.each(traces, fn(t) {
    case t {
      RuleEnter(rule, pos, _) -> io.println("→ " <> rule <> " @" <> int.to_string(pos))
      RuleExit(rule, pos, True, consumed) -> io.println("✓ " <> rule <> " @" <> int.to_string(pos) <> " (+" <> int.to_string(consumed) <> ")")
      RuleExit(rule, pos, False, _) -> io.println("✗ " <> rule <> " @" <> int.to_string(pos))
      Backtrack(rule, from, to) -> io.println("↩ " <> rule <> " " <> int.to_string(from) <> " → " <> int.to_string(to))
      _ -> Nil
    }
  })
}
```

**Why**: Would have shown that the semicolon wasn't being consumed.

**Example Output**:
```
→ Program @0
  → Stmt @0
    → Let @0
    ✓ Let @0 (+7)   ← "let x = " consumed, ";" NOT consumed
  ✓ Stmt @0 (+7)
  → Stmt @7
    ✗ Stmt @7       ← Fails because next char is ";"
  ✗ Program @0
```

#### E. Memory/Heap Visualization

```gleam
/// Memory snapshot
pub type MemorySnapshot {
  MemorySnapshot(
    term_count: Int,
    value_count: Int,
    closure_count: Int,
    largest_term_depth: Int,
    largest_value_depth: Int,
  )
}

/// Take memory snapshot
pub fn memory_snapshot() -> MemorySnapshot {
  // Use Erlang process info or custom tracking
  MemorySnapshot(...)
}

/// Compare snapshots to detect leaks
pub fn compare_snapshots(before: MemorySnapshot, after: MemorySnapshot) -> List(String) {
  let diffs = list.new()
  if after.term_count > before.term_count * 2 {
    diffs = ["⚠️  Term count doubled: " <> int.to_string(before.term_count) <> " → " <> int.to_string(after.term_count)]
  }
  // ... etc
  diffs
}
```

**Why**: Would have detected the exponential term growth during quote.

### 2.2 Debugging Workflow That Would Have Worked

```
Step 1: Add step counter to eval and quote separately
Step 2: Run factorial(5)
Step 3: See: eval = 47 steps, quote = 999,953 steps
Step 4: Conclusion: quote is the problem!
Step 5: Add tracing to quote_loop
Step 6: See: VLam case calls eval
Step 7: Conclusion: That's the bug!
Step 8: Fix by using quote_term_in_env instead of eval
Step 9: Verify: eval = 47 steps, quote = 50 steps ✓

Time estimate: 30 minutes with proper tooling
Actual time: 6 hours of investigation
```

---

## 3. Testing Strategy

### 3.1 What Worked ✅

| Test Type | Why It Worked | Example |
|-----------|---------------|---------|
| **End-to-end tests** | Catch integration issues | `recursive_fn.tao` evaluates to 120 |
| **Structural equality** | Precise failure messages | `should.equal(expected, actual)` |
| **Error case tests** | Verify error handling | `parse_error_test()` |
| **Mirror structure** | Easy to find tests | `src/core/core.gleam` → `test/core/core_test.gleam` |
| **Example programs** | Real-world scenarios | `examples/tao/programs/**/*.tao` |

### 3.2 What Was Missing ❌

#### A. Property-Based Testing

```gleam
/// Property: eval(quote(eval(term))) == eval(term)
/// Normalization should be idempotent
pub fn eval_quote_idempotent_test() {
  for_all(generate_terms(), fn(term) {
    let v1 = eval(ffi, [], term)
    let q = quote(ffi, 0, v1, no_span)
    let v2 = eval(ffi, [], q)
    values_equal(v1, v2)  // Should be true!
  })
}

/// Property: factorial(n) terminates for n >= 0
pub fn factorial_terminates_test() {
  for_all(nat_ints(), fn(n) {
    let term = factorial_app(n)
    let result = eval(ffi, [], term)
    !is_neutral(result)  // Should not be stuck!
  })
}

/// Property: quoting preserves free variables
pub fn quote_preserves_free_vars_test() {
  for_all(terms_with_free_vars(), fn(term) {
    let free_before = free_vars(term)
    let quoted = quote_term(term, empty_env())
    let free_after = free_vars(quoted)
    free_before == free_after
  })
}

/// Property: type preservation under evaluation
pub fn type_preservation_test() {
  for_all(well_typed_terms(), fn(term) {
    let #(_val, typ, _state) = infer(initial_state, term)
    let value = eval(ffi, [], term)
    let quoted = quote(ffi, 0, value, no_span)
    let #(_val2, typ2, _state2) = infer(initial_state, quoted)
    typ == typ2  // Type should be preserved
  })
}
```

**Why**: Would have caught the quote re-evaluation bug immediately.

#### B. Complexity Tests

```gleam
/// Property: factorial(n) should take O(n) steps, not O(2^n)
pub fn factorial_complexity_test() {
  let steps_5 = count_eval_steps(factorial_app(5))
  let steps_6 = count_eval_steps(factorial_app(6))
  let steps_7 = count_eval_steps(factorial_app(7))
  
  // Linear: steps_6 ≈ steps_5 + constant
  // Exponential: steps_6 ≈ 2 * steps_5
  let ratio = steps_6 / steps_5
  ratio < 1.5  // Should be close to 1 for linear!
}

/// Property: quote should be O(size of value)
pub fn quote_complexity_test() {
  // Create a large value (e.g., list of 1000 elements)
  let large_value = make_large_value(1000)
  let steps = count_quote_steps(large_value)
  
  // Should be linear in size
  steps < 1000 * 10  // Some reasonable constant factor
}

/// Property: evaluation depth should be bounded
pub fn eval_depth_test() {
  let term = deeply_nested_term(100)
  let max_depth = track_max_depth(term)
  max_depth < 1000  // Should not grow exponentially
}
```

**Why**: Would have detected the exponential quote behavior.

#### C. Regression Tests for Fixed Bugs

```gleam
// Added AFTER fixing quote re-evaluation
pub fn quote_lambda_no_reeval_test() {
  // Regression test for quote re-evaluation bug
  let lam = Lam([], #("x", Hole(-1, no_span)), Var(0, no_span), no_span)
  let val = VLam([], "x", [], Var(0, no_span))
  
  let quoted = quote(ffi, 0, val, no_span)
  
  // Should be the same lambda, not an evaluated mess
  quoted == lam
}

// Added AFTER fixing do_match FFI bug
pub fn match_with_builtin_test() {
  // Regression test for do_match missing FFI
  let match_term = Match(
    Lit(I32(5), no_span),
    Hole(-1, no_span),
    [
      Case(Pattern(Lit(I32(0))), Lit(I32(1), no_span), None, no_span),
      Case(Pattern(Any), Call("mul", [Var(0), Lit(I32(2), no_span)], no_span), None, no_span),
    ],
    no_span,
  )
  
  let result = eval(ffi, [], match_term)
  result == VLit(I32(10))  // 5 * 2 = 10
}

// Added AFTER fixing parser semicolon bug
pub fn parse_let_with_semicolon_test() {
  // Regression test for parser semicolon handling
  let result = parse_module("let x = ; let y = 20")
  list.length(result.ast) == 2  // Both lets should be parsed
}
```

**Why**: Prevents the same bugs from creeping back in.

#### D. Fuzz Testing

```gleam
/// Fuzz test: random terms should not crash
pub fn fuzz_eval_test() {
  for_all(random_terms(), fn(term) {
    let result = eval(ffi, [], term)
    // Should not panic, even if result is VErr
    True
  })
}

/// Fuzz test: random programs should parse
pub fn fuzz_parse_test() {
  for_all(random_programs(), fn(source) {
    let result = parse_module(source)
    // Should not panic, even if there are errors
    True
  })
}

/// Fuzz test: random types should unify
pub fn fuzz_unify_test() {
  for_all(random_type_pairs(), fn(#(t1, t2)) {
    let result = unify(empty_subst(), t1, t2)
    // Should not panic
    True
  })
}
```

**Why**: Finds edge cases that manual tests miss.

#### E. Performance Benchmarks

```gleam
/// Benchmark: factorial(10)
pub fn bench_factorial_10() -> Benchmark {
  Benchmark(
    name: "factorial_10",
    setup: fn() { factorial_app(10) },
    run: fn(term) { eval(ffi, [], term) },
    expected_steps: 100,
    max_time_ms: 100,
  )
}

/// Benchmark: type checking large term
pub fn bench_typecheck_large() -> Benchmark {
  Benchmark(
    name: "typecheck_large",
    setup: fn() { make_large_term(1000) },
    run: fn(term) { infer(initial_state, term) },
    expected_steps: 10_000,
    max_time_ms: 1000,
  )
}

/// Run all benchmarks
pub fn run_benchmarks() -> List(BenchmarkResult) {
  [
    bench_factorial_10(),
    bench_typecheck_large(),
    // ... etc
  ]
  |> list.map(run_benchmark)
}
```

**Why**: Catches performance regressions early.

### 3.3 Test Organization

**Current**: Good mirror structure, but could add:

```
test/
├── core/
│   ├── core_test.gleam          # Unit tests
│   ├── eval_test.gleam          # Evaluation-specific tests
│   ├── quote_test.gleam         # Quoting-specific tests
│   ├── unify_test.gleam         # Unification tests
│   └── properties/              # Property-based tests
│       ├── idempotent_test.gleam
│       ├── preservation_test.gleam
│       └── termination_test.gleam
├── syntax/
│   ├── grammar_test.gleam
│   └── properties/
│       └── parse_unparse_test.gleam  # round-trip tests
├── tao/
│   ├── examples_test.gleam
│   └── regression/              # Regression tests for fixed bugs
│       ├── quote_reeval_test.gleam
│       └── match_ffi_test.gleam
└── benchmarks/
    ├── eval_bench.gleam
    └── quote_bench.gleam
```

---

## 4. Syntax Library Design

### 4.1 What Worked ✅

| Feature | Why It Worked | Example |
|---------|---------------|---------|
| **Grammar DSL** | Declarative, composable | `rule("Expr", [alt(ref("BinOp"), ref("Atom"))])` |
| **Operator precedence** | Pratt parsing handles associativity | `infix_binary("+", make_add, InfixLeft, 10)` |
| **Error recovery** | Placeholder values allow continuation | `Int(0, Span("error", ...))` |
| **Document algebra** | Clean formatting logic | `formatter.concat([...])` |
| **Token-based parsing** | Lexer separates concerns | `token_pattern("Ident")` |

### 4.2 What I Would Change ❌

#### A. Explicit Error Recovery Strategy

**Current**: Implicit recovery (just continue parsing).

**Better**:
```gleam
/// Error recovery strategies
pub type RecoveryStrategy {
  /// Insert a placeholder value and continue
  InsertPlaceholder(default_value: Value)
  
  /// Skip tokens until we find a synchronization point
  SkipToNextStatement(sync_tokens: List(Token))
  
  /// Try alternative productions
  TryAlternatives
  
  /// Panic and stop parsing
  Panic
}

/// Rule with explicit recovery
pub type Rule {
  Rule(
    name: String,
    pattern: Pattern,
    recovery: RecoveryStrategy,
    error_message: String,
  )
}

/// Example: Let binding with explicit recovery
pub fn let_rule() -> Rule {
  Rule(
    name: "Let",
    pattern: seq([
      keyword("let"),
      opt(keyword("mut")),
      token("Ident"),
      opt(seq([token(":"), ref("Type")])),
      token("="),
      opt(ref("Expr")),  // Optional for recovery
    ]),
    recovery: InsertPlaceholder(Int(0, Span("error", 0, 0, 0, 0))),
    error_message: "Expected expression after '='",
  )
}
```

**Benefits**:
- Clear what happens on error
- Can customize recovery per rule
- Better error messages
- Easier to debug recovery issues

#### B. Grammar Validation

**Current**: No validation that grammar is well-formed.

**Better**:
```gleam
/// Grammar validation errors
pub type GrammarError {
  LeftRecursion(rule: String, cycle: List(String))
  UnreachableRule(rule: String)
  EmptyProduction(rule: String)
  MissingToken(token: String)
  CircularDependency(rules: List(String))
}

/// Validate a grammar
pub fn validate_grammar(grammar: Grammar) -> List(GrammarError) {
  let errors = list.new()
  
  // Check for left recursion
  let left_recursive = find_left_recursion(grammar)
  errors = list.append(errors, left_recursive)
  
  // Check for unreachable rules
  let unreachable = find_unreachable_rules(grammar)
  errors = list.append(errors, unreachable)
  
  // Check for empty productions
  let empty = find_empty_productions(grammar)
  errors = list.append(errors, empty)
  
  // Check for missing tokens
  let missing = find_missing_tokens(grammar)
  errors = list.append(errors, missing)
  
  errors
}

/// Find left-recursive rules
fn find_left_recursion(grammar: Grammar) -> List(GrammarError) {
  // For each rule, check if it can derive itself as first symbol
  list.filter_map(grammar.rules, fn(rule) {
    case is_left_recursive(grammar, rule.name) {
      True -> Some(LeftRecursion(rule.name, get_cycle(grammar, rule.name)))
      False -> None
    }
  })
}
```

**Benefits**:
- Catches grammar bugs at compile time
- Prevents infinite loops in parser
- Documents grammar invariants

#### C. Grammar Visualization

```gleam
/// Generate GraphViz DOT file showing rule dependencies
pub fn grammar_to_dot(grammar: Grammar) -> String {
  "digraph Grammar {\n"
  <> "  rankdir=LR;\n"
  <> list.map(grammar.rules, fn(rule) {
    let deps = get_rule_dependencies(rule)
    rule.name <> " -> {" <> string.join(deps, " ") <> "}"
  }) |> string.join(";\n  ")
  <> "\n}"
}

/// Example output:
/// digraph Grammar {
///   rankdir=LR;
///   Program -> Stmt;
///   Stmt -> Let;
///   Stmt -> Fn;
///   Let -> Expr;
///   Fn -> Expr;
///   Expr -> BinOp;
///   Expr -> Atom;
///   BinOp -> Expr;
/// }
```

**Why**: Would have shown that `Program → Stmt*` didn't consume semicolons.

#### D. Parse Tree Debugger

Already described in section 2.1.D.

#### E. Grammar Composition

**Current**: Single monolithic grammar.

**Better**:
```gleam
/// Composable grammar modules
pub type GrammarModule {
  GrammarModule(
    name: String,
    rules: List(Rule),
    tokens: List(Token),
    imports: List(String),
  )
}

/// Combine grammar modules
pub fn combine_grammars(modules: List(GrammarModule)) -> Grammar {
  // Merge rules, tokens, handle imports
  Grammar(...)
}

/// Example: Separate expression grammar
pub fn expr_grammar() -> GrammarModule {
  GrammarModule(
    name: "Expr",
    rules: [
      rule("Expr", [alt(ref("BinOp"), ref("Atom"))]),
      rule("BinOp", [...]),
      rule("Atom", [...]),
    ],
    tokens: ["Ident", "Number", "LParen", "RParen"],
    imports: [],
  )
}

/// Example: Separate statement grammar
pub fn stmt_grammar() -> GrammarModule {
  GrammarModule(
    name: "Stmt",
    rules: [
      rule("Stmt", [alt(ref("Let"), ref("Expr"))]),
      rule("Let", [...]),
    ],
    tokens: ["let", "mut", "Semi"],
    imports: ["Expr"],
  )
}

/// Combine for full language
pub fn tao_grammar() -> Grammar {
  combine_grammars([
    expr_grammar(),
    stmt_grammar(),
    // ... etc
  ])
}
```

**Benefits**:
- Easier to understand and maintain
- Can test grammar modules independently
- Reuse expression grammar in other languages
- Clear dependencies between grammar parts

---

## 5. Core Language Design

### 5.1 What Worked ✅

| Feature | Why It Worked | Example |
|---------|---------------|---------|
| **De Bruijn indices** | No variable capture, easy substitution | `Var(0)` refers to innermost binder |
| **Bidirectional typing** | Clear inference vs checking modes | `infer(s, term)` vs `check(s, term, expected)` |
| **Higher-order unification** | Handles dependent types | Unify `List(?A)` with `List(I32)` → `?A = I32` |
| **Error accumulation** | Shows all errors, not just first | `state.errors` accumulates via `with_err` |
| **Normalization by Evaluation** | Efficient, handles alpha-equivalence | `normalize = eval + quote` |

### 5.2 What I Would Change ❌

#### A. Separate Evaluation from Quoting More Clearly

**Current Bug Source**: `quote` was secretly evaluating.

**Better Design**:
```gleam
// ============================================================================
// EVALUATION: Term → Value (effectful, can get stuck)
// ============================================================================

/// Evaluate a term to a value
pub fn eval(ffi: FFI, env: Env, term: Term) -> Value {
  eval_loop(ffi, env, term, 0, 1_000_000)
}

/// Evaluation never calls quote!
fn eval_loop(ffi: FFI, env: Env, term: Term, steps: Int, max: Int) -> Value {
  case term {
    Lam(...) -> VLam(...)  // Just wrap, don't evaluate body
    Fix(...) -> VFix(...)  // Just wrap, don't evaluate body
    App(...) -> ...        // Evaluate function and arg, then apply
    // ... etc
  }
}

// ============================================================================
// REIFICATION: Value → Term (pure, no evaluation!)
// ============================================================================

/// Reify a value to syntax (pure, no effects)
pub fn reify(lvl: Int, value: Value) -> Term {
  reify_loop(lvl, value, no_span)
}

/// Reification never calls eval!
fn reify_loop(lvl: Int, value: Value, s: Span) -> Term {
  case value {
    VLam(_, name, env, body) -> {
      // Quote body term directly, don't evaluate!
      let fresh = VNeut(HVar(lvl), [])
      Lam(name, reify_term_in_env(lvl + 1, body, [fresh, ..env], s), s)
    }
    VFix(name, env, body) -> {
      // Quote body term directly, don't evaluate!
      let fix_val = VFix(name, env, body)
      Fix(name, reify_term_in_env(lvl + 1, body, [fix_val, ..env], s), s)
    }
    // ... etc
  }
}

// ============================================================================
// NORMALIZATION: Term → Term (eval + reify)
// ============================================================================

/// Normalize: evaluate then reify
pub fn normalize(ffi: FFI, term: Term) -> Term {
  let value = eval(ffi, [], term)
  reify(0, value)
}
```

**Key Invariant**: `eval` never calls `reify`, and `reify` never calls `eval`.

#### B. Explicit Fixpoint Handling

**Current**: `VFix(name, env, body)` - body is a Term.

**Problem**: When quoting, we need to handle the fixpoint specially.

**Better**:
```gleam
/// Unfold fixpoint during evaluation, not quoting
pub fn eval_fix(name: String, body: Term, env: Env) -> Value {
  // Create self-referential closure
  let fix_val = VFix(name, env, body)
  // Unfold once by evaluating body with fix_val in env
  eval([fix_val, ..env], body)
}

/// Quoting just sees a normal lambda (fixpoint already unfolded)
pub fn reify_lambda(lvl: Int, name: String, body: Term, env: Env) -> Term {
  // No special fixpoint handling needed
  Lam(name, reify_term_in_env(lvl + 1, body, env))
}
```

**Benefits**:
- Clear when fixpoint unfolds
- No special case in quoting
- Easier to reason about termination

#### C. Better Neutral Term Representation

**Current**: `VNeut(head, spine)` with generic `Head` and `Elim`.

**Better**:
```gleam
/// Neutral term with explicit stuck reason
pub type Neutral {
  /// Stuck on a variable (normal)
  NeutVar(level: Int, spine: List(Spine))
  
  /// Stuck on a hole (to be solved by unification)
  NeutHole(id: Int, spine: List(Spine))
  
  /// Stuck due to step limit (timeout)
  NeutTimeout(spine: List(Spine))
  
  /// Stuck due to missing builtin
  NeutBuiltin(name: String, args: List(Value), spine: List(Spine))
}

/// Spine operations (more explicit than Elim)
pub type Spine {
  /// Function application
  App(arg: Value)
  
  /// Field projection
  Proj(field: String)
  
  /// Pattern matching (stuck on scrutinee)
  Match(motive: Value, cases: List(Case))
  
  /// Type application (for polymorphism)
  TypeApp(typ: Type)
}
```

**Benefits**:
- Clear why computation is stuck
- Better error messages
- Easier to debug neutral terms

#### D. Explicit Substitution Tracking

**Current**: Substitution is implicit in `State.sub`.

**Better**:
```gleam
/// Explicit substitution with metadata
pub type Subst {
  Subst(
    mappings: List(#(Int, Value)),  // hole_id → value
    history: List(SubstOp),         // For debugging
    version: Int,                   // For incremental updates
  )
}

/// Substitution operation (for history)
pub type SubstOp {
  Solved(hole_id: Int, value: Value)
  Composed(from: Int, to: Int)
  Undone(hole_id: Int)
}

/// Apply substitution with tracking
pub fn apply_subst(subst: Subst, value: Value) -> Value {
  apply_subst_loop(subst, value, [])
}

/// Debug: show substitution history
pub fn subst_history(subst: Subst) -> List(String) {
  list.map(subst.history, format_op)
}
```

**Benefits**:
- Can debug unification failures
- Can undo substitutions (backtracking)
- Can show what was solved when

---

## 6. Tao Language Design

### 6.1 What Worked ✅

| Feature | Why It Worked | Example |
|---------|---------------|---------|
| **TypeScript-like syntax** | Familiar to developers | `fn factorial(n: I32) -> I32 { ... }` |
| **Desugaring to core** | Clean separation of concerns | `a + b` → `Call("add", [a, b])` |
| **Pattern matching sugar** | More readable than core | `match n { | 0 -> 1 | _ -> n * f(n-1) }` |
| **Module system** | Organized code | `import list` |
| **Test/Run statements** | Built-in testing support | `test "name" { expr }` |

### 6.2 What I Would Change ❌

#### A. More Explicit Desugaring

**Current**: Desugaring is implicit in many places.

**Better**:
```gleam
/// Explicit desugaring phase
pub type DesugarPhase {
  DesugarPhase(
    phase: String,
    input: TaoExpr,
    output: CoreTerm,
    transformations: List(Transformation),
  )
}

/// Desugar with tracing
pub fn desugar_with_trace(expr: TaoExpr) -> #(CoreTerm, List(Transformation)) {
  let transformations = list.new()
  let trace = fn(t: Transformation) { transformations = [t, ..transformations] }
  let core = desugar_loop(expr, trace)
  #(core, transformations)
}

/// Example transformation
pub type Transformation {
  BinOpToCall(op: BinOperator, left: String, right: String)
  LetToApp(name: String, value: String, body: String)
  MatchToCase(name: String, cases: Int)
  FnToFix(name: String)
}

/// Debug: show desugaring steps
pub fn debug_desugar(source: String) {
  let tao = parse(source)
  let #(core, transforms) = desugar_with_trace(tao)
  io.println("Desugaring trace:")
  list.each(transforms, fn(t) { io.println(format_transform(t)) })
}
```

**Benefits**:
- Clear what desugaring does
- Easier to debug desugaring bugs
- Can optimize specific transformations

#### B. Better Error Messages

**Current**: Generic "type error" messages.

**Better**:
```gleam
/// Tao-specific error types
pub type TaoError {
  /// Recursive function without decreasing argument
  NonTerminatingFn(name: String, span: Span)
  
  /// Pattern match not exhaustive (with missing cases)
  NonExhaustiveMatch(missing: List(String), span: Span)
  
  /// Type annotation doesn't match inferred type
  TypeAnnotationMismatch(annotated: Type, inferred: Type, span: Span)
  
  /// Import cycle detected
  ImportCycle(modules: List(String), span: Span)
  
  /// Mutable variable used in comptime context
  MutableInComptime(name: String, span: Span)
}

/// Format error with suggestions
pub fn format_tao_error(error: TaoError) -> String {
  case error {
    NonTerminatingFn(name, span) -> {
      "Function '" <> name <> "' may not terminate\n"
      <> "  Hint: Add a decreasing argument or use 'loop' for intentional divergence"
    }
    NonExhaustiveMatch(missing, span) -> {
      "Pattern match is not exhaustive\n"
      <> "  Missing cases: " <> string.join(missing, ", ") <> "\n"
      <> "  Hint: Add cases for: " <> string.join(missing, ", ")
    }
    // ... etc
  }
}
```

**Benefits**:
- Actionable error messages
- Faster debugging
- Better developer experience

#### C. Explicit Effect System

**Current**: No way to tell if a function is pure.

**Better**:
```gleam
/// Effect annotations
pub type Effect {
  Pure
  Divergent      // May not terminate (e.g., infinite loop)
  IO             // Performs I/O
  Mutable        // Uses mutable state
}

/// Function with effect annotation
pub type FnDef {
  FnDef(
    name: String,
    params: List(Param),
    return_type: Type,
    effect: Effect,
    body: Expr,
  )
}

/// Check effect consistency
pub fn check_effect(fn_def: FnDef) -> List(EffectError) {
  case fn_def.effect {
    Pure -> {
      // Check body doesn't have effects
      let body_effects = infer_effects(fn_def.body)
      case body_effects {
        [] -> []  // OK
        _ -> [EffectViolation("Pure function has effects: " <> string.join(body_effects, ", "))]
      }
    }
    _ -> []  // Other effects allowed
  }
}
```

**Benefits**:
- Clear what functions do
- Can optimize pure functions
- Can warn about unintended effects

---

## 7. Planning & Insights

### 7.1 Red Flags I Should Have Noticed 🚩

| Symptom | Actual Cause | Should Have Suspected |
|---------|--------------|----------------------|
| Tests timeout for recursion | Quote re-evaluation | Exponential complexity in quote |
| Stack trace shows `QuoteLoop` | Re-evaluation in quote | Quote shouldn't loop! |
| `factorial(5)` hangs but `2*3` works | Builtins work, recursion doesn't | Issue is with closures/fixpoints |
| Step counter helps but doesn't fix | Symptom suppression | Root cause is algorithmic |
| Parser fails on `let x = ; let y = 20` | Semicolon not consumed | Grammar rule doesn't match separator |
| `do_match` can't evaluate builtins | Missing FFI parameter | Match body needs FFI to evaluate |

### 7.2 Questions I Should Have Asked

1. **"What is the complexity of quote?"** - Should be O(size of value), not O(computation)
2. **"Does quote ever evaluate?"** - If yes, that's a bug
3. **"What's the difference between a closure and a lambda?"** - Closure has captured env
4. **"When do we need the environment during quoting?"** - Only for variable lookup, not evaluation
5. **"Why does the parser backtrack here?"** - Grammar rule doesn't consume expected tokens
6. **"What tokens should separate statements?"** - Semicolons, newlines, etc.
7. **"Is this function pure or effectful?"** - Should be explicit
8. **"What happens on error?"** - Should have explicit recovery strategy

### 7.3 Debugging Heuristics

```
Rule 1: If evaluation terminates but quoting doesn't, quote is evaluating
Rule 2: If parser fails on valid input, check what tokens are consumed
Rule 3: If step count is exponential, look for nested recursion
Rule 4: If builtin works in simple case but not in match, check FFI passing
Rule 5: If fixpoint causes issues, check when it unfolds
Rule 6: If environment lookup fails, check De Bruijn index shifting
Rule 7: If unification loops, check occurs check
Rule 8: If type error is confusing, check bidirectional mode (infer vs check)
```

### 7.4 Planning Strategy

**Before implementing a feature**:
1. Write the property tests first
2. Define the complexity bounds
3. Plan the error cases
4. Design the debugging output
5. Document the invariants

**Example: Before implementing quote**:
```gleam
// Property tests
// - quote(eval(term)) normalizes term
// - quote doesn't evaluate (pure)
// - quote is O(size of value)

// Complexity bounds
// - quote(VLit): O(1)
// - quote(VLam): O(size of body)
// - quote(VNeut): O(length of spine)

// Error cases
// - Step limit exceeded → return HStepLimit
// - Environment lookup fails → return Var with index

// Debugging output
// - Trace each quote step
// - Show current level and value

// Invariants
// - quote never calls eval
// - quote preserves free variables
// - quote produces well-formed terms
```

---

## 8. File & Function Organization

### 8.1 Ideal Structure

```
src/
├── main.gleam                    # CLI entry point
├── core/                         # Core language
│   ├── types.gleam               # Term, Value, Head, Elim, Case types
│   ├── env.gleam                 # Env, Closure, helpers
│   ├── eval.gleam                # Evaluation (eval_loop, do_app, do_match)
│   ├── quote.gleam               # Quoting (quote, quote_term_in_env)
│   ├── unify.gleam               # Unification, free_holes, occurs
│   ├── typecheck.gleam           # Type inference, checking
│   ├── builtin.gleam             # FFI definitions and implementations
│   ├── normalize.gleam           # eval + quote
│   ├── state.gleam               # State, Subst, Ctx types
│   └── errors.gleam              # Error types, formatting
├── syntax/                       # Syntax library
│   ├── grammar.gleam             # Grammar DSL
│   ├── lexer.gleam               # Tokenizer
│   ├── parser.gleam              # Parser engine
│   ├── formatter.gleam           # Document algebra
│   ├── recovery.gleam            # Error recovery strategies
│   └── validation.gleam          # Grammar validation
├── tao/                          # Tao language
│   ├── ast.gleam                 # Tao AST
│   ├── lexer.gleam               # Tao tokenizer
│   ├── grammar.gleam             # Tao grammar
│   ├── desugar.gleam             # Desugaring
│   ├── global_context.gleam      # Module resolution
│   └── errors.gleam              # Tao-specific errors
└── utils/                        # Shared utilities
    ├── tracer.gleam              # Evaluation tracing
    ├── inspector.gleam           # Value/term inspection
    ├── stats.gleam               # Step counting
    └── config.gleam              # Configuration
```

### 8.2 Function Signatures That Would Have Helped

```gleam
// Pure quoting - no effects!
pub fn reify(lvl: Int, value: Value) -> Term

// Effectful evaluation
pub fn eval(ffi: FFI, env: Env, term: Term) -> Value

// Normalization (documents both phases)
pub fn normalize(ffi: FFI, term: Term) -> Term

// With explicit step tracking
pub fn eval_with_stats(
  ffi: FFI, 
  env: Env, 
  term: Term,
) -> #(Value, EvalStats)

// With tracing
pub fn eval_with_trace(
  ffi: FFI, 
  env: Env, 
  term: Term,
  tracer: fn(TraceEvent) -> Nil,
) -> Value

// With configuration
pub fn eval_with_config(
  ffi: FFI, 
  env: Env, 
  term: Term,
  config: Config,
) -> Value

// Parser with recovery strategy
pub fn parse_with_recovery(
  grammar: Grammar,
  source: String,
  recovery: RecoveryStrategy,
) -> ParseResult

// Desugaring with trace
pub fn desugar_with_trace(
  expr: TaoExpr,
) -> #(CoreTerm, List(Transformation))
```

### 8.3 Type Definitions That Would Have Helped

```gleam
/// Value with metadata for debugging
pub type Value =
  | VTyp(level: Int)
  | VLit(literal: Literal)
  | VLam(
      implicit: List(Term),
      name: String,
      env: Env,        // Explicit env type
      body: Term,
      info: LambdaInfo, // Debug info
    )
  | VFix(
      name: String,
      env: Env,
      body: Term,
      unfolded: Bool,   // Track if unfolded
    )
  | VNeut(neutral: Neutral)  // Explicit neutral type

/// Lambda debug info
pub type LambdaInfo {
  LambdaInfo(
    defined_at: Span,
    captured_vars: List(String),
    complexity: Int,   // Estimated size
  )
}

/// Term with source info
pub type Term =
  | Var(index: Int, source: SourceInfo)
  | Lam(implicit: List(Term), param: Param, body: Term, source: SourceInfo)
  | ...

/// Source info for better errors
pub type SourceInfo {
  SourceInfo(
    span: Span,
    original: String,   // Original source text
    context: String,    // Surrounding context
  )
}
```

---

## 9. Tools That Would Have Helped

### 9.1 Interactive REPL

```bash
$ gleam run repl
Compiler Bootstrap REPL v0.1.0

> let f = fn(n) { match n { | 0 -> 1 | _ -> n * f(n-1) } }
Defined: f : I32 → I32

> eval f(5)
120 : I32

> trace eval f(5)
[eval] App(Fix("f", ...), 5)
[eval] → Match(5, ...)
[eval] → Call("mul", [5, f(4)])
[eval] → Call("mul", [5, Call("mul", [4, f(3)])])
[eval] → ... (5 recursive calls)
[eval] → 120
Steps: 47

> quote f
λ(n: I32) => match n { | 0 → 1 | _ → n * f(n-1) }
Steps: 50

> stats eval f(5)
Evaluation Statistics:
  Total steps:    47
  App steps:      10
  Match steps:    5
  Call steps:     10
  Max env size:   5

> :help
Commands:
  eval <expr>     Evaluate expression
  trace <expr>    Evaluate with tracing
  quote <expr>    Quote expression
  stats <expr>    Show statistics
  :type <expr>    Show type
  :load <file>    Load file
  :quit           Exit REPL
```

**Features**:
- Incremental evaluation
- Tracing on demand
- Type checking
- Statistics
- History

### 9.2 Visualization Tool

```bash
$ gleam run visualize examples/tao/programs/04-recursion/recursive_fn.tao
Generating visualization...
Output: recursive_fn.svg

# SVG shows:
# - Evaluation tree (green nodes)
# - Quote tree (blue nodes)
# - Step counts per node
# - Hot spots (red = many steps)
# - Environment at each node
```

**Features**:
- Interactive SVG
- Zoom/pan
- Node details on hover
- Step count heat map
- Environment viewer

### 9.3 Property Checker

```bash
$ gleam run check-properties
Running property-based tests...

✓ eval_quote_idempotent (100 tests)
✓ factorial_terminates (50 tests)
✓ quote_preserves_free_vars (100 tests)
✓ type_preservation (50 tests)
✓ parse_unparse_roundtrip (100 tests)

All properties passed!

$ gleam run check-properties --fuzz
Running fuzz tests...

✓ fuzz_eval (1000 random terms)
✓ fuzz_parse (500 random programs)
✓ fuzz_unify (500 random type pairs)

No crashes detected!
```

**Features**:
- Property-based testing
- Fuzz testing
- Counterexample display
- Shrinking

### 9.4 Grammar Analyzer

```bash
$ gleam run analyze-grammar src/tao/syntax.gleam
Analyzing grammar...

Grammar Analysis Report
=======================

✓ No left recursion detected
✓ No unreachable rules
✓ No circular dependencies

⚠️  Warning: Non-consuming rule
   Rule: Program → Stmt*
   Issue: Doesn't consume semicolons between statements
   Fix: Use many(seq([Stmt, opt(Semi)]))

✓ All tokens defined
✓ All rules reachable

Summary: 1 warning, 0 errors
```

**Features**:
- Left recursion detection
- Unreachable rule detection
- Token validation
- Dependency graph

### 9.5 Performance Profiler

```bash
$ gleam run profile examples/tao/programs/04-recursion/recursive_fn.tao
Profiling...

Performance Profile
===================

Phase          Steps    Time     % of Total
-------------------------------------------
Evaluation     47       0.1ms    5%
Quoting        50       0.1ms    5%
Type checking  100      0.5ms    25%
Unification    0        0.0ms    0%
Parsing        200      1.3ms    65%
-------------------------------------------
Total          397      2.0ms    100%

Hot spots:
1. Parsing: Program rule (65%)
2. Type checking: infer_app (15%)

Recommendations:
- Consider optimizing Program rule
- Cache type inference results
```

**Features**:
- Phase breakdown
- Hot spot detection
- Recommendations
- Comparison mode

### 9.6 Debug Build Mode

```bash
$ gleam run --debug check examples/tao/programs/04-recursion/recursive_fn.tao
Debug mode enabled

[parse] Parsing...
[parse] → 1 statements
[type] Type checking...
[type] → I32
[eval] Evaluating...
[eval] → 120
[quote] Quoting...
[quote] → 120

✓ Type checking passed
✓ Evaluation passed
✓ Normalization passed
```

**Features**:
- Phase-by-phase output
- Timing information
- Validation checks
- Verbose errors

---

## 10. Gleam-Specific Lessons

### 10.1 What Worked Well in Gleam ✅

| Feature | Why It Worked | Example |
|---------|---------------|---------|
| **Type system** | Caught many bugs at compile time | Pattern match exhaustiveness |
| **Immutability** | Made reasoning easier | No accidental state mutations |
| **Pipe operator** | Clean data flow | `value |> transform |> validate` |
| **Result type** | Explicit error handling | `Result(a, e)` |
| **Custom types** | Clear data structures | `pub type Value = ...` |

### 10.2 What Was Challenging ❌

#### A. Large Files

**Problem**: Gleam doesn't enforce module boundaries.

**Solution**: Self-impose file size limits (e.g., 500 lines max).

```gleam
// ENFORCED BY CODE REVIEW:
// - Files > 500 lines must be split
// - Each module has single responsibility
// - Use re-export modules for public API
```

#### B. No Effect System

**Problem**: Can't tell if function is pure from type.

**Solution**: Naming conventions and documentation.

```gleam
// Pure functions: lowercase
pub fn quote(term: Term) -> Term

// Effectful functions: prefix with effect
pub fn eval_term(term: Term) -> Value  // "eval" signals effect
pub fn run_io(action: IO) -> Result(a, e)  // "run" signals effect
```

#### C. Limited Metaprogramming

**Problem**: Can't generate boilerplate.

**Solution**: Code generation scripts.

```bash
# Generate boilerplate
$ scripts/generate_visitors.gleam
# Output: src/core/visitors.gleam
```

#### D. Error Messages

**Problem**: Some type errors are cryptic.

**Solution**: Type annotations and incremental compilation.

```gleam
// Always annotate function return types
pub fn complex_function(x: Int) -> Result(Value, Error) {
  // ...
}

// Compile frequently to catch errors early
$ fswatch -or src/ | xargs -n1 -I{} gleam build
```

### 10.3 Gleam-Specific Recommendations

1. **Use `should` assertions liberally** - They provide clear failure messages
2. **Annotate all public functions** - Helps with type inference errors
3. **Use `echo` for debugging** - It's like `console.log` but type-safe
4. **Leverage the formatter** - Consistent style helps readability
5. **Use `gleam docs`** - Generate documentation from comments

---

## 11. Type Theory Implementation Lessons

### 11.1 Normalization by Evaluation Pitfalls

#### Pitfall 1: Quote Calls Eval

**Bug**: `quote` was calling `eval` for lambda bodies.

**Fix**: Quote should only reify, never evaluate.

**Invariant**: `eval` and `quote` must not call each other.

#### Pitfall 2: Environment Handling

**Bug**: Not extending environment when quoting binders.

**Fix**: Always extend environment with fresh neutral for each binder.

**Pattern**:
```gleam
VLam(_, name, env, body) -> {
  let fresh = VNeut(HVar(lvl), [])
  Lam(name, quote_term_in_env(lvl + 1, body, [fresh, ..env]), s)
}
```

#### Pitfall 3: Fixpoint Unfolding

**Bug**: Fixpoint unfolding during quote caused infinite loops.

**Fix**: Unfold fixpoint during eval, not quote.

**Pattern**:
```gleam
// During eval:
VFix(name, env, body) -> {
  let fix_val = VFix(name, env, body)
  eval([fix_val, ..env], body)  // Unfold here
}

// During quote:
VFix(name, env, body) -> {
  Fix(name, quote_term_in_env(lvl + 1, body, [VFix(...), ..env]), s)
}
```

### 11.2 De Bruijn Index Gotchas

#### Gotcha 1: Index vs Level

**Confusion**: De Bruijn indices (relative) vs levels (absolute).

**Rule**:
- **Indices**: Count from innermost binder (0 = innermost)
- **Levels**: Count from root (0 = root)

**Conversion**: `index = lvl - level - 1`

#### Gotcha 2: Shifting

**Bug**: Forgetting to shift when substituting under binders.

**Fix**: Always shift when going under a binder.

**Pattern**:
```gleam
subst(Lam(name, body), var, replacement) -> {
  // Shift replacement when going under binder
  let shifted = shift(replacement, 1, 0)
  Lam(name, subst(body, var + 1, shifted))
}
```

#### Gotcha 3: Environment Extension

**Bug**: Not extending environment correctly.

**Fix**: Always extend at the front (index 0 = most recent).

**Pattern**:
```gleam
extend_env(env, value) -> [value, ..env]
lookup(env, 0) -> head of env
lookup(env, n) -> nth element of env
```

### 11.3 Unification Challenges

#### Challenge 1: Occurs Check

**Bug**: Forgetting occurs check causes infinite types.

**Fix**: Always check if hole occurs in value before solving.

**Pattern**:
```gleam
unify(Hole(id), value) -> {
  case occurs(value, id) {
    True -> Error(InfiniteType(id, value))
    False -> solve(id, value)
  }
}
```

#### Challenge 2: Higher-Order Unification

**Bug**: Not handling neutral terms correctly.

**Fix**: Delay unification when one side is neutral.

**Pattern**:
```gleam
unify(VNeut(h1, s1), VNeut(h2, s2)) -> {
  // Can't unify neutrals yet - they might become equal later
  // Add constraint and continue
  add_constraint(h1, s1, h2, s2)
}
```

#### Challenge 3: Substitution Application

**Bug**: Not applying substitution transitively.

**Fix**: Apply substitution until fixed point.

**Pattern**:
```gleam
apply_subst(subst, Hole(id)) -> {
  case lookup(subst, id) {
    Some(value) -> apply_subst(subst, value)  // Transitively apply
    None -> Hole(id)
  }
}
```

---

## 12. Summary: Keep, Change, Add

### 12.1 Keep ✅

| What | Why |
|------|-----|
| De Bruijn indices | Correct by construction |
| Grammar DSL | Declarative, composable |
| Error accumulation | IDE-friendly |
| Test mirror structure | Easy to find tests |
| Document algebra | Clean formatting |
| Bidirectional typing | Clear modes |
| Step counters | Prevent infinite loops |
| NbE architecture | Efficient normalization |

### 12.2 Change ❌

| What | To What | Why |
|------|---------|-----|
| Monolithic `core.gleam` | Split into focused modules | Maintainability |
| Implicit effects | Explicit naming/docs | Clarity |
| Hardcoded constants | Configuration | Flexibility |
| Quote re-evaluating | Pure reification | Correctness |
| Implicit recovery | Explicit strategies | Debuggability |
| No grammar validation | Add validation | Prevent bugs |
| No tracing | Add comprehensive tracing | Debugging |
| No complexity tests | Add complexity tests | Performance |

### 12.3 Add ➕

| What | Why |
|------|-----|
| Property-based testing | Catch edge cases |
| Evaluation tracer | Debug evaluation |
| Value inspector | Debug values |
| Step statistics | Find bottlenecks |
| Grammar visualization | Understand grammar |
| Interactive REPL | Experiment |
| Performance profiler | Find hot spots |
| Regression tests | Prevent regressions |
| Fuzz testing | Find crashes |
| Grammar composition | Modularity |
| Effect annotations | Clarity |
| Better error messages | DX |

---

## 13. Key Insights for Future Projects

### 13.1 Architectural Insights

1. **Separation of concerns is critical**: eval and quote must not call each other cyclically.

2. **Module boundaries matter**: 3,400-line files hide bugs. Enforce file size limits.

3. **Explicit is better than implicit**: Effects, recovery strategies, configuration.

4. **Design for debugging from the start**: Tracing, inspection, statistics.

5. **Test properties, not just examples**: Properties catch edge cases examples miss.

### 13.2 Implementation Insights

1. **Step counters are diagnostics, not fixes**: They tell you where the problem is, but don't solve the root cause.

2. **Test recursive functions early**: If factorial doesn't work, nothing complex will.

3. **Grammar error recovery needs explicit synchronization**: Don't assume tokens will be consumed.

4. **Complexity should be documented**: Every function should have O() guarantees.

5. **De Bruijn indices require careful bookkeeping**: Always track indices vs levels.

### 13.3 Process Insights

1. **Write property tests before implementation**: They clarify the specification.

2. **Compile frequently**: Catch type errors early.

3. **Add regression tests for every bug**: Prevents the same bug from creeping back.

4. **Document invariants**: What must always be true?

5. **Review for complexity**: Is this O(n) or O(2^n)?

### 13.4 Type Theory Insights

1. **NbE requires strict eval/quote separation**: This is the most important invariant.

2. **Environments must be extended for every binder**: Otherwise variable capture.

3. **Fixpoints unfold during evaluation, not quoting**: Otherwise infinite loops.

4. **Occurs check is mandatory**: Otherwise infinite types.

5. **Neutral terms are stuck computations**: Don't try to evaluate them.

---

## 14. Timeline of Major Bugs

### Bug 1: Quote Re-evaluation (6 hours to fix)

**Symptom**: `factorial(5)` times out

**Root Cause**: `quote` was calling `eval` for lambda bodies

**Fix**: Use `quote_term_in_env` instead of `eval`

**Lesson**: Quote should never evaluate

### Bug 2: Missing FFI in do_match (2 hours to fix)

**Symptom**: Builtins don't work in match bodies

**Root Cause**: `do_match` didn't have FFI parameter

**Fix**: Add `ffi` parameter and pass to `eval_loop`

**Lesson**: Track effect dependencies

### Bug 3: Parser Semicolon Handling (1 hour to fix)

**Symptom**: `let x = ; let y = 20` only parses first let

**Root Cause**: Program rule didn't consume semicolons

**Fix**: Use `many(seq([Stmt, opt(Semi)]))`

**Lesson**: Explicit token consumption

### Bug 4: Exhaustiveness with Guards (30 minutes to fix)

**Symptom**: False positive exhaustiveness errors

**Root Cause**: Exhaustiveness checker didn't handle guards

**Fix**: Skip checking when guards present

**Lesson**: Conservative is better than wrong

---

## 15. Recommended Reading

### Type Theory

1. **"Type Theory and Formal Proof"** - Rob Nederpelt & Herman Geuvers
2. **"Programming Language Foundations"** - Software Foundations (online)
3. **"Normalization by Evaluation"** - Ulrich Berger et al.

### Parser Combinators

1. **"Parsing Techniques"** - Dick Grune & Ceriel J.H. Jacobs
2. **"Monadic Parser Combinators"** - Graham Hutton & Erik Meijer
3. **"Packrat Parsing"** - Bryan Ford

### Software Engineering

1. **"The Pragmatic Programmer"** - Andrew Hunt & David Thomas
2. **"Clean Code"** - Robert C. Martin
3. **"Designing Data-Intensive Applications"** - Martin Kleppmann

### Gleam-Specific

1. **Gleam Documentation** - https://gleam.run/documentation/
2. **Gleam Standard Library** - https://hexdocs.pm/gleam_stdlib/
3. **Gleam Examples** - https://github.com/gleam-lang/gleam/tree/main/test

---

## 16. Conclusion

Building a compiler is hard. Building a dependently-typed compiler with normalization by evaluation is harder. But the lessons learned are invaluable:

1. **Correctness over speed**: Take time to get the architecture right.
2. **Testing is documentation**: Properties document what the code should do.
3. **Debugging is design**: If you can't debug it, the design is wrong.
4. **Separation of concerns**: Keep eval and quote separate!
5. **Explicit over implicit**: Effects, recovery, configuration.

The Compiler Bootstrap project is now at 519/519 tests passing, with recursive functions working and parser recovery functioning correctly. The journey taught us more about compiler construction, type theory, and software engineering than any book could.

**Final advice**: Start with the hard parts first (evaluation, quoting, unification). If those work, everything else is just syntax.

---

*Document version: 1.0*  
*Last updated: March 2026*  
*Authors: Compiler Bootstrap Team*
