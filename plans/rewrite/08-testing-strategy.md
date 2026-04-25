# Testing Strategy

## Design Philosophy

> **Tests as examples** — Every function has tests that demonstrate correct usage with example inputs/outputs.

Tests serve a dual purpose: they verify correctness AND document how functions work. Each test should be self-contained and readable enough to understand the expected behavior without reading the source code.

Tests should cover all the main functionality, including the "happy path" and edge cases for each function.

The testing strategy is organized in layers:

1. **Unit tests** — Test each function in isolation with specific examples
2. **Golden tests** — Test round-trip properties (parse → format → parse)
3. **Integration tests** — Test full pipeline stages with complete programs
4. **End-to-end tests** — Test complete compilation from source to value

## Test Organization

```
test/
├── syntax/
│   ├── lexer_test.gleam       # Tokenizer unit tests
│   ├── grammar_test.gleam     # Parser combinator unit tests
│   ├── formatter_test.gleam   # Document algebra + layout tests
│   └── golden_test.gleam      # Parse → format → parse round-trip tests
├── core/
│   ├── ast_test.gleam         # Term/Value type construction tests
│   ├── syntax_test.gleam      # Core parser + formatter tests
│   ├── infer_test.gleam       # Bidirectional type checking tests
│   ├── eval_test.gleam        # Normalization by evaluation tests
│   ├── quote_test.gleam       # Value → Term tests
│   ├── unify_test.gleam       # Unification tests
│   ├── subst_test.gleam       # Substitution tests
│   ├── generalize_test.gleam  # Generalization tests
│   ├── exhaustiveness_test.gleam  # Pattern match coverage tests
│   ├── error_formatter_test.gleam  # Type error diagnostics tests
│   ├── state_test.gleam       # State management tests
│   ├── examples_test.gleam    # End-to-end example programs
│   └── golden_test.gleam      # Core → eval → quote → eval round-trip
├── tao/
│   ├── ast_test.gleam         # Tao AST type construction tests
│   ├── syntax_test.gleam      # Tao parser + formatter tests
│   ├── desugar_test.gleam     # Desugaring correctness tests
│   ├── compiler_test.gleam    # Multi-file compilation tests
│   ├── import_test.gleam      # Module import system tests
│   ├── test_api_test.gleam    # Test framework (REPL-style extraction)
│   ├── examples_test.gleam    # End-to-end example programs
│   └── golden_test.gleam      # Tao → desugar → compile → format round-trip
├── cli/
│   ├── run_test.gleam         # Run mode tests
│   ├── check_test.gleam       # Check mode tests
│   └── test_test.gleam        # Test mode tests (run test statements)
└── integration/
    └── e2e_test.gleam         # Full pipeline tests (Tao source → Core value)
```

## Testing Convention: Assert-Based Testing

> **Tests must use `assert` statements** — Every test must verify correctness using `assert`, not just return `True`/`False`.

GleeUnit 1.x requires tests to use `assert expr == expected` to actually verify correctness. Returning `True` or `False` from a case expression passes the test regardless of the actual result.

### ✅ Correct: Assert-Based Testing

```gleam
pub fn tokenize_integer_literal_test() {
  let tokens = tokenize("42")
  assert list.length(tokens) == 2
  
  // Extract and verify specific token fields
  let first = tokens[0]
  assert first.kind == "Integer"
  assert first.value == "42"
  
  // Verify Eof is present
  assert case tokens[1] {
    Token(kind: "Eof", value: "", ..) -> True
    _ -> False
  }
}

pub fn infer_identity_function_type_test() {
  let body = Var(0, "x")
  let lam = Lam(("x", Hole(-1)), body)
  let state = initial_state([], "True")
  let result = infer(state, lam)
  
  // Property: no errors produced
  assert result.errors == []
}

pub fn check_type_mismatch_error_test() {
  let state = initial_state([], "True")
  let result = check(state, Lit(String("hello")), VLit(ILit(0)))
  
  // Property: exactly one TypeMismatch error with correct position
  assert list.length(result.errors) == 1
  assert case result.errors[0] {
    TypeMismatch(_, "String", "Int", span) -> 
      span.start_line == 1 && span.start_col == 1
    _ -> False
  }
}
```

### ❌ Incorrect: Silent Pass

```gleam
// This passes regardless of the actual result!
pub fn tokenize_integer_literal_test() {
  let tokens = tokenize("42")
  case tokens {
    [Token(kind: "Integer", value: "42", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}
```

**Key rules:**

1. **Use `assert` for every verification** — Never just return True/False
2. **Prefer direct property asserts** — `assert value == expected` over pattern matching when possible
3. **Extract values before asserting** — Makes tests more readable and provides better error messages
4. **Use `assert case` for complex shapes** — When you need to verify specific fields while ignoring others
5. **Test functions must be `pub` and end with `_test`** — GleeUnit 1.x requirement
6. **Document with comments** — Each test should explain what it's testing and why

### Property-Based vs Pattern-Matching Tests

**Prefer property-based asserts** when you care about specific values:

```gleam
pub fn add_two_numbers_test() {
  assert add(1, 2) == 3
  assert add(-1, 1) == 0
  assert add(0, 0) == 0
}
```

**Use pattern matching asserts** when you need to verify complex structures while ignoring irrelevant fields:

```gleam
pub fn parse_let_binding_test() {
  let result = parse("let x = 42")
  assert case result {
    ParseResult(
      ast: Let("x", Lit(42), _),
      errors: [],
      env: Env { vars: [v], .. }
    ) if v.name == "x" -> True
    _ -> False
  }
}
```

---

## Test Coverage Requirements

| Component | Minimum Coverage | Notes |
|-----------|-----------------|-------|
| `syntax/lexer` | 100% | Every token type, every edge case |
| `syntax/grammar` | 100% | Every combinator, every pattern type |
| `syntax/formatter` | 100% | Every document operation, every layout |
| `core/ast` | 100% | Every type constructor |
| `core/infer` | 100% | Every term form, every error case |
| `core/eval` | 100% | Every value form, step limit, FFI |
| `core/quote` | 100% | Every value form |
| `core/unify` | 100% | Every type pair, occurs check |
| `core/generalize` | 100% | Every quantification case |
| `core/exhaustiveness` | 100% | Every pattern combination |
| `tao/desugar` | 100% | Every statement form, every high-level feature |
| `tao/compiler` | 95% | Every file combination, import variants |
| `tao/import` | 95% | Every import variant, circular detection |
| Integration | 90% | Every end-to-end example |

## Tao Test Framework (REPL Style)

Tests in Tao source files use a REPL-style syntax with `///` doc comments:

```tao
// Example: test statements in a Tao file

/// > 1 + 2 ~> 3
/// > "hello" <> " world" ~> "hello world"
/// > fib(10) ~> 55

fn fib(n) {
  // ...
}
```

**How it works:**
1. The Tao parser extracts `/// > expr ~> expected` from doc comments
2. Each line becomes a `TestStatement` in the AST
3. The test framework compiles and evaluates each expression
4. The result is compared against the expected value

**Test framework in `test_api.gleam`:**
- `extract_tests(source)` → List(TestStatement)
- `run_tests(tests, context)` → List(TestResult)
- `run_tests_in_file(path, context)` → List(TestResult)

**CLI `tao test` command:**
- Scans source files for test statements
- Runs each test
- Reports: pass count, fail count, total
- Failed tests show expected vs. actual values

**Test result format:**
```gleam
pub type TestResult {
  Pass(test_name: Option(String))
  Fail(test_name: Option(String), expected: Value, actual: Value)
  Skipped(test_name: Option(String), reason: String)
}
```

## Running Tests

```bash
# Run all tests
gleam test

# Run specific test file
gleam test test/core/infer_test.gleam

# Run specific test
gleam test test/core/infer_test.gleam --name "infer_identity_function_type"

# Watch mode (continuous testing)
fswatch -or src test | xargs -n1 -I{} gleam test

# Run only golden tests
gleam test --tag golden

# Run only unit tests
gleam test --tag unit

# Run Tao tests (test statements in source files)
tao test main.tao
tao test --filter "addition"  # Run only tests matching "addition"
tao test --list               # List all test names
```
