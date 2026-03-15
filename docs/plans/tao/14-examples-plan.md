## Status

### Implemented (March 15, 2026)

**Programs:**
- ✅ `programs/01-basics/` - 10 examples (literals ✓, variables, operators, unary, blocks - currently output 0 due to let parsing limitations)
- ✅ `programs/02-functions/` - 5 examples (syntax demos - currently output 0 due to function call limitations)
- ✅ `programs/03-pattern-matching/` - 6 examples (pattern syntax demos - currently output 0)
- ✅ `programs/04-control-flow/` - 4 examples (control flow syntax - currently output 0)
- ✅ `programs/06-modules/` - 1 example (import error demo)

**Tests:**
- ✅ `test/tao/examples_test.gleam` - E2E test framework with evaluation and output comparison
- ✅ 451 tests passing (including 5 example tests that verify actual output)

**Output Format:**
- ✅ `.output.txt` files contain only the result expression (e.g., `42`, `0`)
- ✅ Test framework evaluates code and compares normalized output

### Known Limitations

1. **Let expression parsing** - Returns placeholder `0` instead of parsing let bindings
2. **Function calls** - Not fully implemented, outputs `0`
3. **Pattern matching** - Syntax parsed but evaluation returns `0`
4. **Control flow** - Syntax parsed but evaluation returns `0`
5. **Statement sequencing** - `DoBlock` simplified, doesn't properly sequence let bindings

### Pending

- ⏳ Fix let expression parsing in `tao/syntax.gleam`
- ⏳ Implement proper statement sequencing in `core_term_to_term`
- ⏳ Error examples (currently compile successfully due to resilient parsing)
- ⏳ Multi-file examples with imports
- ⏳ Real-world programs

> **Goal**: Comprehensive example files that showcase all Tao features and serve as integration tests
> **Status**: 📋 Planning
> **Date**: March 15, 2026

---

## Directory Structure

```
examples/tao/
├── programs/              # Successful programs
│   ├── 01-basics/         # Basic expressions and variables
│   ├── 02-functions/      # Function definitions and calls
│   ├── 03-pattern-matching/  # Match expressions with patterns
│   ├── 04-control-flow/   # Loops and conditionals
│   ├── 05-data-structures/ # Lists, tuples, records
│   ├── 06-modules/        # Multi-file examples with imports
│   ├── 07-advanced/       # Advanced features (polymorphism, etc.)
│   └── 08-real-world/     # Complete small programs
├── errors/                # Examples that should fail
│   ├── syntax_errors/     # Invalid syntax
│   ├── type_errors/       # Type mismatches
│   ├── import_errors/     # Import resolution failures
│   ├── exhaustiveness/    # Non-exhaustive pattern matches
│   └── runtime_errors/    # Runtime failures (if any)
└── features/              # Feature-specific examples (may succeed or fail)
    ├── guards/            # Match guards
    ├── recursion/         # Recursive functions
    └── ...
```

---

## Example Categories

### 1. Basics (`programs/01-basics/`)

| File | Feature | Description |
|------|---------|-------------|
| `hello.tao` | Literals | Integer, float, string literals |
| `variables.tao` | Let bindings | Variable declarations and usage |
| `operators.tao` | Binary ops | Arithmetic, comparison, logical operators |
| `unary.tao` | Unary ops | Negation, logical not |
| `blocks.tao` | Block expressions | Sequential evaluation with `{}` |
| `comments.tao` | Comments | Single-line and multi-line comments |

### 2. Functions (`programs/02-functions/`)

| File | Feature | Description |
|------|---------|-------------|
| `simple_fn.tao` | Basic functions | Function definition and call |
| `recursive_fn.tao` | Recursion | Factorial, fibonacci |
| `nested_fn.tao` | Nested calls | Function composition |
| `overloaded_fn.tao` | Overloading | Operator overloading (if supported) |
| `lambda.tao` | Anonymous functions | Lambda expressions |
| `higher_order.tao` | Higher-order | Functions taking functions |
| `currying.tao` | Currying | Partial application |
| `type_params.tao` | Type parameters | Generic functions |

### 3. Pattern Matching (`programs/03-pattern-matching/`)

| File | Feature | Description |
|------|---------|-------------|
| `variable_pattern.tao` | PVar | Variable binding patterns |
| `wildcard_pattern.tao` | PAny | Wildcard `_` patterns |
| `literal_pattern.tao` | PLit | Literal matching |
| `constructor_pattern.tao` | PCtr | Constructor patterns (Some, None, etc.) |
| `record_pattern.tao` | PRecord | Record field patterns |
| `tuple_pattern.tao` | PTuple | Tuple destructuring |
| `list_pattern.tao` | PList | List patterns with rest |
| `or_pattern.tao` | POr | Alternative patterns (`|`) |
| `as_pattern.tao` | PAs | As-patterns (`x @ pattern`) |
| `nested_patterns.tao` | Nested | Deep pattern matching |
| `exhaustive_match.tao` | Exhaustive | Complete pattern coverage |

### 4. Control Flow (`programs/04-control-flow/`)

| File | Feature | Description |
|------|---------|-------------|
| `if_expr.tao` | If expressions | Conditional evaluation |
| `while_loop.tao` | While loops | Condition-based iteration |
| `for_loop.tao` | For loops | Collection iteration |
| `infinite_loop.tao` | Loop | Infinite loops with break |
| `break_continue.tao` | Break/Continue | Loop control |
| `match_guard.tao` | Guards | Match clause guards |
| `nested_control.tao` | Nested | Mixed control structures |

### 5. Data Structures (`programs/05-data-structures/`)

| File | Feature | Description |
|------|---------|-------------|
| `lists.tao` | Lists | List construction and operations |
| `tuples.tao` | Tuples | Tuple creation and access |
| `records.tao` | Records | Record construction |
| `record_update.tao` | Record update | `..old` syntax |
| `option.tao` | Option type | Maybe/Optional patterns |
| `result.tao` | Result type | Error handling patterns |
| `custom_types.tao` | ADTs | Custom algebraic data types |
| `nested_data.tao` | Nested | Complex nested structures |

### 6. Modules and Imports (`programs/06-modules/`)

| File | Feature | Description |
|------|---------|-------------|
| `simple_import.tao` | ImportModule | `import path` |
| `alias_import.tao` | ImportAlias | `import path as alias` |
| `selective_import.tao` | ImportSelective | `import path {name1, name2}` |
| `wildcard_import.tao` | ImportWildcard | `import path as *` |
| `circular_a.tao` + `circular_b.tao` | Circular | Circular import detection |
| `nested_module.tao` | Nested paths | `import foo/bar/baz` |
| `prelude_import.tao` | Prelude | Prelude module imports |

**Multi-file example structure:**
```
programs/06-modules/math_example/
├── main.tao           # Entry point
├── math.tao           # Math module
├── math/
│   ├── trig.tao       # Trigonometry
│   └── algebra.tao    # Algebra
└── expected.output.txt
```

### 7. Advanced Features (`programs/07-advanced/`)

| File | Feature | Description |
|------|---------|-------------|
| `polymorphism.tao` | Polymorphism | Parametric polymorphism |
| `type_annotations.tao` | Type annotations | Explicit type signatures |
| `type_inference.tao` | Type inference | Implicit type deduction |
| `dependent_types.tao` | Dependent types | Type-level computation |
| `gadt.tao` | GADTs | Generalized algebraic data types |
| `type_classes.tao` | Type classes | Ad-hoc polymorphism (if supported) |
| `effects.tao` | Effects | Monadic effects (if supported) |
| `comptime.tao` | Compile-time | Compile-time evaluation |

### 8. Real-World Programs (`programs/08-real-world/`)

| File | Feature | Description |
|------|---------|-------------|
| `calculator.tao` | All features | Simple calculator with parsing |
| `fibonacci.tao` | Recursion | Fibonacci with memoization |
| `sort.tao` | Algorithms | Sorting algorithms |
| `tree_traversal.tao` | Data structures | Binary tree operations |
| `interpreter.tao` | Meta | Simple expression interpreter |
| `parser.tao` | Parsing | Combinator parsing example |
| `state_machine.tao` | State | Finite state machine |

---

## Error Examples

### Syntax Errors (`errors/syntax_errors/`)

| File | Error | Description |
|------|-------|-------------|
| `missing_paren.tao` | Parse error | Unclosed parentheses |
| `invalid_operator.tao` | Parse error | Invalid operator syntax |
| `unclosed_string.tao` | Parse error | Unterminated string |
| `missing_brace.tao` | Parse error | Unclosed block |
| `invalid_ident.tao` | Parse error | Invalid identifier |
| `trailing_comma.tao` | Parse error | Disallowed trailing comma |

### Type Errors (`errors/type_errors/`)

| File | Error | Description |
|------|-------|-------------|
| `type_mismatch.tao` | Type error | Int vs String mismatch |
| `arity_mismatch.tao` | Type error | Wrong number of arguments |
| `undefined_var.tao` | Type error | Unbound variable |
| `field_not_found.tao` | Type error | Missing record field |
| `constructor_mismatch.tao` | Type error | Wrong constructor arity |
| `infinite_type.tao` | Type error | Occurs check failure |

### Import Errors (`errors/import_errors/`)

| File | Error | Description |
|------|-------|-------------|
| `module_not_found.tao` | Import error | Non-existent module |
| `name_not_exported.tao` | Import error | Private name import |
| `circular_import.tao` | Import error | Circular dependency |
| `invalid_path.tao` | Import error | Malformed import path |

### Exhaustiveness Errors (`errors/exhaustiveness/`)

| File | Error | Description |
|------|-------|-------------|
| `missing_case.tao` | Exhaustiveness | Missing pattern case |
| `missing_constructor.tao` | Exhaustiveness | Missing constructor |
| `incomplete_match.tao` | Exhaustiveness | Incomplete pattern match |

---

## Feature-Specific Examples (`features/`)

### Guards (`features/guards/`)

| File | Feature | Expected |
|------|---------|----------|
| `simple_guard.tao` | Basic guard | Success |
| `complex_guard.tao` | Compound guard | Success |
| `guard_shadowing.tao` | Variable shadowing | Success |
| `guard_error.tao` | Type error in guard | Error |

### Recursion (`features/recursion/`)

| File | Feature | Expected |
|------|---------|----------|
| `tail_recursive.tao` | Tail recursion | Success |
| `mutual_recursion.tao` | Mutual recursion | Success |
| `nested_recursion.tao` | Nested recursion | Success |
| `non_terminating.tao` | Infinite recursion | Runtime (if tracked) |

### Pattern Matching (`features/patterns/`)

| File | Feature | Expected |
|------|---------|----------|
| `irrefutable.tao` | Always matches | Success |
| `refutable.tao` | May fail | Success |
| `pattern_guards.tao` | With guards | Success |
| `pattern_priority.tao` | Order matters | Success |

---

## Test Integration

### Example Test File Structure

```gleam
// test/tao/examples_test.gleam

pub fn main() {
  gleeunit.main()
}

// Program examples (should succeed)
pub fn programs_basics_test() {
  "examples/tao/programs/01-basics"
  |> discover_examples(ShouldSucceed)
  |> run_examples
  |> should.equal([])
}

pub fn programs_functions_test() {
  "examples/tao/programs/02-functions"
  |> discover_examples(ShouldSucceed)
  |> run_examples
  |> should.equal([])
}

// Error examples (should fail with expected errors)
pub fn errors_syntax_test() {
  "examples/tao/errors/syntax_errors"
  |> discover_examples(ShouldFail)
  |> run_examples
  |> should.equal([])
}

pub fn errors_type_test() {
  "examples/tao/errors/type_errors"
  |> discover_examples(ShouldFail)
  |> run_examples
  |> should.equal([])
}

// Multi-file examples
pub fn programs_modules_test() {
  "examples/tao/programs/06-modules"
  |> discover_multi_file_examples(ShouldSucceed)
  |> run_examples
  |> should.equal([])
}
```

### Example Output Format

For successful programs (`*.output.txt`):
```
# Normalized output (e.g., show value)
42
```

For error examples (`*.output.txt`):
```
Parse error: expected ')', got '42'
  at examples/tao/errors/syntax_errors/missing_paren.tao:3:5

Type error: expected Int, got String
  at examples/tao/errors/type_errors/type_mismatch.tao:5:10
```

---

## Implementation Priority

### Phase 1: Core Features (Immediate)
- [ ] `programs/01-basics/` - Basic expressions
- [ ] `programs/02-functions/` - Functions
- [ ] `programs/03-pattern-matching/` - Pattern matching
- [ ] `programs/04-control-flow/` - Control flow
- [ ] `errors/syntax_errors/` - Syntax errors
- [ ] `errors/type_errors/` - Type errors

### Phase 2: Modules and Imports (Short-term)
- [ ] `programs/06-modules/` - Import examples
- [ ] `errors/import_errors/` - Import errors
- [ ] `test/tao/examples_test.gleam` - Test framework

### Phase 3: Advanced Features (Medium-term)
- [ ] `programs/05-data-structures/` - Data structures
- [ ] `programs/07-advanced/` - Advanced features
- [ ] `errors/exhaustiveness/` - Exhaustiveness errors
- [ ] `features/` - Feature-specific examples

### Phase 4: Real-World (Long-term)
- [ ] `programs/08-real-world/` - Complete programs
- [ ] Integration with documentation
- [ ] Performance benchmarks

---

## Notes

1. **Output Normalization**: For examples that produce values, we need a consistent way to show output (e.g., `quote` from NbE, or custom `show` function).

2. **Error Message Stability**: Error messages may change during development. Examples should be updated when error formatting improves.

3. **Multi-file Testing**: The test framework needs to support compiling multiple files together and checking import resolution.

4. **Documentation Integration**: Examples can be extracted for documentation (like Rust's doc tests).

5. **Performance**: Large examples (e.g., interpreter) may need timeout handling in tests.

6. **Feature Flags**: Some examples may require experimental features. Consider a way to skip these in CI.
