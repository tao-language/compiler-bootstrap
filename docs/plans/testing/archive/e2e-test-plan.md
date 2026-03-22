# E2E Test Plan for Compiler Bootstrap

> **Goal**: Automated end-to-end testing for all example files with golden output comparison
> **Status**: 📋 Plan
> **Date**: March 2025

---

## Overview

Create an automated test system that:
1. Discovers all example files under `examples/core/`
2. Runs each example through the compiler
3. Compares output against golden `.output.txt` files
4. Handles both successful runs and expected failures

---

## Directory Structure

```
examples/core/
├── programs/           # Successful programs
│   ├── 01_literals_and_primitives.core.tao
│   ├── 01_literals_and_primitives.output.txt  # Expected stdout
│   └── ...
├── terms/              # Term examples (successful)
│   ├── 01_identity.core.tao
│   ├── 01_identity.output.txt
│   └── ...
└── errors/             # Examples that should fail
    ├── type_errors/
    │   ├── 01_type_mismatch.core.tao
    │   ├── 01_type_mismatch.output.txt  # Expected stderr
    │   └── ...
    ├── syntax_errors/
    ├── syntax_recovery/
    └── exhaustiveness_checks/
```

---

## Test Design

### 1. Auto-Discovery

Tests will automatically discover all `.core.tao` files under `examples/core/`:

```gleam
// Pseudo-code for test discovery
fn discover_examples(base_dir: String) -> List(Example) {
  // Recursively find all .core.tao files
  // Group by subdirectory (programs, terms, errors/type_errors, etc.)
}
```

### 2. Example Record

```gleam
pub type Example {
  Example(
    name: String,              // e.g., "01_literals_and_primitives"
    path: String,              // e.g., "examples/core/programs/01_literals_and_primitives.core.tao"
    output_path: String,       // e.g., "examples/core/programs/01_literals_and_primitives.output.txt"
    category: ExampleCategory, // Programs, Terms, or Errors
    subcategory: String,       // e.g., "type_errors", "programs", "terms"
  )
}

pub type ExampleCategory {
  ShouldSucceed  // programs/, terms/
  ShouldFail     // errors/*/
}
```

### 3. Test Structure

One test function per subdirectory:

```gleam
pub fn test_programs_examples() {
  let examples = discover_examples_in_directory("examples/core/programs")
  examples |> list.each(fn(example) {
    run_example_test(example)
  })
}

pub fn test_terms_examples() {
  let examples = discover_examples_in_directory("examples/core/terms")
  examples |> list.each(fn(example) {
    run_example_test(example)
  })
}

pub fn test_type_errors_examples() {
  let examples = discover_examples_in_directory("examples/core/errors/type_errors")
  examples |> list.each(fn(example) {
    run_example_test(example)
  })
}
```

### 4. Test Execution Logic

```gleam
fn run_example_test(example: Example) {
  let expected_output = read_file(example.output_path)
  
  case example.category {
    ShouldSucceed -> {
      // Run the example
      let result = compiler_bootstrap.run(example.path)
      
      // Check it succeeded
      result.should_be_ok()
      
      // Check output matches
      result.output
      |> should.equal(expected_output, example.name)
    }
    ShouldFail -> {
      // Run the example
      let result = compiler_bootstrap.check(example.path)
      
      // Check it failed
      result.should_be_error()
      
      // Check error message matches
      result.error_output
      |> should.equal(expected_output, example.name)
    }
  }
}
```

### 5. Golden File Format

**For successful programs** (`programs/*.output.txt`):
```
42
```

**For error examples** (`errors/*/ *.output.txt`):
```
❌ error[E0101]: Type mismatch
   ┌─ examples/core/errors/type_errors/01_type_mismatch.core.tao:3:5
   │
 3 │ let x: Int = "hello"
   │     ━━━━━ expected $Type, found $String
   │
   💡 expected because this is $Type
   📝 note: $Type and $String are incompatible types
   🔧 help: Check that the expression has the expected type
```

---

## Implementation Details

### File Discovery

Use `simplifile` to recursively scan directories:

```gleam
fn discover_examples_in_directory(dir: String) -> List(Example) {
  let files = simplifile.read_directory(dir)
  files
  |> list.filter(fn(f) { string.ends_with(f, ".core.tao") })
  |> list.map(fn(path) {
    let name = extract_name(path)
    let category = determine_category(path)
    let output_path = path |> string.replace(".core.tao", ".output.txt")
    Example(name, path, output_path, category, dir)
  })
}
```

### Running Examples

Import and use `compiler_bootstrap` module functions:

```gleam
import compiler_bootstrap

fn run_example(path: String) -> Result(String, String) {
  // Capture stdout/stderr
  // This may need a test helper that wraps compiler_bootstrap
}
```

### Test Output Comparison

Use `should.equal` with custom message:

```gleam
import gleeunit/should

test_output() {
  let expected = "42"
  let actual = run_example("examples/core/programs/01_literals.core.tao")
  
  actual
  |> should.equal(expected, "01_literals_and_primitives")
}
```

---

## Test File Structure

```gleam
// test/core/e2e_test.gleam
import compiler_bootstrap
import gleam/string
import gleam/list
import gleam/io
import gleeunit
import gleeunit/should
import simplifile

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// TEST DISCOVERY
// ============================================================================

pub fn test_programs_examples() {
  "examples/core/programs"
  |> discover_examples
  |> list.each(run_example_test)
}

pub fn test_terms_examples() {
  "examples/core/terms"
  |> discover_examples
  |> list.each(run_example_test)
}

pub fn test_type_errors_examples() {
  "examples/core/errors/type_errors"
  |> discover_examples(ShouldFail)
  |> list.each(run_example_test)
}

pub fn test_syntax_errors_examples() {
  "examples/core/errors/syntax_errors"
  |> discover_examples(ShouldFail)
  |> list.each(run_example_test)
}

pub fn test_syntax_recovery_examples() {
  "examples/core/errors/syntax_recovery"
  |> discover_examples(ShouldFail)
  |> list.each(run_example_test)
}

pub fn test_exhaustiveness_checks_examples() {
  "examples/core/errors/exhaustiveness_checks"
  |> discover_examples(ShouldFail)
  |> list.each(run_example_test)
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

fn discover_examples(dir: String) -> List(Example) {
  // Implementation
}

fn run_example_test(example: Example) {
  // Implementation
}
```

---

## Golden File Generation

For initial setup, provide a script to generate golden files:

```bash
# Generate all golden files
./scripts/generate_golden_files.sh
```

This script will:
1. Run each `.core.tao` file
2. Capture stdout/stderr
3. Write to corresponding `.output.txt` file

---

## Benefits

1. **Automatic Discovery**: New examples are automatically tested
2. **Golden Testing**: Exact output comparison prevents regressions
3. **Error Testing**: Verify error messages are correct and helpful
4. **Documentation**: Examples serve as living documentation
5. **CI/CD Ready**: All tests run in CI pipeline

---

## Implementation Phases

### Phase 1: Infrastructure
- [ ] Create `test/core/e2e_test.gleam`
- [ ] Implement file discovery
- [ ] Implement test runner

### Phase 2: Golden Files
- [ ] Generate golden files for `programs/`
- [ ] Generate golden files for `terms/`
- [ ] Generate golden files for `errors/`

### Phase 3: Integration
- [ ] Add e2e tests to CI pipeline
- [ ] Document how to add new examples
- [ ] Document how to update golden files

---

## Notes

- Tests should use relative paths from project root
- Golden files should be committed to version control
- Error output should be stable (no timestamps, random IDs, etc.)
- Consider adding a `--update-golden` flag for easy updates
