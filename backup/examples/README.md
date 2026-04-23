# Core Language Examples

This directory contains example files that demonstrate the Core language features and serve as test cases for the compiler.

## Directory Structure

```
examples/core/
├── programs/           # Complete programs that should compile successfully
├── terms/              # Individual term examples (successful)
└── errors/             # Examples that demonstrate error cases
    ├── type_errors/           # Type checking errors
    ├── syntax_errors/         # Parse errors
    ├── syntax_recovery/       # Examples testing parser recovery
    └── exhaustiveness_checks/ # Pattern match exhaustiveness errors
```

## File Format

### Source Files (`.core.tao`)

All example files use the `.core.tao` extension and should:

1. **Start with a comment** explaining what the example demonstrates
2. **Include inline comments** for complex or non-obvious code
3. **Be minimal** - only include code necessary to demonstrate the feature
4. **Be self-contained** - should not depend on external files

Example:
```gleam
// Identity Function
// Demonstrates lambda syntax and function application
// The identity function returns its argument unchanged
let id = x -> x in id(42)
```

### Golden Files (`.output.txt`)

Each `.core.tao` file has a corresponding `.output.txt` file containing the expected compiler output.

**For successful examples** (programs/, terms/):
```
✓ Type checking <path>
✓ Evaluating...
Result: <normalized term>
```

**For error examples** (errors/*/):
```
❌ error[E####]: Error category
error[E####]: Error message
  ┌─ input:line:col
  │ source code
  │ ^^^^ error location
  = note: Additional information
  = hint: Suggestion for fixing

📝 note: Additional context
🔧 help: Fix suggestion
```

## Adding New Examples

### 1. Create the Source File

Choose the appropriate directory based on what you're testing:
- `programs/` - Complete, working programs
- `terms/` - Individual language constructs
- `errors/type_errors/` - Type checking failures
- `errors/syntax_errors/` - Parse failures
- `errors/syntax_recovery/` - Parser recovery behavior
- `errors/exhaustiveness_checks/` - Pattern match coverage

Name your file with a number prefix and descriptive name:
```
01_descriptive_name.core.tao
```

### 2. Add Comments

Every example must start with a comment explaining:
- **What** feature is being demonstrated
- **Why** this example is important
- **Expected behavior** (success or specific error)

### 3. Generate Golden File

Run the golden file generation script:
```bash
./scripts/generate_golden_files.sh
```

Or manually:
```bash
# For success examples
gleam run run examples/core/programs/your_file.core.tao > examples/core/programs/your_file.output.txt

# For error examples
gleam run check examples/core/errors/category/your_file.core.tao > examples/core/errors/category/your_file.output.txt
```

### 4. Verify

Run the tests to ensure your example works correctly:
```bash
gleam test
```

## Example Categories

### Programs (`programs/`)

Complete programs that demonstrate language features working together. These should:
- Compile successfully
- Produce meaningful output
- Demonstrate real-world usage patterns

### Terms (`terms/`)

Individual language constructs. These should:
- Focus on a single feature
- Be as minimal as possible
- Show the syntax clearly

### Type Errors (`errors/type_errors/`)

Examples that fail type checking. These should:
- Demonstrate specific type errors
- Include comments explaining why the error occurs
- Show helpful error messages

### Syntax Errors (`errors/syntax_errors/`)

Examples that fail to parse. These should:
- Show common syntax mistakes
- Test parser error messages
- Include comments about what's wrong

### Syntax Recovery (`errors/syntax_recovery/`)

Examples that test parser error recovery. These should:
- Show how the parser handles malformed input
- Demonstrate graceful degradation
- Include comments about expected recovery behavior

### Exhaustiveness Checks (`errors/exhaustiveness_checks/`)

Examples with incomplete pattern matches. These should:
- Show missing pattern cases
- Demonstrate exhaustiveness checking
- Include comments about what patterns are missing

## Testing

All examples are automatically tested by the E2E test system:

```bash
gleam test
```

The test system:
1. Discovers all `.core.tao` files
2. Runs them through the compiler
3. Compares output against `.output.txt` golden files
4. Reports any mismatches

## Updating Golden Files

When compiler output changes intentionally, update golden files:

```bash
./scripts/generate_golden_files.sh
```

Then review the changes:
```bash
git diff examples/core/
```

## Code Style

Examples should follow these conventions:

1. **Comments**: Use `//` for line comments
2. **Spacing**: Use spaces around operators
3. **Naming**: Use descriptive names (not just `x`, `y`, `z`)
4. **Length**: Keep examples under 20 lines when possible
5. **Focus**: Each example should test one thing

## See Also

- [Core Language Specification](../docs/core.md)
- [E2E Test Plan](../docs/plans/testing/02-e2e-test-enhancement.md)
- [Error Reporting](../docs/error-reporting.md)
