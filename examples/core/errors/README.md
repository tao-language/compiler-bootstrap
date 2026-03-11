# Core Language Error Examples

This directory contains examples demonstrating different categories of errors in the core language compiler.

## Directory Structure

```
errors/
├── syntax_errors/          # Parse errors (cannot recover)
├── syntax_recovery/        # Syntax errors with recovery
├── type_errors/            # Type checking errors
└── exhaustiveness_checks/  # Pattern match coverage errors (future)
```

## Error Categories

### 1. Syntax Errors (`syntax_errors/`)

Examples of invalid syntax that the parser **cannot** recover from.

```bash
gleam run -- check examples/core/errors/syntax_errors/01_double_arrow.core.tao
```

**Expected output:** Error with source snippet showing the error location

**Current examples:**
- `01_double_arrow.core.tao` - Multiple consecutive arrows
- `01_unexpected_token.core.tao` - Unexpected token at start
- `02_leading_arrow.core.tao` - Arrow without left-hand side
- `02_malformed_match.core.tao` - Malformed match expression
- `03_leading_colon.core.tao` - Colon without annotation context
- `04_bare_hash.core.tao` - Hash without constructor name
- `05_bare_dollar.core.tao` - Dollar without type name
- `06_unclosed_paren.core.tao` - Opening paren without closing
- `07_unclosed_brace.core.tao` - Opening brace without closing

### 2. Syntax Recovery (`syntax_recovery/`)

Examples of invalid syntax that the parser **can** recover from.

```bash
gleam run -- check examples/core/errors/syntax_recovery/01_trailing_operator.core.tao
```

**Expected output:** Parses successfully (parser ignores/skips invalid tokens)

**Current examples:**
- `01_trailing_operator.core.tao` - Trailing operator
- `02_extra_closing_paren.core.tao` - Extra closing parenthesis

### 3. Type Errors (`type_errors/`)

Examples that parse successfully but fail type checking.

```bash
gleam run -- check examples/core/errors/type_errors/01_param_type_mismatch.core.tao
```

**Expected output:** Type error with source snippet

**Current examples:**
- `01_param_type_mismatch.core.tao` - Function parameter type mismatch
- `02_annotation_mismatch.core.tao` - Type annotation mismatch
- `03_not_a_function.core.tao` - Applying a non-function value
- `04_let_function_inference.core.tao` - Let binding type inference limitation

### 4. Exhaustiveness Checks (`exhaustiveness_checks/`)

**Status**: Placeholder directory for future implementation.

Examples of pattern matching that fail coverage checking will be added once exhaustiveness checking is fully integrated.

**Planned examples:**
- Missing case detection
- Redundant case detection
- Unreachable pattern detection

## Quick Reference

| Category | Phase | Recoverable | Status |
|----------|-------|-------------|--------|
| Syntax Errors | Parsing | ❌ No | ✅ Complete |
| Syntax Recovery | Parsing | ✅ Yes | ✅ Complete |
| Type Errors | Type Checking | N/A | ✅ Complete |
| Exhaustiveness | Coverage Check | N/A | 📋 Future |

## Error Output Format

The CLI provides detailed error messages with source snippets:

### Parse Error Example

```
error[E0001]: Unexpected token
  ┌─ examples/core/errors/syntax_errors/01_double_arrow.core.tao:3:1
1 │ // Parse Error: Multiple consecutive arrows
2 │ // This should fail because the grammar doesn't allow multiple arrows in a row
3 │ -> -> x
    ^
4 │
  = note: Expected: valid alternative
  = note: Got: none
  = hint: Check syntax near this position
```

### Type Error Example

```
error[E0101]: Type mismatch
  ┌─ input:1:1
1 │ 42 : $Type
    ^^ ----
2 │
  = hint: Check that types are compatible
```

## Error Codes

| Code | Description |
|------|-------------|
| E0001 | Unexpected token (parse error) |
| E0101 | Type mismatch |
| E0102 | Undefined variable |
| E0103 | Not a function |
| E0104 | Arity mismatch |
| E0105 | Undefined constructor |
| E0106 | Unsolved hole |
| E0201 | Match missing case |
| E0202 | Match redundant case |
| E0301 | Comptime permission denied |

## Related Documentation

- [Core Language Overview](../../../docs/plans/core/01-overview.md)
- [CLI Documentation](../../../docs/plans/cli/01-overview.md)
- [Error Reporting Plan](../../../docs/plans/error-reporting/01-overview.md)
