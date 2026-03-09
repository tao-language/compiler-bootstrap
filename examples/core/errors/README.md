# Core Language Error Examples

This directory contains examples demonstrating different categories of errors in the core language compiler.

## Directory Structure

```
errors/
├── syntax_errors/          # Parse errors (cannot recover)
├── syntax_recovery/        # Syntax errors with recovery
├── type_errors/            # Type checking errors (future)
└── exhaustiveness_checks/  # Pattern match coverage errors (future)
```

## Error Categories

### 1. Syntax Errors (`syntax_errors/`)

Examples of invalid syntax that the parser **cannot** recover from.

```bash
gleam run -- check examples/core/errors/syntax_errors/01_double_arrow.core.tao
```

**Expected output:** "Parse failed" with stacktrace

**Current examples:**
- `01_double_arrow.core.tao` - Multiple consecutive arrows
- `02_leading_arrow.core.tao` - Arrow without left-hand side
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

**Status**: Placeholder directory for future implementation.

Examples that parse successfully but fail type checking will be added once the `core/core` type checker is integrated with the CLI.

**Planned examples:**
- Type mismatch errors
- Occurs check failures
- Arity mismatches

### 4. Exhaustiveness Checks (`exhaustiveness_checks/`)

**Status**: Placeholder directory for future implementation.

Examples of pattern matching that fail coverage checking will be added once match expression parsing is fixed and exhaustiveness checking is integrated.

**Planned examples:**
- Missing case detection
- Redundant case detection
- Unreachable pattern detection

## Quick Reference

| Category | Phase | Recoverable | Status |
|----------|-------|-------------|--------|
| Syntax Errors | Parsing | ❌ No | ✅ Complete |
| Syntax Recovery | Parsing | ✅ Yes | ✅ Complete |
| Type Errors | Type Checking | N/A | 📋 Future |
| Exhaustiveness | Coverage Check | N/A | 📋 Future |

## Related Documentation

- [Core Language Overview](../../../docs/plans/core/01-overview.md)
- [CLI Documentation](../../../docs/plans/cli/01-overview.md)
- [Syntax Specification](../../../docs/plans/core/02-syntax.md)
