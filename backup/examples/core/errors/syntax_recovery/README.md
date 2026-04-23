# Syntax Recovery Examples

This directory contains examples demonstrating the parser's error recovery capabilities.

These examples show syntax errors that the parser can recover from, allowing it to continue parsing and report multiple errors in a single pass.

## Usage

Run any example to see how the parser recovers:

```bash
gleam run -- check examples/core/errors/syntax_recovery/01_trailing_operator.core.tao
```

## Examples

| File | Code | Recovery Behavior |
|------|------|-------------------|
| `01_trailing_operator.core.tao` | `x +` | Parser recovers after unexpected operator |
| `02_extra_closing_paren.core.tao` | `x))` | Parser ignores extra closing paren |
| `03_multiple_expressions.core.tao` | `x y` | Parser handles adjacent expressions |

## Expected Behavior

Unlike syntax errors in `../syntax_errors/`, these examples may:
- Parse successfully with warnings
- Produce partial ASTs
- Report errors but continue parsing

## Notes

Error recovery is an important feature for IDE support, as it allows the compiler to:
- Report multiple errors in a single pass
- Provide completions and hover info even with errors
- Maintain a usable AST for tooling
