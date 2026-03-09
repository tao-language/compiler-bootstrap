# Parse Error Examples

This directory contains examples of invalid core language syntax that produce parse errors.

## Usage

Run any example to see the parse error:

```bash
gleam run -- check examples/core/errors/01_double_arrow.core.tao
```

## Error Examples

| File | Description | Error Type |
|------|-------------|------------|
| `01_double_arrow.core.tao` | `-> -> x` | Multiple consecutive arrows |
| `02_leading_arrow.core.tao` | `-> x` | Arrow without left-hand side |
| `03_leading_colon.core.tao` | `: $Type` | Colon without annotation context |
| `04_bare_hash.core.tao` | `#` | Hash without constructor name |
| `05_bare_dollar.core.tao` | `$` | Dollar without type name |
| `06_unclosed_paren.core.tao` | `(42` | Opening paren without closing |
| `07_unclosed_brace.core.tao` | `{x: 1` | Opening brace without closing |

## Expected Output

All examples in this directory should produce a "Parse failed" error:

```
Parse failed

stacktrace:
  syntax/grammar.parse src/syntax/grammar.gleam:497
  core/syntax.parse src/core/syntax.gleam:219
  compiler_bootstrap.check_core src/compiler_bootstrap.gleam:209
  compiler_bootstrap.main src/compiler_bootstrap.gleam:67
```

## Notes

The core language parser is designed to be resilient and recover from errors where possible.
Some invalid syntax may be silently ignored (e.g., trailing operators).
The examples in this directory represent syntax that the parser cannot recover from.
