# Type Errors

This directory contains examples that parse successfully but fail type checking.

These examples demonstrate the type checker's error reporting capabilities.

## Usage

Run any example to see the type error:

```bash
gleam run -- check examples/core/errors/type_errors/01_type_mismatch.core.tao
```

## Examples

| File | Description | Error Type |
|------|-------------|------------|
| `01_type_mismatch.core.tao` | Annotating term with wrong type | Type mismatch |
| `02_occurs_check.core.tao` | Recursive type (occurs check failure) | Occurs check |
| `03_arity_mismatch.core.tao` | Wrong number of arguments | Arity mismatch |

## Expected Output

Type errors should include:
- The specific type mismatch
- Source location information
- Expected vs actual types

## Notes

**Status**: These examples are placeholders for future implementation.

The CLI currently only performs parsing, not full type checking. Once the `core/core` type checker is integrated, these examples will demonstrate:
- Type mismatch errors (expected vs actual types)
- Occurs check failures (recursive types)
- Arity mismatches (wrong number of arguments)
- Free variable errors
- Kind errors

Type checking happens after parsing, so these examples parse successfully but would fail during the type inference/checking phase.
