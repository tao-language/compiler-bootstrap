# Core Language Programs

This directory contains real-world programs written in the core language.

## Status

The core language is still being developed. Many features needed for complex programs (recursion, let-bindings, data type definitions) are planned but not yet implemented.

## Current Examples

### 01_fibonacci.core.tao

Simple identity function (placeholder for future fibonacci implementation).

```bash
gleam run -- run examples/core/programs/01_fibonacci.core.tao
```

**Output:** `n -> n`

## Planned Examples

- **Fibonacci**: Recursive fibonacci function (requires fixpoint combinator or let-rec)
- **Vector Operations**: Dependent types with length-indexed vectors
- **List Operations**: Map, filter, fold on lists
- **Church Numerals**: Lambda encoding of natural numbers
- **Boolean Logic**: Church booleans and logical operations

## Language Limitations

Current limitations that prevent complex programs:

1. **No let-bindings**: Cannot define named functions
2. **No recursion**: Requires fixpoint combinator (planned)
3. **No data type definitions**: Constructors must be predefined
4. **No pattern matching in lambdas**: Match expressions work but are verbose

## Workarounds

For now, examples use:
- Lambda abstraction for function definition
- Direct application for function calls
- Simple types that don't require complex definitions

## Related

- [Basic Terms](../terms/) - Core language constructs
- [Error Examples](../errors/) - Invalid syntax and type errors
