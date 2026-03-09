# Exhaustiveness Checking Examples

This directory contains examples of pattern matching that fail exhaustiveness checking.

The exhaustiveness checker uses Maranget's algorithm to determine if all possible cases are covered in a match expression.

## Usage

Run any example to see the exhaustiveness error:

```bash
gleam run -- check examples/core/errors/exhaustiveness_checks/01_missing_case.core.tao
```

## Examples

| File | Description | Error Type |
|------|-------------|------------|
| `01_missing_case.core.tao` | Match missing wildcard case | Missing case |
| `02_redundant_case.core.tao` | Match with unreachable case | Redundant case |
| `03_unreachable_pattern.core.tao` | Pattern that can never match | Unreachable pattern |

## Expected Output

Exhaustiveness errors should include:
- Which patterns are not covered
- Source location of the match expression
- Suggestions for missing cases

## Notes

**Status**: These examples are placeholders for future implementation.

The core language parser currently has issues with match expressions. Once the match parsing is fixed, these examples will demonstrate:
- Missing case detection (not all constructors covered)
- Redundant case detection (unreachable patterns)
- Pattern ordering issues

The exhaustiveness checker uses Maranget's algorithm for efficient coverage analysis.
