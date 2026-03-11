# Core Language Examples

This directory contains working examples of core language syntax and real-world programs.

## Usage

Check an example (type-check only):
```bash
gleam run -- check examples/core/terms/01_identity.core.tao
```

Run an example (type-check and evaluate):
```bash
gleam run -- run examples/core/terms/01_identity.core.tao
```

Run with verbose output:
```bash
gleam run -- run examples/core/terms/01_identity.core.tao --verbose
```

Run with debug output (shows AST):
```bash
gleam run -- run examples/core/terms/01_identity.core.tao --debug
```

## Directory Structure

- `terms/` - Basic term examples demonstrating core language constructs
- `programs/` - Real-world programs (fibonacci, etc.)
- `errors/` - Examples of invalid syntax and type errors

## Basic Term Examples (`terms/`)

| File | Description | Status |
|------|-------------|--------|
| `01_identity.core.tao` | Identity function `x -> x` | ✅ Works |
| `02_constant.core.tao` | Constant function (K combinator) `x -> y -> x` | ✅ Works |
| `03_application.core.tao` | Function application `(x -> x)(42)` | ✅ Works |
| `04_pi_type.core.tao` | Pi type (dependent function type) | ✅ Works |
| `05_constructor.core.tao` | Constructor with argument | ⚠️ Needs definition |
| `06_record.core.tao` | Record with multiple fields | ✅ Works |
| `07_hole.core.tao` | Hole with identifier | ⚠️ Unsolved (expected) |
| `08_annotation.core.tao` | Type annotation | ✅ Works |
| `09_type_universe.core.tao` | Type universe | ✅ Works |
| `10_literal_type.core.tao` | Literal type (I32) | ✅ Works |
| `11_let_binding.core.tao` | Let binding `let x = 42 in x` | ✅ Works |
| `12_let_function.core.tao` | Let with simple value | ✅ Works |

### Notes on Examples

- **Constructor (05)**: Constructors must be defined before use. This example shows the syntax but type checking will fail without a constructor definition. Future feature: data type definitions.
- **Hole (07)**: Holes are metavariables that need to be solved during type checking. This example demonstrates the syntax; the hole remains unsolved (expected behavior).

## Real Programs (`programs/`)

Coming soon:
- Fibonacci function
- Vector operations with dependent types
- List operations
- Church numerals

## Error Examples (`errors/`)

See [`errors/README.md`](errors/README.md) for examples of:
- Syntax errors
- Type errors
- Exhaustiveness check failures

## Syntax Reference

### Lambda
```
x -> body           -- Single parameter
x -> y -> body      -- Multiple parameters (curried)
```

### Pi Type
```
(x : $Type) -> $Type    -- Dependent function type
```

### Constructor
```
#Name               -- Constructor without argument
#Name(expr)         -- Constructor with argument
```

### Record
```
{}                  -- Empty record
{x: expr}           -- Single field
{x: expr, y: expr}  -- Multiple fields
```

### Type Annotation
```
expr : Type         -- Annotate expression with type
```

### Hole
```
?                   -- Anonymous hole
?1                  -- Named hole
```

### Type Universe
```
$Type               -- Type of small types
$Type(1)            -- Type universe at level 1
```

### Literal Type
```
$I32                -- Type of 32-bit integers
$F64                -- Type of 64-bit floats
```

### Match Expression
```
%match arg ~ motive {
  | pattern -> body
  | pattern -> body
}
```

### Built-in Call
```
%call prim.add(x, y)
```

### Comptime
```
%comptime term
```

## Related Documentation

- [Core Language Overview](../../docs/plans/core/01-overview.md)
- [CLI Documentation](../../docs/plans/cli/01-overview.md)
- [Error Examples](errors/README.md)
