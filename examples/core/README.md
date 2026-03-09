# Core Language Examples

This directory contains working examples of core language syntax.

## Usage

Check an example (type-check only):
```bash
gleam run -- check examples/core/01_identity.core.tao
```

Run an example (type-check and evaluate):
```bash
gleam run -- run examples/core/01_identity.core.tao
```

Run with verbose output:
```bash
gleam run -- run examples/core/01_identity.core.tao --verbose
```

Run with debug output (shows AST):
```bash
gleam run -- run examples/core/02_constant.core.tao --debug
```

## Examples

| File | Description | Expected Output |
|------|-------------|-----------------|
| `01_identity.core.tao` | Identity function | `x -> x` |
| `02_constant.core.tao` | Constant function (K combinator) | `x -> y -> x` |
| `03_application.core.tao` | Function application | `var0(var0)` |
| `04_pi_type.core.tao` | Pi type (dependent function type) | `(x : $Type) -> $Type` |
| `05_constructor.core.tao` | Constructor with argument | `#Some(42)` |
| `06_record.core.tao` | Record with multiple fields | `{x: 1, y: 2, z: 3}` |
| `07_hole.core.tao` | Hole with identifier | `?1` |
| `08_annotation.core.tao` | Type annotation | `var0 : $I32` |
| `09_type_universe.core.tao` | Type universe | `$Type` |
| `10_literal_type.core.tao` | Literal type (I32) | `$I32` |

## Subdirectories

- `errors/` - Examples of invalid syntax that produce parse errors

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
