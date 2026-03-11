# Core Language Programs

This directory contains real-world programs written in the core language.

## Usage

Check a program (type-check only):
```bash
gleam run -- check examples/core/programs/01_literals_and_primitives.core.tao
```

Run a program (type-check and evaluate):
```bash
gleam run -- run examples/core/programs/01_literals_and_primitives.core.tao
```

## Current Examples

### Basic Programs

| File | Description | Status |
|------|-------------|--------|
| `01_literals_and_primitives.core.tao` | Literals, type annotations, primitive calls | ✅ Works |
| `02_functions_and_currying.core.tao` | Lambda syntax, curried application | ✅ Works |
| `03_algebraic_data_types.core.tao` | Constructors, pattern matching | ✅ Works |
| `04_records.core.tao` | Record construction, field access | ✅ Works |
| `05_dependent_types.core.tao` | Dependent types, match motives | ✅ Works |
| `06_pattern_guards.core.tao` | Pattern guards, conditional logic | ⚠️ Requires prim.mod |
| `07_comptime.core.tao` | Compile-time evaluation | ✅ Works |
| `08_type_universes_and_holes.core.tao` | Universe levels, hole inference | ✅ Works |
| `09_factorial.core.tao` | Full integration example | ⚠️ Requires recursion |
| `10_church_numerals.core.tao` | Church encoding of naturals | ✅ Works |
| `11_church_booleans.core.tao` | Church encoding of booleans | ✅ Works |
| `12_list_operations.core.tao` | Church-encoded lists | ⚠️ Placeholder |
| `13_vector_dependent.core.tao` | Length-indexed vectors | ⚠️ Golden sample |
| `14_let_function_application.core.tao` | Let with function application | ✅ Works |

### Example Details

#### 01_literals_and_primitives.core.tao

Tests literal types ($I32, $F64), type annotations, and primitive calls.

```text
let x = (42 : $I32) in
let y = (3.14 : $F64) in
%call prim.add(x, x)
```

#### 02_functions_and_currying.core.tao

Verifies lambda syntax and curried application.

```text
let id = (x -> x) in
let add = (x -> (y -> %call prim.add(x, y))) in
add(10)(20)
```

#### 10_church_numerals.core.tao

Lambda encoding of natural numbers.

```text
let zero = (f -> (x -> x));
let one = (f -> (x -> f(x)));
let two = (f -> (x -> f(f(x))));
let succ = (n -> (f -> (x -> f(((n)(f))(x)))));
succ(zero)
```

#### 11_church_booleans.core.tao

Church encoding of boolean logic.

```text
let true = (t -> (f -> t));
let false = (t -> (f -> f));
let and = (a -> (b -> ((a)(b))(false)));
and(true)(false)
```

#### 14_let_function_application.core.tao

Demonstrates hole inference for let-bound functions.

```text
let id = x -> x in id(42)
```

**Output:** `42`

## Language Limitations

Current limitations that prevent some programs from fully working:

1. **No recursion**: Requires fixpoint combinator or let-rec (factorial, list operations)
2. **No data type definitions**: Constructors must be predefined (vectors, custom types)
3. **Limited primitives**: Some primitives like `prim.mod` may not be implemented
4. **Pattern guards**: Syntax supported but requires primitive operations

## Golden Samples

Some examples are "golden samples" - they demonstrate desired syntax that may not fully type-check or evaluate yet, but serve as targets for future implementation:

- `09_factorial.core.tao` - Requires recursion support
- `12_list_operations.core.tao` - Requires recursion for map
- `13_vector_dependent.core.tao` - Requires dependent type support

## Related

- [Basic Terms](../terms/) - Core language constructs
- [Error Examples](../errors/) - Invalid syntax and type errors
- [Learn Core in Y Minutes](../../docs/core-syntax.md) - Syntax reference
