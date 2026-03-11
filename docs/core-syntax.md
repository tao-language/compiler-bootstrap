# Learn Core in Y Minutes

A quick reference for the Core language syntax. Core is a minimal dependently-typed calculus that serves as the target for high-level language compilation.

## Comments

```text
// Single line comment
```

## Literals

```text
42          // I32 integer
3.14        // F64 float
#True       // Constructor (like an enum variant)
#Some(42)   // Constructor with argument
```

## Variables

```text
x           // Variable reference
```

## Lambda Abstraction

```text
x -> x                      // Identity function
x -> y -> x                 // Constant function (K combinator)
x -> y -> %call prim.add(x, y)  // Function using primitive
```

## Function Application

```text
f(x)                        // Apply f to x
f(x)(y)                     // Curried application
(x -> x)(42)                // Apply lambda to 42
```

## Type Annotations

```text
(x : $I32)                  // x has type I32
(42 : $I32)                 // Annotate literal with type
```

## Pi Types (Dependent Function Types)

```text
(x : $Type) -> $Type        // Function type where domain is $Type
(x : $I32) -> $Type         // Dependent type: return depends on value
```

## Type Universe

```text
$Type                       // Type of small types
$Type(1)                    // Type universe at level 1
```

## Literal Types

```text
$I32                        // Type of 32-bit integers
$I64                        // Type of 64-bit integers
$F32                        // Type of 32-bit floats
$F64                        // Type of 64-bit floats
```

## Records

```text
{}                          // Empty record
{x: 42}                     // Single field
{x: 42, y: 3.14}            // Multiple fields
```

## Record Projection

```text
point.x                     // Access field x of record
```

## Constructors

```text
#Some                       // Constructor without argument
#Some(42)                   // Constructor with argument
#Cons(h, t)                 // Constructor with multiple args
```

## Pattern Matching

```text
%match arg ~ motive {
  | pattern -> body
  | pattern -> body
}
```

### Match with Dependent Motive

```text
%match n ~ (k : Nat) -> $Type {
  | #Zero -> $I32
  | #Succ(_pred) -> $Type
}
```

### Match with Guards

```text
%match n ~ ($Type) {
  | k ? (%call prim.leq(k, 1)) -> 1
  | k -> %call prim.mul(k, fact(%call prim.sub(k, 1)))
}
```

## Holes (Metavariables)

```text
?                           // Anonymous hole (to be inferred)
?1                          // Named hole #1
```

## Let Bindings (Syntax Sugar)

```text
let x = 42 in x             // Desugars to: (x -> x)(42)
let id = x -> x in id(42)   // Desugars to: (id -> id(42))(x -> x)
```

## Built-in Calls (FFI)

```text
%call prim.add(x, y)        // Addition
%call prim.sub(x, y)        // Subtraction
%call prim.mul(x, y)        // Multiplication
%call prim.div(x, y)        // Division
%call prim.mod(x, y)        // Modulo
%call prim.eq(x, y)         // Equality
%call prim.leq(x, y)        // Less than or equal
```

## Compile-Time Evaluation

```text
%comptime %call prim.add(10, 5)   // Evaluated at compile-time
let size = %comptime 15 in size   // Use computed value
```

## Complete Example

```text
// Identity function applied to 42
let id = x -> x in
id(42)

// Curried addition
let add = x -> y -> %call prim.add(x, y) in
add(10)(20)

// Pattern matching on constructors
let b = #True in
%match b ~ ($Type) {
  | #True -> 1
  | #False -> 0
}

// Record with projection
let point = {x: 10, y: 20} in
point.x

// Dependent match
%match n ~ ($Type) {
  | #Zero -> #True
  | #Succ(_pred) -> #False
}
```

## Precedence (Low to High)

1. Lambda/Pi: `x -> body`, `(x : A) -> B`
2. Let: `let x = v in body`
3. Match: `%match arg ~ motive { ... }`
4. Application: `f(x)`
5. Annotation: `term : type`
6. Projection: `record.field`
7. Atoms: variables, literals, constructors, records

## Type Checking Rules

- **Bidirectional**: Terms either *check* against a type or *infer* a type
- **Holes**: Create metavariables to be solved during type checking
- **Universes**: `$Type : $Type(1) : $Type(2) : ...`

## Common Patterns

### Polymorphic Identity

```text
(x -> x) : $Type
```

### Constant Function (K Combinator)

```text
x -> y -> x
```

### Function Composition

```text
f -> g -> x -> g(f(x))
```

### Boolean Logic (Church Encoding)

```text
let true = t -> f -> t in
let false = t -> f -> f in
let and = a -> b -> a(b)(false) in
and(true)(false)
```

### Natural Numbers (Church Encoding)

```text
let zero = f -> x -> x in
let one = f -> x -> f(x) in
let two = f -> x -> f(f(x)) in
let succ = n -> f -> x -> f(n(f)(x)) in
succ(zero)
```

## Error Handling

- **Parse Errors**: Invalid syntax reported with source location
- **Type Errors**: Type mismatches reported with expected/got
- **Hole Errors**: Unsolved holes reported at end of checking

## Related Documentation

- [Core Language Overview](plans/core/01-overview.md)
- [Error Examples](../examples/core/errors/README.md)
- [Program Examples](../examples/core/programs/README.md)
