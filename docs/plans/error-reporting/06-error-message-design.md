# Tao Error Message Design

> **Goal**: Delightfully helpful error messages with excellent visual feedback
> **Status**: 📋 Design Complete
> **Date**: March 2025

---

## Core Principles

### 1. Instant Visual Recognition

**Before**:
```
error[E0101]: Type mismatch at line 5
```

**After**:
```
❌ error[E0101]: Type mismatch
   ┌─ src/main.tao:5:10
   │
 5 │ let x: Int = "hello"
   │          ━━┷┷┷┷┷┷━ expected Int, found String
   │
   💡 expected because this is Int
   📝 note: Int and String are incompatible types
   🔧 help: Did you mean to use a number? e.g., `let x: Int = 42`
```

---

### 2. Emoji-Guided Navigation

| Emoji | Meaning | Usage |
|-------|---------|-------|
| ❌ | Error | Critical issues that prevent compilation |
| ⚠️ | Warning | Issues that don't prevent compilation but should be fixed |
| ℹ️ | Info | Additional information |
| 💡 | Tip | Explanation of why something is wrong |
| 📝 | Note | Additional context or facts |
| 🔧 | Help | Suggested fix with code example |
| 📚 | Reference | Link to documentation |
| 🎯 | Target | Points to exact location |
| 🔍 | Context | Shows related code or definitions |
| ✅ | Success | Shows correct version |

---

### 3. Color Coding (Terminal/IDE)

| Element | Color | Purpose |
|---------|-------|---------|
| ❌ Error | Bright Red | Immediate attention |
| ⚠️ Warning | Yellow/Orange | Caution |
| ℹ️ Info | Blue | Information |
| 🔧 Help | Green | Actionable suggestion |
| 📝 Note | Gray | Context |
| Code | Cyan | Code snippets |
| File path | White | Location |

---

### 4. Visual Hierarchy

```
❌ error[E0101]: Type mismatch                          ← Header (bold, red)
   ┌─ src/main.tao:5:10                                ← Location
   │
 5 │ let x: Int = "hello"                              ← Source code
   │          ━━┷┷┷┷┷┷━ expected Int, found String     ← Underline + label
   │
   💡 expected because this is Int                     ← Explanation (blue)
   📝 note: Int and String are incompatible types      ← Note (gray)
   🔧 help: Did you mean...                            ← Suggestion (green)
      │
  3 │ let x: Int = 42                                  ← Code example
      │
```

---

## Enhanced Error Message Examples

### Syntax Errors

#### E0001: Unexpected Token

```tao
// ❌ Wrong
let x = 5 +
```

```
❌ error[E0001]: Unexpected token
   ┌─ src/main.tao:3:13
   │
 3 │ let x = 5 +
   │             ┷ unexpected end of input
   │
   💡 expected an expression after `+`
   🔧 help: provide the right-hand side:
      │
    3 │ let x = 5 + 10
      │             ++
      │
   🔧 help: or remove the operator:
      │
    3 │ let x = 5
      │         ~
      │
```

---

#### E0002: Missing Closing Brace

```tao
// ❌ Wrong
fn add(a: Int, b: Int): Int {
  a + b

```

```
❌ error[E0002]: Missing closing brace
   ┌─ src/main.tao:1:32
   │
 1 │ fn add(a: Int, b: Int): Int {
   │                                ┚ unclosed brace
   │
 2 │   a + b
   │
   💡 this opening brace `{` is never closed
   🔧 help: add a closing brace:
      │
    3 │ }
      │
   📝 note: every opening brace `{` needs a matching closing brace `}`
```

---

#### E0003: Invalid Identifier

```tao
// ❌ Wrong
let 123abc = 5
```

```
❌ error[E0003]: Invalid identifier
   ┌─ src/main.tao:3:5
   │
 3 │ let 123abc = 5
   │     ━━━┷━━ invalid identifier name
   │
   📝 note: identifiers cannot start with a number
   📝 note: identifiers can contain letters, numbers, and underscores
   🔧 help: use a valid identifier name:
      │
    3 │ let abc123 = 5
      │     ~~~~~~
      │
   🔧 help: or use underscore prefix:
      │
    3 │ let _123abc = 5
      │     ~~~~~~~
      │
   📚 reference: https://tao-lang.dev/docs/identifiers
```

---

### Type Errors

#### E0101: Type Mismatch

```tao
// ❌ Wrong
let x: Int = "hello"
```

```
❌ error[E0101]: Type mismatch
   ┌─ src/main.tao:3:14
   │
 3 │ let x: Int = "hello"
   │     ┬      ━━━┷━━━
   │     │      │
   │     │      expected Int, found String
   │     expected because this is Int
   │
   📝 note: Int and String are incompatible types
   🔧 help: use a number instead:
      │
    3 │ let x: Int = 42
      │              ~~
      │
   🔧 help: or change the type annotation:
      │
    3 │ let x: String = "hello"
      │         ~~~~~~
      │
   📚 reference: https://tao-lang.dev/docs/types
```

---

#### E0102: Undefined Variable

```tao
// ❌ Wrong
fn increment(): Int {
  count + 1
}
```

```
❌ error[E0102]: Undefined variable
   ┌─ src/main.tao:4:3
   │
 4 │   count + 1
   │   ━━┷━━
   │   │
   │   this variable is not defined
   │
   📝 note: `count` is not defined in this scope
   🔍 context: function `increment` defined at line 3
   🔧 help: did you forget to define it?
      │
    3 │ fn increment(): Int {
    4 │   let count = 0
      │   +++++++++++++
    5 │   count + 1
      │
   🔧 help: or pass it as a parameter:
      │
    3 │ fn increment(count: Int): Int {
      │              ~~~~~~~~~~
      │
   📚 reference: https://tao-lang.dev/docs/variables
```

---

#### E0103: Not a Function

```tao
// ❌ Wrong
let x = 5
let y = x(10)
```

```
❌ error[E0103]: Cannot call non-function value
   ┌─ src/main.tao:4:11
   │
 4 │ let y = x(10)
   │           ━┛━ cannot call value of type `Int`
   │
   📝 note: `x` has type `Int`, which is not callable
   💡 only functions can be called with parentheses
   🔧 help: did you mean to use a different variable?
   🔧 help: or define `x` as a function:
      │
    2 │ let x = fn(n: Int): Int { n * 2 }
      │         ++++++++++++++++++++++++++
      │
   📚 reference: https://tao-lang.dev/docs/functions
```

---

#### E0104: Arity Mismatch

```tao
// ❌ Wrong
fn add(a: Int, b: Int): Int {
  a + b
}

let result = add(5)
```

```
❌ error[E0104]: Wrong number of arguments
   ┌─ src/main.tao:6:16
   │
 6 │ let result = add(5)
   │              ━━┛━
   │              │
   │              expected 2 arguments, got 1
   │
   📝 note: function signature is `fn add(a: Int, b: Int): Int`
   🔍 context: function defined at line 3
   🔧 help: provide the missing argument:
      │
    6 │ let result = add(5, 10)
      │                    ++++
      │
   📚 reference: https://tao-lang.dev/docs/functions#arguments
```

---

#### E0105: Constructor Undefined

```tao
// ❌ Wrong
type Maybe<T> = Some(T) | None

let x = Just(5)
```

```
❌ error[E0105]: Constructor not found
   ┌─ src/main.tao:5:9
   │
 5 │ let x = Just(5)
   │         ━━┛━ constructor not found for type `Maybe`
   │
   📝 note: `Just` is not a constructor for type `Maybe<T>`
   🔍 available constructors:
   │
   │   ✅ Some(T)
   │   ✅ None
   │
   💡 you might be thinking of `Some` from the `Maybe` type
   🔧 help: use the correct constructor:
      │
    5 │ let x = Some(5)
      │         ~~~~
      │
   📚 reference: https://tao-lang.dev/docs/sum-types
```

---

#### E0106: Unsolved Hole

```tao
// ❌ Wrong
fn incomplete<T>(x: T): T {
  ?
}
```

```
❌ error[E0106]: Unsolved hole
   ┌─ src/main.tao:3:3
   │
 3 │   ?
   │   ┷ hole not solved
   │
   📝 note: hole #1 expects type `T`
   📝 note: holes must be filled during type checking
   💡 holes are placeholders that must be inferred or provided
   🔧 help: provide an implementation:
      │
    3 │   x  // return the input
      │   ~
      │
   🔧 help: or use a typed hole:
      │
    3 │   ?(x: T)
      │
   📚 reference: https://tao-lang.dev/docs/holes
```

---

### Pattern Matching Errors

#### E0201: Match Missing Case

```tao
// ❌ Wrong
type Result<T, E> = Ok(T) | Err(E)

fn unwrap<T, E>(result: Result<T, E>): T {
  match result {
    Ok(x) -> x,
  }
}
```

```
❌ error[E0201]: Pattern match not exhaustive
   ┌─ src/main.tao:6:3
   │
 6 │ ╭   match result {
 7 │ │     Ok(x) -> x,
 8 │ │   }
   │ ╰───┚ not all cases are covered
   │
   📝 note: type `Result<T, E>` has 2 constructors
   📝 note: you've covered 1 constructor: `Ok`
   🔍 missing constructors:
   │
   │   ❌ Err(E)
   │
   🔧 help: add the missing case:
      │
    8 │     Err(e) -> panic("unwrap called on Err"),
      │
   🔧 help: or use the `?` operator to propagate:
      │
    6 │   result?
      │
   🔧 help: or use `unwrap_or` with a default:
      │
    6 │   result.unwrap_or(default)
      │
   📚 reference: https://tao-lang.dev/docs/pattern-matching
```

---

#### E0202: Match Redundant Case

```tao
// ❌ Wrong
type Maybe<T> = Some(T) | None

fn process(m: Maybe<Int>): Int {
  match m {
    Some(x) if x > 0 -> x,
    Some(x) if x > 0 -> 0,  // Redundant!
    _ -> 0,
  }
}
```

```
⚠️ warning[W0202]: Redundant pattern
   ┌─ src/main.tao:7:5
   │
 7 │     Some(x) if x > 0 -> 0,  // Redundant!
   │     ━━━━━━━━━━━━━━ this case is already handled
   │
   📝 note: this pattern matches the same values as a previous case
   🔍 previous case:
   │
 6 │     Some(x) if x > 0 -> x,
   │     ━━━━━━━━━━━━━━
   │
   🔧 help: remove the redundant case, or use a different guard:
      │
    7 │     Some(x) if x <= 0 -> 0,
      │                ~~~~~~
      │
   💡 redundant cases are safe to remove and won't change behavior
```

---

#### E0203: Invalid Pattern

```tao
// ❌ Wrong
match x {
  5 + 3 -> "eight",
  _ -> "other",
}
```

```
❌ error[E0203]: Invalid pattern
   ┌─ src/main.tao:3:3
   │
 3 │   5 + 3 -> "eight",
   │   ━┛━━━ patterns cannot contain operators
   │
   📝 note: patterns must be constructors, literals, or variables
   📝 note: `5 + 3` is an expression, not a pattern
   🔧 help: use a literal pattern:
      │
    3 │   8 -> "eight",
      │   ~
      │
   🔧 help: or use a guard with a variable:
      │
    3 │   n if n == 8 -> "eight",
      │   ~~~~~~~~~~~
      │
   📚 reference: https://tao-lang.dev/docs/patterns
```

---

### Scope Errors

#### E0301: Variable Shadowing (Warning)

```tao
// ⚠️ Warning (not error, but helpful)
let x = 5
let x = "hello"  // Shadows previous `x`
```

```
⚠️ warning[W0301]: Variable shadowing
   ┌─ src/main.tao:4:5
   │
 4 │ let x = "hello"
   │     ┬ this shadows the previous `x`
   │     
   │
   🔍 previous definition:
   │
 3 │ let x = 5
   │     - defined here
   │
   📝 note: shadowing is allowed but may be confusing
   🔧 help: use a different name:
      │
    4 │ let message = "hello"
      │     ~~~~~~~
      │
   💡 pass `--allow shadowing` to suppress this warning
   💡 shadowing can be useful for transforming values: `let x = transform(x)`
```

---

#### E0302: Out of Scope

```tao
// ❌ Wrong
{
  let x = 5
}
print(x)
```

```
❌ error[E0302]: Variable out of scope
   ┌─ src/main.tao:5:7
   │
 5 │ print(x)
   │       ┷ this variable is out of scope
   │
   📝 note: `x` was defined in a block that has ended
   🔍 definition location:
   │
 2 │ {
 3 │   let x = 5
   │       - defined here
 4 │ }
   │ - block ends here
   │
   🔧 help: move the usage inside the block:
      │
    2 │ {
    3 │   let x = 5
    4 │   print(x)
      │   +++++++++
    5 │ }
      │
   🔧 help: or define `x` outside the block:
      │
    1 │ let x = 5
    2 │ {
    3 │   print(x)
      │
   📚 reference: https://tao-lang.dev/docs/scope
```

---

### Mutability Errors

#### E0401: Cannot Assign to Immutable Variable

```tao
// ❌ Wrong
let x = 5
x = 10  // Error: `x` is immutable
```

```
❌ error[E0401]: Cannot assign to immutable variable
   ┌─ src/main.tao:4:1
   │
 4 │ x = 10
   │ ┷ cannot assign to immutable variable
   │
   📝 note: `x` was declared as immutable
   🔍 declaration location:
   │
 3 │ let x = 5
   │     - declared here without `mut`
   │
   🔧 help: declare `x` as mutable:
      │
    3 │ let mut x = 5
      │     +++
      │
   🔧 help: or create a new variable:
      │
    4 │ let y = 10
      │     ~
      │
   💡 in Tao, variables are immutable by default for safety
   📚 reference: https://tao-lang.dev/docs/mutability
```

---

#### E0402: Mutable Parameter Not Allowed

```tao
// ❌ Wrong
fn process(mut x: Int): Int {
  x + 1
}
```

```
❌ error[E0402]: Mutable parameter not allowed
   ┌─ src/main.tao:3:14
   │
 3 │ fn process(mut x: Int): Int {
   │              ━┛ parameters are always immutable
   │
   📝 note: function parameters cannot be mutable
   💡 parameters are passed by value and cannot be modified
   🔧 help: use a local mutable variable instead:
      │
    3 │ fn process(x: Int): Int {
    4 │   mut y = x
    5 │   y = y + 1
    6 │   y
      │
   🔧 help: or just use the parameter directly:
      │
    3 │ fn process(x: Int): Int {
    4 │   x + 1
      │
   📚 reference: https://tao-lang.dev/docs/functions#parameters
```

---

### Comptime Errors

#### E0501: Comptime Evaluation Failed

```tao
// ❌ Wrong
const factorial = comptime {
  fn fact(n: Int): Int {
    if n <= 1 { 1 } else { n * fact(n - 1) }
  }
  fact(-5)  // Infinite recursion!
}
```

```
❌ error[E0501]: Comptime evaluation failed
   ┌─ src/main.tao:6:3
   │
 6 │   fact(-5)
   │   ━━━━┛━━━ stack overflow during comptime evaluation
   │
   📝 note: maximum recursion depth exceeded (1000 calls)
   📝 note: comptime evaluation must terminate
   💡 the base case `n <= 1` is never reached for negative numbers
   🔧 help: add a check for negative numbers:
      │
    4 │   fn fact(n: Int): Int {
    5 │     if n < 0 { panic("negative") }
    6 │     if n <= 1 { 1 } else { n * fact(n - 1) }
      │
   🔧 help: or use an absolute value:
      │
    6 │   fact(n.abs())
      │
   📚 reference: https://tao-lang.dev/docs/comptime
```

---

#### E0502: Permission Denied

```tao
// ❌ Wrong
@permission(Read("/etc/passwd"))
fn read_config(): String {
  comptime {
    read_file("/etc/shadow")  // Not allowed!
  }
}
```

```
❌ error[E0502]: Permission denied
   ┌─ src/main.tao:5:5
   │
 5 │     read_file("/etc/shadow")
   │     ━━━━━━━━━━━━━━━━━━━━━━━━ this operation requires Write("/etc/shadow")
   │
   📝 note: comptime code requires explicit permissions
   🔍 current permissions:
   │
   │   ✅ Read("/etc/passwd")
   │   ❌ Write("/etc/shadow")  ← missing!
   │
   🔧 help: add the required permission:
      │
    2 │ @permission(Read("/etc/passwd"), Write("/etc/shadow"))
      │                                +++++++++++++++++++++++
      │
   🔧 help: or use a file you have permission for:
      │
    5 │     read_file("/etc/passwd")
      │                 ~~~~~~~~~~~
      │
   📚 reference: https://tao-lang.dev/docs/permissions
```

---

### Import Errors

#### E0601: Module Not Found

```tao
// ❌ Wrong
import nonexistent_module
```

```
❌ error[E0601]: Module not found
   ┌─ src/main.tao:3:8
   │
 3 │ import nonexistent_module
   │        ━━━━━━━━━━━━━━━━━ could not find module `nonexistent_module`
   │
   🔍 searched in:
   │
   │   ❌ ./src/nonexistent_module.tao
   │   ❌ ./src/nonexistent_module/index.tao
   │   ❌ ./lib/nonexistent_module.tao
   │
   🔧 help: check the module name and path
   🔧 help: or create the module file:
      │
      │   touch src/nonexistent_module.tao
      │
   📚 reference: https://tao-lang.dev/docs/modules
```

---

#### E0602: Import Not Exported

```tao
// ❌ Wrong
// utils.tao
fn helper(): Int { 42 }  // Private by default

// main.tao
import utils { helper }
```

```
❌ error[E0602]: Import not exported
   ┌─ src/main.tao:3:18
   │
 3 │ import utils { helper }
   │                  ━━━━━━ `helper` is not exported from `utils`
   │
   📝 note: `helper` is private (not marked with `pub`)
   🔍 definition location:
   │
   │   // In utils.tao:
   │   fn helper(): Int { 42 }
   │   ━━━━━━━━━━━━━━━━━━━━━━━ defined here as private
   │
   🔧 help: export the function:
      │
      │   // In utils.tao:
      │   pub fn helper(): Int { 42 }
      │   +++
      │
   🔧 help: or import the private function (if in same package):
      │
    3 │ import utils { _helper }
      │                  ~~~~~~
      │
   💡 in Tao, items are private by default for encapsulation
   📚 reference: https://tao-lang.dev/docs/modules#exports
```

---

### Operator Errors

#### E0701: Operator Overload Not Found

```tao
// ❌ Wrong
type Point = { x: Int, y: Int }

let p1 = Point { x: 1, y: 2 }
let p2 = Point { x: 3, y: 4 }
let p3 = p1 + p2  // No `add` function for Point
```

```
❌ error[E0701]: Operator overload not found
   ┌─ src/main.tao:6:14
   │
 6 │ let p3 = p1 + p2
   │              ┷ no `add` function for type `Point`
   │
   📝 note: the `+` operator desugars to `add(p1, p2)`
   📝 note: `add` is not defined for type `Point`
   🔍 operator resolution:
   │
   │   `p1 + p2`  →  `add(p1, p2)`
   │   types: `Point + Point`  →  `add(Point, Point): ?`
   │
   🔧 help: define the operator overload:
      │
      │ fn add(a: Point, b: Point): Point {
      │   Point { x: a.x + b.x, y: a.y + b.y }
      │ }
      │
   🔧 help: or use a method:
      │
    6 │ let p3 = p1.add(p2)
      │             ~~~
      │
   📚 reference: https://tao-lang.dev/docs/operators
```

---

## Error Code Reference

| Code | Severity | Category | Description |
|------|----------|----------|-------------|
| E0001 | ❌ Error | Syntax | Unexpected token |
| E0002 | ❌ Error | Syntax | Missing closing brace |
| E0003 | ❌ Error | Syntax | Invalid identifier |
| E0101 | ❌ Error | Type | Type mismatch |
| E0102 | ❌ Error | Type | Undefined variable |
| E0103 | ❌ Error | Type | Not a function |
| E0104 | ❌ Error | Type | Arity mismatch |
| E0105 | ❌ Error | Type | Constructor undefined |
| E0106 | ❌ Error | Type | Unsolved hole |
| E0201 | ❌ Error | Pattern | Match missing case |
| E0202 | ⚠️ Warning | Pattern | Match redundant case |
| E0203 | ❌ Error | Pattern | Invalid pattern |
| E0301 | ⚠️ Warning | Scope | Variable shadowing |
| E0302 | ❌ Error | Scope | Out of scope |
| E0401 | ❌ Error | Mutability | Cannot assign to immutable |
| E0402 | ❌ Error | Mutability | Mutable parameter not allowed |
| E0501 | ❌ Error | Comptime | Evaluation failed |
| E0502 | ❌ Error | Comptime | Permission denied |
| E0601 | ❌ Error | Import | Module not found |
| E0602 | ❌ Error | Import | Import not exported |
| E0701 | ❌ Error | Operator | Operator overload not found |

---

## JSON Schema for LSP/AI Assistants

### Diagnostic Schema

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "Tao Diagnostic",
  "description": "Error/warning diagnostic for Tao language",
  "type": "object",
  "required": ["code", "severity", "message", "location"],
  "properties": {
    "code": {
      "type": "string",
      "description": "Error code (e.g., 'E0101')",
      "pattern": "^[EW][0-9]{4}$"
    },
    "severity": {
      "type": "string",
      "enum": ["error", "warning", "info"],
      "description": "Severity level"
    },
    "message": {
      "type": "string",
      "description": "Short error message"
    },
    "location": {
      "$ref": "#/definitions/SourceLocation"
    },
    "highlights": {
      "type": "array",
      "items": {
        "$ref": "#/definitions/Highlight"
      },
      "description": "Highlighted spans in source code"
    },
    "explanation": {
      "type": "string",
      "description": "Detailed explanation of the error"
    },
    "notes": {
      "type": "array",
      "items": {
        "type": "object",
        "required": ["message"],
        "properties": {
          "message": {
            "type": "string",
            "description": "Note message"
          },
          "location": {
            "$ref": "#/definitions/SourceLocation"
          }
        }
      },
      "description": "Additional context notes"
    },
    "suggestions": {
      "type": "array",
      "items": {
        "$ref": "#/definitions/Suggestion"
      },
      "description": "Suggested fixes"
    },
    "references": {
      "type": "array",
      "items": {
        "type": "object",
        "required": ["title", "url"],
        "properties": {
          "title": {
            "type": "string",
            "description": "Reference title"
          },
          "url": {
            "type": "string",
            "format": "uri",
            "description": "Reference URL"
          }
        }
      },
      "description": "Documentation references"
    },
    "context": {
      "type": "object",
      "properties": {
        "expectedType": {
          "type": "string",
          "description": "Expected type"
        },
        "actualType": {
          "type": "string",
          "description": "Actual type"
        },
        "availableConstructors": {
          "type": "array",
          "items": { "type": "string" },
          "description": "Available constructors"
        },
        "missingConstructors": {
          "type": "array",
          "items": { "type": "string" },
          "description": "Missing constructors"
        }
      },
      "description": "Additional context for specific error types"
    }
  },
  "definitions": {
    "SourceLocation": {
      "type": "object",
      "required": ["file", "startLine", "startColumn", "endLine", "endColumn"],
      "properties": {
        "file": {
          "type": "string",
          "description": "File path"
        },
        "startLine": {
          "type": "integer",
          "minimum": 1,
          "description": "1-based start line"
        },
        "startColumn": {
          "type": "integer",
          "minimum": 1,
          "description": "1-based start column"
        },
        "endLine": {
          "type": "integer",
          "minimum": 1,
          "description": "1-based end line"
        },
        "endColumn": {
          "type": "integer",
          "minimum": 1,
          "description": "1-based end column"
        }
      }
    },
    "Highlight": {
      "type": "object",
      "required": ["location", "style"],
      "properties": {
        "location": {
          "$ref": "#/definitions/SourceLocation"
        },
        "style": {
          "type": "string",
          "enum": ["primary", "secondary"],
          "description": "Highlight style"
        },
        "label": {
          "type": "string",
          "description": "Label text for highlight"
        }
      }
    },
    "Suggestion": {
      "type": "object",
      "required": ["message", "edits"],
      "properties": {
        "message": {
          "type": "string",
          "description": "Suggestion description"
        },
        "edits": {
          "type": "array",
          "items": {
            "type": "object",
            "required": ["location", "newText"],
            "properties": {
              "location": {
                "$ref": "#/definitions/SourceLocation"
              },
              "newText": {
                "type": "string",
                "description": "Replacement text"
              }
            }
          },
          "description": "Text edits to apply"
        },
        "priority": {
          "type": "integer",
          "minimum": 0,
          "maximum": 100,
          "default": 50,
          "description": "Suggestion priority (higher = more likely)"
        }
      }
    }
  }
}
```

### Example JSON Diagnostic

```json
{
  "code": "E0101",
  "severity": "error",
  "message": "Type mismatch",
  "location": {
    "file": "src/main.tao",
    "startLine": 3,
    "startColumn": 14,
    "endLine": 3,
    "endColumn": 21
  },
  "highlights": [
    {
      "location": {
        "file": "src/main.tao",
        "startLine": 3,
        "startColumn": 8,
        "endLine": 3,
        "endColumn": 9
      },
      "style": "secondary",
      "label": "expected because this is Int"
    },
    {
      "location": {
        "file": "src/main.tao",
        "startLine": 3,
        "startColumn": 14,
        "endLine": 3,
        "endColumn": 21
      },
      "style": "primary",
      "label": "expected Int, found String"
    }
  ],
  "explanation": "The type annotation specifies Int but the value is a String",
  "notes": [
    {
      "message": "Int and String are incompatible types"
    }
  ],
  "suggestions": [
    {
      "message": "Use a number instead",
      "edits": [
        {
          "location": {
            "file": "src/main.tao",
            "startLine": 3,
            "startColumn": 14,
            "endLine": 3,
            "endColumn": 21
          },
          "newText": "42"
        }
      ],
      "priority": 80
    },
    {
      "message": "Change the type annotation",
      "edits": [
        {
          "location": {
            "file": "src/main.tao",
            "startLine": 3,
            "startColumn": 8,
            "endLine": 3,
            "endColumn": 11
          },
          "newText": "String"
        }
      ],
      "priority": 60
    }
  ],
  "references": [
    {
      "title": "Tao Type System",
      "url": "https://tao-lang.dev/docs/types"
    }
  ],
  "context": {
    "expectedType": "Int",
    "actualType": "String"
  }
}
```

---

## Visual Design Guidelines

### 1. Terminal Output

```
❌ error[E0101]: Type mismatch
   ┌─ src/main.tao:3:10
   │
 3 │ let x: Int = "hello"
   │          ━━┷┷┷┷┷┷━ expected Int, found String
   │
   💡 expected because this is Int
   📝 note: Int and String are incompatible types
   🔧 help: Did you mean to use a number? e.g., `let x: Int = 42`
```

**Colors**:
- ❌ `error` - Bright Red (`\x1b[91m`)
- ⚠️ `warning` - Yellow (`\x1b[93m`)
- ℹ️ `info` - Blue (`\x1b[94m`)
- 🔧 `help` - Green (`\x1b[92m`)
- 📝 `note` - Gray (`\x1b[90m`)
- Code - Cyan (`\x1b[96m`)
- File path - White (`\x1b[97m`)

### 2. IDE Integration

**Inline Display**:
```
let x: Int = "hello"
           ━━━━━━━━
           ❌ Expected Int, found String
           💡 Did you mean: 42?
```

**Hover Tooltip**:
```
❌ Type mismatch (E0101)

Expected: Int
Found:    String

💡 Int and String are incompatible types

🔧 Quick Fix: Use a number (42)
🔧 Quick Fix: Change type to String
📚 Read more: tao-lang.dev/docs/types
```

**Quick Fix Menu**:
```
Quick Fixes...
  ✅ Use a number: 42
  ✅ Change type to String
  📖 Open documentation
  🔍 Find similar errors
```

### 3. Accessibility

- **Screen Readers**: Provide text alternatives for emojis
- **Color Blindness**: Don't rely solely on color (use icons too)
- **High Contrast**: Support high contrast mode
- **Font Size**: Support scalable fonts

---

## Additional Improvements

### 1. Error Grouping

Group related errors together:

```
❌ 3 errors found in src/main.tao

❌ error[E0101]: Type mismatch (line 5)
❌ error[E0102]: Undefined variable (line 10)
❌ error[E0201]: Match missing case (line 15)

💡 tip: Fix errors from top to bottom - later errors may be caused by earlier ones
```

### 2. Error Chaining

Show cascading errors:

```
❌ error[E0101]: Type mismatch
   ┌─ src/main.tao:5:10
   │
 5 │ let x: Int = "hello"
   │          ━━┷┷┷┷┷┷━
   │
   💡 this error may be causing 2 other errors below

⚠️ error[E0102]: Undefined variable (possibly caused by error above)
⚠️ error[E0302]: Out of scope (possibly caused by error above)
```

### 3. Progress Indicators

For long-running checks:

```
⏳ Type checking... 45%
   ✓ Parsing complete
   ✓ Name resolution complete
   ⏳ Type checking in progress...
   ○ Exhaustiveness checking pending
   ○ Comptime evaluation pending
```

### 4. Error Statistics

At the end of compilation:

```
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
❌ 3 errors, ⚠️ 2 warnings found

Error breakdown:
  Type errors:      2
  Pattern errors:   1

Most common error: Type mismatch (E0101)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 5. Learning Mode

For beginners, add extra explanations:

```
❌ error[E0101]: Type mismatch
   ┌─ src/main.tao:3:14
   │
 3 │ let x: Int = "hello"
   │              ━━━━━━━━
   │
   📚 LEARNING MODE:
   │
   │ In programming, every value has a type.
   │ Types include: Int (numbers), String (text), Bool (true/false)
   │
   │ You said `x` should be Int (a number),
   │ but you gave it "hello" (text).
   │
   │ This is like putting text in a number-only box!
   │
   🔧 help: Use a number: let x: Int = 42
   📚 reference: https://tao-lang.dev/learn/types
```

---

## Implementation Checklist

### Phase 1: Core Infrastructure
- [ ] Define JSON schema for diagnostics
- [ ] Implement diagnostic type in compiler
- [ ] Add emoji support to terminal output
- [ ] Implement color coding

### Phase 2: Error Messages
- [ ] Implement all 23 error types
- [ ] Add source snippet formatting
- [ ] Add suggestions with code edits
- [ ] Add notes and explanations

### Phase 3: IDE Integration
- [ ] Implement LSP diagnostic conversion
- [ ] Add quick fix support
- [ ] Add hover tooltip support
- [ ] Add inline error display

### Phase 4: Advanced Features
- [ ] Implement error grouping
- [ ] Implement error chaining
- [ ] Add learning mode
- [ ] Add error statistics

---

## Related Documents

- **[01-overview.md](./01-overview.md)** - Tao language overview
- **[02-syntax.md](./02-syntax.md)** - Tao syntax specification
- **[03-desugaring.md](./03-desugaring.md)** - Desugaring rules
- **[../../docs/cli.md](../../docs/cli.md)** - CLI documentation
- **[../../docs/syntax-library.md](../../docs/syntax-library.md)** - Syntax library

---

## References

- [Rust Compiler Errors](https://doc.rust-lang.org/error-index.html) - Gold standard with emojis
- [Elm Compiler Errors](https://elm-lang.org/news/compiler-errors-for-humans) - Human-friendly errors
- [Gleam Compiler Errors](https://gleam.run/book/tour/errors.html) - Modern functional errors
- [TypeScript Errors](https://www.typescriptlang.org/docs/handbook/error.html) - Familiar syntax errors
- [LSP Diagnostic](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#diagnostic) - Language Server Protocol spec
