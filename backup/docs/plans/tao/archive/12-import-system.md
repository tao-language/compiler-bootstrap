# Import System

> **Goal**: Explicit, unambiguous name resolution with support for function and operator overloading
> **Status**: 📋 Planned
> **Date**: March 14, 2026
> **Author**: Tao Compiler Team

---

## Status

### What's Pending

- Import syntax design and specification
- Import resolution algorithm
- Overloading-aware name lookup
- Implicit prelude imports
- Circular import detection
- Import desugaring to Core FFI calls
- Import tests

### Related

- See **[01-overview.md](./01-overview.md)** for Tao language overview
- See **[../tao/11-test-system.md](./11-test-system.md)** for test system (uses imports)
- See **[../core/02-syntax.md](../core/02-syntax.md)** for Core FFI system

---

## Core Principle

**Explicit over implicit, unambiguous over convenient.**

Every name in Tao must resolve to exactly one definition at compile time. Overloading is resolved through explicit type annotations or fully qualified names, never through implicit inference.

---

## Import Syntax

### Basic Forms

```tao
-- Import entire module (all public names)
import result

-- Import with alias
import result as res

-- Import specific types (includes constructors automatically)
import result { Result }  -- Also imports Ok, Error

-- Import specific names (types, functions, operators)
import result { Ok, Error, map }

-- Import specific names with aliases
import result { Ok as Success, Error as Failure }

-- Import with alias and specific names
import result as res { Result, map }

-- Import everything with wildcard alias (special case)
import result as *
```

### Type Imports Include Constructors

**Decision**: Importing a type automatically imports its constructors.

```tao
-- result.tao
pub type Result(a, b) {
  Ok(a)
  Error(b)
}

-- Usage
import result { Result }  -- Also imports Ok, Error automatically

let x: Result(I32, String) = Ok(42)  -- Ok is available
```

**Rationale**: Type annotations already indicate the source. Forcing explicit constructor imports is verbose without adding clarity.

### Directory vs File Imports

**Decision**: Both are allowed with clear semantics.

```tao
-- Import file
import prelude/result      -- Imports prelude/result.tao

-- Import directory (imports ALL files in directory)
import prelude             -- Imports prelude/*.tao (except _*.tao)

-- Import specific names from directory
import prelude { Result, Option }
```

**Directory Import Semantics**:

When importing a directory, ALL `.tao` files in that directory are imported, EXCEPT files starting with `_`:

```
lib/prelude/
├── result.tao      -- Imported by `import prelude`
├── option.tao      -- Imported by `import prelude`
├── string.tao      -- Imported by `import prelude`
└── _internal.tao   -- NOT imported (private file)
```

**Accessing Private Files**:

Files starting with `_` can still be imported explicitly:

```tao
import prelude/_internal  -- OK: explicit import of private file
```

**Rationale**:

| Approach | Pros | Cons |
|----------|------|------|
| **Index file** (`prelude/prelude.tao`) | Explicit re-exports | Verbose, maintenance burden |
| **Auto-import all** (current) | No boilerplate, `_` convention | Less control over exports |
| **Explicit list** | Full control | Very verbose for large modules |

**Decision**: **Auto-import all except `_` files** - consistent with function/type visibility, no boilerplate.

### Intra-Directory Visibility

**Decision**: **Explicit imports required** - files in the same directory do NOT see each other automatically.

```tao
-- math/trig.tao
import math/base  -- Required: explicit import

-- NOT automatic:
-- base.sin(x)  -- Error: base not in scope
```

**Rationale**:

| Approach | Pros | Cons |
|----------|------|------|
| **Automatic** (Python `__init__.py`) | Less typing | Unclear dependencies, accidental coupling |
| **Explicit** (Rust `mod`) | Clear dependencies, easier refactoring | More typing |

**Decision**: **Explicit imports** - makes dependencies clear, consistent with "explicit over implicit" principle.

**Example**:

```
lib/math/
├── base.tao      -- sin, cos, tan
├── trig.tao      -- Uses base: `import math/base`
└── calculus.tao  -- Uses trig: `import math/trig`
```

```tao
-- math/trig.tao
import math/base

fn sine(x: F64) -> F64 {
  base.sin(x)  -- Clear where sin comes from
}

-- math/calculus.tao
import math/trig

fn derivative(f: F64 -> F64, x: F64) -> F64 {
  (trig.sine(x + 0.001) - trig.sine(x)) / 0.001
}
```

**Rule**: Every import must be explicit, even within the same directory. This makes the dependency graph clear and refactorable.

### Prelude Self-Imports

**Decision**: Prelude files can import other prelude files. Implicit prelude import is a no-op for prelude files themselves.

```tao
-- prelude/result.tao
import prelude/option  -- OK: explicit import of sibling module
-- Implicit `import prelude as *` is ignored (no-op)

-- prelude/option.tao  
import prelude/result  -- OK: explicit import of sibling module

-- main.tao (non-prelude file)
-- Implicit `import prelude as *` is active
let x = prelude.Result.Ok(42)
```

**Circular Import Prevention**:
- Prelude files use explicit imports for dependencies
- Implicit prelude import is skipped for files IN the prelude module
- Import stack tracking prevents infinite loops

### Wildcard Import Semantics

`import module as *` imports all public names from the module, making them available **with the module name as prefix**:

```tao
import result as *

-- Available as:
result.Ok(42)
result.Error("message")

-- NOT available as:
-- Ok(42)        -- Error: unbound variable
-- Error("msg")  -- Error: unbound variable
```

**Rationale**: Wildcard imports should never cause name collisions. The `as *` syntax makes the module name available, not all its contents.

### Qualified vs Unqualified Imports

| Syntax | Unqualified Names | Qualified Names |
|--------|------------------|-----------------|
| `import result` | None | `result.Ok`, `result.Error` |
| `import result as res` | None | `res.Ok`, `res.Error` |
| `import result {Ok, Error}` | `Ok`, `Error` | `result.Ok` (if module name known) |
| `import result as res {Ok, Error}` | `Ok`, `Error` | `res.Ok`, `res.Error` |
| `import result {Ok as Success}` | `Success` | `result.Ok` (if module name known) |
| `import result as *` | None | `result.*` (all public names) |

---

## Name Resolution Algorithm

### Resolution Order

1. **Local scope** - Function parameters, let bindings, local definitions
2. **Imported names** - Unqualified imports (in order of import)
3. **Qualified names** - `module.name` lookups
4. **Implicit prelude** - Automatically imported names

### Shadowing Rules

```tao
import result { Ok }

fn test() {
  let Ok = 42  -- Shadows imported Ok
  Ok  -- Refers to 42, not result.Ok
}
```

**Rule**: Later imports shadow earlier imports. Local bindings shadow imports.

### Duplicate Import Handling

```tao
import result { Ok }
import option { Some }
import result { Error }  -- OK: same module, different names

import result { Ok }     -- Warning: Ok already imported from result
import option { Some }   -- Warning: Some already imported from option
```

**Rule**: Importing the same name twice from different modules is an error. Importing the same name from the same module is a warning (redundant).

---

## Overloading Support

### Function Overloading

Tao supports ad-hoc polymorphism through explicit overloads:

```tao
-- Define overloaded function
fn add(x: I32, y: I32) -> I32 { x + y }

fn add(x: F64, y: F64) -> F64 { x + y }

fn add(x: String, y: String) -> String { string.concat(x, y) }

-- Usage requires type annotation for resolution
let result = add(1, 2)           -- I32 overload (inferred from literals)
let result = add(1.0, 2.0)       -- F64 overload
let result = add("a", "b") as String  -- Explicit annotation
```

### Operator Overloading

Operators are desugared to function calls:

```tao
-- Operator definition
fn (+)(x: I32, y: I32) -> I32 { /* ... */ }

fn (+)(x: F64, y: F64) -> F64 { /* ... */ }

-- Usage
let result = 1 + 2      -- Desugars to: add_i32(1, 2)
let result = 1.0 + 2.0  -- Desugars to: add_f64(1.0, 2.0)
```

### Import Resolution with Overloading

```tao
-- Module: math.tao
fn add(x: I32, y: I32) -> I32 { ... }
fn add(x: F64, y: F64) -> F64 { ... }
fn (+)(x: I32, y: I32) -> I32 { ... }

-- Module: vectors.tao
fn add(x: Vec2, y: Vec2) -> Vec2 { ... }
fn (+)(x: Vec2, y: Vec2) -> Vec2 { ... }

-- Usage module
import math
import vectors

-- Ambiguous without type annotation
let result = math.add(1, 2)      -- OK: qualified, resolves to math.add_i32
let result = add(1, 2)           -- Error: ambiguous (math.add or vectors.add?)

-- Disambiguation
let result = add(1, 2) as I32    -- OK: type annotation selects math.add
let result = add(vec2(1, 2), vec2(3, 4))  -- OK: type inference selects vectors.add
```

### Desugaring Strategy

Overloaded functions generate a match expression on type:

```tao
-- Source
import math { add }
let result = add(x, y)

-- Desugared to Core
match type_of(x, y) {
  (I32, I32) -> math_add_i32(x, y)
  (F64, F64) -> math_add_f64(x, y)
  _ -> type_error("No overload matches")
}
```

**Note**: This is a simplification. Actual implementation uses type-directed desugaring at compile time, not runtime type checks.

---

## Implicit Prelude

### Automatically Imported

Every Tao file implicitly imports:

```tao
import prelude as *
```

This makes the following available (all qualified with `prelude.`):

- `prelude.I32`, `prelude.F64`, `prelude.Bool`, `prelude.String`
- `prelude.Ok`, `prelude.Error` (Result type)
- `prelude.Some`, `prelude.None` (Option type)
- `prelude.(+)`, `prelude.(-)`, `prelude.(*)`, `prelude.(/)` (operators)
- `prelude.(==)`, `prelude.(!=)`, `prelude.(<)`, `prelude.(>)` (comparisons)

### Shadowing Prelude

```tao
-- Can shadow prelude names explicitly
import mylib { Result }  -- Shadows prelude.Result

-- Or use qualified prelude names
let x = prelude.Result.Ok(42)
```

### Prelude Module Structure

```
lib/prelude/
├── types.tao       # I32, F64, Bool, String, Result, Option
├── operators.tao   # +, -, *, /, ==, !=, <, >, etc.
├── result.tao      # Result type and functions
├── option.tao      # Option type and functions
├── string.tao      # String functions
└── prelude.tao     # Re-exports all of the above
```

## Visibility and Privacy

### Public by Default

**Decision**: All names are public by default. Names starting with `_` are private.

```tao
-- Public function (exported)
fn add(x: I32, y: I32) -> I32 { x + y }

-- Private function (not exported, starts with _)
fn _internal_helper(x: I32) -> I32 { x * 2 }

-- Public type
pub type Result(a, b) {
  Ok(a)
  Error(b)
}

-- Private type (starts with _)
type _InternalState {
  State(I32)
}
```

### Import Behavior

```tao
-- Import all public names
import result  -- Gets Result, Ok, Error, map, etc. (not _internal)

-- Import specific names (must be public)
import result { Result, Ok }  -- OK

import result { _InternalState }  -- Error: cannot import private name
```

### Rationale

**Python-style visibility** chosen over ML-style explicit `pub`:

| Approach | Pros | Cons |
|----------|------|------|
| **Public by default** (Python) | Less boilerplate, obvious private with `_` | Can accidentally export |
| **Private by default** (ML/Rust) | Explicit opt-in for exports | Verbose, mostly all public anyway |

**Decision**: **Public by default** with `_` prefix convention for private names.

---

## Module System

### Module Paths

```tao
-- Relative imports (from current file's directory)
import ./utils
import ../common/helpers
import ../../lib/result

-- Absolute imports (from project root)
import lib/prelude/result
import src/utils/formatting

-- Standard library imports (from lib/ directory)
import prelude/result
import collections/list
import collections/map
```

### Module Resolution

1. **Relative paths** (`.`, `..`) - Resolved from current file's directory
2. **Absolute paths** - Resolved from project root
3. **Standard library** - Resolved from `lib/` directory

### File to Module Mapping

```
project/
├── src/
│   ├── main.tao           → Module: src/main
│   └── utils/
│       ├── format.tao     → Module: src/utils/format
│       └── parse.tao      → Module: src/utils/parse
├── lib/
│   └── prelude/
│       └── result.tao     → Module: lib/prelude/result (or prelude/result)
```

---

## Circular Import Detection

### Direct Cycles

```tao
-- a.tao
import b  -- Error: circular import a → b → a

-- b.tao
import a
```

### Indirect Cycles

```tao
-- a.tao
import b  -- Error: circular import a → b → c → a

-- b.tao
import c

-- c.tao
import a
```

### Detection Algorithm

1. Maintain import stack during resolution
2. When importing module M, check if M is in current stack
3. If yes, report circular import with full cycle path
4. If no, push M to stack and continue

---

## Import Desugaring

### To Core FFI

```tao
-- Tao source
import result { Ok, Error }

fn test() {
  Ok(42)
}

-- Desugared to Core
-- (Import becomes FFI function references)
let result_ok = ffi("prelude.result", "Ok")
let result_error = ffi("prelude.result", "Error")

fn test() {
  result_ok(42)
}
```

### Qualified Name Resolution

```tao
-- Tao source
import result as res

fn test() {
  res.Ok(42)
}

-- Desugared to Core
fn test() {
  -- Qualified lookup resolved at compile time
  prelude_result_Ok(42)
}
```

---

## Design Decisions

### 1. Wildcard Import Semantics

**Decision**: `import module as *` makes module name available, not contents.

**Alternatives Considered**:

| Option | Pros | Cons |
|--------|------|------|
| `import module as *` → `module.*` | No name collisions | More verbose usage |
| `import module as *` → all unqualified | Concise usage | Name collision risk |
| `import module.*` → all unqualified | Explicit about wildcard | Still has collision risk |

**Rationale**: Name collisions are a major source of bugs. Explicit is better than implicit.

### 2. Overloading Resolution

**Decision**: Type-directed resolution at compile time, not runtime dispatch.

**Alternatives Considered**:

| Option | Pros | Cons |
|--------|------|------|
| Compile-time resolution | Zero runtime cost, clear errors | Requires type annotations |
| Runtime dispatch | More flexible, Duck typing | Runtime cost, late errors |
| Type classes (Haskell) | Powerful, extensible | Complex, steep learning curve |

**Rationale**: Tao prioritizes performance and clarity. Compile-time resolution provides both.

### 3. Implicit Prelude

**Decision**: Prelude is imported as `prelude.*`, not unqualified names.

**Alternatives Considered**:

| Option | Pros | Cons |
|--------|------|------|
| `import prelude as *` → `prelude.*` | No collisions, explicit | More typing |
| `import prelude` → unqualified | Concise | Collision risk |
| No implicit prelude | Fully explicit | Verbose, boilerplate |

**Rationale**: Implicit prelude is convenient for beginners. Qualified access prevents collisions.

### 4. Import Order Matters

**Decision**: Later imports shadow earlier imports.

**Alternatives Considered**:

| Option | Pros | Cons |
|--------|------|------|
| Order matters (current) | Predictable, simple | Order-dependent |
| Error on duplicates | Catches mistakes early | More restrictive |
| Merge imports | Flexible | Ambiguous resolution |

**Rationale**: Shadowing is predictable and matches most languages.

---

## Known Issues

### 1. Import Performance

**Issue**: Resolving imports at compile time requires loading and parsing all imported modules.

**Impact**: Large projects with many imports may have slow compile times.

**Mitigation**:
- Module caching (parse once, reuse)
- Incremental compilation (only reparse changed modules)
- Import graph analysis (parallel parsing)

### 2. Overload Ambiguity

**Issue**: Some overload resolutions may be ambiguous without explicit annotations.

**Example**:
```tao
import math { add }
let result = add(x, y)  -- Ambiguous if x, y are polymorphic
```

**Mitigation**:
- Require type annotations in ambiguous cases
- Provide better error messages with suggested disambiguations

### 3. Circular Dependencies

**Issue**: Circular imports are a compile error, but may be hard to refactor.

**Mitigation**:
- Provide clear error messages with full cycle path
- Suggest refactoring strategies (extract common module, use interfaces)

---

## Testing Strategy

### Unit Tests

- Import parsing (all syntax variations)
- Name resolution (shadowing, qualification)
- Overload resolution (type-directed selection)
- Circular import detection

### Integration Tests

- Multi-module projects
- Prelude shadowing
- Import + overload interaction
- Import + test system interaction

### Test Files

```
test/tao/
├── imports/
│   ├── basic_import_test.tao
│   ├── alias_import_test.tao
│   ├── selective_import_test.tao
│   ├── wildcard_import_test.tao
│   ├── shadowing_test.tao
│   ├── circular_import_test.tao (should fail)
│   └── overload_import_test.tao
└── prelude_test.tao  -- Tests prelude module itself
```

---

## Future Work

### Phase 1: Basic Import System

- [ ] Import syntax parsing
- [ ] Name resolution (unqualified)
- [ ] Qualified name lookup
- [ ] Import validation (no circular imports)

### Phase 2: Advanced Features

- [ ] Selective imports with aliases
- [ ] Wildcard imports (`as *`)
- [ ] Import shadowing warnings
- [ ] Implicit prelude

### Phase 3: Overloading Integration

- [ ] Overload-aware name resolution
- [ ] Type-directed desugaring
- [ ] Operator overloading imports
- [ ] Better ambiguity errors

### Phase 4: Performance

- [ ] Module caching
- [ ] Incremental compilation
- [ ] Parallel import resolution

---

## Open Questions

### 1. Import Path Separator

**Decision**: ✅ **Slash-separated** (`import math/trigonometry`)

**Rationale**: Matches filesystem structure, familiar to users.

```tao
-- Filesystem:
lib/prelude/result.tao

-- Import:
import prelude/result
```

### 2. Duplicate Import Behavior

**Decision**: ✅ **Warning** (does not affect correctness)

```tao
import result { Ok }
import result { Ok }  -- Warning: Ok already imported from result

import result { Ok }
import option { Ok }  -- Error: Ok imported from multiple modules
```

**Rationale**: Duplicate imports from same module are redundant but harmless. Duplicates from different modules are ambiguous and should error.

### 3. Module Visibility

**Decision**: ✅ **Public by default** (Python-style)

- Names starting with `_` are private
- All other names are public
- No explicit `pub` keyword needed

```tao
fn public_function() { ... }      -- Exported
fn _private_function() { ... }    -- Not exported
```

### 4. Operator Imports

**Decision**: ✅ **Yes, operators are importable functions**

Operators are functions with special names and precedence:

```tao
-- Definition
fn (+)(x: I32, y: I32) -> I32 { ... }

-- Import
import math { (+), (-), (*) }

-- Usage
let result = 1 + 2  -- Uses imported (+)
```

**Rationale**: Operators are just functions with special syntax. No need for separate import rules.

---

## Change Log

| Date | Change | Status |
|------|--------|--------|
| March 14, 2026 | Initial plan created | 📋 Planned |
| March 14, 2026 | Added import syntax specification | 📋 Planned |
| March 14, 2026 | Added name resolution algorithm | 📋 Planned |
| March 14, 2026 | Added overloading support design | 📋 Planned |
| March 14, 2026 | Added implicit prelude specification | 📋 Planned |
| March 14, 2026 | Added design decisions with alternatives | 📋 Planned |
| March 14, 2026 | **Updated**: Type imports include constructors automatically | 📋 Planned |
| March 14, 2026 | **Updated**: Directory imports auto-import all files (except `_*.tao`) | 📋 Planned |
| March 14, 2026 | **Updated**: Removed index.tao requirement (no tribal knowledge) | 📋 Planned |
| March 14, 2026 | **Updated**: Intra-directory visibility requires explicit imports | 📋 Planned |
| March 14, 2026 | **Updated**: Prelude self-imports are no-ops | 📋 Planned |
| March 14, 2026 | **Resolved**: Slash-separated paths (matches filesystem) | ✅ Decided |
| March 14, 2026 | **Resolved**: Duplicate imports are warnings | ✅ Decided |
| March 14, 2026 | **Resolved**: Public by default, `_` prefix = private | ✅ Decided |
| March 14, 2026 | **Resolved**: Operators are importable functions | ✅ Decided |

---

## Review Checklist

Before implementing, review:

- [ ] Import syntax covers all use cases
- [ ] Name resolution is unambiguous
- [ ] Overloading integration is sound
- [ ] Prelude design is practical
- [ ] Error messages are helpful
- [ ] Performance considerations addressed
- [ ] Testing strategy is comprehensive

---

## Related Documents

- **[Tao Overview](./01-overview.md)** - Language overview
- **[Test System](./11-test-system.md)** - Uses imports for prelude tests
- **[Core Syntax](../core/02-syntax.md)** - FFI target for imports
- **[Lessons Learned](../lessons-learned.md)** - Implementation insights
