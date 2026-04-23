# Import System Specification

> **Goal**: Enable modular code organization with automatic prelude import and explicit module imports
> **Status**: ⏳ **In Progress** - Design complete, implementation starting
> **Date**: March 2026

---

## Status

### What's Working

- ✅ Core language parsing and type checking
- ✅ Tao desugaring to Core
- ✅ File-based compilation (single file)
- ✅ **424 tests passing**

### What's Pending

- 📋 Import statement parsing (Tao syntax)
- 📋 Module resolution (file system lookup)
- 📋 Multi-file compilation
- 📋 Automatic prelude import
- 📋 Import cycle detection
- 📋 Re-export syntax

### Related

- See **[../stdlib/01-overview.md](../stdlib/01-overview.md)** for standard library overview
- See **[../tao/10-overloading.md](../tao/10-overloading.md)** for Tao overloading
- See **[../core/01-overview.md](../core/01-overview.md)** for Core language

---

## Core Principle

**Simple and Explicit**: Import system should be simple enough to understand in 5 minutes, explicit about dependencies, and support automatic prelude import for convenience.

### Design Goals

1. **Minimal syntax** - One import form, easy to parse
2. **File-based modules** - Each `.tao` or `.core.tao` file is a module
3. **Automatic prelude** - Prelude always available, no import needed
4. **Explicit imports** - All other modules must be explicitly imported
5. **No cycles** - Import cycles detected at compile time

---

## Architecture

### Module Structure

```
lib/
├── prelude/
│   ├── prelude.core.tao    # Auto-imported
│   ├── bool.core.tao
│   ├── option.core.tao
│   └── result.core.tao
├── math/
│   ├── int.core.tao
│   └── float.core.tao
└── collections/
    ├── list.core.tao
    └── vector.core.tao

src/
├── main.tao                # User code
└── utils.core.tao
```

### Import Syntax (Tao)

```tao
// Import entire module
import math/int

// Import specific items
import collections/list.{List, cons, nil, map}

// Import with alias
import collections/vector as Vec

// Import relative path
import ../utils/core
```

### Import Syntax (Core)

```core
// Core uses simpler syntax (lower-level)
%import "math/int"
%import "collections/list" { List, cons, nil }
```

### Compilation Flow

```
┌─────────────┐
│  main.tao   │
└──────┬──────┘
       │ Parse
       ▼
┌─────────────┐
│ Tao AST     │
│ + imports   │
└──────┬──────┘
       │ Resolve imports
       ▼
┌─────────────┐
│ Module Graph│
└──────┬──────┘
       │ Check cycles
       ▼
┌─────────────┐
│ Desugar     │
│ (Tao→Core)  │
└──────┬──────┘
       │ Inline imports
       ▼
┌─────────────┐
│ Core AST    │
│ (merged)    │
└──────┬──────┘
       │ Type check
       ▼
┌─────────────┐
│ Result      │
└─────────────┘
```

---

## Design Principles

### 1. **Prelude Auto-Import**

Prelude is always available - no import statement needed:

```tao
// This works without any import
let x: Option(I32) = Some(42)
let y: Result(I32, String) = Ok(100)
```

**Implementation**: Prelude constructors registered in initial Core state.

### 2. **File = Module**

Each file is a module. Module path = file path relative to `lib/` or project root:

```
lib/math/int.core.tao  →  import math/int
src/utils.core.tao     →  import utils (from src/)
```

### 3. **Import = Copy Definitions**

Imports copy definitions into current scope (no separate namespace):

```tao
import math/int

// int.add is now available as add
let x = add(1, 2)  // Not int.add(1, 2)
```

**Rationale**: Simpler than qualified names, matches Tao's flat namespace.

### 4. **No Implicit Exports**

All top-level definitions are exported by default:

```tao
// lib/math/int.core.tao
%let add = a -> b -> a + b in  // Exported
%let internal = 42 in          // Also exported (no private yet)
add  // Module result
```

**Future**: Add `private` keyword for internal definitions.

---

## Implementation Plan

### Phase 1: Automatic Prelude Import

**Goal**: Prelude constructors available without import.

#### Step 1.1: Register Prelude Constructors

Modify `src/core/core.gleam` `initial_state()`:

```gleam
pub fn initial_state() -> State {
  State(
    ctx: [],
    ffi: [
      #("add", Builtin(add_impl, [])),
      // ... other builtins
    ],
    ctrs: [
      // Bool
      #("True", CtrDef("True", [], [], Typ(0), [], Span("", 0, 0, 0, 0))),
      #("False", CtrDef("False", [], [], Typ(0), [], Span("", 0, 0, 0, 0))),
      // Option
      #("Some", CtrDef("Some", [CtrParam("a", Var(0))], [], Pi([], "a", Typ(0), Typ(0)), [], Span("", 0, 0, 0, 0))),
      #("None", CtrDef("None", [], [CtrParam("a", Var(0))], Pi([], "a", Typ(0), Typ(0)), [], Span("", 0, 0, 0, 0))),
      // Result
      #("Ok", CtrDef("Ok", [CtrParam("a", Var(0)), CtrParam("e", Var(1))], [], Pi([], "e", Pi([], "a", Typ(0), Typ(0)), Typ(0)), [], Span("", 0, 0, 0, 0))),
      #("Err", CtrDef("Err", [CtrParam("a", Var(0)), CtrParam("e", Var(1))], [], Pi([], "e", Pi([], "a", Typ(0), Typ(0)), Typ(0)), [], Span("", 0, 0, 0, 0))),
      // Ordering
      #("LT", CtrDef("LT", [], [], Typ(0), [], Span("", 0, 0, 0, 0))),
      #("EQ", CtrDef("EQ", [], [], Typ(0), [], Span("", 0, 0, 0, 0))),
      #("GT", CtrDef("GT", [], [], Typ(0), [], Span("", 0, 0, 0, 0))),
    ],
    // ... rest of state
  )
}
```

#### Step 1.2: Update CLI

Modify `src/compiler_bootstrap.gleam` to always use prelude-enabled initial state.

**Status**: 📋 **Pending**

---

### Phase 2: Import Statement Parsing

**Goal**: Parse import statements in Tao.

#### Step 2.1: Extend Tao AST

Add import to `src/tao/ast.gleam`:

```gleam
pub type MvpExpr {
  // ... existing
  MvpImport(module: String, items: List(String), alias: Option(String), span: Span)
}
```

#### Step 2.2: Extend Tao Grammar

Add import rule to `src/tao/syntax.gleam`:

```gleam
// Import: import path or import path.{items} or import path as alias
rule("Import", [
  seq([
    keyword("import"),
    ref("ModulePath"),
    opt(seq([token("LBrace"), ref("ImportItems"), token("RBrace")])),
    opt(seq([keyword("as"), token("Ident")])),
  ]),
  make_import,
])
```

**Status**: 📋 **Pending**

---

### Phase 3: Module Resolution

**Goal**: Resolve import paths to files.

#### Step 3.1: Module Resolver

Create `src/module/resolver.gleam`:

```gleam
pub fn resolve(import_path: String, current_file: String) -> Result(String, ResolveError) {
  // Search paths:
  // 1. Relative to current file
  // 2. lib/ directory
  // 3. Project root
  
  case string.starts_with(import_path, "../") {
    True -> resolve_relative(current_file, import_path)
    False -> resolve_in_lib(import_path)
  }
}
```

#### Step 3.2: File Loader

Create `src/module/loader.gleam`:

```gleam
pub fn load_module(path: String) -> Result(Module, LoadError) {
  // 1. Read file
  // 2. Parse (Tao or Core)
  // 3. Return AST
}
```

**Status**: 📋 **Pending**

---

### Phase 4: Multi-File Compilation

**Goal**: Compile multiple files with imports.

#### Step 4.1: Module Graph

Create `src/module/graph.gleam`:

```gleam
pub type ModuleGraph {
  ModuleGraph(
    modules: Dict(String, Module),
    imports: Dict(String, List(String)),  // module -> imports
  )
}

pub fn build_graph(files: List(File)) -> Result(ModuleGraph, CycleError) {
  // 1. Parse all files
  // 2. Extract imports
  // 3. Build dependency graph
  // 4. Check for cycles
}
```

#### Step 4.2: Import Inlining

Modify desugarer to inline imports:

```gleam
pub fn desugar_with_imports(
  ast: MvpExpr,
  modules: Dict(String, Module),
) -> Term {
  // 1. Process imports
  // 2. Rename imported definitions
  // 3. Inline into current scope
  // 4. Desugar as normal
}
```

**Status**: 📋 **Pending**

---

## Import Syntax Details

### Module Paths

```tao
// Absolute path (from lib/)
import math/int           // lib/math/int.core.tao
import collections/list   // lib/collections/list.core.tao

// Relative path (from current file)
import ../utils           // Parent directory
import ./helpers          // Same directory

// With extension (optional)
import math/int.core.tao  // Same as math/int
```

### Import Forms

```tao
// Import everything
import math/int

// Import specific items
import collections/list.{List, cons, nil, map}

// Import with alias
import collections/vector as Vec
// Use: Vec.from_list(...)

// Import multiple
import math/int
import math/float
import collections/list.{List, cons}
```

### Name Conflicts

```tao
import math/int
import math/float

// Conflict: both define 'add'
// Solution: later import wins, or use alias

import math/int as Int
import math/float as Float

// Now use: Int.add, Float.add
```

---

## Error Handling

### Import Errors

```tao
// Module not found
import nonexistent/module
// Error: Module 'nonexistent/module' not found
// Searched: lib/nonexistent/module.core.tao, ...

// Cycle detected
// A imports B, B imports A
// Error: Import cycle detected: A -> B -> A
```

### Type Errors

```tao
import math/int

// int.add expects I32, got String
let x = int.add("hello", "world")
// Error: Type mismatch in imported function
```

---

## Testing Strategy

### Unit Tests

```gleam
// test/module/resolver_test.gleam
pub fn resolves_absolute_path_test() {
  resolve("math/int", "src/main.tao")
  |> should.equal(Ok("lib/math/int.core.tao"))
}

pub fn resolves_relative_path_test() {
  resolve("../utils", "src/lib/helper.tao")
  |> should.equal(Ok("src/utils.core.tao"))
}
```

### Integration Tests

```tao
// examples/stdlib/imports_example.tao
import math/int
import collections/list.{cons, nil}

%let xs = cons(1, cons(2, nil)) in
%let sum = int.add(10, 20) in
Rcd([("xs", xs), ("sum", sum)])
```

### Expected Output

```bash
$ gleam run run examples/stdlib/imports_example.tao
✓ Resolving imports...
✓ Loading 2 modules
✓ Type checking...
Rcd([("xs", ...), ("sum", 30)])
```

---

## Alternatives Considered

### Alternative 1: Qualified Imports Only

```tao
import math/int as int
let x = int.add(1, 2)  // Always qualified
```

**Rejected**: Too verbose for common case.

### Alternative 2: Explicit Exports

```tao
// lib/math/int.core.tao
export { add, sub, mul, div }
%let add = ... in
%let internal = ... in  // Not exported
```

**Rejected**: Adds complexity. Defer to future "private" keyword.

### Alternative 3: Namespace Per Module

```tao
import math/int
let x = int.add(1, 2)  // Module name as namespace
```

**Rejected**: Conflicts with Tao's flat namespace design.

---

## Open Questions

1. **Should imports be hoisted?** - Yes, imports always at top level
2. **Can imports be inside functions?** - No, only top-level
3. **Circular imports?** - Detected and rejected at compile time
4. **Dynamic imports?** - Not supported (compile-time only)

---

## Future Work

### Phase 5: Private Definitions

```tao
private %let internal = 42 in  // Not exported
%let public = add(1, 2) in     // Exported
```

### Phase 6: Re-exports

```tao
// lib/collections/core.tao
export list.{List, cons, nil}
export vector.{Vector, empty, push}
```

### Phase 7: Import Groups

```tao
import math/{
  int.{add, sub},
  float.{add, sub},
}
```

---

## Change Log

| Date | Change |
|------|--------|
| March 2026 | Initial specification created |
| March 2026 | Phase 1 (Prelude auto-import) started |
