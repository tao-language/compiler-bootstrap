# Import System Design

## Design Philosophy

1. **Everything is a let binding** — Imports desugar to `let` bindings
2. **No runtime overhead** — Imports are resolved at compile time only
3. **Circular import detection** — Detected at compile time before any evaluation
4. **Selective and wildcard imports** — Both supported at the syntax level
5. **Type and constructor imports** — Types and their constructors can be imported separately

## Import Syntax

```tao
// Wildcard import: all public names
import std/io *

// Selective import
import std/math { sin, cos, tan as tangent }

// Type import (imports the type and its constructors)
import data/maybe { Option, Some, None }

// Relative import
import ./utils { helper_function }

// aliased import
import std/io as io
```

## Import Resolution Flow

```
┌─────────────────────────────────────────────────────┐
│                 IMPORT RESOLUTION                    │
├─────────────────────────────────────────────────────┤
│                                                     │
│  1. Parse import statement → ImportItem AST         │
│                                                     │
│  2. Resolve path → File system lookup               │
│     - Absolute: /std/io.tao                         │
│     - Relative: ./utils.tao                         │
│     - Module: std/io (from library paths)           │
│                                                     │
│  3. Load module → Parse → Desugar → Type check      │
│                                                     │
│  4. Extract public names → Export table             │
│     - fn add(a, b) → add                           │
│     - type Option → Option, Some, None             │
│     - let x = 42 → x                                │
│                                                     │
│  5. Desugar import → let binding                    │
│     import std/io * → let io = @std.io             │
│     import std/math { sin } → let sin = @math.sin  │
│                                                     │
└─────────────────────────────────────────────────────┘
```

## Type Definitions

### Import AST

```gleam
/// An import item in a Tao module
pub type ImportItem {
  /// import path * (all public names)
  ImportAll(path: String, span: Span)
  
  /// import path { name1, name2 as n2 }
  ImportSelective(
    path: String,
    names: List(ImportName),
    span: Span,
  )
}

/// A single imported name with optional alias
pub type ImportName {
  ImportName(
    name: String,     // Original name
    alias: Option(String),  // Optional alias
    span: Span,
  )
}
```

### Module Metadata

```gleam
/// A compiled module with its public interface
pub type Module {
  Module(
    path: String,               // File path
    name: String,               // Module name (e.g., "std.io")
    body: Term,                 // Desugared Core term
    public_names: List(String), // Exported names
    public_types: List(#(String, List(String))), // type → [constructors]
    dependencies: List(String), // Imported module paths
    span: Span,
  )
}

/// Global context for module resolution
pub type GlobalContext {
  GlobalContext(
    modules: List(Module),      // Loaded modules (path → Module)
    library_paths: List(String), // Directories to search for imports
    step_limit: Int,            // Evaluation step limit
  )
}
```

### Import Resolution Result

```gleam
/// Result of resolving an import
pub type ImportResult {
  /// Import resolved successfully
  Success(
    module: Module,
    bindings: List(#(String, Term)),  // name → resolved term
  )
  
  /// Import failed with errors
  Error(ImportError)
}

pub type ImportError {
  ModuleNotFound(path: String, span: Span)
  CircularImport(from: String, to: String, span: Span)
  ParseError(path: String, errors: List(ParseError))
  TypeError(path: String, errors: List(TypeError))
  NameNotFound(name: String, available: List(String), span: Span)
}
```

## Desugaring: Import → Core

### Wildcard Import

```tao
// Tao source
import std/io *
```

```gleam
// Desugars to Core
let io = @std_io  // Module reference (desugarer creates this)
// All public names from std/io are now available
```

### Selective Import

```tao
// Tao source
import std/math { sin, cos, tan as tangent }
```

```gleam
// Desugars to Core
let sin = @std_math.sin
let cos = @std_math.cos
let tangent = @std_math.tan
```

### Type Import

```tao
// Tao source
import data/maybe { Option, Some, None }
```

```gleam
// Desugars to Core
let Option = @data_maybe.Option        // Type (universe)
let Some = @data_maybe.Some            // Constructor
let None = @data_maybe.None            // Constructor
```

The constructor `Some` and `None` are resolved through the `CtrEnv` during type checking. The type checker looks up `Some` and `None` in the constructor environment, which was built from the imported module's type declarations.

## Module Loading Pipeline

```gleam
/// Load and compile a module (recursively loading dependencies)
pub fn load_module(path: String, ctx: GlobalContext) -> Result(Module, ImportError) {
  // Check if already loaded
  case list.find(ctx.modules, fn(m) -> m.path == path) {
    Ok(module) -> Ok(module)
    Error(_) -> {
      // Check for circular imports
      case is_circular(path, ctx.loaded_modules) {
        True -> Error(CircularImport(path, "current", ctx.current_span))
        False -> {
          // Parse
          let source = read_file(path)
          let parse_result = parse(source, path)
          
          // Desugar
          let desugar_result = desugar(parse_result.ast, ctx)
          
          // Type check
          let type_result = type_check(desugar_result.term, ctx)
          
          // Build module
          let module = build_module(path, parse_result.ast, desugar_result.term, type_result)
          
          // Add to context
          Ok(update_context(ctx, module))
        }
      }
    }
  }
}
```

## Public Name Resolution

### How Names Become Public

```gleam
/// Extract public names from a module body
pub fn get_public_names(stmts: List(Stmt)) -> List(String) {
  stmts
  |> list.filter(fn(stmt) -> is_public(stmt))
  |> list.map(fn(stmt) -> get_name(stmt))
  |> list.append(list.map(get_type_constructors(stmts)))
}

/// Check if a statement is public (starts with underscore or is a fn/type)
pub fn is_public(stmt: Stmt) -> Bool {
  case stmt {
    StmtLet(name, _, _, _, _) -> !string.starts_with(name, "_")
    StmtFn(name, _, _, _, _, _) -> !string.starts_with(name, "_")
    StmtType(name, _, _, _, _) -> !string.starts_with(name, "_")
    _ -> False
  }
}

/// Get type constructors for a type declaration
pub fn get_type_constructors(stmts: List(Stmt)) -> List(#(String, List(String))) {
  stmts
  |> list.filter(fn(stmt) -> case stmt { StmtType(_, _, ctors, _) -> True; _ -> False })
  |> list.map(fn(stmt) -> {
    case stmt {
      StmtType(name, _, constructors, _) ->
        #(name, list.map(constructors, fn(c) -> c.name))
      _ -> panic
    }
  })
}
```

## Test API

The test framework uses the import system:

```tao
// Tao source
import std/test { test, expect }
import my_module { add }

test "addition" {
  expect(1 + 1 == 2)
}

test "imported function" {
  expect(add(1, 2) == 3)
}
```

```gleam
// Desugars to Core
let test = @std_test.test
let expect = @std_test.expect
let add = @my_module.add

test("addition", expect(eq(+(1, 2), 2)))
test("imported function", expect(add(1, 2) == 3))
```

## Circular Import Detection

```gleam
/// Detect circular imports by tracking loading order
pub fn is_circular(current: String, loaded: List(String)) -> Bool {
  loaded |> list.contains(current)
}

/// Track module loading order
pub fn update_context(ctx: GlobalContext, module: Module) -> GlobalContext {
  let updated_modules = [module, ..ctx.modules]
  let updated_loaded = list.append(module.dependencies, ctx.loaded_modules)
  
  ctx |> {
    .modules = updated_modules
    .loaded_modules = updated_loaded
  }
}
```

## Example: Complete Import Flow

```tao
// main.tao
import std/io { println }
import data/list { map, foldl }
import utils { helper }

fn main() {
  let nums = [1, 2, 3]
  let doubled = map(\x -> x * 2, nums)
  println(foldl(\(acc, x) -> acc + x, 0, doubled))
}
```

```gleam
// Desugars to Core
let io = @std_io
let println = io.println

let list = @data_list
let map = list.map
let foldl = list.foldl

let utils = @utils
let helper = utils.helper

let nums = [1, 2, 3]
let doubled = map(\x -> x * 2, nums)
println(foldl(\(acc, x) -> acc + x, 0, doubled))
```

All imports are resolved at compile time. The desugarer looks up each imported name in the appropriate module's public interface, creating the appropriate Core term references.
