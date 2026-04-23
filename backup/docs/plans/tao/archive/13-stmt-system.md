# Tao Stmt System

> **Goal**: Uniform statement system supporting definitions, control flow, and expressions
> **Status**: 📋 **Planned** - Design complete, implementation pending
> **Date**: March 14, 2026

---

## Status

### What's Working

- ✅ Design finalized
- ✅ Import system integration planned
- ✅ Module → DoBlock translation specified

### What's Pending

- ⏳ Add `Stmt` type to `ast.gleam`
- ⏳ Add `Pattern` type to `ast.gleam`
- ⏳ Update `Module` type to use `List(Stmt)`
- ⏳ Parser for all statement forms
- ⏳ Desugaring to Core

### Related

- See **[00-tao-implementation.md](./00-tao-implementation.md)** for overall status
- See **[12-import-system.md](./12-import-system.md)** for import system
- See **[../core/01-overview.md](../core/01-overview.md)** for Core language

---

## Core Insight

**A module is just a `DoBlock` that returns a `Record` of public names.**

```tao
-- math/trig.tao
import prelude/result
fn sin(x: F64) -> F64 { ... }
fn cos(x: F64) -> F64 { ... }
mut counter = 0
counter += 1

-- Compiles to Core:
DoBlock(
  [
    Let(counter, Ref(MutCell(0))),
    Let(sin, Lam(...)),
    Let(cos, Lam(...)),
  ],
  Rcd([
    #("sin", Var("sin")),
    #("cos", Var("cos")),
    #("counter", Var("counter")),
  ])
)
```

---

## Data Structures

### Module

```gleam
pub type Module {
  Module(
    path: String,
    body: List(Stmt),
    span: Span,
  )
}
```

**Design Decision**: Module body is `List(Stmt)`, not separate imports + declarations.

**Rationale**:
- Uniform: everything is a statement
- Flexible: imports allowed anywhere (inside functions, blocks, etc.)
- Future-proof: easy to add new statement types
- Simpler desugaring: all statements → Core uniformly

---

### Stmt

```gleam
pub type Stmt {
  /// let [mut] x [: Type] = expr
  Let(
    name: String,
    mutable: Bool,
    type_ann: Option(Expr),
    value: Expr,
    span: Span,
  )
  
  /// fn name(params) [: Type] { body }
  Fn(
    name: String,
    params: List(Param),
    return_type: Option(Expr),
    body: Expr,
    span: Span,
  )
  
  /// import path [as alias] {names}
  Import(
    import: Import,
    span: Span,
  )
  
  /// for pattern in collection { body... }
  For(
    pattern: Pattern,
    collection: Expr,
    body: List(Stmt),
    span: Span,
  )
  
  /// while condition { body... }
  While(
    condition: Expr,
    body: List(Stmt),
    span: Span,
  )
  
  /// loop { body... }
  Loop(
    body: List(Stmt),
    span: Span,
  )
  
  /// break
  Break(
    span: Span,
  )
  
  /// continue
  Continue(
    span: Span,
  )
  
  /// return [expr]
  Return(
    value: Option(Expr),
    span: Span,
  )
  
  /// yield expr (for generators/streams)
  Yield(
    value: Expr,
    span: Span,
  )
  
  /// expr (expression statement, result discarded)
  Expr(
    value: Expr,
    span: Span,
  )
  
  /// <- pattern = expr (monadic bind)
  Bind(
    pattern: Pattern,
    value: Expr,
    span: Span,
  )
  
  /// mut target = expr (reassignment, e.g., mut x = 5 or mut x += 1)
  Mut(
    target: Expr,
    value: Expr,
    span: Span,
  )
}
```

### Categories

| Category | Statements | Description |
|----------|------------|-------------|
| **Definitions** | `Let`, `Fn`, `Import` | Bindings and imports |
| **Control Flow** | `For`, `While`, `Loop`, `Break`, `Continue` | Iteration |
| **Flow** | `Return`, `Yield` | Function/generator control |
| **Expressions** | `Expr`, `Bind`, `Mut` | Expression statements |

---

### Param

```gleam
pub type Param {
  Param(
    name: String,
    type_ann: Option(Expr),
    span: Span,
  )
}
```

---

### Pattern

```gleam
pub type Pattern {
  /// _ wildcard
  Any(span: Span)
  
  /// identifier
  Var(name: String, span: Span)
  
  /// literal (42, "hello")
  Lit(value: Literal, span: Span)
  
  /// constructor pattern: Some(x), Ok(y)
  Ctr(name: String, args: List(Pattern), span: Span)
  
  /// record pattern: {x, y}
  Record(fields: List(#(String, Pattern)), span: Span)
  
  /// as pattern: x @ Some(y)
  As(name: String, pattern: Pattern, span: Span)
}
```

---

## Desugaring Rules

### Import → Let

| Tao Import | Core Desugaring |
|------------|-----------------|
| `import math/trig` | `let math_trig = @math_trig` |
| `import math/trig as trig` | `let trig = @math_trig` |
| `import math/trig {sin}` | `let sin = @math_trig.sin` |
| `import math/trig {sin as s}` | `let s = @math_trig.sin` |
| `import math` | `let math = @math` |
| `import math as *` | `let math = @math` + all fields |

**Implementation**:
```gleam
fn desugar_import(import: Import) -> List(CoreTerm) {
  case import {
    Import(path, None, None, _) -> {
      [Let(alias_from_path(path), ModuleRef(path), no_span)]
    }
    Import(path, Some(alias), None, _) -> {
      [Let(alias, ModuleRef(path), no_span)]
    }
    Import(path, None, Some(names), _) -> {
      list.map(names, fn(name) {
        Let(name, Dot(ModuleRef(path), name, no_span), no_span)
      })
    }
    -- etc.
  }
}
```

---

### Fn → Let Lam

```tao
fn add(x: I32, y: I32) -> I32 { x + y }

-- Desugars to:
let add = Lam("x", Lam("y", Add(Var("x"), Var("y"))))
```

---

### Module → DoBlock

```gleam
fn module_to_core(module: Module) -> CoreTerm {
  // Collect public names (not starting with _)
  let public_names = list.filter(module.body, fn(stmt) {
    case stmt {
      Let(name, _, _, _, _) -> !string.starts_with(name, "_")
      Fn(name, _, _, _, _) -> !string.starts_with(name, "_")
      _ -> False
    }
  })
  
  // Desugar all statements
  let core_stmts = list.map(module.body, fn(stmt) {
    desugar_stmt(stmt)
  })
  
  // Build return record
  let return_record = Rcd(
    list.map(public_names, fn(stmt) {
      let name = get_stmt_name(stmt)
      #(name, Var(name, no_span))
    }),
    no_span,
  )
  
  // DoBlock(stmts, return_record)
  DoBlock(core_stmts, return_record, no_span)
}
```

---

### Mut → Set

```tao
mut x = 5
mut x += 1

-- Desugars to:
Set(Var("x"), 5)
Set(Var("x"), Add(Var("x"), 1))
```

---

### Bind → Match

```tao
<- x = maybe_value
<- y = result_value

-- Desugars to:
Match(maybe_value,
  Case(PAs(PAny, "x"), ...),
  Case(PAny, Return(None))  -- Early return on None
)
```

---

## Control Flow Desugaring

### While → Fixpoint

```tao
while cond {
  stmt1
  stmt2
}

-- Desugars to:
Fix("loop",
  If(cond,
    DoBlock([stmt1, stmt2], Var("loop")),
    Rcd([])  -- Return empty record on exit
  )
)
```

### For → Fold

```tao
for x in collection {
  stmt1
  stmt2
}

-- Desugars to:
Fold(collection,
  Lam("acc", Lam("x", DoBlock([stmt1, stmt2], Var("acc")))),
  Rcd([])  -- Initial accumulator
)
```

### Loop → Fixpoint

```tao
loop {
  stmt1
  if done { break }
  stmt2
}

-- Desugars to:
Fix("loop",
  DoBlock([
    stmt1,
    If(done, Return(Rcd([])), DoBlock([stmt2], Var("loop")))
  ])
)
```

---

## Error Handling

| Error | Action |
|-------|--------|
| Missing module | `Err("Module not found")` placeholder |
| Name not exported | `Err("Name not found")` placeholder |
| Circular import | No special handling - Core detects |
| Duplicate import | Let shadowing (no-op) |
| Type error | Core type checker reports |

**Principle**: Never stop compilation. Use placeholders (`VErr`, `Err(...)`) to continue.

---

## Future-Proof Considerations

### 1. Mutable Variables

```tao
let mut x = 5
mut x = 10
mut x += 1
```

Already supported via `Let(mutable: True)` and `Mut` statement.

### 2. Monadic Bind

```tao
fn main() {
  <- x = maybe_value
  <- y = result_value
  return x + y
}
```

Supported via `Bind` statement → `Match` in Core.

### 3. Generators

```tao
fn range(start, end) {
  for i in start..end {
    yield i
  }
}
```

Supported via `Yield` statement → `Stream` in Core.

### 4. Pattern Matching in Let

```tao
let Some(x) = maybe_value
let {x, y} = point
```

Supported via `Pattern` type in `Let` and `Bind`.

---

## Implementation Plan

| Step | Task | Files | Complexity |
|------|------|-------|------------|
| **6.0** | Add `Stmt` type | `ast.gleam` | Medium |
| **6.1** | Add `Pattern` type | `ast.gleam` | Low |
| **6.2** | Update `Module` type | `ast.gleam` | Low |
| **6.3** | Remove duplicate `Expr` | `syntax.gleam` | Medium |
| **6.4** | Parser for `Stmt` | `syntax.gleam` | High |
| **6.5** | Global context | New file | Medium |
| **6.6** | Desugar `Stmt` → Core | `desugar.gleam` | High |
| **6.7** | Module → `DoBlock` | `desugar.gleam` | Medium |

---

## Design Decisions

### 1. Fn as Stmt

**Decision**: `Stmt.Fn(name, params, body)` not separate `Declaration`.

**Rationale**: More natural syntax, easier pattern matching, uniform treatment.

### 2. For Body = List(Stmt)

**Decision**: `For(pattern, collection, body: List(Stmt))` not `Expr`.

**Rationale**: Consistent with module body, allows multiple statements without explicit `do {}`.

### 3. Mut as Explicit Statement

**Decision**: `Stmt.Mut(target: Expr, value: Expr)` explicit in AST.

**Rationale**: Easier to analyze, clear intent in AST.

### 4. Imports Anywhere

**Decision**: Imports allowed inside functions, blocks, etc.

**Rationale**: No technical reason to forbid, desugars to local let.

---

## Testing Strategy

### Unit Tests

- Each statement type parses correctly
- Each statement type desugars correctly
- Pattern matching in `Let` and `Bind`
- Import desugaring (all forms)

### Integration Tests

- Module with mixed statements
- Import chains (A imports B, B imports C)
- Circular imports (should error gracefully)
- Public/private name filtering

### Error Recovery Tests

- Missing module (continue with placeholder)
- Name not exported (continue with placeholder)
- Syntax errors in statements (recover and continue)

---

## Change Log

| Date | Change | Status |
|------|--------|--------|
| March 14, 2026 | Initial design | 📋 Planned |
| March 14, 2026 | Import integration plan | 📋 Planned |
| March 14, 2026 | Control flow desugaring | 📋 Planned |

---

## Related Documents

- **[00-tao-implementation.md](./00-tao-implementation.md)** - Overall implementation plan
- **[12-import-system.md](./12-import-system.md)** - Import system specification
- **[../core/01-overview.md](../core/01-overview.md)** - Core language (DoBlock, Rcd)
