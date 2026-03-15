# Tao Language Implementation Plans

> **Goal**: Simple, pragmatic functional language with dependent types—TypeScript-like syntax without the complexity
> **Status**: ⏳ **In Progress** - Stmt system and import integration in progress
> **Date**: March 14, 2026 (Updated: Stmt design finalized)

---

## Status

### What's Working

- ✅ Core language (type checking, normalization, evaluation)
- ✅ Syntax library (grammar DSL, lexer, formatter)
- ✅ Tao expression parsing (arithmetic, variables, overloaded functions)
- ✅ Test system (parser, filter, runner, CLI integration)
- ✅ Import system design (AST types, resolution, directory imports, prelude handling)
- ✅ Stmt type implemented (all statement variants)
- ✅ Module type updated (body: List(Stmt))
- ✅ Conversion layer (syntax.Expr → ast.Expr)
- ✅ Parser for Stmt (parse_module function)
- ✅ Global context module (tracks all modules as @path records)
- ✅ Desugarer skeleton (import desugaring, module → DoBlock)
- ✅ CoreTerm → core/core.Term conversion
- ✅ Full expression desugaring (variables, literals, lambdas, applications, operators, records, tuples, lists, blocks, let expressions)
- ✅ If expression desugaring (conditional evaluation)
- ✅ Match expression desugaring with full pattern support:
  - Variable patterns (PVar)
  - Wildcard patterns (PAny)
  - Literal patterns (PLit)
  - Constructor patterns (PCtr)
  - Record patterns (PRecord)
  - Tuple patterns (PTuple)
  - List patterns (PList)
  - Or patterns (POr)
  - As patterns (PAs)
  - Guard expressions
- ✅ Optional chaining desugaring
- ✅ Record update desugaring
- ✅ Variable scoping with De Bruijn indices (bound vs. free variables)
- ✅ Lambda scoping (parameters added to scope for body)
- ✅ Control flow statements (For, While, Loop, Break, Continue, Return, Yield)
- **432 tests passing**

### What's Pending

- ⏳ Full import desugaring integration with CLI
- ⏳ Comprehensive desugarer tests
- ⏳ Proper fixpoint-based recursion for loops (currently simplified)
- ⏳ Multi-clause match chaining (currently uses first matching clause)

### Related

- See **[01-overview.md](./01-overview.md)** for Tao language overview
- See **[12-import-system.md](./12-import-system.md)** for import system specification
- See **[13-stmt-system.md](./13-stmt-system.md)** for Stmt design **(NEW)**
- See **[../core/01-overview.md](../core/01-overview.md)** for Core language

---

## Implementation Phases

| Phase | Component | Status | Tests |
|-------|-----------|--------|-------|
| **1-3** | Test System | ✅ Complete | 41 tests |
| **4-5** | Import AST + Resolution | ✅ Complete | Pending |
| **6** | Stmt System + Desugaring | ⏳ In Progress | Pending |
| **7** | Import System Tests | 📋 Planned | Pending |

---

## Key Design Decisions

### 1. Modules as DoBlocks

**Decision**: A module compiles to a `DoBlock` that returns a `Record` of public names.

```tao
-- math/trig.tao
fn sin(x) { ... }
fn cos(x) { ... }
fn _private() { ... }  -- Not exported

-- Compiles to Core:
DoBlock(
  [Let("sin", Lam(...)), Let("cos", Lam(...)), Let("_private", Lam(...))],
  Rcd([#("sin", Var("sin")), #("cos", Var("cos"))])
)
```

**Rationale**: Uniform treatment of modules and blocks, simple desugaring.

### 2. Imports as Let Aliases

**Decision**: All imports desugar to `let` bindings.

```tao
import math/trig as trig {sin, cos}

-- Desugars to:
let trig = @math_trig
let sin = trig.sin
let cos = trig.cos
```

**Rationale**: No special import handling, Core type checker finds all errors.

### 3. Statements Everywhere

**Decision**: Module body is `List(Stmt)`, not separate imports + declarations.

```gleam
pub type Module {
  Module(path: String, body: List(Stmt))
}

pub type Stmt {
  Let(...), Fn(...), Import(...),  -- Definitions
  For(...), While(...), Loop(...), Break, Continue,  -- Control flow
  Return(...), Yield(...),  -- Flow control
  Expr(...), Bind(...), Mut(...)  -- Expressions
}
```

**Rationale**: Uniform, flexible, future-proof.

### 4. Error Recovery

**Decision**: Never stop compilation on errors. Use placeholders (`VErr`, `Err(...)`).

| Error | Action |
|-------|--------|
| Missing module | `Err("Module not found")` placeholder |
| Name not exported | `Err("Name not found")` placeholder |
| Circular import | No special handling - Core detects |
| Duplicate import | Let shadowing (no-op) |

**Rationale**: LSP server must be robust, continue checking after errors.

---

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│  Phase 1: Parse All Modules                                 │
│  - Each .tao file → Module {path, body: List(Stmt)}         │
│  - Store: Map<FilePath, Module>                             │
└─────────────────────────────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────┐
│  Phase 2: Create Global Placeholders                        │
│  - For each module: ModuleRef {path, public_names, None}    │
│  - GlobalCtx {modules: Map<Path, ModuleRef>}                │
│  - No cycle detection needed!                               │
└─────────────────────────────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────┐
│  Phase 3: Desugar Each Module                               │
│  - Inject implicit prelude (import prelude as *)            │
│  - Stmt → Core (Import → let, Fn → let Lam, etc.)           │
│  - Module → DoBlock([...stmts], Rcd(public_names))          │
└─────────────────────────────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────┐
│  Phase 4: Core Type Check + Evaluate                        │
│  - All modules are Core Exprs                               │
│  - Core resolves circular references                        │
│  - Core finds missing modules, wrong types, etc.            │
└─────────────────────────────────────────────────────────────┘
```

---

## Change Log

| Date | Change | Status |
|------|--------|--------|
| March 14, 2026 | Test system complete (parser, filter, runner, CLI) | ✅ Complete |
| March 14, 2026 | Import AST types (import_ast.gleam) | ✅ Complete |
| March 14, 2026 | Import resolution (import_resolver.gleam) | ✅ Complete |
| March 14, 2026 | Directory imports (auto-import public files) | ✅ Complete |
| March 14, 2026 | Prelude self-imports (no-op for prelude files) | ✅ Complete |
| March 14, 2026 | Stmt system design finalized | ✅ Designed |
| March 14, 2026 | Stmt type implemented (all variants) | ✅ Complete |
| March 14, 2026 | Module type updated (body: List(Stmt)) | ✅ Complete |
| March 14, 2026 | Conversion layer (syntax.Expr → ast.Expr) | ✅ Complete |
| March 14, 2026 | Parser for Stmt (parse_module function) | ✅ Complete |
| March 14, 2026 | Global context module (global_context.gleam) | ✅ Complete |
| March 14, 2026 | Desugarer skeleton (desugar.gleam) | ✅ Skeleton |
| March 14, 2026 | CoreTerm → Term conversion | ✅ Complete |
| March 14, 2026 | AST unification plan (remove duplicate Expr) | 📋 Planned |
| March 14, 2026 | Import → let desugaring (full implementation) | 📋 Planned |

---

## Open Questions

### 1. Fn as Stmt vs Separate Declaration

**Option A**: `Stmt.Fn(name, params, body)`
**Option B**: `Declaration.Fn(...)` separate from `Stmt`

**Decision**: **Option A** - more natural syntax, easier pattern matching.

### 2. For Loop Body Type

**Option A**: `For(pattern, collection, body: List(Stmt))`
**Option B**: `For(pattern, collection, body: Expr)`

**Decision**: **Option A** - consistent with module body, allows multiple statements.

### 3. Mut Statement

**Option A**: `Stmt.Mut(target: Expr, value: Expr)` explicit
**Option B**: Desugar directly to `Set(ref, value)`

**Decision**: **Option A** - explicit in AST, easier to analyze.

### 4. Imports Inside Functions

**Question**: Should `import` be allowed inside function bodies?

```tao
fn foo() {
  import math/trig
  trig.sin(1.0)
}
```

**Decision**: **Yes** - no technical reason to forbid, desugars to local let.

---

## Implementation Plan

| Step | Task | Files | Status |
|------|------|-------|--------|
| **6.0** | Add Stmt type | `ast.gleam` | ✅ Complete |
| **6.1** | Add Pattern type | `ast.gleam` | ✅ Already existed |
| **6.2** | Update Module type | `ast.gleam` | ✅ Complete |
| **6.3** | Add conversion layer | `syntax.gleam` | ✅ Complete |
| **6.4** | Parser for Stmt | `syntax.gleam` | ✅ Complete |
| **6.5** | Global context | `global_context.gleam` | ✅ Complete |
| **6.6** | Desugar Stmt → Core | `desugar.gleam` | ✅ Skeleton |
| **6.7** | Module → DoBlock | `desugar.gleam` | ✅ Skeleton |

---

## Related Documents

- **[01-overview.md](./01-overview.md)** - Tao language overview
- **[02-syntax.md](./02-syntax.md)** - Tao syntax specification
- **[03-desugaring.md](./03-desugaring.md)** - Desugaring rules
- **[10-overloading-design.md](./10-overloading-design.md)** - Overloading design
- **[11-test-system.md](./11-test-system.md)** - Test system specification
- **[12-import-system.md](./12-import-system.md)** - Import system specification
- **[13-stmt-system.md](./13-stmt-system.md)** - Stmt system design **(NEW)**
