# Rewrite Architecture Overview

## Philosophy

> Simple, clean, maintainable, correct and sound.

This rewrite takes everything learned from the current codebase and applies these principles:

1. **Single source of truth for every concept** — no duplicate type definitions between layers
2. **Language-agnostic core** — Core has zero Tao-specific assumptions
3. **Error resilience everywhere** — every phase accumulates errors and recovers
4. **Declarative grammar** — one grammar definition produces both parser and formatter
5. **Clear pipeline stages** — each stage has explicit input/output types
6. **Tests as examples** — every function has example-based tests

## Directory Structure

```
compiler-bootstrap/
├── src/
│   ├── syntax/                    # Language-agnostic grammar library
│   │   ├── lexer.gleam            # Tokenizer (shared by all languages)
│   │   ├── grammar.gleam          # Parser combinator DSL
│   │   ├── formatter.gleam        # Document algebra + layout algorithm
│   │   ├── error_reporter.gleam   # Parse error diagnostics
│   │   └── span.gleam             # Source location type
│   ├── core/                      # Core language (language-agnostic)
│   │   ├── ast.gleam              # Term, Value, Pattern types
│   │   ├── syntax.gleam           # Core parser + formatter (uses grammar lib)
│   │   ├── infer.gleam            # Bidirectional type inference/checking
│   │   ├── eval.gleam             # Normalization by evaluation
│   │   ├── quote.gleam            # Value → Term
│   │   ├── unify.gleam            # Higher-order unification
│   │   ├── subst.gleam            # Substitution
│   │   ├── generalize.gleam       # Generalization
│   │   ├── exhaustiveness.gleam   # Maranget-style pattern match checking
│   │   ├── error_formatter.gleam  # Type error diagnostics
│   │   ├── state.gleam            # Type checker state
│   │   ├── list_utils.gleam       # List helpers
│   │   └── ast_string.gleam       # Debug stringification
│   ├── tao/                       # Tao high-level language
│   │   ├── ast.gleam              # Tao AST (Stmt, Expr, Pattern)
│   │   ├── syntax.gleam           # Tao parser + formatter (uses grammar lib)
│   │   ├── lexer.gleam            # Tao tokenizer (extends base lexer)
│   │   ├── desugar.gleam          # Expr → Term desugaring
│   │   ├── compiler.gleam         # Multi-file compilation pipeline
│   │   ├── global_context.gleam   # Module resolution
│   │   ├── import_resolver.gleam  # Import module system
│   │   ├── import_ast.gleam       # Import AST helpers
│   │   ├── ffi.gleam              # FFI builtin definitions
│   │   ├── language_config.gleam  # Language configuration (constructors, ops)
│   │   ├── error_reporter.gleam   # Tao-specific error reporting
│   │   ├── test_api.gleam         # Test framework
│   │   ├── test_parser.gleam      # Test annotation parsing
│   │   ├── test_reporter.gleam    # Test output formatting
│   │   └── test_filter.gleam      # Test name matching
│   ├── compiler_bootstrap.gleam   # CLI entry point
│   └── exit_code.gleam            # Exit code management
├── test/
│   ├── syntax/
│   │   ├── lexer_test.gleam       # Tokenizer tests
│   │   ├── grammar_test.gleam     # Parser combinator tests
│   │   ├── formatter_test.gleam   # Document algebra tests
│   │   └── error_reporter_test.gleam  # Parse error diagnostics
│   ├── core/
│   │   ├── ast_test.gleam         # Term/Value types
│   │   ├── syntax_test.gleam      # Core parser/formatter
│   │   ├── infer_test.gleam       # Bidirectional type checking
│   │   ├── eval_test.gleam        # Normalization by evaluation
│   │   ├── quote_test.gleam       # Value → Term
│   │   ├── unify_test.gleam       # Unification
│   │   ├── subst_test.gleam       # Substitution
│   │   ├── generalize_test.gleam  # Generalization
│   │   ├── exhaustiveness_test.gleam  # Pattern match coverage
│   │   ├── error_formatter_test.gleam  # Type error diagnostics
│   │   ├── state_test.gleam       # State management
│   │   └── examples_test.gleam    # End-to-end examples
│   ├── tao/
│   │   ├── ast_test.gleam         # Tao AST types
│   │   ├── syntax_test.gleam      # Tao parser/formatter
│   │   ├── desugar_test.gleam     # Desugaring correctness
│   │   ├── compiler_test.gleam    # Multi-file compilation
│   │   ├── import_test.gleam      # Module import system
│   │   └── examples_test.gleam    # End-to-end examples
│   └── integration/
│       └── e2e_test.gleam         # Full pipeline tests
├── examples/
│   ├── core/
│   │   ├── terms/                 # Core term examples
│   │   │   ├── 01_identity.core.tao
│   │   │   ├── 01_identity.output.txt
│   │   │   └── ...
│   │   └── programs/              # Full Core programs
│   └── tao/
│       ├── modules/               # Tao module examples
│       └── programs/              # Full Tao programs
├── plans/
│   └── rewrite/                   # This directory
│       ├── 01-architecture-overview.md
│       ├── 02-grammar-library.md
│       ├── 03-core-language.md
│       ├── 04-tao-language.md
│       ├── 05-compiler-pipeline.md
│       ├── 06-import-system.md
│       ├── 07-error-handling.md
│       ├── 08-testing-strategy.md
│       ├── 09-desugaring-reference.md
│       ├── 10-operator-overloading.md
│       └── 11-implementation-roadmap.md
├── old/                           # Backup of existing codebase
│   ├── src/
│   ├── test/
│   └── docs/
└── gleam.toml
```

## Layer Dependencies (No Cycles)

```
syntax ──┬──► core
         │
         └──► tao ──► core (imports core types for desugaring)
         
compiler_bootstrap ──► tao ──► core ──► syntax
```

**Key constraint:** Core imports from syntax only (never from tao). Tao imports from both syntax and core. Compiler bootstrap imports from tao and core.

## Type Definitions Overview

### Core AST (Language-Agnostic)

```gleam
// Core terms use De Bruijn INDICES (syntax)
// All terms carry source spans for error reporting.
// Keywords use $ prefix: $fn, $let, $match, $pi, $type, $error, $Int, $Float, $Type
pub type Term {
  Var(index: Int, span: Span)
  Hole(id: Int, span: Span)
  Lam(implicits: List(#(String, Term)), param: #(String, Term), body: Term, span: Span)
  App(fun: Term, arg: Term, span: Span)
  Pi(implicits: List(#(String, Term)), domain: #(String, Term), codomain: Term, span: Span)
  Lit(value: Literal, span: Span)
  Ctr(tag: String, arg: Term, span: Span)
  Match(arg: Term, cases: List(Case), span: Span)
  Ann(term: Term, type_: Term, span: Span)
  Call(name: String, args: List(Term), typed_args: List(#(Term, Term)), return_type: Option(Term), span: Span)
  Rcd(fields: List(#(String, Term)), span: Span)
  Typ(level: Int, span: Span)
  TypeDef(name: String, constructors: List(#(String, Term, Term, Span)), span: Span)
  Err(message: String, span: Span)
}

// Values use De Bruijn LEVELS (semantics)
pub type Value {
  VNeut(head: Head, spine: List(Elim))
  VLam(env: Env, implicits: List(#(String, Value)), param: #(String, Value), body: Term)
  VPi(env: Env, implicits: List(#(String, Value)), domain: #(String, Value), codomain: Value)
  VLit(value: Literal)
  VCtr(tag: String, arg: Value)
  VRcd(fields: List(#(String, Value)))
  VTypeDef(name: String, constructors: List(#(String, Value, Value, Span)))
  VErr
}
```

### Extended Numeric Type System

Core supports a full hierarchy of numeric types:

```
$Int       — wildcard matching ANY integer type ($I8, $I16, $I32, $I64, $U8, $U16, $U32, $U64)
$Float     — wildcard matching ANY float type ($F16, $F32, $F64)
$I8, $I16, $I32, $I64   — signed integers
$U8, $U16, $U32, $U64   — unsigned integers
$F16, $F32, $F64       — floating point
```

Type inference produces specific types (`$I32`), but patterns can match the general `$Int`/`$Float` wildcards.

### Record Type Defaults

Record types can specify default values for fields:

```
${x: $Int, y: $Int = 0}  — type with optional field y defaulting to 0
{x: 1}                   — record literal, missing y filled with default
```

The TypeDef constructor system supports this naturally: record types are just another term that can carry default annotations.

### GADT-Style Type Definitions

Type definitions support Generalized Algebraic Data Types with:
- Type-level constraints in constructor argument patterns
- Computed result types via FFI calls
- Type parameters passed as records

```
gleam
// Vec example from tour:
$let Vec = $fn(args: ${n: $U32, a: $Type}) => $match args {
| {n, a} => $type {
  | #Nil({}) -> #Vec({n: 0, a: a})
  | #Cons({x: a, xs: #Vec({n: m, a: a})}) -> #Vec({n: m, a: a})
  }
}
```

### Advanced Pattern Matching

Core supports 10+ pattern types:

| Pattern | Syntax | Description |
|---------|--------|-------------|
| Wildcard | `_` | Matches anything, no binding |
| Variable | `name` | Matches anything, binds variable |
| Constructor | `#Tag(pattern)` | Matches constructor with inner pattern |
| Alias | `name@pattern` | Matches and binds with alias name |
| Type | `$Type`, `$Type<n>`, `$Type<x>` | Matches type universes |
| Int literal | `42` | Matches integer literals |
| Record | `{x: pattern, y: _}` | Matches record fields |
| Record type | `${x: $Int}` | Matches record type fields |
| Error | `$error` | Matches error terms |
| Unit | `()` | Matches empty records |

### Two-Stage Guards

Guards use a two-stage pattern matching format:

```
| pattern ? expression ~ pass_pattern => body
```

The guard evaluates `expression` (in the scope of bound variables), then tries to match it against `pass_pattern`. If the match succeeds, the case body executes.

```
gleam
$match 42 {
| x ? x ~ 42 => 0   // succeeds: 42 matches 42
| _ => 1
}
```

This allows language-agnostic guards that don't depend on boolean types.

### Implicit Parameters

Lambda and Pi types support implicit type parameters enclosed in angle brackets:

```
$fn<a: $Type>(x: a) => x      // lambda with implicit param
$pi<a: $Type>(a) -> a         // non-dependent pi with implicit param
```

During type inference, implicit parameters are auto-expanded as needed:
- `identity(42)` — type inference fills `<a: $Int>`
- `identity($Int)(42)` — explicit implicit parameter
- `identity($Int)($Int)(42)` — explicit twice (redundant but valid)

### FFI Call Syntax

FFI builtins use `%` prefix and support typed arguments with return types:

```
%i32_add(1: $I32, 2: $I32) -> $I32
%i32_to_f32(1: $I32) -> $F32
```

The Call term carries:
- `name`: builtin function name
- `args`: untyped argument terms
- `typed_args`: paired (term, type) for type checking
- `return_type`: optional expected return type

### Tao AST (High-Level)

Tao desugars to Core using `$`-prefixed syntax. Key desugaring targets:

```gleam
// Tao syntax: fn(x) { x + 1 }
// Core syntax: $fn(x: $Int) => x + 1

// Tao syntax: let x = 42
// Core syntax: $let x: $Int = 42  (followed by implicit body)

// Tao syntax: if cond { a } else { b }
// Core syntax: $match cond { | #True(_) => a | #False(_) => b }

// Tao syntax: for item in list { ... }
// Core syntax: $let _ = foldl(list, init, fn(acc, item) => ...)
```

Tao's high-level AST (string-based variable names) includes:

```gleam
pub type Expr {
  Var(name: String)
  Lit(literal: Literal)
  Lambda(params: List(Param), body: Expr)
  Call(fun: Expr, args: List(Expr))
  BinOp(left: Expr, op: BinOp, right: Expr)
  Ctr(name: String, args: List(Expr))
  Match(arg: Expr, cases: List(MatchClause))
  If(cond: Expr, then: Expr, else_: Expr)
  Ann(term: Expr, typ: TypeAst)
  Record(fields: List(#(String, Expr)))
}

pub type Stmt {
  Let(name: String, value: Expr)
  Fn(name: String, params: List(Param), body: Expr)
  Import(import_item: Import)
  TypeDef(name: String, constructors: List(Constructor))
  For(name: String, collection: Expr, body: Expr)
  While(cond: Expr, body: Expr)
  Expr(Expr)
}
```

## Pipeline Overview

```
Tao Source
    │
    ▼
┌─────────────┐
│ Tao Lexer    │ → List(Token)
└─────────────┘
    │
    ▼
┌─────────────┐
│ Tao Parser   │ → Expr + ParseErrors
│ (grammar DSL)│
└─────────────┘
    │
    ▼
┌─────────────┐
│ Tao Desugar  │ → Term + Errors
└─────────────┘
    │
    ▼
┌─────────────┐
│ Core Parse   │ (for .core.tao files)
│ (grammar DSL)│ → Term + ParseErrors
└─────────────┘
    │
    ▼
┌─────────────┐
│ Type Checker │ → Type + Errors
│ (infer/check)│
└─────────────┘
    │
    ▼
┌─────────────┐
│ Evaluator    │ → Value + Errors
│ (NBE)        │
└─────────────┘
    │
    ▼
┌─────────────┐
│ Quoter       │ → Term (Value back to syntax)
└─────────────┘
    │
    ▼
┌─────────────┐
│ Formatter    │ → String
│ (grammar DSL)│
└─────────────┘
```

## Key Design Decisions

1. **One grammar library, two parser implementations** — Core parser defines its own grammar; Tao parser defines its own grammar. Both use the same `grammar.gleam` combinator API.

2. **One formatter, two formatter implementations** — The document algebra (`formatter.gleam`) is language-agnostic. Each language implements `format_term` and `format_expr` functions that produce `Doc` values. The grammar library extracts precedence/operator info from the grammar to guide formatting.

3. **Core is truly language-agnostic** — No Tao-specific types, no Tao-specific FFI, no Tao-specific configuration. Core knows nothing about Tao.

4. **Tao desugars to Core** — All high-level features (for-loops, while-loops, mutable variables, operators, etc.) are desugared to Core terms before type checking.

5. **Error accumulation** — Each phase returns `(result, errors)` tuples. The compiler pipeline collects all errors and reports them at the end.

6. **Tests as examples** — Every public function has tests that demonstrate correct usage with example inputs/outputs.
