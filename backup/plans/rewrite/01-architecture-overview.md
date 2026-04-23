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
pub type Term {
  Var(index: Int)
  Hole(id: Int)
  Lam(param: Param, body: Term)
  App(fun: Term, arg: Term)
  Pi(domain: Term, codomain: Term)
  Lit(literal: Literal)
  Ctr(tag: String, arg: Term)
  Match(arg: Term, cases: List(Case))
  // ... other core constructs
}

// Values use De Bruijn LEVELS (semantics)
pub type Value {
  VNeut(head: Head, spine: List(Elim))
  VLam(param: Param, body: Term)       // body still uses indices
  VPi(domain: Value, codomain: Term)
  VLit(literal: Literal)
  VCtr(tag: String, arg: Value)
  // ...
}
```

### Tao AST (High-Level)

```gleam
// High-level syntax (string-based variable names)
pub type Expr {
  Var(name: String)
  Lit(literal: Literal)
  Lambda(params: List(Param), body: Expr)
  Call(fun: Expr, args: List(Expr))
  BinOp(left: Expr, op: BinOp, right: Expr)
  Ctr(name: String, args: List(Expr))
  Match(arg: Expr, cases: List(MatchClause))
  // ... Tao-specific constructs
}

pub type Stmt {
  Let(name: String, value: Expr)
  Fn(name: String, params: List(Param), body: Expr)
  Import(import_item: Import)
  TypeDef(name: String, constructors: List(Constructor))
  // ... block statements
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
