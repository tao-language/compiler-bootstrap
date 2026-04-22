# Compiler Bootstrap — Architecture Guide for AI Agents

## What This Project Is

A Gleam-based compiler toolkit that provides three layered components:

| Layer | Purpose | Key Files |
|-------|---------|-----------|
| **Syntax library** | Grammar DSL, lexer, formatter, error reporter | `src/syntax/` |
| **Core language** | Dependently typed language with bidirectional type checking | `src/core/` |
| **Tao language** | High-level language that desugars to Core | `src/tao/` |

**Entry point:** `src/compiler_bootstrap.gleam` (CLI)

---

## High-Level Architecture

```
User writes .tao or .core.tao files
│
▼
┌─────────────────────────────────────────────┐
│  SYNTAX LIBRARY (language-agnostic)          │
│                                              │
│  grammar.gleam   — Parser combinator DSL     │
│  lexer.gleam     — Tokenizer with spans      │
│  formatter.gleam — Document algebra          │
│  error_reporter  — Source snippets + highlight│
└─────────────────────────────────────────────┘
│
▼
┌─────────────────────────────────────────────┐
│  CORE LANGUAGE                               │
│                                              │
│  Term (syntax, De Bruijn indices)            │
│  → Type check (bidirectional infer/check)    │
│  → Value (semantics, De Bruijn levels)       │
│  → Evaluate → Quote back to syntax           │
│                                              │
│  infer.gleam    — Bidirectional type checker  │
│  eval.gleam     — Normalization by evaluation │
│  quote.gleam    — Evaluate → syntax          │
│  unify.gleam    — Higher-order unification    │
│  exhaustiveness.gleam — Maranget algorithm    │
└─────────────────────────────────────────────┘
│
▼
┌─────────────────────────────────────────────┐
│  TAO LANGUAGE                                │
│                                              │
│  Expr (Tao AST, de Bruijn indices)           │
│  → Desugar to CoreTerm                       │
│  → Type check (reuses core/infer)            │
│  → Evaluate (reuses core/eval)               │
│                                              │
│  desugar.gleam  — Desugaring pass            │
│  import_resolver.gleam — Module resolution   │
│  test_api.gleam — Test framework             │
│  compiler.gleam — Multi-file compilation     │
└─────────────────────────────────────────────┘
```

---

## Three Key Abstractions

### 1. Term (Core Syntax) vs Value (Core Semantics)

These are the two most important concepts in the core language:

- **`Term`** — Raw AST representing what the programmer wrote. Uses De Bruijn **indices** (relative references, e.g., `Var(0)` = "the closest binding above me").
- **`Value`** — Evaluated result. Uses De Bruijn **levels** (absolute references, e.g., `Var(0)` = "the innermost binder").

**Critical rule:** Never pass a `Term` where a `Value` is expected, or vice versa. The type checker and evaluator each have their own types and they are not interchangeable.

### 2. Infer (Synthesis) vs Check (Verification)

Bidirectional type checking uses two modes:

- **`infer`** — Figure out the type of an expression from its shape (top-down, "synthesize").
- **`check`** — Verify an expression has a given type (bottom-up, "verify against").

The type checker accumulates errors in `State.errors` rather than stopping — this is intentional for IDE-like feedback.

### 3. Desugar (Tao → Core) → Type Check → Evaluate → Quote

The Tao pipeline:

1. Parse `.tao` source into `Expr` AST
2. Desugar `Expr` → `Term` (resolve constructors, inline sugar, etc.)
3. Type check `Term` using `core/infer`
4. Evaluate `Term` → `Value` using `core/eval`
5. Quote `Value` back to `Term` using `core/quote`
6. Format `Term` to string using `syntax/formatter`

---

## Directory Structure

```
src/
├── compiler_bootstrap.gleam   # CLI entry point
├── exit_code.gleam            # Non-zero exit on failure
├── syntax/                    # Language-agnostic parser/formatter
│   ├── grammar.gleam          # Parser combinator DSL (grammar definition)
│   ├── lexer.gleam            # Tokenizer with source location
│   ├── formatter.gleam        # Document algebra, line breaking
│   ├── error_reporter.gleam   # Source snippets, diagnostic formatting
│   └── source_snippet.gleam   # Source text helpers
├── core/                      # Core language (dependently typed λ-calculus)
│   ├── ast.gleam              # Term, Value, Literal types
│   ├── syntax.gleam           # Core parser + formatter
│   ├── infer.gleam            # Bidirectional type checking
│   ├── eval.gleam             # Normalization by evaluation
│   ├── quote.gleam            # Value → Term (quote)
│   ├── unify.gleam            # Higher-order unification
│   ├── subst.gleam            # Substitution (force levels to indices)
│   ├── generalize.gleam       # Generalization (quantify holes)
│   ├── exhaustiveness.gleam   # Pattern match coverage (Maranget)
│   ├── error_formatter.gleam  # Diagnostic message formatting
│   ├── state.gleam            # Type-checking state (holes, substitutions)
│   ├── list_utils.gleam       # List helper functions
│   ├── ast_string.gleam       # Term/Value debug stringification
│   ├── color.gleam            # ANSI color codes
│   └── infer_utils.gleam      # Type inference helpers
└── tao/                       # High-level language
    ├── ast.gleam              # Tao AST (Stmt, Expr types)
    ├── syntax.gleam           # Tao parser (generated from grammar.gleam DSL)
    ├── lexer.gleam            # Tao tokenizer
    ├── desugar.gleam          # Expr → Term desugaring
    ├── compiler.gleam         # Multi-file compilation
    ├── global_context.gleam   # Module context management
    ├── import_resolver.gleam  # Import resolution
    ├── import_ast.gleam       # Import AST helpers
    ├── ffi.gleam              # FFI builtin definitions
    ├── language_config.gleam  # Language configuration
    ├── test_api.gleam         # Test execution (single source of truth)
    ├── test_parser.gleam      # Test annotation parsing
    ├── test_reporter.gleam    # Test output formatting
    ├── test_filter.gleam      # Test name matching
    └── test_api.gleam         # Test execution
```

---

## Error Handling Philosophy

**Error recovery is intentional.** The compiler never stops on the first error — it accumulates all issues. This is critical for IDE feedback.

- Errors flow through `State.errors` list, never through exceptions
- Use `with_err` to accumulate errors while continuing evaluation
- `VErr` values in evaluation should propagate, not be swallowed
- Never "fix" error accumulation patterns without understanding the feedback loop

---

## Testing Conventions

- **Framework:** `gleeunit` with `should` assertions
- **Pattern:** Mirror `src/` in `test/` with `_test` suffix
- **Best practices:**
  - One assertion per test
  - Check structural equality, not just success
  - Test error cases, not just happy paths
  - Descriptive test names
  - One assertion per test
  - Check structural equality, not just success

---

## Common Pitfalls

### De Bruijn Indices vs Levels

- **Term (syntax):** De Bruijn **indices** — `Var(0)` = closest binder above
- **Value (semantics):** De Bruijn **levels** — `Var(0)` = innermost binder
- **`subst.force`:** Converts levels → indices (value → term representation)

### Quote Should Never Evaluate

`quote` transforms a `Value` back to a `Term` by re-wrapping evaluated lambdas. It does **not** call `eval`. If `quote` is calling `eval`, something is wrong — this was a critical bug in the past.

### Holes and Unification

- Holes (`Hole(id)`) are untyped placeholders resolved during unification
- The unifier stores bindings in `State.subst`
- Holes with negative IDs are synthesized (infer); positive IDs are verified against (check)

### Exhaustiveness Checking

Uses Maranget's algorithm via `exhaustiveness.gleam`. It's conservative with guards — a match is only non-exhaustive if it can be proven statically.

---

## Key Files to Read Before Making Changes

| When working on... | Read first |
|-------------------|------------|
| Type checking / unification | `src/core/ast.gleam`, `src/core/unify.gleam`, `src/core/infer.gleam` |
| Evaluation / quoting | `src/core/eval.gleam`, `src/core/quote.gleam` |
| Tao desugaring | `src/tao/desugar.gleam` |
| Parsing / grammar | `src/syntax/grammar.gleam`, `src/tao/syntax.gleam` |
| Error reporting | `src/syntax/error_reporter.gleam`, `src/core/error_formatter.gleam` |
| Test framework | `src/tao/test_api.gleam` |
| General principles | `docs/lessons-learned.md` |

---

## Running the Project

```bash
gleam run check path/to/file.core.tao   # Type-check a file
gleam run run path/to/file.core.tao     # Type-check and evaluate
gleam run test                          # Run all tests
gleam run test --list                   # List all tests
fswatch -or src test | xargs -n1 -I{} gleam test  # Continuous testing
```

---

## Dependencies

| Package | Purpose |
|---------|---------|
| `gleam_stdlib` | Standard library |
| `argv` | Command-line argument parsing |
| `simplifile` | File system utilities |
| `gleeunit` | Test framework (dev) |

---

## Recent History (For Context)

| Area | What changed | Why it matters |
|------|-------------|----------------|
| Quote re-evaluation | `quote` was accidentally calling `eval` on lambda bodies | Quote must not evaluate — causes exponential blowup |
| Match environment | Case bodies were converted with empty env | Caused all variables to resolve to `Var(0)` |
| Prelude loading | Removed hardcoded prelude, now loads dynamically | All prelude knowledge lives in `.tao` files |
| Boolean operators | Changed from operator desugaring to FFI calls | `not`/`and`/`or` must resolve to user-defined functions |
| Unification perf | `occurs` check was traversing entire environments | Fixed by only checking explicit type components |
| Constructor resolution | Prelude constructors not available in tests | Fixed by merging prelude `ctr_env` into test context |

These changes represent **learned patterns** about how the compiler must behave. Similar changes will likely follow similar reasoning.
