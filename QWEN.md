# Compiler Bootstrap - Project Context

## Project Overview

This is a **compiler bootstrap project** written in Gleam, implementing a dependently typed core language with:
- **Normalization by Evaluation (NbE)** for equality checking
- **Bidirectional type checking** (infer/check) with metavariable solving
- **Integrated exhaustiveness checking** using Maranget's algorithm
- **Error recovery** that never fails completely - always returns partial AST with errors
- **Generic parser combinator library** with Pratt parsing for operator precedence

The project aims to be a foundation for higher-level languages, providing reusable parser/formatter infrastructure.

## Project Structure

```
compiler-bootstrap/
├── gleam.toml              # Project config (Gleam package)
├── manifest.toml           # Dependency lock file
├── README.md               # Package documentation
├── QWEN.md                 # This file - AI context
│
├── src/
│   ├── main.gleam          # Entry point
│   ├── parser.gleam        # Generic parser combinator library (COMPLETE)
│   └── core/
│       └── core.gleam      # Core language: type checker, evaluator, unifier (1400+ lines)
│
├── test/
│   ├── compiler_bootstrap_test.gleam
│   └── core_test.gleam
│
├── docs/
│   ├── core.md             # Core language specification (detailed)
│   ├── grammar.md          # Grammar DSL and parser/formatter docs
│   ├── parser-combinator-plan.md  # Parser library implementation plan
│   └── README.md
│
└── grammar-reference/      # Haskell reference implementation
    ├── Parser.hs           # Parser combinators with error recovery
    ├── Formatter.hs        # Pretty printing with layout
    └── Grammar.hs          # Grammar DSL
```

## Key Technologies

- **Language**: Gleam (functional, type-safe, runs on BEAM/JavaScript)
- **Dependencies**: `gleam_stdlib`, `gleeunit` (testing)
- **Build Tool**: `gleam` (build, test, run, docs)

## Building and Running

```bash
# Run the project
gleam run

# Run tests
gleam test

# Watch mode (if fswatch installed)
fswatch -or src test | xargs -n1 -I{} gleam test

# Generate documentation
gleam docs
```

## Current Implementation State

### ✅ Completed

1. **Parser Combinator Library** (`src/parser.gleam`)
   - Core combinators: `ok`, `fail`, `one_of`, `chain`, `zero_or_more`, `one_or_more`
   - Character/text parsers: `char`, `text`, `word`, `integer`, `number`
   - Padding/delimiters: `padded`, `delimited_by`, `separated_by`
   - Lookahead: `lookahead`, `lookahead_not`, `assert`
   - Error handling: `expect`, `commit`, `recover`, `sync_to`
   - Pratt parsing: `ExprParser`, `atom`, `prefix`, `infix_l`, `infix_r`, `precedence`
   - Error types: `ParseError`, `ParseResult`, `ErrorSeverity`

2. **Core Language** (`src/core/core.gleam`)
   - Syntax: `Term`, `Pattern`, `Case`, `Span`
   - Semantics: `Value`, `Head`, `Elim`, `Env`, `Context`
   - Evaluation: `eval`, `do_app`, `do_match`
   - Normalization: `normalize`, `quote`
   - Unification: `unify`, `force`, `occurs_check`
   - Type checking: `infer`, `check`, `bind_pattern`
   - Exhaustiveness: `check_exhaustiveness`, `useful`, `specialize`
   - Error collection: `list_errors`, `with_err`

### 🔄 In Progress / TODO

1. **Formatter Library** (`src/formatter.gleam`) - NOT YET CREATED
   - Pretty printing with layout algebra (inspired by Wadler's "A Prettier Printer")
   - Grammar-aware formatting
   - Precedence-aware expression formatting

2. **Grammar DSL** (`src/grammar.gleam`) - NOT YET CREATED
   - Declarative grammar definition
   - Automatic parser generation from grammar
   - Automatic formatter generation from grammar
   - Single source of truth for syntax

3. **Tests** - MINIMAL
   - Basic tests exist in `test/`
   - Need comprehensive tests for parser combinators
   - Need tests for formatter
   - Need tests for grammar DSL

## Core Architecture Concepts

### Parser Combinators

The parser library uses **state-passing style** with error recovery:

```gleam
pub type Parser(a) {
  Parser(fn(State) -> Result(#(a, State), State))
}

pub type State {
  State(
    remaining: String,
    filename: String,
    pos: Position,
    index: Int,
    expected: String,
    committed: String,
  )
}
```

**Key Design**: Parsers never fail completely. On error, they return the failed state for recovery.

### Error Recovery

```gleam
pub type ParseResult(a) {
  ParseResult(ast: a, errors: List(ParseError))
}
```

- Always returns a result (even if partial)
- Collects all errors, doesn't stop at first
- Supports sync points and recovery strategies

### Pratt Parsing

Expression parsing via operator precedence:

```gleam
pub type ExprParser(a) {
  Atom(fn(Parser(a)) -> Parser(a))
  Prefix(Int, fn(Parser(a)) -> Parser(a))
  InfixL(Int, fn(a, Parser(a)) -> Parser(a))
  InfixR(Int, fn(a, Parser(a)) -> Parser(a))
}
```

### Core Language: Syntax vs. Semantics

| Syntax (`Term`) | Semantics (`Value`) |
|-----------------|---------------------|
| Raw AST | Evaluated result |
| De Bruijn **Indices** | De Bruijn **Levels** |
| `Lam("x", body)` | `VLam("x", env, body)` (closure) |
| `Var(0)` | Look up index 0 in environment |

### De Bruijn Indices vs. Levels

**Indices** (in `Term`): Relative distance to binder
```
Term: λ. λ. Var(1)  -- Skip 1 binder, get outer λ
```

**Levels** (in `Value`): Absolute order of creation
```
Value: λ. λ. HVar(0)  -- First variable created
```

### Bidirectional Type Checking

Two modes:
- **`infer`**: "What is the type of this term?" (synthesis)
- **`check`**: "Does this term have the expected type?" (checking)

### Normalization by Evaluation (NbE)

To check equality:
1. **Evaluate** both terms to values
2. **Quote** both back to syntax
3. **Compare** structurally

## Development Conventions

### Code Style

- Use descriptive type names (`Term`, `Value`, `Pattern`)
- Document modules with `///` comments
- Use `pub type` for public types, internal functions without `pub`
- Follow Gleam naming: `snake_case` for functions, `PascalCase` for types

### Error Handling

- Never throw errors - use `Result` types
- Accumulate errors in `state.errors`
- Return `VErr` for error values (propagates through evaluation)
- Use `list_errors(value)` to extract nested errors from closures

### Testing

- Tests use `gleeunit`
- Test files mirror source structure
- Run tests with `gleam test`

## Key Files to Know

### Parser Library (`src/parser.gleam`)

**Types**:
- `Parser(a)`, `State`, `Position`, `Location`, `Range`
- `ParseError`, `ParseResult(a)`, `ErrorSeverity`
- `ExprParser(a)` for Pratt parsing

**Core Combinators**:
- `ok`, `fail`, `state`, `position`
- `any_char`, `char`, `text`, `word`, `integer`, `number`
- `one_of`, `chain`, `zero_or_more`, `one_or_more`
- `padded`, `delimited_by`, `separated_by`
- `lookahead`, `lookahead_not`, `assert`
- `expect`, `commit`, `recover`, `sync_to`

**Pratt Parsing**:
- `atom`, `prefix`, `suffix`, `infix_l`, `infix_r`
- `precedence`

### Core Language (`src/core/core.gleam`)

**Types**:
- `Term`, `TermData`, `Pattern`, `Case`
- `Value`, `Head`, `Elim`, `Type`
- `Env`, `Context`, `Subst`, `State`
- `Error` (all error types)

**Functions**:
- `eval`, `quote`, `normalize`
- `infer`, `check`, `unify`
- `bind_pattern`, `check_exhaustiveness`
- `list_errors`, `with_err`

## Planned Architecture (Grammar DSL)

The grammar system will provide a **single source of truth** for language syntax:

```
grammar.gleam (Grammar DSL)
     ↓
   ┌─┴─┐
   ↓   ↓
parser.gleam  formatter.gleam
   ↓           ↓
ParseTree   String
```

### Grammar DSL API (Planned)

```gleam
import grammar

let g = grammar.grammar("Expr", [
  grammar.rule("Expr", grammar.choice([
    grammar.seq([
      grammar.token("let"),
      grammar.pattern("Ident"),
      grammar.token("="),
      grammar.ref("Expr"),
    ]),
    grammar.ref("Term"),
  ])),
  grammar.rule("Term", grammar.choice([
    grammar.pattern("Ident"),
    grammar.pattern("Number"),
  ])),
])

// Generate parser and formatter
let parse = grammar.to_parser(g)
let format = grammar.to_formatter(g)
```

### Grammar Combinators (Planned)

- `grammar.token(value)` - Match literal token
- `grammar.ref(name)` - Reference another rule
- `grammar.seq([symbols])` - Sequence
- `grammar.choice([alternatives])` - Choice
- `grammar.opt(symbol)` - Optional
- `grammar.rep(symbol)` - Zero or more
- `grammar.rep1(symbol)` - One or more
- `grammar.pattern(name)` - Named pattern (captures token)

## References

### Parser Combinators
- [Haskell Reference](grammar-reference/Parser.hs) - Complete implementation with error recovery
- [Parser Combinator Plan](docs/parser-combinator-plan.md) - Detailed implementation plan

### Core Language
- [Core Language Spec](docs/core.md) - Comprehensive specification with examples
- Based on: NbE, bidirectional typing, Maranget's exhaustiveness checking

### Formatter
- [Haskell Reference](grammar-reference/Formatter.hs) - Layout algebra implementation
- Based on: Wadler's "A Prettier Printer" paper

## For AI Assistants

When working with this codebase:

1. **Parser Library**: Already complete - use existing combinators
2. **Formatter/Grammar**: Need implementation - follow Haskell reference but improve DX
3. **Core Language**: Complex - understand De Bruijn indices vs. levels distinction
4. **Error Recovery**: Intentional design - don't "fix" `VErr` propagation
5. **Tests**: Add tests for new features, especially formatter/grammar

### Key Invariants

- `eval` never modifies environment (functional)
- `quote` is inverse of `eval` (for normal forms)
- `unify` accumulates solutions in `State.sub`
- Errors are accumulated, never thrown
- Parsers never fail completely - always return recoverable state

## Next Steps

1. Implement `src/formatter.gleam` with layout algebra
2. Implement `src/grammar.gleam` with grammar DSL
3. Connect grammar to parser/formatter generation
4. Add comprehensive tests for all modules
5. Integrate with core language parsing/formatting
