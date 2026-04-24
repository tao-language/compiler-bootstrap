# Simplified Design: Prototype-First, Extendable

## Philosophy

> Build the smallest thing that works. Add complexity only when it's needed.

This is the **starting point**. Every simplified type/feature has a documented extension path to the full design. We begin here and add features incrementally.

## Extension Roadmap: Simplified → Full

```
START (Simplified)    →    EXTENSIONS (Incremental)    →    FINAL (Full Design)
────────────────────────     ─────────────────────────     ─────────────────────

Literal {              →    Add bit-width & signedness:   →    LitValue { ILit, FLit, StrLit }
  Int, Float,         }                               }    LitType { I32T, I64T, U32T, U64T, F32T, F64T, ILitT, FLitT }
  String             }                               }

No truth/false ctr    →    Add truth/false constructors  →    State with truth_ctor, false_ctor
                            (core knows which to match on)

No implicit params    →    Add implicit params to Lam   →    Lam(param: #(String, Term))
                            for overloaded functions     →    VLam(implicit: List(String), ...)

No record values      →    Add VRcd to Value            →    Full record support

No FFI overloads      →    Add pattern matching         →    FfiEntry with (value, type) pairs
                            on implicit args             →    Operator overloading

No comptime           →    Add Comptime to Term         →    Compile-time evaluation
                                                    →    Permission tracking

No streams/yield      →    Add yield to Expr            →    Generator/Stream system

No error codes        →    Add E-prefix codes           →    E0001, E0101, etc.

No pretty formatting  →    Add source context           →    Fancy diagnostics

No visitor pattern    →    Add visitor                  →    Visitor module (if needed)

No multi-file         →    Add import system            →    Full module system
                                                    →    Circular import detection

```

**Rule:** Each extension is a separate feature that can be built and tested independently. The simplified design works fully on its own.

## What's Cut (and Why)

### Core Simplifications

| Feature | Why Cut Initially | How to Extend Later |
|---------|-------------------|-------------------|
| No bit-width types | One generic `Int/Float` is enough | Add I32/I64/U32/U64/F32/F64 as `LitType` variants |
| No truth/false ctr | Match on `True`/`False` in FFI | Add `truth_ctor: String` to State |
| No implicit params | Not needed for non-overloaded funcs | Add implicit params to Lam for overloading |
| No records in Value | Desugar to Ctr/fields | Add VRcd to Value |
| No comptime | Adds permission tracking | Add Comptime to Term, evaluate at compile time |
| No streams | Can be a library | Add yield + Stream type |
| No error codes | Not useful for debugging MVP | Add E-prefix codes later |
| No pretty formatting | Basic messages sufficient | Add source context formatting |
| No visitor | Boilerplate for 20+ constructors | Add visitor when duplication hurts |
| No multi-file | Start single-file | Add import system later |
| No `mut` keyword | All variables immutable | Not needed (desugar to new bindings) |

### Tao Simplifications

| Feature | Why Cut Initially | How to Extend Later |
|---------|-------------------|-------------------|
| No `mut` keyword | All variables immutable | Add mutation tracking in desugarer |
| No `loop` keyword | Use `while True` | Add loop keyword desugar |
| No `break`/`continue` | Explicit return works | Add loop control with Maybe |
| No `yield` | No streams initially | Add yield + Stream type |
| No `comptime` | Not essential | Add comptime block + compile-time eval |
| No `run` | Not essential | Add FFI run builtin |
| No block syntax | Flat expressions work | Add `{ e1; e2; e3 }` desugar |
| No record update | Just use field access | Add record update desugar |
| No optional chaining | Low-impact | Add optional chaining desugar |

## Revised Directory Structure (Simpler)

```
src/
├── syntax/
│   ├── lexer.gleam       # Tokenizer: String → List(Token)
│   ├── grammar.gleam     # Parser combinator DSL
│   ├── parser.gleam      # Core + Tao parsers (grammar consumers)
│   └── span.gleam        # Source location type
├── core/
│   ├── ast.gleam         # Term, Value, Pattern types
│   ├── state.gleam       # State, FfiEntry, Error types
│   ├── infer.gleam       # Bidirectional type checking
│   ├── eval.gleam        # Normalization by evaluation
│   ├── quote.gleam       # Value → Term
│   ├── unify.gleam       # Higher-order unification
│   ├── subst.gleam       # Substitution
│   ├── generalize.gleam  # Quantify holes
│   ├── exhaustiveness.gleam  # Pattern match checking
│   └── error.gleam       # Error formatting (simple)
├── tao/
│   ├── ast.gleam         # Tao AST (Stmt, Expr, Pattern)
│   ├── lexer.gleam       # Tao tokenizer
│   ├── syntax.gleam      # Tao parser + formatter
│   ├── desugar.gleam     # Expr → Term desugaring
│   ├── compiler.gleam    # Compilation pipeline
│   ├── ffi.gleam         # FFI builtins
│   ├── language_config.gleam  # Language configuration
│   ├── import_resolver.gleam  # Import system (Phase 4)
│   └── test_api.gleam    # Test framework
├── cli/
│   ├── main.gleam        # CLI entry point (run, check, test)
│   ├── run.gleam         # Run mode: compile + evaluate
│   ├── check.gleam       # Check mode: compile + type check only
│   └── test.gleam        # Test mode: find and run tests
└── exit_code.gleam       # Exit codes
```

**Why `cli/` directory:** The CLI is the entry point for users. It coordinates the pipeline and provides the three modes: `run`, `check`, `test`. This makes the CLI testable independently.

## Simplified Type Definitions

### Core AST (Minimal but Extensible)

```gleam
/// Core terms (De Bruijn indices)
pub type Term {
  Var(index: Int, span: Span)
  Hole(id: Int, span: Span)
  Lam(param: String, body: Term, span: Span)          // param: name only (EXTEND: #(name, type))
  App(fun: Term, arg: Term, span: Span)
  Pi(domain: Term, codomain: Term, span: Span)
  Lit(value: Literal, span: Span)                     // Generic literal (EXTEND: ILit/FLit)
  Ctr(tag: String, arg: Term, span: Span)
  Match(arg: Term, cases: List(Case), span: Span)     // motive inferred (EXTEND: add motive)
  Let(name: String, value: Term, body: Term, span: Span)
  Fix(name: String, body: Term, span: Span)
  Call(name: String, args: List(Term), span: Span)    // simple call (EXTEND: typed args)
  Ann(term: Term, typ: Term, span: Span)
  Unit(span: Span)
  Err(message: String, span: Span)
  Typ(universe: Int, span: Span)
}

/// Core values (De Bruijn levels)
pub type Value {
  VNeut(head: Head, spine: List(Elim))
  VLam(param: String, body: Term, env: Env)           // param: name only (EXTEND: implicit params)
  VPi(domain: Value, codomain: Term)
  VLit(value: Literal)                                // Generic literal (EXTEND: I32T etc.)
  VCtr(tag: String, arg: Value)
  VUnit
  VErr
}

pub type Head {
  HVar(level: Int)
  HHole(id: Int)
}

pub type Elim {
  EApp(arg: Value)
  EDot(name: String)
}

pub type Case {
  Case(pattern: Pattern, body: Term, span: Span)
}

pub type Pattern {
  PAny(span: Span)
  PVar(name: String, span: Span)
  PCtr(tag: String, arg: Pattern, span: Span)
  PUnit(span: Span)
  PLit(value: Literal, span: Span)
}

/// Simplified literal types
pub type Literal {
  Int(value: Int, span: Span)     // Generic int (EXTEND: ILit)
  Float(value: Float, span: Span) // Generic float (EXTEND: FLit)
  String(value: String, span: Span)
}
```

**Extension notes:**
- `Lam(param: String, ...)` → `Lam(param: #(String, Term), ...)` adds type to lambda
- `VLam(param: String, ...)` → `VLam(implicit: List(String), param: String, ...)` adds implicit params
- `Literal { Int, Float, String }` → `LitValue { ILit, FLit, StrLit }` adds bit-width
- `VLit(Literal)` → `VLit(LitValue)` with `LitType { I32T, ..., ILitT, FLitT }` for concrete types

### State (Simplified but Extensible)

```gleam
pub type State {
  State(
    ctrs: List(#(String, #(String, Term))),  // name → (arg_name, arg_type)
    errors: List(Error),
    ffi: List(FfiEntry),
    holes: List(#(Int, Value)),  // hole_id → expected_type
    subst: List(#(Int, Value)),  // level → value
  )
}

pub type Error {
  TypeMismatch(expected: Value, got: Value, expected_span: Span, got_span: Span)
  VarUndefined(index: Int, span: Span)
  HoleUnsolved(id: Int, span: Span)
  NotAFunction(term: Term, span: Span)
  ArityMismatch(expected: Int, actual: Int, span: Span)
  ConstructorUndefined(name: String, span: Span)
  PatternTypeMismatch(pattern: Pattern, expected: Value, span: Span)
  MatchNonExhaustive(span: Span, missing: List(Pattern))
}

pub type FfiEntry {
  FfiEntry(
    name: String,
    impl: fn(List(Value)) -> Value,
    arg_types: List(Value),
    ret_type: Value,
  )
}
```

**Extension notes:**
- `FfiEntry.impl: fn(List(Value)) -> Value` → `fn(List(#(Value, Value))) -> Option(Value)` adds (value, type) pairs
- `State` adds `truth_ctor: String` and `step_limit: Int`
- `Error` adds error codes, notes, hints
- `List(#(Int, Value))` subst → `Subst` type with shift operations

### Tao AST (Simplified)

```gleam
/// High-level expressions (string-based variable names)
pub type Expr {
  Var(name: String, span: Span)
  Lit(value: Literal, span: Span)
  Lambda(params: List(Param), body: Expr, span: Span)
  Call(fun: Expr, args: List(Expr), span: Span)
  BinOp(left: Expr, op: BinOp, right: Expr, span: Span)
  Ctr(name: String, args: List(Expr), span: Span)
  Match(arg: Expr, cases: List(MatchClause), span: Span)
  If(cond: Expr, then: Expr, else_: Expr, span: Span)
  Ann(term: Expr, typ: TypeAst, span: Span)
  Hole(span: Span)
  Record(fields: List(#(String, Expr)), span: Span)
  Dot(record: Expr, field: String, span: Span)
  // EXTEND: Comptime(Expr), IfThenElse(Expr, Expr), Block(List(Stmt))
}

pub type Param {
  Param(name: String, type_: Option(TypeAst), span: Span)
}

pub type TypeAst {
  TVar(name: String, span: Span)
  TApp(name: String, args: List(TypeAst), span: Span)
  TFn(args: List(TypeAst), ret: TypeAst, span: Span)
  THole(span: Span)
}

/// Statements
pub type Stmt {
  Let(name: String, value: Expr, span: Span)
  Fn(name: String, params: List(Param), body: Expr, span: Span)
  Import(path: String, span: Span)
  TypeDef(name: String, constructors: List(#(String, List(#(String, TypeAst)))), span: Span)
  For(name: String, collection: Expr, body: Expr, span: Span)
  While(cond: Expr, body: Expr, span: Span)
  Expr(Expr, span: Span)  // expression statement
  // EXTEND: Test(name: String, expr: Expr, expect: Pattern, Span)
}

/// Test statement (REPL-style)
/// > expression
/// result
pub type TestStatement {
  TestStatement(name: Option(String), expr: Expr, expect: Pattern, span: Span)
}
```

**Extension notes:**
- `Expr` adds `Comptime`, `Block`, `IfThenElse`
- `Stmt` adds `Test(name, expr, expect, span)` — REPL style `/// > expr ~> result`
- `BinOp` is desugared in the parser (not in AST)

## Simplified Pipeline

```
┌─────────────────────────────────────────────────┐
│              COMPILATION PIPELINE                │
│                                                  │
│  1. PARSE    String → Expr + ParseError         │
│  2. DESUGAR  Expr → Term + DesugarError         │
│  3. CHECK    Term → Type + TypeError            │
│  4. EVAL     Term → Value                       │
│  5. QUOTE    Value → Term (for display)         │
│                                                  │
│  All errors accumulated in State.errors          │
└─────────────────────────────────────────────────┘
```

### Core Functions

```gleam
/// Parse source into expression
pub fn parse(grammar: Grammar, source: String) -> #(Expr, List(ParseError))

/// Desugar expression to core term
pub fn desugar(expr: Expr, ctx: Context) -> #(Term, List(Error))

/// Infer type of term — returns (resolved term, inferred type, updated state)
pub fn infer(state: State, term: Term) -> #(Term, Value, State)

/// Check term against expected type — returns (resolved term, verified type, updated state)
pub fn check(state: State, term: Term, expected: Value) -> #(Term, Value, State)

/// Evaluate term to value
pub fn evaluate(term: Term) -> Value

/// Quote value back to term
pub fn quote(value: Value) -> Term

/// Full compilation pipeline
pub fn compile(source: String, ctx: Context) -> Result(#(Term, Value), List(Error))
```

### CLI Commands (The Three Modes)

```gleam
/// Run mode: compile and evaluate a Tao program
pub fn run(source: String, ctx: Context) -> RunResult {
  // 1. Parse → 2. Desugar → 3. Check → 4. Evaluate → 5. Print result
  // Returns: Value (or errors from all phases)
}

/// Check mode: compile and type-check only (don't evaluate)
pub fn check(source: String, ctx: Context) -> CheckResult {
  // 1. Parse → 2. Desugar → 3. Check
  // Returns: Type (or errors from all phases)
}

/// Test mode: find all test statements and run them
pub fn test(source: String, ctx: Context) -> TestResult {
  // 1. Parse → 2. Desugar → 3. Check → 4. Evaluate tests
  // Returns: #[pass, fail, total]
  // Test statements are extracted from the AST (/// > expr ~> result)
}
```

## Revised Implementation Plan (Phases for CLI First)

### Phase 1: Lexer + Core Types (2-3 days)

**Goal:** Can tokenize and represent Core terms. No parsing yet.

**Deliverables:**
- Tokenizer with span tracking (Integer, Float, String, Name, Op, Keyword, etc.)
- Core AST types (Term, Value, Pattern, Literal, etc.)
- State and Error types
- Basic span utilities

**Tests:**
- Tokenizer: every token type
- AST types: structural equality, basic construction

### Phase 2: Parser + Core Type Checker + Run Command (4-5 days)

**Goal:** Can run simple Core programs. First working CLI: `tao run <file>`.

**Deliverables:**
- Core grammar + parser (produces Core Term)
- Core formatter (optional, for debugging)
- Bidirectional type checker (infer, check)
- NBE evaluator
- Quote (Value → Term)
- Unification + substitution
- Exhaustiveness checking
- **CLI `run` command** — compile + evaluate

**Tests:**
- Lexer: every token type
- Core parser: every syntax form
- Type checker: every term form, every error case
- Evaluator: every value form
- Quote: every value form
- Unification: every type pair
- Exhaustiveness: every pattern combination

### Phase 3: Tao + Desugaring + Test Framework (4-5 days)

**Goal:** Can write Tao programs. Add `tao check <file>` and `tao test <file>`.

**Deliverables:**
- Tao AST types
- Tao parser (uses grammar DSL from Phase 2)
- Desugarer (every Tao feature → Core term)
- **CLI `check` command** — compile + type check only
- **Test framework** (REPL style: `/// > expr ~> result`)
- **CLI `test` command** — find and run test statements

**Tests:**
- Tao parser: every syntax form
- Desugarer: every high-level feature
- Compiler: end-to-end examples
- Test framework: REPL-style test extraction and evaluation

### Phase 4: Multi-file + Import System (3-4 days)

**Goal:** Multi-file compilation with imports.

**Deliverables:**
- Module loading
- Import resolver (module-not-found → empty module, name-not-found → deferred)
- Multi-file compilation
- Language configuration (truth constructor, operators)

**Tests:**
- Import resolution: every variant
- Multi-file compilation: every file combination
- Error handling: module-not-found, name-not-found (deferred)

### Phase 5: Polish + Extended Features (3-4 days)

**Goal:** Full design features added incrementally.

**Deliverables:**
- Literal type extensions (ILit/FLit, I32T/I64T/etc.)
- Operator overloading (pattern matching on implicit args)
- Truth/false constructor matching
- Better error messages
- Error codes (E0001, E0101, etc.)
- Pretty error formatting with source context
- Optional: Comptime, Streams, Record update

**Tests:**
- Literal type unification
- Operator overloading resolution
- Error code system
- Source context formatting

## Summary

| Phase | Days | Deliverables | CLI Commands |
|-------|------|-------------|-------------|
| 1: Lexer + Core Types | 2-3 | Tokenizer, Core AST, State, Error | — |
| 2: Parser + Type Checker + **Run** | 4-5 | Core parser, type checker, NBE, Quote | `run` ✅ |
| 3: Tao + Desugar + **Check + Test** | 4-5 | Tao parser, desugarer, test framework | `run` ✅, `check` ✅, `test` ✅ |
| 4: Multi-file + Import | 3-4 | Module loading, import resolver | `run` ✅, `check` ✅, `test` ✅ |
| 5: Polish + Extended Features | 3-4 | Literal types, overloading, error codes, formatting | `run` ✅, `check` ✅, `test` ✅ |

**First working CLI by end of Phase 2.** Full CLI (run/check/test) by end of Phase 3.

## Expected Test Count

| Category | Simplified | Full Design |
|----------|-----------|-------------|
| Lexer | 15 | 15 |
| Parser (Core) | 20 | 30 |
| Parser (Tao) | 20 | 30 |
| Core type checker | 30 | 50 |
| Core evaluator | 20 | 25 |
| Quote | 10 | 15 |
| Unification | 15 | 20 |
| Exhaustiveness | 15 | 20 |
| Desugarer | 25 | 40 |
| Import system | 20 | 40 |
| CLI tests | 10 | 20 |
| Error handling | 10 | 30 |
| **Total** | **~175** | **~340** |

## What This Approach Gains

1. **Working CLI early** — `run` command by end of Phase 2 (not Phase 7)
2. **Testable incrementally** — Each phase delivers something runnable
3. **Clear extension path** — Simplified → Full via documented extension points
4. **No wasted effort** — Features built only when needed
5. **CLI-first design** — `run`, `check`, `test` are first-class entry points, not afterthoughts
