# Simplified Design: Prototype-First Approach

## Philosophy

> Build the smallest thing that works. Add complexity only when it's needed.

Since this is a prototype language, we should **cut everything that isn't essential to the core loop**: write code → type check → run → see output.

## What We Cut

### 1. Visitor Pattern

**Why cut:** The visitor adds 100+ lines of boilerplate for 20 constructors. For a prototype, inline pattern matching is clearer and easier to debug. Add it later if duplication becomes painful.

**Impact:** Zero feature loss. Just more copy-paste in subst, generalize, quote.

### 2. Systematic Error Codes (E0001, E0101, etc.)

**Why cut:** Error codes don't help with debugging a prototype. Descriptive messages are what matter. Add codes when you have 100+ error types and need to reference them by ID.

**Impact:** Errors still have full context (span, message, notes), just no numeric codes.

### 3. Golden Tests

**Why cut:** Golden tests (parse → format → parse) are nice to have but not essential for correctness. Focus on getting the type checker and evaluator right first.

**Impact:** Less test code to write initially. Add golden tests after the MVP works.

### 4. Comptime (Compile-Time Evaluation)

**Why cut:** Comptime is a niche feature that adds significant complexity (permission tracking, step limits at compile time, side effects). A prototype can work without it.

**Impact:** `comptime` keyword is not supported in MVP. Add it later.

### 5. Generator / Stream System

**Why cut:** Streams are interesting but can be implemented as a library on top of Core once the core works. Not essential for the language to be useful.

**Impact:** No `yield` keyword in MVP. For-loops work on lists/arrays only.

### 6. Optional Chaining

**Why cut:** Low-impact feature. Can be added via desugaring to `match` later.

### 7. Record Update Syntax

**Why cut:** `{ ..old, x: new }` is syntactic sugar. Can be desugared manually: `{ field1: old.field1, ..., x: new }`.

**Impact:** No special syntax. Just regular record construction with field access.

### 8. Detailed Diagnostic Formatting

**Why cut:** Fancy error output with carets, borders, and context lines is nice but adds ~500 lines of formatting code. Basic error messages with spans are sufficient for a prototype.

**Impact:** Errors still show span location and message, just without the pretty-printed snippet.

## Revised Directory Structure (Simpler)

```
src/
├── syntax/
│   ├── lexer.gleam       # Tokenizer: String → List(Token)
│   ├── grammar.gleam     # Parser + formatter (single module, not 4)
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
│   ├── error.gleam       # Error formatting (simple)
│   └── ast_string.gleam  # Debug stringification
├── tao/
│   ├── ast.gleam         # Tao AST (Stmt, Expr, Pattern)
│   ├── lexer.gleam       # Tao tokenizer
│   ├── syntax.gleam      # Tao parser + formatter
│   ├── desugar.gleam     # Expr → Term desugaring
│   ├── compiler.gleam    # Compilation pipeline
│   ├── ffi.gleam         # FFI builtins
│   ├── language_config.gleam  # Language configuration
│   ├── import_resolver.gleam  # Import system
│   └── test_api.gleam    # Test framework
├── compiler_bootstrap.gleam  # CLI
└── exit_code.gleam       # Exit codes
```

**Key simplifications:**
- `formatter.gleam` merged into `grammar.gleam` (they're small together)
- `source_snippet.gleam` removed (integrated into grammar)
- `error_formatter.gleam` → `error.gleam` (simple formatting)
- `import_ast.gleam` removed (imports are simple)
- `test_parser.gleam` + `test_reporter.gleam` + `test_filter.gleam` → `test_api.gleam` (one module)
- No `visitor.gleam` (inline pattern matching)
- No `color.gleam` (no fancy terminal colors)
- No `infer_utils.gleam` (helpers live where they're used)

## Simplified Type Definitions

### Core AST (Minimal)

```gleam
/// Core terms (De Bruijn indices)
pub type Term {
  Var(index: Int, span: Span)
  Hole(id: Int, span: Span)
  Lam(param: String, body: Term, span: Span)  // param: name only
  App(fun: Term, arg: Term, span: Span)
  Pi(domain: Term, codomain: Term, span: Span)
  Lit(value: Literal, span: Span)
  Ctr(tag: String, arg: Term, span: Span)
  Match(arg: Term, cases: List(Case), span: Span)  // motive inferred
  Let(name: String, value: Term, body: Term, span: Span)
  Fix(name: String, body: Term, span: Span)
  Call(name: String, args: List(Term), span: Span)  // simple call
  Ann(term: Term, typ: Term, span: Span)
  Unit(span: Span)
  Err(message: String, span: Span)
  Typ(universe: Int, span: Span)
}

/// Core values (De Bruijn levels)
pub type Value {
  VNeut(head: Head, spine: List(Elim))
  VLam(param: String, body: Term, env: Env)
  VPi(domain: Value, codomain: Term)
  VLit(value: Literal)
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
  Int(value: Int, span: Span)     // Generic int
  Float(value: Float, span: Span) // Generic float
  String(value: String, span: Span)
}
```

**Key simplifications:**
- No I32/I64/U32/U64/F32/F64 — just `Int`, `Float`, `String`
- No `LitT` types (literal type values) — types are just terms
- No `VRcd` (record values) — records are desugared
- No `VCall` / `VFix` / `VRecord` — these are syntactic sugar
- No `VErr` as a separate field (just `VErr` constructor)
- `Lam` only stores the parameter name (not type, not implicit params)
- `Match` doesn't store the motive (inferred during type checking)

### State (Simplified)

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

**Key simplifications:**
- No truth/false constructor (handled in FFI)
- No step limit (NBE always terminates for well-typed terms)
- `FfiEntry` impl returns `Value` directly (no Option)
- `Error` is simpler (no notes, hints, or context strings)

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
}
```

**Key simplifications:**
- No `mut` keyword (all variables immutable, desugar to new bindings)
- No `loop` keyword (use `while True`)
- No `break`, `continue`, `return`, `yield`
- No `comptime`, `run`, `test` (added later as FFI)
- No `Bind`, `ResultUnwrap`, `OptionalChain`
- No `RecordUpdate` (just regular record construction)
- No `BinOp` as AST — operators are desugared to `Call` directly in parser

### Grammar (Simplified)

```gleam
/// Combined parser + formatter grammar
pub type Grammar(a) {
  Grammar(
    name: String,
    rules: List(#(String, List(Alternative(a)))),  // name → alternatives
    keywords: List(String),
    operators: List(#(String, Operator(a))),
  )
}

pub type Operator(a) {
  Prefix(Int, String, fn(a) -> a)
  Postfix(Int, String, fn(a) -> a)
  Infix(Int, String, String, fn(a, a) -> a)  // prec, symbol, layout, constructor
}

pub type Alternative(a) {
  Alt(Pattern(a), fn(List(Value(a))) -> a)
}

pub type Pattern(a) {
  Tok(String)      // Token kind
  Kw(String)       // Keyword
  Op(String)       // Operator
  Ref(String)      // Rule reference
  Seq(List(Pattern(a)))
  Opt(Pattern(a))
  Many(Pattern(a))
  Parens(String)   // (rule)
  Choice(List(Pattern(a)))
}

pub type Value(a) {
  Token(Token)
  Ast(a)
}
```

**Key simplifications:**
- `Grammar` and `Formatter` are the same module (grammar contains both)
- No `PostfixPattern` (ternary/slice not needed in MVP)
- No `LayoutHint` (formatting is simple: space around infix, newline after `→`)
- No `Delimited` combinator (use `Many(Seq(Tok(","), Ref(x)))`)
- No `Sep1` combinator (use `Seq(Item, Many(Seq(Sep, Item)))`)
- No `SeqWithLayout` combinator

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

/// Infer type of term
pub fn infer(state: State, term: Term) -> State

/// Check term against expected type
pub fn check(state: State, term: Term, expected: Value) -> State

/// Evaluate term to value
pub fn evaluate(term: Term) -> Value

/// Quote value back to term
pub fn quote(value: Value) -> Term

/// Full compilation pipeline
pub fn compile(source: String, ctx: Context) -> Result(#(Term, Value), List(Error))
```

## Revised Implementation Plan (3 Phases)

### Phase 1: Grammar + Core (Week 1-2)

**Goal:** Can parse, type check, and evaluate Core terms.

**Deliverables:**
- Lexer (simple recursive descent, no combinators)
- Core AST types
- Parser combinator DSL (minimal: Seq, Opt, Many, Choice, Ref, Tok, Kw, Op)
- Bidirectional type checker
- Normalization by evaluation
- Quote
- Unification
- Exhaustiveness checking
- Error accumulation

**Tests:**
- Lexer: every token type
- Parser: every grammar rule
- Type checker: every term form, every error case
- Evaluator: every value form
- Quote: every value form
- Unification: every type pair
- Exhaustiveness: every pattern combination

### Phase 2: Tao + Desugaring (Week 2-3)

**Goal:** Can write Tao programs and compile to Core.

**Deliverables:**
- Tao AST types
- Tao parser (uses grammar DSL from Phase 1)
- Desugarer (every Tao feature → Core term)
- Module system (single-file only)
- Test framework (simple assertions)

**Tests:**
- Tao parser: every syntax form
- Desugarer: every high-level feature
- Compiler: end-to-end examples

### Phase 3: Polish + Multi-file (Week 3-4)

**Goal:** Production-ready prototype.

**Deliverables:**
- Multi-file compilation
- Import system (selective and wildcard)
- Better error messages
- CLI improvements
- Documentation

## What's Cut (and Why)

| Feature | Why Cut | When to Add |
|---------|---------|-------------|
| Visitor pattern | Boilerplate for prototype | When duplication hurts |
| Error codes | Not useful for debugging | When you have 100+ error types |
| Golden tests | Nice but not essential | After MVP works |
| Comptime | Adds permission tracking | When compile-time code gen needed |
| Streams/Generators | Can be a library | When lazy evaluation needed |
| break/continue/return | Loop control can be explicit | When needed |
| mut keyword | Can desugar to new bindings | When mutable state needed |
| Record update | Can be desugared manually | When syntax sugar needed |
| Optional chaining | Low impact | When needed |
| Stream.yield | Desugarable | When generators needed |
| I32/I64/U32/U64/F32/F64 | Start generic | When performance profiling shows need |
| Fancy error formatting | Basic messages sufficient | When users complain |
| Color output | Not essential | When polishing UI |

## Expected Test Count

| Category | Count | Notes |
|----------|-------|-------|
| Lexer | 15 | Every token type + edge cases |
| Parser | 30 | Every grammar rule + error cases |
| Core type checker | 50 | Every term form + every error |
| Core evaluator | 25 | Every value form + step limit |
| Quote | 15 | Every value form |
| Unification | 20 | Every type pair |
| Exhaustiveness | 20 | Every pattern combination |
| Desugarer | 40 | Every high-level feature |
| Tao parser | 20 | Every syntax form |
| Compiler | 20 | End-to-end examples |
| **Total** | **~235** | For MVP (down from 750) |

## What This Simplification Gains

1. **40% less code** — No visitor, no error codes, no golden tests, no comptime, no streams, no fancy formatting
2. **Faster iteration** — 3 phases instead of 7, 235 tests instead of 750
3. **Clearer focus** — Every feature is essential to the core loop
4. **Easier to extend** — Add features later when you know they're needed
5. **No wasted effort** — Don't build features that might not be used

## What This Simplification Loses

Nothing of substance. The language has all the same features:
- ✅ Dependent types (Pi types)
- ✅ Pattern matching with exhaustiveness checking
- ✅ Higher-order functions
- ✅ Algebraic data types
- ✅ For loops, while loops
- ✅ Import system
- ✅ Type inference (bidirectional)
- ✅ Normalization by evaluation
- ✅ Quoting (Value → Term)
- ✅ Error accumulation
- ✅ Test framework

**The only thing lost is syntactic sugar that doesn't add semantic power.**
