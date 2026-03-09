# Unified Grammar System Design

> **Goal**: Single source of truth for grammar that automatically generates both parser and formatter
> **Principles**: Declarative, type-safe, minimal boilerplate, intuitive
> **Status**: ✅ Parser complete, ⏳ Automatic formatter generation in progress

---

## Problem Statement

The current implementation has several issues:

1. **Mixed designs**: Symbol DSL + parser combinators creates confusion
2. **Manual formatters**: AST pattern matching defeats "automatic generation" goal
3. **Verbose constructors**: `ParseChild` pattern matching is repetitive
4. **Leaky abstractions**: Users must understand internal representation

---

## Core Insight

A grammar rule should specify **what** to parse and **how** to format it, not **how** to parse it. The system should handle the mechanics automatically.

```
Grammar (single source of truth)
    ├── Parser (automatically generated) ✅
    └── Formatter (automatically generated) ⏳
```

---

## Current Implementation Status

### ✅ Working (Parser)

- Lexer tokenizes numbers, identifiers, operators, parentheses, strings, comments
- Grammar DSL with declarative builder pattern
- Parser handles all patterns (Token, Keyword, Op, Ref, Seq, Choice, Opt, Many, Sep1, Parens)
- Left-associative operator parsing with correct folding
- Operator precedence handling
- Parenthesized expressions
- **238 tests passing**

### ⏳ In Progress (Formatter)

- Manual formatter implemented for calc example (`src/examples/calc.gleam`)
- Precedence-based parenthesization working correctly
- Round-trip tests passing (parse → format → parse)
- **Automatic formatter generation from grammar** - needs implementation

---

## Key Insights from Implementation

### 1. Precedence-Based Parenthesization is Critical

From the manual calc formatter implementation, we learned:

```gleam
// For left-associative operators:
// - Left operand: same precedence (no parens for same level)
// - Right operand: precedence + 1 (parens for same level)
Add(l, r) ->
  format_binop(
    format_expr(l, 10),   // Left: same prec
    format_expr(r, 11),   // Right: prec + 1
    " + ",
    10,                   // Operator precedence
    parent_prec,
  )
```

This ensures:
- `1 + 2 + 3` → `1 + 2 + 3` (not `(1 + 2) + 3`)
- `1 + 2 * 3` → `1 + 2 * 3` (correct precedence)
- `(1 + 2) * 3` → `(1 + 2) * 3` (parens preserved when needed)

### 2. Deconstructors are Essential for Automatic Formatting

The manual formatter needs to deconstruct AST nodes:

```gleam
case ast {
  Add(l, r) -> format_binop(format_expr(l, 11), format_expr(r, 10), " + ", ...)
  Mul(l, r) -> format_binop(format_expr(l, 21), format_expr(r, 20), " * ", ...)
}
```

For automatic generation, we need to store **how to deconstruct** alongside **how to construct**.

### 3. Operator Information Must Be Bidirectional

Current `Operator` type:
```gleam
pub type Operator(a) {
  Operator(
    keyword: String,
    constructor: fn(a, a) -> a,  // For parsing
    precedence: Int,
    associativity: Associativity,
    layout: LayoutStyle,
  )
}
```

Needs deconstructor for formatting:
```gleam
pub type Operator(a) {
  Operator(
    keyword: String,
    constructor: fn(a, a) -> a,      // For parsing: (left, right) -> AST
    deconstructor: fn(a) -> #(a, a), // For formatting: AST -> (left, right)
    precedence: Int,
    associativity: Associativity,
    layout: LayoutStyle,
  )
}
```

### 4. Token Value Extraction Needs Handling

For `Number` token → `Int(n)` conversion:

**Current approach** (manual in constructor):
```gleam
grammar.alt(grammar.token_pattern("Number"), fn(values) {
  case values {
    [TokenValue(token)] -> Int(int.parse(token.value) |> result.unwrap(0))
    _ -> panic as "Expected Number"
  }
})
```

**Better approach** (built-in converters):
```gleam
grammar.alt(grammar.int_token("Number"), fn(n) { Int(n) })
```

---

## Proposed Design (Updated)

### 1. Declarative Grammar DSL

```gleam
pub fn calc_grammar() -> Grammar(Expr) {
  use g <- grammar.define

  // Left-associative operators with precedence
  g |> grammar.left_assoc("Expr", "Term", [
    grammar.op("+", Add, 10),
    grammar.op("-", Sub, 10),
  ])
  |> grammar.left_assoc("Term", "Factor", [
    grammar.op("*", Mul, 20),
    grammar.op("/", Div, 20),
  ])
  |> grammar.rule("Factor", [
    grammar.alt(grammar.int_token("Number"), fn(n) { Int(n) }),
    grammar.alt(grammar.parens("Expr"), fn(e) { e }),
  ])
}
```

### 2. Automatic Formatter Generation

The formatter is derived from the grammar structure with stored deconstructors:

```gleam
// From the grammar definition above, this is auto-generated:
//
// format(Add(l, r), parent_prec) =
//   let doc = format(l, 10) <> " + " <> format(r, 11)
//   wrap_parens(doc, 10 < parent_prec)
//
// format(Int(n), _) = int.to_string(n)
//
// With automatic precedence-based parenthesization!
```

### 3. Type-Safe Constructors and Deconstructors

```gleam
// Old way (verbose, error-prone):
fn(children) {
  case children {
    [ChildToken(token)] -> Int(int.parse(token.value) |> result.unwrap(0))
    [_, ChildAST(expr), _] -> expr
    _ -> panic as "Invalid"
  }
}

// New way (type-safe, concise):
fn(n) { Int(n) }  // Number token parsed to Int automatically
fn(e) { e }       // Parenthesized expression
```

---

## Grammar DSL Specification

### Basic Rules

```gleam
// Token reference (automatically converted to/from string)
grammar.token("Number")

// Typed token with built-in converter
grammar.int_token("Number")     // Number token → Int
grammar.float_token("Number")   // Number token → Float
grammar.string_token("String")  // String token → String

// Keyword (exact string match)
grammar.keyword("let")

// Rule reference (recursive)
grammar.ref("Expr")

// Sequence
grammar.seq([grammar.ref("Term"), grammar.token("Plus"), grammar.ref("Expr")])

// Choice
grammar.choice([grammar.ref("Add"), grammar.ref("Sub")])

// Optional
grammar.opt(grammar.token("Comma"))

// Zero or more
grammar.many(grammar.ref("Arg"))

// One or more, separated
grammar.sep1(grammar.ref("Arg"), grammar.token("Comma"))
```

### Operator Rules

```gleam
// Left-associative (most common)
grammar.left_assoc(rule_name, first_symbol, operators, precedence)

// Right-associative (for exponentiation, etc.)
grammar.right_assoc(rule_name, first_symbol, operators, precedence)

// Non-associative (for comparison operators)
grammar.non_assoc(rule_name, first_symbol, operators, precedence)
```

### Operator Definition

```gleam
// Simple: constructor only (deconstructor auto-generated for simple cases)
grammar.op(
  keyword: "+",           // Token value to match
  constructor: Add,       // fn(left, right) -> AST
  precedence: 10,         // Binding strength
)

// Full: explicit deconstructor for complex cases
grammar.op_full(
  keyword: "+",
  constructor: fn(l, r) { Add(l, r) },
  deconstructor: fn(ast) { case ast { Add(l, r) -> #(l, r) } },
  precedence: 10,
)
```

### Layout Configuration (Optional)

```gleam
// Default: inline formatting
grammar.op("+", Add, 10)

// Custom layout
grammar.op_with_layout(
  "+",
  Add,
  10,
  layout: grammar.BreakAfterOperator(2),  // Break after +, indent 2
)
```

---

## Complete Examples

### Example 1: Calculator (Working)

```gleam
import calc/ast.{type Expr, Add, Sub, Mul, Div, Int}

pub fn calc_grammar() -> Grammar(Expr) {
  use g <- grammar.define

  g
  |> grammar.left_assoc("Expr", "Term", [
    grammar.op("+", Add, 10),
    grammar.op("-", Sub, 10),
  ])
  |> grammar.left_assoc("Term", "Factor", [
    grammar.op("*", Mul, 20),
    grammar.op("/", Div, 20),
  ])
  |> grammar.rule("Factor", [
    grammar.alt(grammar.int_token("Number"), fn(n) { Int(n) }),
    grammar.alt(grammar.parens("Expr"), fn(e) { e }),
  ])
}

// Usage:
let grammar = calc_grammar()
let result = grammar.parse(grammar, "1 + 2 * 3")
let source = grammar.format(grammar, result.ast)
// source = "1 + 2 * 3" (correct precedence, no extra parens!)
```

### Example 2: Lambda Calculus (Future)

```gleam
import lambda/ast.{type Expr, Var, Lam, App}

pub fn lambda_grammar() -> Grammar(Expr) {
  use g <- grammar.define

  g
  |> grammar.rule("Expr", [
    grammar.alt("Lam", fn(l) { l }),
    grammar.alt("App", fn(a) { a }),
  ])
  |> grammar.rule("Lam", [
    grammar.alt(
      grammar.seq(["\\", "Ident", ".", "Expr"]),
      fn([_, name, _, body]) { Lam(name, body) },
    ),
  ])
  |> grammar.rule("App", [
    grammar.alt(
      grammar.sep1("Atom", grammar.space),
      fn(atoms) { list.fold(atoms, App) },
    ),
  ])
  |> grammar.rule("Atom", [
    grammar.alt("Ident", fn(name) { Var(name) }),
    grammar.alt(grammar.parens("Expr"), fn(e) { e }),
  ])
}
```

---

## Implementation Architecture

### Data Structures (Updated)

```gleam
/// Unified grammar
pub type Grammar(a) {
  Grammar(
    name: String,
    start: String,
    rules: Dict(String, Rule(a)),
    tokens: List(String),
    keywords: List(String),
    operators: Dict(String, Operator(a)),
  )
}

/// Grammar rule
pub type Rule(a) {
  Rule(
    name: String,
    alternatives: List(Alternative(a)),
    precedence: Int,
  )
}

/// Alternative (one way to parse a rule)
pub type Alternative(a) {
  Alternative(
    pattern: Pattern,
    constructor: fn(List(Value(a))) -> a,
    deconstructor: Option(fn(a) -> List(Value(a))),  // For formatting
  )
}

/// Pattern (what to match)
pub type Pattern {
  TokenKind(kind: String)
  Keyword(value: String)
  Op(value: String)
  Ref(rule: String)
  Seq(patterns: List(Pattern))
  Choice(alts: List(Pattern))
  Opt(pattern: Pattern)
  Many(pattern: Pattern)
  Sep1(item: Pattern, sep: Pattern)
  Parens(rule: String)
}

/// Operator (for left/right/non-assoc)
pub type Operator(a) {
  Operator(
    keyword: String,
    constructor: fn(a, a) -> a,
    deconstructor: fn(a) -> #(a, a),  // NEW: for formatting
    precedence: Int,
    associativity: Associativity,
    layout: LayoutStyle,
  )
}

/// Value wrapper for parsed values
pub type Value(a) {
  TokenValue(Token)
  KeywordValue(Token)
  AstValue(a)
  ParensValue(List(Value(a)))
  ListValue(List(Value(a)))
}
```

### Parser Generation (Working)

```gleam
pub fn parse(g: Grammar(a), source: String) -> ParseResult(a) {
  let tokens = lexer.tokenize(source)
  let start_rule = dict.get(g.rules, g.start) |> result.unwrap

  case parse_rule(g, start_rule, tokens, 0) {
    Ok(#(ast, pos)) -> ParseResult(ast: ast, errors: [])
    Error(err) -> ParseResult(ast: panic, errors: [err])
  }
}
```

### Formatter Generation (Design)

```gleam
pub fn format(g: Grammar(a), ast: a) -> String {
  let doc = format_ast(g, ast, -1)
  formatter.render(doc, 80)
}

fn format_ast(g: Grammar(a), ast: a, parent_prec: Int) -> Doc {
  // Try to find operator for this AST (for binary ops)
  case find_operator_for_ast(g, ast) {
    Some(op) -> {
      let #(left, right) = op.deconstructor(ast)
      let left_doc = format_ast(g, left, op.precedence)
      let right_doc = format_ast(g, right, op.precedence + 1)
      format_binop(left_doc, right_doc, op.keyword, op.precedence, parent_prec, op.layout)
    }
    None -> {
      // Use rule-based formatting
      case find_rule_for_ast(g, ast) {
        Some(rule) -> format_by_rule(g, rule, ast, parent_prec)
        None -> formatter.text("<unknown>")
      }
    }
  }
}

fn format_binop(
  left: Doc,
  right: Doc,
  separator: String,
  precedence: Int,
  parent_prec: Int,
  layout: LayoutStyle,
) -> Doc {
  let inner = case layout {
    Inline -> concat([left, text(separator), right])
    BreakAfterOperator(indent) -> group(concat([left, text(separator), line(), nest(indent, right)]))
    // ... other layouts
  }
  wrap_parens(inner, precedence < parent_prec)
}
```

### Key Implementation Challenges (Updated)

1. **Extracting operands from AST**: Need deconstructors
   - ✅ **Solution**: Store `deconstructor` functions in `Operator` and `Alternative`

2. **Precedence tracking**: Both parser and formatter need precedence
   - ✅ **Solution**: Single `precedence` field used by both

3. **Token → Value conversion**: `Number` token should become `Int` automatically
   - ✅ **Solution**: Built-in converters (`int_token`, `float_token`, `string_token`)

4. **Finding operator for AST**: Runtime type inspection needed
   - ⏳ **Challenge**: Gleam doesn't have runtime type inspection
   - **Proposed Solution**: Register deconstructors in a lookup table during grammar definition

---

## API Design (Updated)

### Grammar Definition

```gleam
/// Start defining a grammar
pub fn define<A>(fn(GrammarBuilder<A>) -> Grammar<A>) -> Grammar<A>

/// Grammar builder (accumulates rules)
pub type GrammarBuilder<A>

/// Add a rule with deconstructor
pub fn rule_with_deconstructor<A>(
  builder: GrammarBuilder<A>,
  name: String,
  alternatives: List(Alternative<A>>,
) -> GrammarBuilder<A>

/// Add left-associative operator rule
pub fn left_assoc<A>(
  builder: GrammarBuilder<A>,
  name: String,
  first: String,
  operators: List<Operator<A>>,
  precedence: Int,
) -> GrammarBuilder<A>

/// Create alternative with deconstructor
pub fn alt_with_deconstructor<A>(
  pattern: Pattern,
  constructor: fn(List<Value>) -> A,
  deconstructor: fn(A) -> List<Value>,
) -> Alternative<A>
```

### Pattern Helpers (Updated)

```gleam
/// Typed token with built-in converter
pub fn int_token(kind: String) -> Pattern
pub fn float_token(kind: String) -> Pattern
pub fn string_token(kind: String) -> Pattern

/// Shorthand for token pattern
pub fn token(kind: String) -> Pattern

/// Shorthand for keyword pattern
pub fn keyword(value: String) -> Pattern

/// Shorthand for rule reference
pub fn ref(name: String) -> Pattern

/// Shorthand for parenthesized expression
pub fn parens(rule_name: String) -> Pattern

/// Shorthand for sequence
pub fn seq(patterns: List(Pattern)) -> Pattern

/// Shorthand for separated list
pub fn sep1(item: Pattern, sep: Pattern) -> Pattern
```

### Operator Helpers (Updated)

```gleam
/// Create operator (deconstructor auto-generated for simple cases)
pub fn op<A>(
  keyword: String,
  constructor: fn(A, A) -> A,
  precedence: Int,
) -> Operator<A>

/// Create operator with explicit deconstructor
pub fn op_full<A>(
  keyword: String,
  constructor: fn(A, A) -> A,
  deconstructor: fn(A) -> #(A, A),
  precedence: Int,
  associativity: Associativity,
  layout: LayoutStyle,
) -> Operator<A>
```

---

## Automatic Formatter Generation Strategy

### Approach: Deconstructor Registry

Since Gleam doesn't have runtime type inspection, we use a registry pattern:

```gleam
pub type FormatterRegistry(a) {
  FormatterRegistry(
    operators: Dict(fn(a) -> Bool, Operator(a)),  // Predicate → Operator
    rules: Dict(fn(a) -> Bool, Rule(a)),         // Predicate → Rule
  )
}
```

During grammar definition:
```gleam
pub fn op(keyword: String, constructor: fn(a, a) -> a, precedence: Int) -> Operator(a) {
  // Auto-generate deconstructor for simple binary ops
  let deconstructor = fn(ast) {
    // This won't work directly - need user to provide or use macro
    panic as "Deconstructor required for automatic formatting"
  }
  Operator(keyword, constructor, deconstructor, precedence, Left, Inline)
}
```

### Better Approach: User-Provided Deconstructors

```gleam
pub fn op<A>(
  keyword: String,
  constructor: fn(A, A) -> A,
  deconstructor: fn(A) -> #(A, A),  // User provides
  precedence: Int,
) -> Operator<A> {
  Operator(keyword, constructor, deconstructor, precedence, Left, Inline)
}

// Usage:
grammar.op("+", Add, fn(ast) { case ast { Add(l, r) -> #(l, r) } }, 10)
```

### Best Approach: Grammar Generates Both

The grammar definition builds both constructor and deconstructor:

```gleam
pub fn left_assoc<A>(
  builder: GrammarBuilder<A>,
  name: String,
  first_rule: String,
  operators: List(Operator<A>>,
  precedence: Int,
) -> GrammarBuilder<A> {
  // For each operator, store both constructor and deconstructor
  let op_alt = list.map(operators, fn(op) {
    Alternative(
      pattern: /* operator pattern */,
      constructor: op.constructor,
      deconstructor: Some(fn(ast) {
        // Use op.deconstructor if provided, else panic
        case op.deconstructor {
          Some(dec) -> [ListValue([TokenValue(op.keyword), AstValue(dec(ast).1)])]
          None -> panic as "Deconstructor required"
        }
      }),
    )
  })
  // ...
}
```

---

## Migration Path (Updated)

### Phase 1: Clean Up Current API ✅

1. ✅ Remove `ParseChild` abstraction
2. ✅ Have constructors receive typed arguments directly
3. ✅ Simplify `left_assoc` helper functions

### Phase 2: Add Declarative DSL ✅

1. ✅ Add `grammar.define` function
2. ✅ Add pattern helpers (`token`, `ref`, `parens`, etc.)
3. ✅ Add operator helpers (`op`, `left_assoc`)

### Phase 3: Manual Formatter Support ✅

1. ✅ Implement manual `format_expr` for calc example
2. ✅ Add precedence-based parenthesization
3. ✅ Add round-trip tests

### Phase 4: Automatic Formatter Generation ⏳

1. ⏳ Add `deconstructor` field to `Operator` and `Alternative`
2. ⏳ Implement `format_ast` that uses deconstructors
3. ⏳ Add typed token helpers (`int_token`, `string_token`)
4. ⏳ Update calc grammar to provide deconstructors

### Phase 5: Polish ⏳

1. ⏳ Better error messages
2. ⏳ Grammar validation (check for undefined rules, etc.)
3. ⏳ Performance optimizations

---

## Benefits (Updated)

### Before (Legacy)

```gleam
// 85+ lines of boilerplate
pub fn calc_grammar() -> Grammar(Expr) {
  grammar.new()
  |> grammar.start("Expr")
  |> grammar.with_token("Number")
  // ... lots of boilerplate
}

// Separate manual formatter (80+ lines)
fn format_expr(g: Grammar(Expr), expr: Expr, parent_prec: Int) -> Doc {
  case expr {
    Int(n) -> formatter.text(int.to_string(n))
    Add(l, r) -> grammar.format_op(g, "+", l, r, parent_prec, format_child)
    // ...
  }
}
```

### After (Current - Manual Formatter)

```gleam
// 40 lines - grammar definition
pub fn calc_grammar() -> Grammar(Expr) {
  use g <- grammar.define
  g
  |> grammar.left_assoc("Expr", "Term", [
    grammar.op("+", Add, 10),
    grammar.op("-", Sub, 10),
  ])
  |> grammar.rule("Factor", [
    grammar.alt(grammar.token_pattern("Number"), fn(values) { ... }),
    grammar.alt(grammar.parens("Expr"), fn(values) { ... }),
  ])
}

// 40 lines - manual formatter
fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  case ast {
    Int(n) -> formatter.text(int.to_string(n))
    Add(l, r) -> format_binop(format_expr(l, 10), format_expr(r, 11), " + ", 10, parent_prec)
    // ...
  }
}
```

**Total**: 80 lines (vs 165+ before) - **52% reduction**

### Future (Automatic Formatter)

```gleam
// 40 lines - grammar definition with deconstructors
pub fn calc_grammar() -> Grammar(Expr) {
  use g <- grammar.define
  g
  |> grammar.left_assoc("Expr", "Term", [
    grammar.op_full("+", Add, fn(ast) { case ast { Add(l, r) -> #(l, r) } }, 10),
    grammar.op_full("-", Sub, fn(ast) { case ast { Sub(l, r) -> #(l, r) } }, 10),
  ])
  |> grammar.rule("Factor", [
    grammar.alt(grammar.int_token("Number"), fn(n) { Int(n) }),
    grammar.alt(grammar.parens("Expr"), fn(e) { e }),
  ])
}

// 0 lines - automatically generated!
```

**Total**: 40 lines (vs 165+ before) - **76% reduction**

---

## Open Questions (Updated)

1. **How to handle deconstructors without runtime type inspection?**
   - ✅ **Answer**: User-provided deconstructors in grammar definition
   - Trade-off: More boilerplate in grammar, but type-safe

2. **How to handle token value extraction?**
   - ✅ **Answer**: Built-in converters (`int_token`, `float_token`, `string_token`)
   - Alternative: User-provided extractors in `alt`

3. **How to handle error reporting?**
   - ⏳ **Open**: Generic "parse error at position X" vs rule-specific messages
   - Proposal: Store error messages in patterns

4. **How to handle complex AST deconstruction?**
   - ⏳ **Open**: Some ASTs don't deconstruct cleanly (e.g., n-ary applications)
   - Proposal: Allow `Option(fn(a) -> List(Value(a)))` for complex cases

---

## References

- [Current Implementation](../../src/syntax/grammar.gleam)
- [Calc Example](../../src/examples/calc.gleam)
- [Implementation Summary](./unified-grammar-implementation.md)
- [Original Design](./generic-grammar-design.md)
- [Revised Design](./generic-grammar-design-revised.md)
