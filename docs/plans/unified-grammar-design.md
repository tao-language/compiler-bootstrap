# Unified Grammar System Design

> **Goal**: Single source of truth for grammar that automatically generates both parser and formatter
> **Principles**: Declarative, type-safe, minimal boilerplate, intuitive
> **Status**: Design proposal

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
    ├── Parser (automatically generated)
    └── Formatter (automatically generated)
```

---

## Proposed Design

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
    grammar.alt("Number", fn(n) { Int(n) }),
    grammar.alt(parens("Expr"), fn(e) { e }),
  ])
}
```

**Key improvements:**
- No `ParseChild` pattern matching
- No manual formatter needed
- Constructor functions receive typed arguments directly
- Precedence specified once, used for both parsing and formatting

### 2. Automatic Formatter Generation

The formatter is derived from the grammar structure:

```gleam
// From the grammar definition above, this is auto-generated:
//
// format(Add(l, r)) = format(l) <> " + " <> format(r)
// format(Mul(l, r)) = format(l) <> " * " <> format(r)
// format(Int(n))    = int.to_string(n)
// format(Parens(e)) = "(" <> format(e) <> ")"
//
// With automatic precedence-based parenthesization!
```

### 3. Type-Safe Constructors

Instead of `fn(List(ParseChild(a))) -> a`, constructors receive typed arguments:

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
grammar.op(
  keyword: "+",           // Token value to match
  constructor: Add,       // fn(left, right) -> AST
  precedence: 10,         // Binding strength
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

### Example 1: Calculator

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
    grammar.alt("Number", fn(n) { Int(n) }),
    grammar.alt(parens("Expr"), fn(e) { e }),
  ])
}

// Usage:
let grammar = calc_grammar()
let result = grammar.parse(grammar, "1 + 2 * 3")
let source = grammar.format(grammar, result.ast)
// source = "1 + 2 * 3" (correct precedence, no extra parens!)
```

### Example 2: Lambda Calculus

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
    grammar.alt(parens("Expr"), fn(e) { e }),
  ])
}

// Usage:
// Parse: "\\x. \\y. x y" → Lam("x", Lam("y", App(Var("x"), Var("y"))))
// Format: Lam("x", Lam("y", App(Var("x"), Var("y")))) → "\\x. \\y. x y"
```

### Example 3: Let-Language with Types

```gleam
import lang/ast.{type Expr, type Type, Let, Var, Lam, Ann, Int, Arrow}

pub fn lang_grammar() -> Grammar(Expr) {
  use g <- grammar.define

  g
  |> grammar.rule("Expr", [
    grammar.alt(
      grammar.seq(["let", "Ident", "=", "Expr", "in", "Expr"]),
      fn([_, name, _, bind, _, body]) { Let(name, bind, body) },
    ),
    grammar.alt("LamExpr", fn(l) { l }),
    grammar.alt("IfExpr", fn(i) { i }),
    grammar.alt("BinOp", fn(b) { b }),
  ])
  |> grammar.rule("LamExpr", [
    grammar.alt(
      grammar.seq(["\\", "Ident", ":", "Type", "->", "Expr"]),
      fn([_, name, _, ty, _, body]) { Lam(name, Ann(ty), body) },
    ),
  ])
  |> grammar.left_assoc("BinOp", "Primary", [
    grammar.op("+", Add, 10),
    grammar.op("*", Mul, 20),
  ])
  |> grammar.rule("Primary", [
    grammar.alt("Number", fn(n) { Int(n) }),
    grammar.alt("Ident", fn(name) { Var(name) }),
    grammar.alt(parens("Expr"), fn(e) { e }),
  ])
  |> grammar.rule("Type", [
    grammar.alt("IntType", fn(_) { Int }),
    grammar.alt(
      grammar.seq(["Type", "->", "Type"]),
      fn([l, _, r]) { Arrow(l, r) },
    ),
  ])
}
```

---

## Implementation Architecture

### Data Structures

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
    constructor: fn(List(Value)) -> a,
  )
}

/// Pattern (what to match)
pub type Pattern {
  TokenPattern(kind: String)
  KeywordPattern(value: String)
  RefPattern(rule: String)
  SeqPattern(patterns: List(Pattern))
  ChoicePattern(alts: List(Pattern))
  OptPattern(pattern: Pattern)
  ManyPattern(pattern: Pattern)
  Sep1Pattern(item: Pattern, sep: Pattern)
  ParensPattern(pattern: Pattern)  // Special handling for parens
}

/// Operator (for left/right/non-assoc)
pub type Operator(a) {
  Operator(
    keyword: String,
    constructor: fn(a, a) -> a,
    precedence: Int,
    associativity: Associativity,
  )
}
```

### Parser Generation

The parser is generated from the grammar:

```gleam
pub fn parse(g: Grammar(a), source: String) -> ParseResult(a) {
  let tokens = lexer.tokenize(source)
  let start_rule = dict.get(g.rules, g.start) |> result.unwrap

  case parse_rule(g, start_rule, tokens, 0) {
    Ok(#(ast, pos)) -> ParseResult(ast: ast, errors: [])
    Error(err) -> ParseResult(ast: panic, errors: [err])
  }
}

fn parse_rule(g: Grammar(a), rule: Rule(a), tokens: List(Token), pos: Int) {
  // Try each alternative
  case rule.alternatives {
    [alt, ..rest] -> {
      case parse_pattern(g, alt.pattern, tokens, pos) {
        Ok(#(values, new_pos)) -> {
          // Apply constructor to parsed values
          let ast = alt.constructor(values)
          Ok(#(ast, new_pos))
        }
        Error(_) -> parse_rule(g, Rule(..rule, alternatives: rest), tokens, pos)
      }
    }
    [] -> Error(Nil)
  }
}
```

### Formatter Generation

The formatter is also generated from the grammar:

```gleam
pub fn format(g: Grammar(a), ast: a) -> String {
  let doc = format_ast(g, ast, -1)
  formatter.render(doc, 80)
}

fn format_ast(g: Grammar(a), ast: a, parent_prec: Int) -> Doc {
  // Use operator info for binary ops
  case find_operator_for_ast(g, ast) {
    Some(op) -> {
      let #(left, right) = extract_operands(ast)
      let left_doc = format_ast(g, left, op.precedence)
      let right_doc = format_ast(g, right, op.precedence + 1)
      format_binop(left_doc, right_doc, op.keyword, op.precedence, parent_prec)
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
```

### Key Implementation Challenges

1. **Extracting operands from AST**: Need a way to deconstruct AST for formatting
   - Solution: Store deconstructor functions in `Operator` and `Alternative`

2. **Precedence tracking**: Both parser and formatter need precedence
   - Solution: Single `precedence` field used by both

3. **Token → Value conversion**: `Number` token should become `Int` automatically
   - Solution: Built-in converters for common token types

---

## API Design

### Grammar Definition

```gleam
/// Start defining a grammar
pub fn define<A>(fn(GrammarBuilder<A>) -> Grammar<A>) -> Grammar<A>

/// Grammar builder (accumulates rules)
pub type GrammarBuilder<A>

/// Add a rule
pub fn rule<A>(
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

/// Create alternative
pub fn alt<A>(
  pattern: Pattern,
  constructor: fn(List<Value>) -> A,
) -> Alternative<A>
```

### Pattern Helpers

```gleam
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

### Operator Helpers

```gleam
/// Create operator
pub fn op<A>(
  keyword: String,
  constructor: fn(A, A) -> A,
  precedence: Int,
) -> Operator<A>

/// Create operator with custom associativity
pub fn op_with_assoc<A>(
  keyword: String,
  constructor: fn(A, A) -> A,
  precedence: Int,
  associativity: Associativity,
) -> Operator<A>
```

---

## Migration Path

### Phase 1: Clean Up Current API

1. Remove `ParseChild` abstraction
2. Have constructors receive typed arguments directly
3. Simplify `left_assoc` helper functions

### Phase 2: Add Declarative DSL

1. Add `grammar.define` function
2. Add pattern helpers (`token`, `ref`, `parens`, etc.)
3. Add operator helpers (`op`, `left_assoc`)

### Phase 3: Automatic Formatter

1. Store deconstructors in `Operator` and `Alternative`
2. Generate formatter from grammar structure
3. Remove need for manual `format_expr` functions

### Phase 4: Polish

1. Better error messages
2. Grammar validation (check for undefined rules, etc.)
3. Performance optimizations

---

## Benefits

### Before (Current)

```gleam
pub fn calc_grammar() -> Grammar(Expr) {
  grammar.new()
  |> grammar.start("Expr")
  |> grammar.with_token("Number")
  |> grammar.with_token("Operator")
  |> grammar.with_token("LParen")
  |> grammar.with_token("RParen")
  |> grammar.left_assoc(
    "Expr",
    grammar.ref("Term"),
    [
      grammar.op(
        "+",
        fn(l, r) { Add(l, r) },
        " +",
        10,
        grammar.Left,
        grammar.BreakAfterOperator(2),
      ),
    ],
    10,
  )
  |> grammar.left_assoc(
    "Term",
    grammar.ref("Factor"),
    [
      grammar.op(
        "*",
        fn(l, r) { Mul(l, r) },
        " *",
        20,
        grammar.Left,
        grammar.BreakAfterOperator(2),
      ),
    ],
    20,
  )
  |> grammar.rule(
    "Factor",
    grammar.choice([
      grammar.token("Number"),
      grammar.seq([
        grammar.token("LParen"),
        grammar.ref("Expr"),
        grammar.token("RParen"),
      ]),
    ]),
    fn(children) {
      case children {
        [ChildToken(token)] -> Int(int.parse(token.value) |> result.unwrap(0))
        [_, ChildAST(expr), _] -> expr
        _ -> panic as "Invalid factor"
      }
    },
    30,
    grammar.TemplateSeq([]),
  )
}

// Separate formatter (manual, error-prone):
fn format_expr(g: Grammar(Expr), expr: Expr, parent_prec: Int) -> Doc {
  case expr {
    Int(n) -> formatter.text(int.to_string(n))
    Add(l, r) -> grammar.format_op(g, "+", l, r, parent_prec, format_child)
    Mul(l, r) -> grammar.format_op(g, "*", l, r, parent_prec, format_child)
  }
}
```

### After (Proposed)

```gleam
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
    grammar.alt("Number", fn(n) { Int(n) }),
    grammar.alt(parens("Expr"), fn(e) { e }),
  ])
}

// No manual formatter needed - automatically generated!
```

**Lines of code**: 85 → 15 (82% reduction)
**Cognitive load**: High (understand ParseChild, constructors, formatters) → Low (just declare grammar)
**Maintainability**: Low (changes in multiple places) → High (single source of truth)

---

## Open Questions

1. **How to handle custom formatting?**
   - Option A: Allow `format_fn` override in `alt`
   - Option B: Post-process generated formatter
   - Option C: Accept some manual formatting for edge cases

2. **How to handle token value extraction?**
   - Option A: Built-in converters (Number → Int, String → String, etc.)
   - Option B: User-provided extractors in `alt`
   - Option C: Both (built-ins with override)

3. **How to handle error reporting?**
   - Option A: Generic "parse error at position X"
   - Option B: Rule-specific error messages
   - Option C: Expected token suggestions

---

## References

- [Current Implementation](../../src/grammar.gleam)
- [Calc Example](../../src/calc/syntax.gleam)
- [Original Design](./generic-grammar-design.md)
- [Revised Design](./generic-grammar-design-revised.md)
- [Parser Combinator Plan](./parser-combinator-plan.md)
