# Grammar DSL Specification

> **Goal**: Declarative, type-safe grammar definition with minimal boilerplate
> **Status**: ✅ Complete and tested (37 tests passing)
> **Date**: March 2025

---

## Status

### What's Working

- Grammar type parameterized by AST type (`Grammar(a)`)
- `Alternative` with constructor, deconstructor (stub), and formatter
- Pattern types: `TokenKind`, `Keyword`, `Ref`, `Seq`, `SeqWithLayout`, `Choice`, `Opt`, `Many`, `Sep1`, `Parens`
- Operator types with precedence, associativity, layout
- Grammar builder API: `define`, `name`, `start`, `token`, `keyword`, `rule`, `left_assoc`, `right_assoc`
- Pattern helpers: `token_pattern`, `keyword_pattern`, `ref`, `seq`, `seq_with_layout`, `parens`
- Layout hints: `SoftBreak`, `HardBreak`, `Space`, `NoSeparator`
- Operator layouts: `default_op_layout`, `break_before_op_layout`
- Position helpers: `span_from_values`, `span_from_token`, `span_from_tokens`
- Calculator example working with +, -, *, /
- Full source location tracking (line, column)

### What's Pending

- **Deconstructor implementation** - Currently panics with `"Deconstructor not implemented"`
  - Needed for automatic formatter generation
  - Manual formatters work fine for now
- **Automatic formatter generation** - Each language implements manual formatters
- **Core language grammar** - Need to define grammar for core language Term variants

### Implementation Details

**File**: `src/syntax/grammar.gleam` (~786 lines)

**Key Types**:
- `Grammar(a)` - Parameterized grammar
- `Alternative(a)` - Pattern + constructor + deconstructor + formatter
- `Pattern` - Token, Keyword, Ref, Seq, Choice, etc.
- `Operator(a)` - Keyword + constructor + precedence + layout
- `Value(a)` - TokenValue, KeywordValue, AstValue, ParensValue, ListValue
- `Span` - Source location with file, start_line, start_col, end_line, end_col

**Key Functions**:
- `define()` - Start grammar definition
- `left_assoc()` - Left-associative operator rules
- `right_assoc()` - Right-associative operator rules
- `parse()` - Parse source with grammar (returns `ParseResult(a)`)
- `format()` - Format AST (language-specific)
- `span_from_values()` - Extract span from parsed values
- `span_from_token()` - Create span from single token
- `span_from_tokens()` - Create span covering multiple tokens

### Related

- See **[01-overview.md](./01-overview.md)** for overall implementation status
- See **[03-parser-library.md](./03-parser-library.md)** for parser details
- See **[04-formatter-library.md](./04-formatter-library.md)** for formatter details
- See **[05-source-location-tracking.md](./05-source-location-tracking.md)** for position tracking
- See **[../../syntax-library.md](../../syntax-library.md)** for user-facing docs

---

## Core Types

```gleam
/// Unified grammar parameterized by AST type
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
    deconstructor: Option(fn(a) -> List(Value(a))),
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
    deconstructor: fn(a) -> #(a, a),
    precedence: Int,
    associativity: Associativity,
    layout: LayoutStyle,
  )
}

pub type Associativity {
  Left
  Right
  NonAssoc
}

pub type LayoutStyle {
  Inline
  BreakAfterOperator(indent: Int)
  BreakBeforeOperator(indent: Int)
  Block(open: String, close: String, indent: Int)
}
```

---

## Grammar Definition API

### Basic Structure

```gleam
pub fn calc_grammar() -> Grammar(Expr) {
  use g <- grammar.define

  g
  |> grammar.left_assoc("Expr", "Term", [
    grammar.op("+", Add, 10),
    grammar.op("-", Sub, 10),
  ])
  |> grammar.rule("Factor", [
    grammar.alt(grammar.int_token("Number"), fn(n) { Int(n) }),
    grammar.alt(grammar.parens("Expr"), fn(e) { e }),
  ])
}
```

### Grammar Construction

```gleam
/// Start defining a grammar
pub fn define<A>(fn(GrammarBuilder<A>) -> Grammar<A>) -> Grammar<A>

/// Set grammar name
pub fn name(builder: GrammarBuilder<A>, name: String) -> GrammarBuilder<A>

/// Set start rule
pub fn start(builder: GrammarBuilder<A>, rule: String) -> GrammarBuilder<A>

/// Add token kind
pub fn token(builder: GrammarBuilder<A>, kind: String) -> GrammarBuilder<A>

/// Add keyword
pub fn keyword(builder: GrammarBuilder<A>, value: String) -> GrammarBuilder<A>
```

### Rule Definition

```gleam
/// Add a basic rule
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
  operators: List(Operator<A>>,
  precedence: Int,
) -> GrammarBuilder<A>

/// Add right-associative operator rule
pub fn right_assoc<A>(
  builder: GrammarBuilder<A>,
  name: String,
  first: String,
  operators: List(Operator<A>>,
  precedence: Int,
) -> GrammarBuilder<A>

/// Add non-associative operator rule
pub fn non_assoc<A>(
  builder: GrammarBuilder<A>,
  name: String,
  first: String,
  operators: List(Operator<A>>,
  precedence: Int,
) -> GrammarBuilder<A>
```

### Pattern Helpers

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

/// Shorthand for choice
pub fn choice(alternatives: List(Pattern)) -> Pattern

/// Shorthand for optional
pub fn opt(pattern: Pattern) -> Pattern

/// Shorthand for zero or more
pub fn many(pattern: Pattern) -> Pattern

/// Shorthand for one or more, separated
pub fn sep1(item: Pattern, sep: Pattern) -> Pattern
```

### Alternative Helpers

```gleam
/// Create alternative
pub fn alt<A>(
  pattern: Pattern,
  constructor: fn(List(Value)) -> A,
) -> Alternative<A>

/// Create alternative with deconstructor
pub fn alt_with_deconstructor<A>(
  pattern: Pattern,
  constructor: fn(List<Value>) -> A,
  deconstructor: fn(A) -> List<Value>,
) -> Alternative<A>
```

### Operator Helpers

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
) -> Operator<A>

/// Create operator with layout
pub fn op_with_layout<A>(
  keyword: String,
  constructor: fn(A, A) -> A,
  precedence: Int,
  layout: LayoutStyle,
) -> Operator<A>
```

---

## Pattern Types

### Terminals

```gleam
// Token kind (matches any token of that kind)
grammar.token("Number")
grammar.token("Ident")
grammar.token("Operator")

// Typed tokens (with built-in converters)
grammar.int_token("Number")     // Number token → Int
grammar.float_token("Number")   // Number token → Float
grammar.string_token("String")  // String token → String

// Keyword (exact string match)
grammar.keyword("let")
grammar.keyword("fn")
grammar.keyword("if")

// Operator (exact value match)
grammar.op("+", Add, 10)
grammar.op("=>", Arrow, 5)
```

### Non-Terminals

```gleam
// Rule reference (recursive)
grammar.ref("Expr")
grammar.ref("Statement")

// Parenthesized expression (special handling)
grammar.parens("Expr")  // Matches "( Expr )"
```

### Combinators

```gleam
// Sequence (all must match in order)
grammar.seq([
  grammar.keyword("let"),
  grammar.ref("Pattern"),
  grammar.token("Equal"),
  grammar.ref("Expr"),
])

// Choice (first match wins)
grammar.choice([
  grammar.ref("Add"),
  grammar.ref("Sub"),
  grammar.ref("Term"),
])

// Optional (0 or 1)
grammar.opt(grammar.token("Comma"))

// Zero or more
grammar.many(grammar.ref("Argument"))

// One or more, separated
grammar.sep1(grammar.ref("Argument"), grammar.token("Comma"))
```

---

## Operator Definitions

### Simple Operator

```gleam
grammar.op("+", Add, 10)
```

For simple binary ops, deconstructor is auto-generated.

### Full Operator

```gleam
grammar.op_full(
  "+",
  fn(l, r) { Add(l, r) },
  fn(ast) { case ast { Add(l, r) -> #(l, r) } },
  10,
)
```

Use when auto-generation doesn't work.

### Operator with Layout

```gleam
grammar.op_with_layout(
  "+",
  Add,
  10,
  grammar.BreakAfterOperator(2),  // Break after +, indent 2
)
```

### Layout Styles

```gleam
// Inline (default): "1 + 2"
grammar.Inline

// Break after operator: "1 +\n  2"
grammar.BreakAfterOperator(2)

// Break before operator: "1\n  + 2"
grammar.BreakBeforeOperator(2)

// Block: "{\n  field1,\n  field2\n}"
grammar.Block("{", "}", 2)
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
    grammar.alt(grammar.int_token("Number"), fn(n) { Int(n) }),
    grammar.alt(grammar.parens("Expr"), fn(e) { e }),
  ])
}
```

### Example 2: Lambda Calculus

```gleam
import lambda/ast.{type Expr, Var, Lam, App}

pub fn lambda_grammar() -> Grammar(Expr) {
  use g <- grammar.define

  g
  |> grammar.rule("Expr", [
    grammar.alt(grammar.ref("Lam"), fn(l) { l }),
    grammar.alt(grammar.ref("App"), fn(a) { a }),
  ])
  |> grammar.rule("Lam", [
    grammar.alt(
      grammar.seq([
        grammar.token("Backslash"),
        grammar.token("Ident"),
        grammar.token("Dot"),
        grammar.ref("Expr"),
      ]),
      fn([_, name, _, body]) { Lam(name, body) },
    ),
  ])
  |> grammar.rule("App", [
    grammar.alt(
      grammar.sep1(grammar.ref("Atom"), grammar.space),
      fn(atoms) { list.fold(atoms, App) },
    ),
  ])
  |> grammar.rule("Atom", [
    grammar.alt(grammar.token("Ident"), fn(name) { Var(name) }),
    grammar.alt(grammar.parens("Expr"), fn(e) { e }),
  ])
}
```

### Example 3: Let-Language with Records

```gleam
import lang/ast.{type Expr, Let, Record, Field}

pub fn lang_grammar() -> Grammar(Expr) {
  use g <- grammar.define

  g
  |> grammar.rule("Expr", [
    grammar.alt(grammar.ref("Let"), fn(l) { l }),
    grammar.alt(grammar.ref("Record"), fn(r) { r }),
    grammar.alt(grammar.ref("BinOp"), fn(b) { b }),
  ])
  |> grammar.rule("Let", [
    grammar.alt(
      grammar.seq([
        grammar.keyword("let"),
        grammar.token("Ident"),
        grammar.token("Equal"),
        grammar.ref("Expr"),
        grammar.keyword("in"),
        grammar.ref("Expr"),
      ]),
      fn([_, name, _, value, _, body]) { Let(name, value, body) },
    ),
  ])
  |> grammar.rule("Record", [
    grammar.alt(
      grammar.seq([
        grammar.token("LBrace"),
        grammar.sep1(grammar.ref("Field"), grammar.token("Comma")),
        grammar.token("RBrace"),
      ]),
      fn([_, fields, _]) { Record(fields) },
    ),
  ])
  |> grammar.rule("Field", [
    grammar.alt(
      grammar.seq([
        grammar.token("Ident"),
        grammar.token("Colon"),
        grammar.ref("Expr"),
      ]),
      fn([name, _, value]) { Field(name, value) },
    ),
  ])
}
```

---

## Value Types

```gleam
pub type Value(a) {
  TokenValue(Token)
  KeywordValue(Token)
  AstValue(a)
  ParensValue(List(Value(a)))
  ListValue(List(Value(a)))
}
```

### Constructor Examples

```gleam
// Simple token → value
grammar.alt(grammar.int_token("Number"), fn(n) { Int(n) })

// Parenthesized expression → unwrap
grammar.alt(grammar.parens("Expr"), fn(e) { e })

// Sequence → extract from list
grammar.alt(
  grammar.seq([
    grammar.keyword("let"),
    grammar.token("Ident"),
    grammar.token("Equal"),
    grammar.ref("Expr"),
  ]),
  fn([_, name, _, value]) { Let(name, value) },
)

// Fold list → build n-ary structure
grammar.alt(
  grammar.sep1(grammar.ref("Arg"), grammar.token("Comma")),
  fn(args) { list.fold(args, App) },
)
```

---

## Design Decisions

### 1. Deconstructors for Formatting

**Problem**: Formatter needs to extract operands from AST.

**Solution**: Store deconstructors in `Operator` and `Alternative`:

```gleam
pub type Operator(a) {
  Operator(
    // ...
    deconstructor: fn(a) -> #(a, a),
  )
}
```

### 2. Typed Tokens

**Problem**: `Number` token → `Int` conversion is repetitive.

**Solution**: Built-in converters:

```gleam
grammar.int_token("Number")     // Automatically parses to Int
grammar.float_token("Number")   // Automatically parses to Float
```

### 3. Operator Registry

**Problem**: Need to lookup operator by keyword for formatting.

**Solution**: Store operators in `Grammar.operators` dict:

```gleam
pub type Grammar(a) {
  Grammar(
    // ...
    operators: Dict(String, Operator(a)),
  )
}
```

### 4. Layout in Grammar

**Problem**: Formatting rules duplicated in grammar and formatter.

**Solution**: Store layout metadata in grammar:

```gleam
pub type Operator(a) {
  Operator(
    // ...
    layout: LayoutStyle,
  )
}
```

---

## Trade-offs

### Pros ✅

1. **Declarative**: Describe syntax, not parsing mechanics
2. **Type-Safe**: Grammar parameterized by AST type
3. **Minimal Boilerplate**: Operator helpers reduce repetition
4. **Bidirectional**: Same grammar for parsing and formatting
5. **Extensible**: Custom constructors for complex cases

### Cons ❌

1. **Deconstructors Required**: Need explicit deconstructors for formatting
2. **Runtime Lookup**: Dict lookup for operators (minor cost)
3. **Pattern Match Still Needed**: Formatter still needs `case ast {}`

---

## See Also

- [Parser Library](./03-parser-library.md)
- [Formatter Library](./04-formatter-library.md)
- [Implementation Plan](./05-implementation-plan.md)
