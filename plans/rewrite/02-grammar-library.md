# Language-Agnostic Grammar Library

## Design Goals

1. **Declarative** — Define grammar once, get parser + formatter for free
2. **Error-resilient** — Parser recovers from errors, accumulates all parse errors
3. **Span-safe** — Every AST node carries accurate source spans from lexer tokens
4. **Operator-aware** — Precedence, associativity, and layout are specified in the grammar
5. **Language-generic** — The grammar library is completely independent of Core and Tao

## Directory Structure

```
src/syntax/
├── lexer.gleam        # Tokenizer: String → List(Token)
├── span.gleam         # Source location: Span type
├── grammar.gleam      # Parser combinator DSL + grammar definitions
├── formatter.gleam    # Document algebra + layout
├── error_reporter.gleam # Parse error diagnostics
└── parser.gleam       # Generated parser API (by each language)
```

## Core Types

### Span

```gleam
pub type Span {
  Span(file: String, start_line: Int, start_col: Int, end_line: Int, end_col: Int)
}

// Helper constructors
fn span_from_token(token: Token, filename: String) -> Span
fn span_from_tokens(first: Token, last: Token, filename: String) -> Span
fn span_dummy() -> Span  // For synthesized nodes (desugaring, etc.)
```

**Design rationale:** Spans are created from actual lexer tokens during parsing. For synthesized nodes (e.g., desugarer output), `span_dummy()` is used — but the type checker and formatter can propagate spans from child nodes.

### Token

```gleam
pub type Token {
  Token(
    kind: String,      // "Integer", "Float", "String", "Name", "Op", etc.
    value: String,     // The literal text
    start: Int,        // Character offset (0-based)
    end: Int,          // Character offset (0-based)
    line: Int,         // Line number (1-based)
    column: Int,       // Column number (1-based)
  )
}
```

### Parse Error

```gleam
pub type ParseError {
  ParseError(
    span: Span,
    expected: String,  // What the parser expected
    got: String,       // What it actually found
    context: String,   // Additional context (e.g., "in expression", "at module level")
  )
}

pub type ParseResult(a) {
  ParseResult(
    ast: a,            // Partial AST (may be error nodes)
    errors: List(ParseError),  // ALL parse errors found
  )
}
```

**Key difference from current code:** `ParseResult` contains BOTH the AST (even if partial/error) AND all errors. The old code stored errors in a separate `State` or used exceptions. This makes error accumulation explicit and type-safe.

## Grammar DSL

### Grammar Structure

```gleam
pub type Grammar(a) {
  Grammar(
    name: String,
    start: String,      // Start rule name
    rules: List(Rule(a)),
    keywords: List(String),
    operators: List(#(String, Operator(a))),  // symbol → operator
  )
}

pub type Rule(a) {
  Rule(
    name: String,
    alternatives: List(Alternative(a)),
    precedence: Int,    // 0 = non-operator rule, >0 = operator rule
  )
}

pub type Alternative(a) {
  Alternative(
    pattern: Pattern(a),
    constructor: fn(List(Value(a))) -> a,
  )
}

pub type Pattern(a) {
  Token(String)
  Keyword(String)
  Op(String)
  Ref(String)        // Reference to another rule
  Seq(List(Pattern(a)))
  SeqWithLayout(List(#(Pattern(a), LayoutHint)))
  Choice(List(Pattern(a)))
  Opt(Pattern(a))
  Many(Pattern(a))
  Sep1(Pattern(a), Pattern(a))
  Parens(String)     // (rule)
  Delimited(Pattern, Pattern, Pattern, Pattern)  // (item (sep item)*)
}

pub type LayoutHint {
  SoftBreak          // Space when flat, newline+indent when broken
  HardBreak          // Always newline+indent
  Space              // Always space
  NoSeparator        // No separator
}
```

### Operator Types

```gleam
pub type OperatorKind {
  KindPrefix
  KindPostfix
  InfixLeft
  InfixRight
}

pub type PostfixPattern {
  None
  Close(String)       // Just closing token: a[i]
  Continue(String, PostfixPattern)  // a ? b : c
}

pub type Operator(a) {
  Prefix(Int, String, fn(a) -> a)
  Postfix(Int, String, fn(a) -> a)
  Infix(
    OperatorKind,
    Int,                    // precedence
    String,                 // infix_op symbol
    PostfixPattern,         // what follows rhs
    fn(a, a) -> a,          // constructor
  )
}
```

### Operator Kinds Explained

| Kind | Example | Parsing |
|------|---------|---------|
| `KindPrefix` | `-x`, `!x` | `<symbol> <expr>` |
| `KindPostfix` | `x!`, `x++` | `<expr> <symbol>` |
| `InfixLeft` | `a + b + c` → `(a + b) + c` | `lhs <op> rhs` |
| `InfixRight` | `a -> b -> c` → `a -> (b -> c)` | `lhs <op> rhs` |

### PostfixPattern Explained

```
None            → "x + y"     (nothing after rhs)
Close("]")      → "a[i]"      (just closing bracket)
Close(")")      → "f(x)"      (just closing paren)
Continue(":", None)    → "a ? b :"   (ternary separator)
Continue(":", Close("]")) → "a[b:c]"  (slice with separator + close)
```

## Parser API

### Core Functions

```gleam
/// Parse a grammar, returning partial AST + all errors
pub fn parse(grammar: Grammar(a), source: String, error_ast: a) -> ParseResult(a)

/// Parse a single rule at a given position
fn parse_rule(grammar: Grammar(a), rule: Rule(a), pos: Int) -> Result(#(a, Int), ParseError)

/// Try all alternatives for a rule (backtracking)
fn try_alternatives(grammar: Grammar(a), alternatives: List(Alternative(a)), pos: Int) -> Result(#(a, Int), ParseError)
```

### Error Recovery Strategy

The parser uses **panic recovery** at every node:
- When a pattern fails, try the next alternative
- If all alternatives fail, return a synthetic `error_ast` node with the error attached
- Continue parsing from the current position (don't backtrack)
- Accumulate all errors in `ParseResult.errors`

```gleam
/// Parse a pattern, recovering with error_ast on failure
fn parse_pattern(grammar: Grammar(a), pattern: Pattern(a), tokens: List(Token), pos: Int) -> Result(#(List(Value(a)), Int), Nil) {
  // On any error, the caller is responsible for creating the error_ast node
  // We return Nil (no match) rather than an error so alternatives can be tried
  // The top-level parse creates the ParseResult with all accumulated errors
}
```

**Why this design:** By returning `Nil` for non-match and accumulating errors at the top level, we get:
- Clean backtracking through alternatives
- No premature error reporting
- All parse errors are collected before any AST is constructed

### Position Tracking

```gleam
/// Get span for entire value list
pub fn span_from_value_list(values: List(Value(a)), filename: String) -> Span

/// Extract first token from values
pub fn first_token(values: List(Value(a))) -> Result(Token, Nil)

/// Extract last token from values (recursively)
pub fn last_token(values: List(Value(a)), filename: String) -> Span
```

## Formatter API (Document Algebra)

### Document Types

```gleam
pub type Doc {
  Empty
  Text(String)
  Line               // Breakable space (becomes " " when flat, nothing when broken)
  HardLine           // Unbreakable newline
  Group(Doc)         // Optimize: flatten if fits on one line
  Nest(Int, Doc)     // Indent by N spaces
  Concat(List(Doc))
}
```

### Layout Helpers

```gleam
/// Join documents with separator (space when flat, comma+newline when broken)
pub fn join(sep: Doc, docs: List(Doc)) -> Doc

/// Space-separated list
pub fn space_sep(docs: List(Doc)) -> Doc

/// Comma-separated list with line breaks
pub fn comma_sep(docs: List(Doc)) -> Doc

/// Wrap in parentheses/braces/brackets
pub fn parens(doc: Doc) -> Doc
pub fn braces(doc: Doc) -> Doc
pub fn brackets(doc: Doc) -> Doc
```

### Grammar-Guided Formatting

```gleam
/// Format binary operator with precedence extracted from grammar
pub fn format_binop_with_grammar(
  grammar: Grammar(a),
  format_fn: fn(a, Int, Grammar(a)) -> Doc,
  left: a,
  right: a,
  constructor_key: #(String, fn(a, a) -> a),
  parent_prec: Int,
) -> Doc
```

**Key innovation:** Precedence is defined ONCE in the grammar, then reused by the formatter. No duplication.

## Example: Core Grammar

```gleam
pub fn core_grammar() -> Grammar(CoreTerm) {
  // Operators
  let ops = [
    grammar.op("->", make_pi, 10),      // Right-associative
    grammar.op("+", make_add, 20),
    grammar.op("*", make_mul, 30),
  ]

  // Rules
  let rules = [
    grammar.rule("Term", [
      grammar.alt(grammar.ref("Var"), fn(v) { CoreVar(v.0) }),
      grammar.alt(grammar.ref("Lit"), fn(v) { CoreLit(v.0) }),
      grammar.alt(
        grammar.seq([
          grammar.keyword("-"),
          grammar.ref("Term"),
        ]),
        fn(v) { CoreLam(..., grammar.ref("Term")) },  // Lambda
      ),
      grammar.alt(
        grammar.seq([
          grammar.ref("Term"),
          grammar.op("->"),
          grammar.ref("Term"),
        ]),
        fn(v) { CoreApp(v.0, v.2) },  // Application
      ),
      // ... more alternatives
    ]),
  ]

  Grammar(
    name: "Core",
    start: "Term",
    rules: rules,
    keywords: ["fn", "let", "in", "match", "case", "type", "of"],
    operators: ops,
  )
}
```

## Example: Tao Grammar

```gleam
pub fn tao_grammar() -> Grammar(TaoExpr) {
  // Tao-specific operators
  let ops = [
    grammar.op("->", make_tao_fn, 10),
    grammar.op("+", make_tao_add, 20),
    grammar.op(".", make_field_access, 30),  // High precedence
    grammar.op(".", make_record, 40),
    grammar.op("=", make_tao_eq, 15),
    grammar.op("==", make_tao_eq, 15),
    grammar.op("|>", make_pipe, 5),
    grammar.op("::", make_cons, 25),
  ]

  // Tao has statement-level constructs (fn, let, type, import)
  // These are parsed as a separate "Stmt" rule
  let rules = [
    grammar.rule("Expr", [ ... ]),
    grammar.rule("Stmt", [
      grammar.alt(
        grammar.seq([
          grammar.keyword("fn"),
          grammar.ref("Name"),
          grammar.parens("Params"),
          grammar.opt(grammar.seq([grammar.keyword("->"), grammar.ref("Type")])),
          grammar.braces("Expr"),
        ]),
        fn(v) { TaoFnStmt(...) },
      ),
      grammar.alt(
        grammar.seq([
          grammar.keyword("let"),
          grammar.opt(grammar.keyword("mut")),
          grammar.ref("Name"),
          grammar.opt(grammar.seq([grammar.keyword(":"), grammar.ref("Type")])),
          grammar.keyword("="),
          grammar.ref("Expr"),
        ]),
        fn(v) { TaoLetStmt(...) },
      ),
      // ... more statement types
    ]),
  ]

  Grammar(
    name: "Tao",
    start: "Module",
    rules: rules,
    keywords: ["fn", "let", "mut", "in", "match", "case", "type", "of",
               "import", "as", "module", "test", "run", "comptime",
               "if", "else", "for", "while", "loop", "break", "continue", "return"],
    operators: ops,
  )
}
```

## Testing Strategy for Grammar Library

### Unit Tests (lexer_test.gleam)

```gleam
// Single tokens
should("tokenize integer literal") {
  tokenize("42") == [Token("Integer", "42", 0, 2, 1, 1)]
}

should("tokenize string with escape sequences") {
  tokenize("\"hello\\nworld\"") == [Token("String", "hello\nworld", 0, 14, 1, 1)]
}

should("tokenize operators with correct precedence") {
  tokenize("+") == [Token("Op", "+", 0, 1, 1, 1)]
}
```

### Unit Tests (grammar_test.gleam)

```gleam
// Parser combinator correctness
should("parse optional pattern") {
  parse(opt(ref("Name")), "foo") == Ok("foo")
  parse(opt(ref("Name")), "") == Ok("")
}

should("parse many pattern") {
  parse(many(ref("Name")), "foo bar baz") == ["foo", "bar", "baz"]
}

should("parse delimited list") {
  parse(delimited(LParen, Name, Comma, RParen), "(a, b, c)") == ["a", "b", "c"]
  parse(delimited(LParen, Name, Comma, RParen), "()") == []
}

// Error accumulation
should("accumulate multiple parse errors") {
  parse(grammar, "foo ; bar ; baz") ==
    ParseResult(ast: error_node, errors: [err1, err2, err3])
}

// Span accuracy
should("produce accurate spans from tokens") {
  let result = parse(grammar, "let x = 42")
  span_start(result.ast) == Span(file: "test", line: 1, col: 1)
  span_end(result.ast) == Span(file: "test", line: 1, col: 12)
}
```

### Unit Tests (formatter_test.gleam)

```gleam
// Document algebra
should("join with comma separator") {
  join(comma_sep, [Text("a"), Text("b"), Text("c")]) == "a,\nb,\nc"
}

// Grammar-guided formatting
should("wrap expression when parent has higher precedence") {
  format(Add(Lit(1), Lit(2)), parent_prec: 25) == "(1 + 2)"
}

should("not wrap when parent has lower precedence") {
  format(Add(Lit(1), Lit(2)), parent_prec: 15) == "1 + 2"
}
```

### Golden Tests (golden_test.gleam)

```gleam
// Round-trip test: parse → format → parse
should("round-trip through format") {
  let source = "let x = 42"
  let parsed = parse(grammar, source)
  let formatted = format(parsed.ast)
  let reparsed = parse(grammar, formatted)
  parsed.ast == reparsed.ast  // Structural equality
}
```
