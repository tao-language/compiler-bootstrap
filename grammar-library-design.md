# Design Document: Declarative Grammar Library for Gleam

A library that defines a language grammar in an intuitive, declarative way, then derives both a parser and a formatter as generic functions over a user-defined AST.

## 1. Design Principles

### 1.1 Bidirectional Combinators (FormatParser Pattern)

The core insight from FormatParser (Haskell): parsing and formatting are inverse operations
that share the same structural information. Each grammar element is **bidirectional** — it
carries both a parse function and a format function. This guarantees they stay in sync
automatically, because they are constructed from the same source.

```
Grammar(ast) {
  parse:  List(Token) -> Result(ast, ParseError)
  format: ast -> List(Token)
}
```

**Why this over separate grammar + formatter?**
- No code generation or macros needed
- The formatter is a first-class function, not a generated artifact
- Changing a grammar element's format logic is as simple as passing a different `format` fn
- Both functions share the same structure, so they're inherently consistent

### 1.2 Pratt Parsing for Operator Precedence

Pratt (Top-Down Operator Precedence) parsing is the gold standard for operator precedence:
- Precedence and associativity are **explicitly declared** per operator, not implicit in grammar structure
- Handles prefix, infix, postfix, and mixfix operators uniformly
- No grammar obfuscation needed (no `expr = term (("+" | "-") term)*` anti-pattern)
- Each operator has a numeric binding power; higher binds tighter

### 1.3 Generic Over User AST

The parser and formatter are **polymorphic functions** that operate over any AST the user
defines. The grammar describes *how* to parse/format each AST constructor. The user provides:
1. The AST type(s)
2. A tokenizer (user-defined or provided)
3. The grammar definition (combinators assembled from their AST)

### 1.4 Descriptive, Actionable Error Messages

Errors include:
- **Position** (character offset, line, column)
- **Context** (what was expected, nearby tokens)
- **Suggestions** (e.g., "did you mean `if`?", "missing `)`")
- **Recovery hints** (for partial parsing, if desired)

---

## 2. Core Types

### 2.1 Tokens

```gleam
/// A token in the input stream.
/// `span` is optional — users may provide positions or omit them.
pub type Token {
  Token(value: String, span: Option(TokenSpan))
}

pub type TokenSpan {
  TokenSpan(start: Int, end: Int)  // character offsets in original input
}

/// For richer error messages, tokens can carry semantic type info.
/// This is optional — pure token-based operation works fine too.
pub type TokenKind {
  Id
  LitInt
  LitFloat
  LitString
  LitBool
  Op(String)
  Punct(String)
  Keyword(String)
  // ...
}
```

### 2.2 Parse Result and State

```gleam
pub type ParseResult(a) {
  ParseResult(value: a, remainder: List(Token), idx: Int)
}

pub type ParseError {
  ParseError(
    message: String,
    idx: Int,              // character offset where error occurred
    expected: List(String), // what was expected (for suggestions)
    span: Option(TokenSpan),
  )
}
```

### 2.3 The Grammar Type

```gleam
/// A bidirectional grammar element.
///
/// `parse`  consumes tokens → produces an AST node.
/// `format` takes an AST node → produces formatted tokens.
/// `format_hint` returns a string hint for error messages, e.g. "\"if\" keyword"
pub type Grammar(ast) {
  Grammar(
    parse:    fn(List(Token)) -> Result(ParseResult(ast), ParseError),
    format:   fn(ast) -> List(Token),
    format_hint: String,
  )
}
```

**Key insight:** `Grammar` is polymorphic over `ast`. Every combinator constructs a new
`Grammar` where the `ast` type is determined by the combinator's logic. Gleam's monomorphization
means each combinator call instantiates its own types — this is exactly what we want.

---

## 3. Combinators

### 3.1 Terminal Combinators

```gleml
/// Match a literal token exactly.
pub fn lit(expected: String) -> Grammar(String) {
  Grammar(
    parse: fn(tokens) {
      case tokens {
        [Token(expected, span), ..rest] ->
          Ok(ParseResult(expected, rest, length(expected)))
        [Token(_, span), ..rest] ->
          Error(ParseError(
            message: "expected \"" <> expected <> "\"",
            idx: ...,
            expected: [expected],
            span,
          ))
        [] -> ...
      }
    },
    format: fn(s) -> [Token(s, None)],
    format_hint: "\"" <> expected <> "\"",
  )
}

/// Match an identifier (word character sequence).
/// Binds to a user-provided constructor for the AST.
pub fn ident() -> Grammar(String) {
  Grammar(
    parse: fn(tokens) {
      case tokens {
        [Token(v, _), ..rest] when is_identifier(v) ->
          Ok(ParseResult(v, rest, length(v)))
        ...
      }
    },
    format: fn(s) -> [Token(s, None)],
    format_hint: "<identifier>",
  )
}

/// Match any token (wildcard).
pub fn any() -> Grammar(String) { ... }

/// Match a keyword specifically.
pub fn keyword(kw: String) -> Grammar(String) { ... }
```

### 3.2 Structural Combinators

```gleam
/// Sequence: parse A, then parse B. Combine results with a function.
/// This is where AST constructors are applied.
pub fn seq(
  a: Grammar(a),
  b: Grammar(b),
  combine: fn(a, b) -> c,
) -> Grammar(c) {
  Grammar(
    parse: fn(tokens) {
      case a.parse(tokens) {
        Ok(ParseResult(va, remainder1, idx1)) ->
          case b.parse(remainder1) {
            Ok(ParseResult(vb, remainder2, idx2)) ->
              Ok(ParseResult(combine(va, vb), remainder2, idx2))
            Error(e) -> wrap_error(e, a.format_hint, idx1)
          }
        Error(e) -> e
      }
    },
    format: fn(cv) {
      let #(va, vb) = deconstruct(cv)  // user must provide this
      a.format(va) ++ b.format(vb)
    },
    format_hint: a.format_hint <> ", then " <> b.format_hint,
  )
}

/// Choice: try each parser in order, return first success.
pub fn choice(gs: List(Grammar(a))) -> Grammar(a) { ... }

/// Optional: return None if parser fails.
pub fn opt(g: Grammar(a)) -> Grammar(OPTION(a)) { ... }

/// Zero-or-more repetition.
pub fn many(g: Grammar(a)) -> Grammar(List(a)) { ... }

/// Separated by: A B A B A ...
pub fn sep_by(g: Grammar(a), sep: Grammar(sep)) -> Grammar(List(a)) { ... }

/// Between delimiters: open content close
pub fn between(open: Grammar(a), content: Grammar(b), close: Grammar(c))
  -> Grammar(b) {
  seq(seq(open, content, fn(_, b) -> b), close, fn(b, _) -> b)
}
```

### 3.3 Pratt Expression Combinator (Core Feature)

This is where operator precedence shines. The `pratt` combinator wraps an "atom" parser
with a set of operators. It returns a `Grammar(Expr)` where `Expr` is the user's expression AST.

```gleam
/// An operator in the Pratt parser.
pub type OpAssoc {
  Left
  Right
  None
}

pub type OpInfo(operand, result) {
  // Binary infix operator
  Infix {
    tokens: List(Token),   // what to match, e.g. [Token("+", _)]
    precedence: Int,       // higher = binds tighter
    associativity: OpAssoc,
    build: fn(operand, operand) -> result,
  },
  // Unary prefix operator
  Prefix {
    tokens: List(Token),
    precedence: Int,
    build: fn(operand) -> result,
  },
  // Unary postfix operator
  Postfix {
    tokens: List(Token),
    precedence: Int,
    build: fn(operand) -> result,
  },
}

/// Build a Pratt expression grammar from atoms and operators.
///
/// `atoms` is the base parser (literals, identifiers, parenthesized exprs).
/// `operators` is the full list of operators at all precedence levels.
pub fn pratt(
  atoms: Grammar(Expr),
  operators: List(OpInfo(Expr, Expr)),
) -> Grammar(Expr) {
  Grammar(
    parse: fn(tokens) -> ...  // Pratt parsing algorithm below
    format: fn(expr) -> ...   // precedence-aware formatting below
    format_hint: "<expression>",
  )
}
```

#### Pratt Parsing Algorithm

```gleam
/// The Pratt parser itself.
///
/// Strategy:
///   1. Parse a "naked" term (atom or prefix operator + term) at the given
///      minimum precedence.
///   2. If the next token is an infix operator with precedence >= min_prec,
///      parse it and its right operand at min_prec + 1.
///   3. Repeat step 2 while operators have matching precedence.
///   4. Apply associativity: if left-associative, fold; if right, nest.
fn pratt_parse(
  atoms: fn(List(Token)) -> Result(ParseResult(Expr), ParseError),
  operators: List(OpInfo(Expr, Expr)),
  tokens: List(Token),
  min_prec: Int,
) -> Result(ParseResult(Expr), ParseError) {
  let subject = parse_naked(atoms, operators, tokens, min_prec)
  case subject {
    Ok(ParseResult(lhs, rest, idx)) ->
      parse_infix_chain(operators, lhs, rest, idx, min_prec)
    Error(e) -> Error(e)
  }
}

/// Parse a term that has no left operand yet.
/// Handles prefix operators and atoms.
fn parse_naked(...) {
  // Try each prefix operator at its precedence (if >= min_prec)
  // If none match, fall back to an atom
}

/// After having the left operand, consume infix operators.
fn parse_infix_chain(operators, lhs, tokens, idx, min_prec) {
  loop {
    match look_ahead(tokens) {
      Some(op) if op.precedence >= min_prec -> {
        let rhs_prec = case op.associativity {
          Left   -> op.precedence + 1   // force left fold
          Right  -> op.precedence       // allow right nesting
          None   -> op.precedence + 1   // force non-associative
        }
        let rhs = pratt_parse(atoms, operators, tokens_after_op, rhs_prec)
        let combined = op.build(lhs, rhs.value)
        parse_infix_chain(operators, combined, rhs.remainder, rhs.idx, min_prec)
      }
      _ -> Ok(ParseResult(lhs, tokens, idx))
    }
  }
}
```

#### Pratt Formatting Algorithm (Precedence-Aware)

```gleam
/// Format an expression, adding parentheses only when needed.
///
/// `parent_prec` is the precedence of the parent operator (0 for top-level).
/// Wrap in parens if this node's operator has strictly lower precedence.
fn format_expr(expr: Expr, parent_prec: Int) -> List(Token) {
  case expr {
    Expr::Literal(n) -> [Token(int_to_string(n), None)]
    Expr::Variable(name) -> [Token(name, None)]
    Expr::Paren(inner) -> format_expr(*inner, parent_prec)
    Expr::Op(op, lhs, rhs) -> {
      let needs_parens = op.precedence < parent_prec
      let lhs_tokens = format_expr(lhs, op.precedence)
      let rhs_tokens = format_expr(rhs, op.precedence)
      let lhs_str = tokens_to_string(lhs_tokens)
      let rhs_str = tokens_to_string(rhs_tokens)
      let op_str = tokens_to_string(op.tokens)

      let wrapped = case needs_parens {
        True  -> "(" <> lhs_str <> " " <> op_str <> " " <> rhs_str <> ")"
        False -> lhs_str <> " " <> op_str <> " " <> rhs_str
      }
      string_to_tokens(wrapped)
    }
    Expr::Prefix(op, operand) -> {
      let needs_parens = op.precedence < parent_prec
      let op_str = tokens_to_string(op.tokens)
      let operand_str = format_expr(operand, op.precedence)
      ...
    }
    Expr::Postfix(op, operand) -> { ... }
  }
}
```

### 3.4 Token-Level Combinators

```gleam
/// Skip whitespace between tokens.
/// Wraps any grammar element to add whitespace handling.
pub fn tok(g: Grammar(a)) -> Grammar(a) { ... }

/// Require end of input after parsing.
pub fn eof(g: Grammar(a)) -> Grammar(a) { ... }

/// Parse a list of tokens into a single string (for error reporting).
pub fn tokens_to_string(tokens: List(Token)) -> String { ... }
```

---

## 4. Error Handling Strategy

### 4.1 Position Tracking

```gleam
/// Thread position through parsing.
/// Each parser tracks the character offset and provides it on errors.
pub type ParserState {
  ParserState(
    tokens: List(Token),
    idx: Int,          // number of tokens consumed
    char_offset: Int,  // character offset in original string
    context: List(ContextMarker),  // active parsing context
  )
}

pub type ContextMarker {
  Expecting(String)    // e.g., Expecting("expression")
  ExpectingToken(String) // e.g., ExpectingToken("operator")
}
```

### 4.2 Error Enrichment

```gleam
/// Wrap a parse error with context from a grammar element.
/// Pushes the grammar's format_hint onto the context stack.
fn enrich_error(
  error: ParseError,
  hint: String,
  tokens: List(Token),
) -> ParseError {
  ParseError(
    message: error.message <> " (expected " <> hint <> ")",
    idx: error.idx,
    expected: error.expected ++ [hint],
    span: error.span,
  )
}

/// Provide suggestions based on similar tokens.
fn suggest(similar: List(String), actual: String) -> String {
  // Fuzzy match: if actual is one edit distance from a known token,
  // suggest it. E.g., "fuc" -> "did you mean 'func'?"
}
```

### 4.3 Error Formatting

```gleam
/// Format a parse error for human consumption.
/// Produces a message like:
///   "Parse error at line 3, column 12:
///    expected \")\" but got \";\"
///    help: was an expression expected here?"
pub fn format_error(error: ParseError, source: String) -> String {
  let line = char_to_line(source, error.idx)
  let col = char_to_column(source, error.idx)
  let context = format_context(error)
  let suggestion = format_suggestion(error)
  "Parse error at line " <> to_string(line) <> ", column " <> to_string(col) <> ":\n"
  <> "  " <> error.message <> "\n"
  <> context <> "\n"
  <> suggestion
}
```

---

## 5. Usage Example: Arithmetic Expression Language

### 5.1 User Defines Their AST

```gleam
pub type Expr {
  Literal(Int)
  Variable(String)
  Add(Box<Expr>, Box<Expr>)
  Sub(Box<Expr>, Box<Expr>)
  Mul(Box<Expr>, Box<Expr>)
  Div(Box<Expr>, Box<Expr>)
  Pow(Box<Expr>, Box<Expr>)
  Neg(Box<Expr>)
  Factorial(Box<Expr>)
}
```

### 5.2 User Defines the Grammar

```gleam
import grammar.{type Grammar, lit, ident, pratt, tok, many, sep_by}
import grammar/pratt.{Infix, Prefix, Postfix, Left, Right}

// Atoms: literals, identifiers, parenthesized expressions
fn make_atom(grammar: Grammar(Expr)) -> Grammar(Expr) {
  let number = lit("number")  // user provides this from tokenizer
  let variable = ident()
    |> map(fn(name) -> Variable(name))
  let parens = between(
    lit("("),
    grammar,
    lit(")"),
  )
  choice([number, variable, parens])
}

// Operators with explicit precedence
fn make_operators() -> List(grammar/pratt.OpInfo(Expr, Expr)) {
  [
    // Postfix: factorial (highest precedence)
    Postfix {
      tokens: [Token("!", None)],
      precedence: 10,
      build: fn(e) -> Factorial(e),
    },
    // Exponentiation (right-associative)
    Infix {
      tokens: [Token("^", None)],
      precedence: 8,
      associativity: Right,
      build: fn(l, r) -> Pow(l, r),
    },
    // Multiplication and division (left-associative, same precedence)
    Infix {
      tokens: [Token("*", None)],
      precedence: 6,
      associativity: Left,
      build: fn(l, r) -> Mul(l, r),
    },
    Infix {
      tokens: [Token("/", None)],
      precedence: 6,
      associativity: Left,
      build: fn(l, r) -> Div(l, r),
    },
    // Addition and subtraction (left-associative, lowest)
    Infix {
      tokens: [Token("+", None)],
      precedence: 4,
      associativity: Left,
      build: fn(l, r) -> Add(l, r),
    },
    Infix {
      tokens: [Token("-", None)],
      precedence: 4,
      associativity: Left,
      build: fn(l, r) -> Sub(l, r),
    },
    // Unary negation (higher than subtraction)
    Prefix {
      tokens: [Token("-", None)],
      precedence: 7,
      build: fn(e) -> Neg(e),
    },
  ]
}

// The full expression grammar
pub fn expr_grammar() -> Grammar(Expr) {
  let atoms = fn(tokens) -> ...  // from make_atom
  pratt(atoms, make_operators())
}

// Full language grammar (wrapping expressions)
pub fn lang_grammar() -> Grammar(LanguageAST) {
  let expr = expr_grammar()
  let statements = sep_by(expr, lit(";"))
  map(statements, fn(stmts) -> Program(stmts))
}
```

### 5.3 User Calls Derived Functions

```gleam
import grammar/derived

pub fn main() {
  let grammar = lang_grammar()
  let tokens = tokenize("3 + 4 * 2 ^ 3 - -1!")

  // Parse
  case derived.parse(grammar, tokens) {
    Ok(ast) ->
      io.println("Parsed: " <> inspect(ast))
    Error(err) ->
      io.println(format_error(err, "3 + 4 * 2 ^ 3 - -1!"))
  }

  // Format (round-trip test)
  case derived.format(grammar, ast) {
    Ok(formatted) ->
      io.println("Formatted: " <> formatted)
    Error(err) ->
      io.println("Format error: " <> err.message)
  }
}
```

**Output for `3 + 4 * 2 ^ 3 - -1!`:**
- **Parse**: `Sub(Add(Literal(3), Mul(4, Pow(2, 3))), Neg(Factorial(Literal(1))))`
- **Format**: `3 + 4 * 2 ^ 3 - -1!` (exact round-trip)

**Output for `3 + (4 * 2) ^ 3`:**
- **Parse**: `Add(3, Pow(Mul(4, 2), 3))`
- **Format**: `3 + (4 * 2) ^ 3` (parens preserved because `Pow` at prec 8 > `Add` at prec 4
  but parens are explicit in AST)

---

## 6. Architecture Summary

```
┌─────────────────────────────────────────────────────┐
│                    User Code                         │
│  1. Define AST types (Gleam custom types)            │
│  2. Define tokenizer (user-provided)                 │
│  3. Assemble grammar from combinators                │
└──────────────────┬──────────────────────────────────┘
                   │
┌──────────────────▼──────────────────────────────────┐
│              Grammar Library                         │
│                                                      │
│  Core Types:                                         │
│    Grammar(ast)       — bidirectional combinator     │
│    ParseResult(a)     — parse outcome                │
│    ParseError         — enriched error info          │
│    OpInfo(operand, result) — Pratt operator metadata │
│                                                      │
│  Combinators:                                        │
│    lit(s)             — terminal token               │
│    ident()            — identifier token             │
│    keyword(s)         — keyword token                │
│    seq(a, b, f)       — sequence                     │
│    choice(gs)         — ordered choice               │
│    opt(g)             — optional                     │
│    many(g)            — repetition                   │
│    sep_by(g, sep)     — separated list               │
│    between(open, c, c)— delimited content            │
│    map(g, f)          — transform AST                │
│    tok(g)             — whitespace handling          │
│    eof(g)             — end-of-input guard            │
│                                                      │
│  Pratt Parser:                                       │
│    pratt(atoms, ops)  — expression grammar with      │
│                         precedence-aware parse &     │
│                         format from same definition   │
│                                                      │
│  Error Handling:                                     │
│    enrich_error       — add context to failures      │
│    format_error       — human-readable error output  │
│    suggest            — fuzzy token suggestions      │
└──────────────────┬──────────────────────────────────┘
                   │
    ┌──────────────┴──────────────┐
    ▼                             ▼
┌──────────┐               ┌──────────┐
│ parse()  │──── AST ──→   │ format() │
└──────────┘               └──────────┘
```

---

## 7. Key Design Decisions

### 7.1 Why Bidirectional Combinators Over Separate Grammar + Codegen?

| Aspect | Bidirectional Combinators | Separate Grammar + Codegen |
|--------|--------------------------|---------------------------|
| **Runtime cost** | None (functions directly) | Codegen step required |
| **Type safety** | Gleam's type system enforces consistency | Must verify generated code |
| **Customization** | User passes different format fns | Hard to customize without editing generated code |
| **Debugging** | Standard Gleam tooling | Two artifacts to maintain |
| **Learning curve** | Learn combinators (one model) | Learn DSL + codegen + AST mapping |

### 7.2 Why Pratt Over PEG for Expressions?

| Aspect | PEG Expression Rules | Pratt Parsing |
|--------|---------------------|---------------|
| **Precedence** | Implicit in rule ordering | Explicit per-operator |
| **Adding operators** | Refactor entire rule set | Add one operator entry |
| **Associativity** | Hard to express | Built-in per operator |
| **Prefix/postfix** | Extra rules needed | First-class support |
| **Readability** | "expr = term (("+"|"-"") term)*" | `Infix("+", 4, Left, Add)` |

### 7.3 Why Generic Over User AST?

- The library doesn't know or care about the AST structure
- Users can have complex ASTs with spans, comments, metadata attached
- The formatter works on the *exact* AST the user defined, no intermediate representation
- Enables round-trip parsing: `format(parse(text)) == text`

### 7.4 Whitespace Strategy

The library provides `tok(g)` to wrap any grammar element with whitespace skipping. This
gives users full control:
- `tok(lit("if"))` — skip whitespace before/after `if`
- `tok(ident())` — skip whitespace around identifiers
- For languages where whitespace is significant (Python), users simply don't use `tok()`

---

## 8. Future Extensions

### 8.1 Mixfix Operators

Operators with placeholders, like C's `expr = expr ? expr : expr` (ternary). The Pratt
combinator would extend to:

```gleam
Mixfix {
  tokens: List(Token),     // [Token("?", _), Token(":", _)]
  placeholders: List(String), // ["?", ":"]
  precedence: Int,
  build: fn(lhs, mid, rhs) -> result,
}
```

### 8.2 Formatting Rules Module

For languages where formatting is not purely structural (e.g., line wrapping, indentation),
provide a `FormattingRules` type:

```gleam
pub type FormattingRules {
  FormattingRules(
    indent: Int,              // spaces per indent level
    max_line: Int,            // max line length (for wrapping)
    wrap_before: List(String), // wrap before these operators
    trailing_newline: Bool,   // require trailing newline
  )
}
```

### 8.3 Spanned AST Support

For compilers that attach source positions to AST nodes:

```gleam
pub type Span = Span(start: Int, end: Int)

pub type GrammarWithSpan(ast) {
  GrammarWithSpan(
    parse: fn(List(Token)) -> Result(ParseResult(ast, Span), ParseError),
    format: fn(ast) -> List(Token),
  )
}
```

### 8.4 Partial Parsing / Error Recovery

For IDE-like tools that want to parse as much as possible:

```gleam
/// Parse with error recovery, returning a partial AST.
pub fn parse_recover(grammar, tokens) -> PartialParse(ast) { ... }
```

---

## 9. Comparison to Existing Approaches

| Library | Language | Bidirectional | Pratt | Generic AST | Error Quality |
|---------|----------|--------------|-------|-------------|---------------|
| **This library** | Gleam | ✅ Yes | ✅ Yes | ✅ Yes | Rich, contextual |
| FormatParser | Haskell | ✅ Yes | ❌ No | ⚠️ Limited | Moderate |
| Glindo | Gleam | ❌ No | ❌ No | ⚠️ Limited | Basic |
| chumsky | Rust | ❌ No | ✅ Yes | ✅ Yes | Good |
| pest | Rust | ❌ No | ✅ Yes | ❌ No | Good |
| Parsec | Haskell | ❌ No | ❌ No | ✅ Yes | Moderate |

---

## 10. Implementation Roadmap

### Phase 1: Core Combinators
- [ ] `Grammar`, `ParseResult`, `ParseError` types
- [ ] `lit`, `ident`, `keyword` terminal combinators
- [ ] `seq`, `choice`, `opt`, `map` structural combinators
- [ ] Basic `parse()` function
- [ ] Basic `format()` function
- [ ] Tokenizer abstraction

### Phase 2: Pratt Parsing
- [ ] `OpInfo` type (Infix, Prefix, Postfix)
- [ ] `pratt()` combinator with full Pratt algorithm
- [ ] Precedence-aware `format_expr()` formatter
- [ ] Associativity handling (left fold vs right nest)
- [ ] Comprehensive Pratt tests (precedence, associativity, round-trip)

### Phase 3: Error Handling
- [ ] Position tracking (`idx`, `span`)
- [ ] Context stack enrichment
- [ ] Token suggestion engine (fuzzy matching)
- [ ] Human-readable error formatting
- [ ] Error recovery (optional)

### Phase 4: Polish
- [ ] `tok()` whitespace handler
- [ ] `sep_by`, `many`, `between` combinators
- [ ] `eof` guard
- [ ] Example languages (arithmetic, JSON, a small DSL)
- [ ] Benchmarking
- [ ] Documentation

---

## 11. Naming Conventions

Suggested library name: **`gram`** (short, Gleam-style, "grammar")

Module structure:
```
gram/grammar.gleam    — core Grammar type and combinators
gram/pratt.gleam      — Pratt operator types and algorithm
gram/error.gleam      — error types and formatting
gram/token.gleam      — token types and tokenizer
gram/derived.gleam    — public parse() and format() entry points
```

Combinator naming: follow Gleam conventions (snake_case), consistent with Glindo's style:
- `lit`, `ident`, `keyword` — terminals
- `seq`, `choice`, `opt`, `map` — structural
- `sep_by`, `many`, `between` — repetition
- `tok`, `eof` — modifiers
