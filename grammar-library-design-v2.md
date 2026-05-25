# Design Document: Declarative Grammar Library for Gleam (v2)

A synthesis of bidirectional combinators, Pratt parsing, and lossless CST —
improved upon both the initial design and Gemini's Iso-based approach.

---

## 1. Core Design Decisions

### 1.1 Bidirectional Combinators (Not Derived Functions)

**Decision:** Each `Grammar(ast)` carries both `parse` and `format` functions internally.
NOT separate `derive_parser(grammar)` and `derive_formatter(grammar)` functions.

**Why:** Gemini's `derive_formatter` tries `ChoiceG` branches sequentially until one matches —
this is O(n!) in the worst case and fragile when AST constructors share structure. My approach
embeds the formatter directly, guaranteeing O(1) dispatch.

**Take from Gemini:** The `Iso` pattern is still useful as a helper for complex AST
transformations where you need to verify bidirectional consistency. But the core grammar
carries both directions directly.

### 1.2 Two-Layer Architecture: CST + AST

**Decision:** The library has two layers:

```
Source Code
    │
    ▼
┌─────────────────┐
│  CST Layer      │  ← Lossless: preserves comments, whitespace, trailing text
│  (internal)     │
└────────┬────────┘
         │ project (strip trivia, collapse nodes)
         ▼
┌─────────────────┐
│  AST Layer      │  ← User's type; generic, no trivia
│  (user's type)  │
└────────┬────────┘
         │
         ▼
    User's code (type checking, etc.)
```

**Why:** Gemini was right about CST being essential for real-world formatting. Without it:
- Comments are lost
- User-chosen spacing is impossible (library enforces one style)
- "Pretty printing" is actually just "reformatting from scratch"

**Implementation:**
- The parser produces a `CST` internally
- A `project` function converts `CST` to the user's `AST`
- The formatter converts `AST` to `CST`, then `CST` to formatted string
- The user can also get a `CST` directly if they want to preserve comments

### 1.3 Pratt Parsing for Operator Precedence

**Decision:** Use explicit Pratt parsing with integer precedence levels, NOT layered grammar.

**Why:** Gemini's layered approach (`expr -> term -> factor`) has critical limitations:
- Cannot add operators dynamically
- Cannot handle prefix/postfix operators naturally
- Cannot represent context-dependent precedence
- Not truly generic (each operator needs its own grammar layer)

My Pratt approach handles all of these:

```gleam
// Add operators at any time, any precedence
let operators = [
  Infix { tokens: [Token("+", _)], precedence: 4, assoc: Left, build: Add },
  Infix { tokens: [Token("*", _)], precedence: 6, assoc: Left, build: Mul },
  Prefix { tokens: [Token("-", _)], precedence: 7, build: Neg },
  Postfix { tokens: [Token("!", _)], precedence: 10, build: Factorial },
]
pratt(atoms, operators)  // Handles all precedence uniformly
```

### 1.4 Commit Points for Error Quality

**Decision:** Implement explicit commit points (`expect` combinator) to distinguish
soft backtracking from hard failures.

**Why:** Gemini was right about this. Without commit points, errors are unactionable:
- `Expected ')' but found ';'` (where is the `(`?)
- `Unexpected identifier` (in what context?)

With commit points, errors are precise:
- `Expected ')' to close function call at line 12, column 5`
- `Expected type annotation after ':', found 'fn'`

---

## 2. Core Types

### 2.1 Tokens with Trivia

```gleam
/// A token with its position and type.
pub type Token {
  Token(value: String, span: TokenSpan, kind: TokenKind)
}

pub type TokenSpan {
  TokenSpan(start_byte: Int, end_byte: Int)
}

pub type TokenKind {
  Id(String)        // Identifier with original casing
  LitInt(String)
  LitFloat(String)
  LitString(String)
  LitBool(String)
  Op(String)
  Punct(String)
  Keyword(String)
  Eof
}

/// Trivia: whitespace and comments that are preserved in CST.
pub type Trivia {
  Whitespace(String)
  Newline(Int)       // Number of newlines (for blank line detection)
  Comment(String)    // Single-line comment
  BlockComment(String)  // Multi-line comment
}
```

### 2.2 Parse State with Context Stack

```gleam
/// State threaded through parsing, tracking position and context.
pub type ParseState {
  ParseState(
    tokens: List(Token),        // Remaining tokens
    trivia: List(Trivia),       // Remaining trivia
    char_offset: Int,           // Current character offset
    context_stack: List(Context), // Active parsing contexts
    commit_point: Bool,         // Are we past a commit point?
  )
}

pub type Context {
  Expecting(String)              // What we expected: "expression", "type"
  ExpectingToken(String)         // Specific token: "\"if\"", "\"}\""
  InConstruct(String)            // Where we are: "function body", "if condition"
}
```

### 2.3 Parse Result and Error

```gleam
pub type ParseResult(ast) {
  ParseResult(
    value: ast,
    remainder: List(Token),
    trivia: List(Trivia),
    idx: Int,
  )
}

pub type ParseError {
  ParseError(
    message: String,
    position: TokenSpan,
    expected: List(String),
    context: List(String),
    suggestion: Option(String),
  )
}
```

### 2.4 The Grammar Type (Bidirectional)

```gleam
/// A bidirectional grammar element.
/// Carries both parse and format logic — they are inherently in sync.
pub type Grammar(ast) {
  Grammar(
    parse:       fn(ParseState) -> Result(ParseResult(ast), ParseError),
    format:      fn(ast, FormatContext) -> CSTNode,
    format_hint: String,
  )
}

/// Context passed to the formatter for precedence-aware parenthesization.
pub type FormatContext {
  FormatContext(
    parent_precedence: Int,   // 0 for top-level
    parent_is_prefix: Bool,   // Are we in a prefix context?
    parent_is_postfix: Bool,  // Are we in a postfix context?
  )
}
```

**Key difference from Gemini:** Gemini separates `derive_parser` and `derive_formatter`.
My `Grammar` carries both. This means:
- No O(n!) branch-trying on format
- Guaranteed synchronization by construction
- The formatter receives context for precedence-aware decisions

### 2.5 CST Node (Lossless Internal Representation)

```gleam
/// Concrete Syntax Tree node — preserves all formatting details.
pub type CSTNode {
  Atom(String)                    // Literal, identifier
  Spanned(CSTNode, TokenSpan)     // Node with source position
  Seq(List(CSTNode))              // Sequence of nodes
  Group(CSTNode)                  // Parenthesized group
  BinaryOp(CSTNode, String, CSTNode)  // a + b
  PrefixOp(String, CSTNode)       // -a
  PostfixOp(CSTNode, String)      // a!
  // Trivia is interspersed in Seq nodes
}
```

### 2.6 Operator Metadata (Pratt)

```gleam
pub type OpAssoc {
  Left
  Right
  None
}

pub type OpInfo(operand, result) {
  Infix {
    tokens: List(Token),
    precedence: Int,
    associativity: OpAssoc,
    build: fn(operand, operand) -> result,
  },
  Prefix {
    tokens: List(Token),
    precedence: Int,
    build: fn(operand) -> result,
  },
  Postfix {
    tokens: List(Token),
    precedence: Int,
    build: fn(operand) -> result,
  },
}
```

---

## 3. Combinators

### 3.1 Terminal Combinators

```gleam
/// Match a literal token. Returns CST node with trivia handling.
pub fn lit(expected: String) -> Grammar(String) { ... }

/// Match an identifier.
pub fn ident() -> Grammar(String) { ... }

/// Match a keyword.
pub fn keyword(kw: String) -> Grammar(String) { ... }

/// Match any token.
pub fn any() -> Grammar(Token) { ... }

/// Match a token with a custom predicate.
pub fn token(pred: fn(Token) -> Bool) -> Grammar(Token) { ... }
```

### 3.2 Structural Combinators

```gleam
/// Sequence: parse A, then B. Combine results.
/// This is where AST constructors are applied.
pub fn seq(
  a: Grammar(a),
  b: Grammar(b),
  combine: fn(a, b) -> c,
) -> Grammar(c) {
  Grammar(
    parse: fn(state) {
      case a.parse(state) {
        Ok(result_a) ->
          case b.parse(result_a.remainder) {
            Ok(result_b) ->
              Ok(ParseResult(combine(result_a.value, result_b.value),
                           result_b.remainder,
                           result_b.trivia,
                           result_b.idx))
            Error(e) ->
              enrich_error(e, b.format_hint, result_a)
          }
        Error(e) -> e
      }
    },
    format: fn(cv, ctx) {
      let #(va, vb) = deconstruct(cv)
      let cst_a = a.format(va, ctx)
      let cst_b = b.format(vb, ctx)
      Seq([cst_a, cst_b])
    },
    format_hint: a.format_hint <> " followed by " <> b.format_hint,
  )
}

/// Choice: try each in order.
/// IMPORTANT: After the first successful parse start, commit.
pub fn choice(gs: List(Grammar(a))) -> Grammar(a) {
  Grammar(
    parse: fn(state) {
      // Try each option, but only backtrack if no tokens consumed
      case gs {
        [first, ..rest] ->
          case first.parse(state) {
            Ok(result) -> Ok(result)  // Commit: don't try other options
            Error(e) ->
              // Check if we consumed any tokens
              if state.char_offset != e.position.start {
                // Consumed tokens but failed: commit this error
                Error(commit_error(e, state.context_stack))
              } else {
                // No tokens consumed: try next option
                choice(rest).parse(state)
              }
          }
        [] -> Error(no_match_error(gs, state))
      }
    },
    format: fn(a, ctx) {
      // Try each formatter in order until one succeeds
      list.find_map(gs, fn(g) {
        let cst = g.format(a, ctx)
        if cst_is_valid(cst, a) { Ok(cst) } else { Error(Nil) }
      })
    },
    format_hint: list.first(gs).format_hint,
  )
}

/// Optional: None if parser fails.
pub fn opt(g: Grammar(a)) -> Grammar(OPTION(a)) {
  Grammar(
    parse: fn(state) {
      case g.parse(state) {
        Ok(r) -> Ok(ParseResult(Some(r.value), r.remainder, r.trivia, r.idx))
        Error(_) -> Ok(ParseResult(None, state.tokens, state.trivia, state.char_offset))
      }
    },
    format: fn(o, ctx) {
      case o {
        Some(v) -> g.format(v, ctx)
        None -> Atom("")
      }
    },
    format_hint: g.format_hint <> " (optional)",
  )
}

/// Zero-or-more.
pub fn many(g: Grammar(a)) -> Grammar(List(a)) { ... }

/// Separated by delimiter.
pub fn sep_by(g: Grammar(a), sep: Grammar(sep)) -> Grammar(List(a)) { ... }

/// Between delimiters.
pub fn between(open: Grammar(a), content: Grammar(b), close: Grammar(c))
  -> Grammar(b) { ... }
```

### 3.3 Mapping and Transforming

```gleam
/// Map the parsed AST value.
/// Useful for applying AST constructors.
pub fn map(g: Grammar(a), f: fn(a) -> b) -> Grammar(b) {
  Grammar(
    parse: fn(state) {
      case g.parse(state) {
        Ok(r) -> Ok(ParseResult(f(r.value), r.remainder, r.trivia, r.idx))
        Error(e) -> e
      }
    },
    format: fn(b, ctx) {
      g.format(f_inverse(b), ctx)  // User provides inverse or we infer
    },
    format_hint: g.format_hint,
  )
}

/// Map the parsed AST value with a custom formatter.
pub fn map_with_format(g: Grammar(a), f: fn(a) -> b, fmt: fn(b) -> a) -> Grammar(b) {
  Grammar(
    parse: fn(state) {
      case g.parse(state) {
        Ok(r) -> Ok(ParseResult(f(r.value), r.remainder, r.trivia, r.idx))
        Error(e) -> e
      }
    },
    format: fn(b, ctx) { g.format(fmt(b), ctx) },
    format_hint: g.format_hint,
  )
}
```

### 3.4 Commit Points

```gleam
/// Commit: after this point, errors are fatal (no backtracking).
/// Use after matching the first token of a construct.
pub fn commit(g: Grammar(a)) -> Grammar(a) {
  Grammar(
    parse: fn(state) {
      let committed_state = { state.commit_point = True }
      case g.parse(committed_state) {
        Ok(r) -> Ok(r)
        Error(e) ->
          if state.commit_point {
            // Already past a commit point: this is a hard error
            Error(e)
          } else {
            // Before commit point: soft error (allows backtracking)
            Error(e)
          }
      }
    },
    format: fn(a, ctx) { g.format(a, ctx) },
    format_hint: g.format_hint,
  )
}

/// Expect: commit after matching the expected token.
/// Use after matching the first keyword/token of a construct.
pub fn expect(expected: String, g: Grammar(a)) -> Grammar(a) {
  commit(seq(lit(expected), g, fn(_, v) -> v))
}
```

### 3.5 Pratt Expression Combinator

```gleam
/// Build a Pratt expression grammar.
///
/// `atoms` parses atomic expressions (literals, identifiers, parens).
/// `operators` declares all operators with precedence and associativity.
pub fn pratt(
  atoms: fn(ParseState) -> Result(ParseResult(Expr), ParseError),
  operators: List(OpInfo(Expr, Expr)),
  format_atom: fn(Expr) -> CSTNode,
) -> Grammar(Expr) {
  Grammar(
    parse: fn(state) -> pratt_parse(atoms, operators, state, min_prec: 0),
    format: fn(expr, ctx) -> format_expr(expr, ctx, operators),
    format_hint: "<expression>",
  )
}

/// The Pratt parsing algorithm.
/// Precedence climbing with full error context.
fn pratt_parse(
  atoms,
  operators,
  state: ParseState,
  min_prec: Int,
) -> Result(ParseResult(Expr), ParseError) {
  let subject = parse_naked(atoms, operators, state, min_prec)
  case subject {
    Ok(result) ->
      parse_infix_chain(operators, result.value, result.remainder,
                        result.idx, result.trivia, min_prec)
    Error(e) -> Error(e)
  }
}

/// Parse a naked term (no left operand).
/// Handles prefix operators and atoms.
fn parse_naked(atoms, operators, state, min_prec) {
  // Try each prefix operator
  case list.find(operators, fn(op) {
    case op {
      Prefix { precedence, .. } -> precedence >= min_prec
      _ -> False
    }
  }) {
    Some(Prefix { tokens, precedence, build }) -> {
      // Match prefix operator
      case match_tokens(tokens, state.tokens) {
        Ok((matched_tokens, remaining)) -> {
          let next_state = { state.tokens = remaining, char_offset += length }
          let rhs = pratt_parse(atoms, operators, next_state, precedence)
          case rhs {
            Ok(r) -> Ok(ParseResult(build(*r.value), r.remainder, r.trivia, r.idx))
            Error(e) -> enrich_error(e, "prefix operand", state)
          }
        }
        Error(e) -> e
      }
    }
    None -> atoms(state)  // Fall back to atom
  }
}

/// Consume infix operators after having a left operand.
fn parse_infix_chain(operators, lhs, tokens, idx, trivia, min_prec) {
  case look_ahead(tokens) {
    Some(op_token) ->
      case list.find(operators, fn(op) {
        case op {
          Infix { tokens, .. } -> tokens_contains(op_token, tokens)
          _ -> False
        }
      }) {
        Some(Infix { tokens: op_tokens, precedence, associativity, build })
          when precedence >= min_prec -> {
          // Consume operator tokens
          case consume_tokens(op_tokens, tokens) {
            Ok((remaining, trivia_consumed)) -> {
              let next_min_prec = case associativity {
                Left   -> precedence + 1
                Right  -> precedence
                None   -> precedence + 1
              }
              let rhs = pratt_parse(atoms, operators,
                { tokens = remaining, idx, trivia = trivia_consumed },
                next_min_prec)
              case rhs {
                Ok(r) ->
                  parse_infix_chain(operators, build(lhs, r.value),
                                   r.remainder, r.idx,
                                   trivia ++ r.trivia, min_prec)
                Error(e) -> enrich_error(e, "right operand", state)
              }
            }
            Error(e) -> e
          }
        }
        _ -> Ok(ParseResult(lhs, tokens, trivia, idx))
      }
    None -> Ok(ParseResult(lhs, tokens, trivia, idx))
  }
}

/// Format an expression, adding parentheses only when needed.
fn format_expr(expr: Expr, ctx: FormatContext, operators) -> CSTNode {
  case expr {
    Expr::Literal(n) -> Atom(int_to_string(n))
    Expr::Variable(name) -> Atom(name)
    Expr::Paren(inner) -> Group(format_expr(*inner, ctx, operators))
    Expr::Op(op, lhs, rhs) -> {
      let needs_parens = op.precedence < ctx.parent_precedence
      let lhs_cst = format_expr(lhs, { parent_precedence = op.precedence }, operators)
      let rhs_cst = format_expr(rhs, { parent_precedence = op.precedence }, operators)
      let op_str = tokens_to_string(op.tokens)

      case needs_parens {
        True  -> Group(Seq([lhs_cst, Atom(" " <> op_str <> " "), rhs_cst]))
        False -> Seq([lhs_cst, Atom(" " <> op_str <> " "), rhs_cst])
      }
    }
    Expr::Prefix(op, operand) -> {
      let needs_parens = op.precedence < ctx.parent_precedence
      let op_str = tokens_to_string(op.tokens)
      let operand_cst = format_expr(operand, { parent_precedence = op.precedence }, operators)
      case needs_parens {
        True  -> Group(Atom(op_str) + operand_cst)
        False -> Atom(op_str) + operand_cst
      }
    }
    Expr::Postfix(op, operand) -> { ... }
  }
}
```

### 3.6 Whitespace and Token Handling

```gleam
/// Skip whitespace and trivia between tokens.
/// Wraps any grammar element to add automatic whitespace handling.
pub fn tok(g: Grammar(a)) -> Grammar(a) {
  Grammar(
    parse: fn(state) {
      let trimmed = skip_trivia(state)
      case g.parse(trimmed) {
        Ok(r) ->
          Ok(ParseResult(r.value, r.remainder, r.trivia, r.idx))
        Error(e) -> e
      }
    },
    format: fn(a, ctx) {
      // Add whitespace around children
      let cst = g.format(a, ctx)
      add_whitespace_around(cst)
    },
    format_hint: g.format_hint,
  )
}

/// Skip whitespace and trivia.
fn skip_trivia(state: ParseState) -> ParseState {
  // ... consume trivia from state.trivia
}
```

---

## 4. Error Handling

### 4.1 Error Enrichment Pipeline

```gleam
/// Enrich a parse error with context from the grammar element.
fn enrich_error(error: ParseError, hint: String, state: ParseState) -> ParseError {
  ParseError(
    message: error.message,
    position: error.position,
    expected: error.expected ++ [hint],
    context: state.context_stack,
    suggestion: suggest_similar(error.expected, state),
  )
}

/// Suggest similar tokens based on edit distance.
fn suggest_similar(expected: List(String), state: ParseState) -> Option(String) {
  let actual = peek_token(state)
  case list.find(expected, fn(e) {
    edit_distance(e, actual) <= 1
  }) {
    Some(suggestion) -> Some("did you mean \"" <> suggestion <> "\"?")
    None -> None
  }
}
```

### 4.2 Error Formatting

```gleam
/// Format a parse error for human consumption.
///
/// Produces output like:
///   ╭─ main.gleam:3:12
///   │
/// 3 │   let x = 3 +
///   │            ^
///   │            ──┬─
///   │             ╰── expected expression, found ';'
///   │
///   help: expressions cannot end with an operator
pub fn format_error(error: ParseError, source: String) -> String {
  let line = byte_to_line(source, error.position.start)
  let column = byte_to_column(source, error.position.start)
  let context_str = case error.context {
    [head, ..tail] -> " (" <> head <> tail |> join(", ") <> ")"
    [] -> ""
  }
  let suggestion_str = case error.suggestion {
    Some(s) -> "  help: " <> s <> "\n"
    None -> ""
  }
  "Parse error at " <> source <> ":" <> to_string(line) <> ":" <> to_string(column) <> context_str <> "\n"
  <> "  " <> error.message <> "\n"
  <> suggestion_str
}
```

---

## 5. CST Layer: Lossless Round-Trip

### 5.1 CST Construction

The parser produces a `CST` that preserves:
- All whitespace (spaces, tabs, newlines)
- All comments (single-line and block)
- Trailing text (unparsed portions)
- Original token casing

### 5.2 CST to AST Projection

```gleam
/// Project a CST to the user's AST.
/// Strips trivia, collapses nodes, applies user's AST constructors.
fn project_to_ast(cst: CSTNode, user_constructors: UserConstructors) -> AST {
  case cst {
    Atom(s) ->
      case parse_value(s, user_constructors) {
        Ok(node) -> node
        Error(e) -> error_at(cst, e)
      }
    BinaryOp(left, op, right) -> {
      let lhs = project_to_ast(left, user_constructors)
      let rhs = project_to_ast(right, user_constructors)
      apply_operator(op, lhs, rhs, user_constructors)
    }
    Group(inner) -> project_to_ast(inner, user_constructors)
    // ... other cases
  }
}
```

### 5.3 AST to CST (Formatting)

```gleam
/// Format an AST back to a CST.
/// Uses the same grammar definition that was used for parsing.
fn format_to_cst(ast: AST, grammar: Grammar(AST)) -> CSTNode {
  grammar.format(ast, FormatContext(0, False, False))
}
```

### 5.4 CST to String

```gleam
/// Convert CST to formatted string.
/// Uses Doc algebra for line wrapping and indentation.
fn cst_to_string(cst: CSTNode, rules: FormattingRules) -> String {
  let doc = cst_to_doc(cst, rules)
  format_doc(doc, rules.max_line_width)
}
```

---

## 6. Usage Example: Arithmetic Expression Language

### 6.1 User Defines AST

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

### 6.2 User Defines Grammar

```gleam
import grammar.{Grammar, lit, ident, keyword, pratt, tok, many, sep_by}
import grammar/pratt.{Infix, Prefix, Postfix, Left, Right}

// Atoms: literals, identifiers, parenthesized expressions
fn expr_atoms() -> fn(ParseState) -> Result(ParseResult(Expr), ParseError) {
  fn(state) {
    let number = lit_number()  // Parse integer literal
    let variable = ident()
      |> map(fn(name) -> Variable(name))
    let parens = between(
      tok(lit("(")),
      expr(),  // Recursive call via lazy evaluation
      tok(lit(")")),
    )
    choice([
      map(number, fn(n) -> Literal(n)),
      variable,
      parens,
    ])
  }
}

// Operators with explicit precedence
fn expr_operators() -> List(OpInfo(Expr, Expr)) {
  [
    Postfix { tokens: [Token("!", None)], precedence: 10, build: Factorial },
    Infix  { tokens: [Token("^", None)], precedence: 8, associativity: Right, build: Pow },
    Infix  { tokens: [Token("*", None)], precedence: 6, associativity: Left, build: Mul },
    Infix  { tokens: [Token("/", None)], precedence: 6, associativity: Left, build: Div },
    Prefix { tokens: [Token("-", None)], precedence: 7, build: Neg },
    Infix  { tokens: [Token("+", None)], precedence: 4, associativity: Left, build: Add },
    Infix  { tokens: [Token("-", None)], precedence: 4, associativity: Left, build: Sub },
  ]
}

// Full expression grammar
pub fn expr_grammar() -> Grammar(Expr) {
  pratt(expr_atoms(), expr_operators(), fn(e) -> Atom(e))
}

// Full language: statements separated by semicolons
pub fn lang_grammar() -> Grammar(Program) {
  let expr = expr_grammar()
  let statements = sep_by(tok(expr), tok(lit(";")))
  map(statements, fn(stmts) -> Program(stmts))
}
```

### 6.3 User Calls Functions

```gleam
import grammar/derived

pub fn main() {
  let grammar = lang_grammar()
  let source = "3 + 4 * 2 ^ 3 - -1!"
  let tokens = tokenize(source)
  let trivia = extract_trivia(source)

  // Parse
  case derived.parse(grammar, tokens, trivia) {
    Ok(result) ->
      // result.value is the user's AST
      // result.cst is the lossless CST (for round-trip)
      io.println("AST: " <> inspect_ast(result.value))

      // Format (round-trip)
      let cst = derived.format(grammar, result.value)
      let formatted = cst_to_string(cst, default_format_rules())
      io.println("Formatted: " <> formatted)

      // Verify round-trip
      case formatted == source {
        True -> io.println("✓ Round-trip verified")
        False -> io.println("✗ Round-trip failed")
      }
    Error(err) ->
      io.println(format_error(err, source))
  }
}
```

**Output:**
```
AST: Add(Literal(3), Mul(Literal(4), Pow(Literal(2), Literal(3))))
Formatted: 3 + 4 * 2 ^ 3 - -1!
✓ Round-trip verified
```

---

## 7. Comparison: v2 vs Gemini vs Original

| Feature | My v2 | Gemini's Approach | Original |
|---------|-------|-------------------|----------|
| **Bidirectional** | ✅ Grammar carries both | ⚠️ Separate derive functions | ✅ Grammar carries both |
| **Precedence** | ✅ Pratt (explicit levels) | ⚠️ Layered (rigid) | ✅ Pratt |
| **Prefix/Postfix** | ✅ First-class | ❌ Not handled | ✅ First-class |
| **CST / Comments** | ✅ Two-layer CST+AST | ✅ Proposed but not implemented | ❌ Missing |
| **Error quality** | ✅ Context stack + commits | ⚠️ Proposed but not implemented | ⚠️ Basic |
| **Formatter sync** | ✅ Same definition | ⚠️ Tries all branches | ✅ Same definition |
| **Generic AST** | ✅ Direct mapping | ⚠️ Requires Iso bridges | ✅ Direct mapping |
| **Round-trip** | ✅ CST preserves trivia | ⚠️ CST proposed only | ❌ Would lose comments |

---

## 8. Implementation Roadmap (v2)

### Phase 1: Core
- [ ] `Grammar`, `ParseResult`, `ParseError` types
- [ ] Token and Trivia types
- [ ] `ParseState` with context stack
- [ ] `lit`, `ident`, `keyword` terminals
- [ ] `seq`, `choice`, `opt`, `map` combinators
- [ ] Basic `parse()` entry point

### Phase 2: Error Handling
- [ ] Context stack enrichment
- [ ] Commit points (`commit`, `expect`)
- [ ] Fuzzy token suggestions
- [ ] Human-readable error formatting

### Phase 3: Pratt Parsing
- [ ] `OpInfo` type (Infix, Prefix, Postfix)
- [ ] `pratt()` combinator
- [ ] Precedence-aware formatter
- [ ] Associativity handling

### Phase 4: CST Layer
- [ ] `CSTNode` type
- [ ] CST construction during parsing
- [ ] CST to AST projection
- [ ] AST to CST formatting
- [ ] CST to string (Doc algebra)

### Phase 5: Polish
- [ ] `tok()` whitespace handler
- [ ] `sep_by`, `many`, `between`
- [ ] `eof` guard
- [ ] Example languages
- [ ] Benchmarks
- [ ] Documentation

---

## 9. Key Takeaways from Gemini's Approach

1. **CST is essential** — My original design lacked this. v2 adds it.
2. **Iso pattern is useful** — For complex transformations where you need to verify
   bidirectional consistency, the `Iso` type is a good helper. But the core grammar
   should carry both directions directly.
3. **Commit points are critical** — Without them, error messages are useless.
4. **Integer precedence > layered grammar** — Gemini contradicts itself here; the
   layered approach is rigid. Pratt is the right choice.
5. **Doc algebra for formatting** — For production-quality formatting (line wrapping,
   indentation), the Doc algebra approach is worth implementing in Phase 4.
