# Design Document v3: True Derivation from Grammar

The grammar encodes structure. Both parser and formatter are derived from it.
No hand-written format functions. No hand-written parse functions.

## 1. Core Insight: Grammar is Rich Enough

The key realization: a grammar definition carries **all** the information needed for
both parsing and formatting. The grammar doesn't just say "this is a sequence of X and Y" —
it says:

1. **Structure**: what the element is (sequence, choice, repetition, etc.)
2. **Terminal symbols**: what tokens to match (and emit)
3. **AST constructors**: how to build AST nodes from parsed elements
4. **Precedence**: how operators bind (for the Pratt expression grammar)

From this, we derive:
- **Parser**: consume tokens → build AST using the same structure
- **Formatter**: emit tokens from AST using the same structure in reverse

## 2. The Grammar Type

```gleam
/// A grammar rule.
/// Encodes structure + terminals + AST constructors.
/// Both parser and formatter are derived from this.
pub type Rule(ast) {
  /// Terminal: match/emit a literal token string
  Literal(String)

  /// Identifier: match/emit identifier tokens
  /// Binds to Variable(name) in the AST
  Identifier(IdentBinding)

  /// Sequence: A followed by B
  Sequence(List(Rule(ast)))

  /// Choice: try each option in order
  Choice(List(Rule(ast)))

  /// Optional: absent is valid
  Optional(Box<Rule(ast)>)

  /// Zero-or-more
  Repeat(Box<Rule(ast)>)

  /// Separated by: A sep A sep A ...
  SeparatedBy(Box<Rule(ast)>, Box<Rule(ast)>)

  /// Between delimiters: open content close
  Between(Box<Rule(ast)>, Box<Rule(ast)>, Box<Rule(ast)>)

  /// Pratt expression: atoms + operators with precedence
  Expression {
    atoms: Box<Rule(ast)>,
    operators: List(OperatorInfo(ast)),
  }

  /// Apply an AST constructor to the parsed result
  Constructor {
    constructor: fn(List(RuleResult)) -> ast,
    destructors: List(fn(ast) -> Option<RuleResult>),
    /// For formatting: how to format the result of this constructor
    format_hint: String,
  }
}

/// What an identifier binds to in the AST
pub type IdentBinding {
  /// This identifier becomes this field name in the AST constructor
  Bind(String)
}

/// Result of parsing/formatting a single rule
pub type RuleResult {
  Value(any)
  Trivia(Trivia)
  Token(Token)
}
```

## 3. Operator Info (for Pratt Expressions)

```gleam
pub type OpAssoc { Left, Right, None }

pub type OperatorInfo(ast) {
  Infix {
    /// Tokens to match (and emit)
    tokens: List(String),
    /// Binding strength (higher = tighter)
    precedence: Int,
    /// How it associates
    associativity: OpAssoc,
    /// AST constructor: infix(left, right) -> expr
    constructor: fn(ast, ast) -> ast,
  },
  Prefix {
    tokens: List(String),
    precedence: Int,
    constructor: fn(ast) -> ast,
  },
  Postfix {
    tokens: List(String),
    precedence: Int,
    constructor: fn(ast) -> ast,
  },
}
```

## 4. Derivation: Parser

```gleam
/// Derive a parser from a grammar rule.
/// parser(rule) returns a function: List(Token) -> Result(AST, ParseError)
pub fn parser(rule: Rule(ast)) -> fn(List(Token)) -> Result(ast, ParseError) {
  fn(tokens) {
    case parse_rule(rule, tokens, context_stack: []) {
      Ok((value, remainder, _trivia)) -> Ok(value)
      Error(e) -> Error(e)
    }
  }
}

/// Parse a rule against tokens.
/// Returns (parsed_value, remaining_tokens, parsed_trivia)
fn parse_rule(rule: Rule(ast), tokens, context) -> Result(#(any, List(Token), List(Trivia)), ParseError) {
  case rule {
    Literal(expected) -> {
      // Match a literal token
      case tokens {
        [Token(expected, span), ..rest] ->
          Ok((expected, rest, []))
        [Token(actual, span), .._] ->
          Error(ParseError(
            message: "expected \"" <> expected <> "\"",
            position: span,
            expected: [expected],
            context: context,
          ))
        [] ->
          Error(ParseError(
            message: "expected \"" <> expected <> "\" but reached end of input",
            position: last_position(tokens),
            expected: [expected],
            context: context,
          ))
      }
    }

    Identifier(binding) -> {
      // Match any identifier token
      case tokens {
        [Token(value, span), ..rest] if is_identifier(value) ->
          Ok((Value(value), rest, []))
        [Token(value, span), .._] ->
          Error(ParseError(
            message: "expected identifier but found \"" <> value <> "\"",
            position: span,
            expected: ["<identifier>"],
            context: context,
          ))
        [] ->
          Error(ParseError(
            message: "expected identifier but reached end of input",
            position: last_position(tokens),
            expected: ["<identifier>"],
            context: context,
          ))
      }
    }

    Sequence(rules) -> {
      // Parse each rule in sequence
      parse_sequence(rules, tokens, context)
    }

    Choice(rules) -> {
      // Try each rule in order
      parse_choice(rules, tokens, context)
    }

    Optional(inner) -> {
      case parse_rule(inner, tokens, context) {
        Ok((value, rest, trivia)) -> Ok((Option.Some(value), rest, trivia))
        Error(_) -> Ok((Option.None, tokens, []))  // Optional: success with None
      }
    }

    Repeat(inner) -> {
      // Zero-or-more
      parse_repeat(inner, tokens, context)
    }

    SeparatedBy(content, sep) -> {
      // content sep content sep content ...
      parse_separated_by(content, sep, tokens, context)
    }

    Between(open, content, close) -> {
      // open content close
      case parse_rule(open, tokens, context) {
        Ok((_, rest1, _)) ->
          case parse_rule(content, rest1, context) {
            Ok((value, rest2, _)) ->
              case parse_rule(close, rest2, context) {
                Ok((_, rest3, _)) -> Ok((value, rest3, []))
                Error(e) -> Error(e)
              }
            Error(e) -> Error(e)
          }
        Error(e) -> Error(e)
      }
    }

    Expression { atoms, operators } -> {
      // Pratt parsing
      parse_expression(atoms, operators, tokens, context)
    }

    Constructor { constructor, destructors, format_hint } -> {
      // This rule just wraps the result in an AST constructor.
      // The inner rules handle the actual parsing.
      // For derivation purposes, this is transparent — it's applied
      // after the inner rules produce their results.
      // We don't parse this directly; it's part of a Sequence or similar.
      Error(ParseError(
        message: "unexpected constructor at top level",
        position: last_position(tokens),
        expected: ["<non-constructor rule>"],
        context: context,
      ))
    }
  }
}

/// Parse a sequence of rules, collecting results.
fn parse_sequence(rules: List(Rule(ast)), tokens, context)
  -> Result(#(any, List(Token), List(Trivia)), ParseError) {
  case rules {
    [] -> Ok(([], tokens, []))
    [first, ..rest] -> {
      case parse_rule(first, tokens, context) {
        Ok((value, rest_tokens, trivia)) -> {
          case parse_sequence(rest, rest_tokens, context) {
            Ok((values, final_tokens, final_trivia)) ->
              Ok(([value, ..values], final_tokens, trivia ++ final_trivia))
            Error(e) -> Error(enrich_context(e, first, context))
          }
        }
        Error(e) -> Error(enrich_context(e, first, context))
      }
    }
  }
}

/// Parse a choice of rules, trying each in order.
fn parse_choice(rules: List(Rule(ast)), tokens, context)
  -> Result(#(any, List(Token), List(Trivia)), ParseError) {
  case rules {
    [] -> Error(ParseError(
      message: "no alternative matched",
      position: last_position(tokens),
      expected: rules.map(r -> rule_hint(r)),
      context: context,
    ))
    [first, ..rest] -> {
      case parse_rule(first, tokens, context) {
        Ok(result) -> Ok(result)
        Error(e1) -> {
          // Try remaining options
          case parse_choice(rest, tokens, context) {
            Ok(result) -> Ok(result)
            Error(e2) -> {
              // All failed: return the first error (most informative)
              Error(e1)
            }
          }
        }
      }
    }
  }
}

/// Parse zero-or-more repetitions.
fn parse_repeat(inner: Rule(ast), tokens, context)
  -> Result(#(any, List(Token), List(Trivia)), ParseError) {
  case parse_rule(inner, tokens, context) {
    Ok((value, rest, trivia)) -> {
      case parse_repeat(inner, rest, context) {
        Ok((values, final_tokens, final_trivia)) ->
          Ok(([value, ..values], final_tokens, trivia ++ final_trivia))
        Error(e) -> Error(e)
      }
    }
    Error(_) -> Ok(([], tokens, []))  // Zero repetitions is valid
  }
}

/// Parse Pratt expression with operator precedence.
fn parse_expression(atoms: Rule(ast), operators, tokens, context)
  -> Result(#(any, List(Token), List(Trivia)), ParseError) {
  parse_pratt(atoms, operators, tokens, context, min_prec: 0)
}

fn parse_pratt(atoms, operators, tokens, context, min_prec)
  -> Result(#(any, List(Token), List(Trivia)), ParseError) {
  // Parse a naked term (prefix operator + atom)
  case parse_naked(atoms, operators, tokens, context, min_prec) {
    Ok((lhs, rest, trivia)) ->
      parse_infix_chain(atoms, operators, lhs, rest, trivia, context, min_prec)
    Error(e) -> Error(e)
  }
}

fn parse_naked(atoms, operators, tokens, context, min_prec)
  -> Result(#(any, List(Token), List(Trivia)), ParseError) {
  // Try each prefix operator at its precedence
  case list.find(operators, fn(op) {
    case op {
      Prefix { tokens: op_tokens, precedence, .. } ->
        precedence >= min_prec && matches_prefix(op_tokens, tokens)
      _ -> False
    }
  }) {
    Some(Prefix { tokens: op_tokens, precedence, constructor }) -> {
      // Consume prefix operator
      case consume_tokens(op_tokens, tokens) {
        Ok((_, rest)) -> {
          let rhs = parse_pratt(atoms, operators, rest, context, precedence)
          case rhs {
            Ok((rhs_val, rhs_rest, rhs_trivia)) ->
              Ok((constructor(rhs_val), rhs_rest, rhs_trivia))
            Error(e) -> Error(e)
          }
        }
        Error(e) -> e
      }
    }
    None -> atoms_parse(atoms, tokens, context)  // Fall back to atom
  }
}

fn parse_infix_chain(atoms, operators, lhs, tokens, trivia, context, min_prec)
  -> Result(#(any, List(Token), List(Trivia)), ParseError) {
  case list.find(operators, fn(op) {
    case op {
      Infix { tokens: op_tokens, .. } ->
        matches_infix(op_tokens, tokens)
      _ -> False
    }
  }) {
    Some(Infix { tokens: op_tokens, precedence, associativity, constructor })
      when precedence >= min_prec -> {
      case consume_tokens(op_tokens, tokens) {
        Ok((_, rest)) -> {
          let next_prec = case associativity {
            Left   -> precedence + 1
            Right  -> precedence
            None   -> precedence + 1
          }
          let rhs = parse_pratt(atoms, operators, rest, context, next_prec)
          case rhs {
            Ok((rhs_val, rhs_rest, rhs_trivia)) ->
              parse_infix_chain(atoms, operators,
                              constructor(lhs, rhs_val),
                              rhs_rest, trivia ++ rhs_trivia,
                              context, min_prec)
            Error(e) -> Error(e)
          }
        }
        Error(e) -> Error(e)
      }
    }
    _ -> Ok((lhs, tokens, trivia))  // No more matching operators
  }
}
```

## 5. Derivation: Formatter

```gleam
/// Derive a formatter from a grammar rule.
/// formatter(rule) returns a function: AST -> Result(List(Token), FormatError)
pub fn formatter(rule: Rule(ast)) -> fn(ast) -> Result(List(Token), FormatError) {
  fn(node) {
    format_rule(rule, node, format_ctx: { parent_prec: 0, parent_is_prefix: False })
    |> result.map(fn(tokens, _) -> tokens)
  }
}

/// Format an AST node back into tokens using the grammar rule.
fn format_rule(rule: Rule(ast), node: ast, ctx)
  -> Result(List(Token), FormatError) {
  case rule {
    Literal(expected) -> {
      // For formatting, we just emit the literal.
      // The user is responsible for ensuring the AST state matches
      // what this literal represents.
      // In practice, Literals are terminal tokens that don't come from
      // the AST — they're structural. So we emit them unconditionally.
      Ok([Token(expected, None)])
    }

    Identifier(binding) -> {
      // Emit the identifier value from the AST.
      // This requires the AST to carry the identifier string.
      // We need to extract it from the AST somehow.
      // This is where the AST constructor/destructor pattern helps.
      extract_identifier(node, binding)
      |> result.map(fn(name) -> [Token(name, None)])
    }

    Sequence(rules) -> {
      // Format each sub-rule and concatenate.
      // For formatting, we need to destructure the AST node to extract
      // the parts that correspond to each sub-rule.
      format_sequence(rules, node, ctx)
    }

    Choice(rules) -> {
      // Try each rule's formatter until one succeeds.
      // This is the expensive part: O(n) in the number of choices.
      format_choice(rules, node, ctx)
    }

    Optional(inner) -> {
      // Check if the AST node represents the "present" case
      case is_option_some(node) {
        True -> format_rule(inner, get_option_value(node), ctx)
        False -> Ok([])  // Omit optional elements when absent
      }
    }

    Repeat(inner) -> {
      // Format each element in the list
      format_repeat(inner, node, ctx)
    }

    SeparatedBy(content, sep) -> {
      // Format content elements separated by sep
      format_separated(content, sep, node, ctx)
    }

    Between(open, content, close) -> {
      // Format: open content close
      let open_tokens = format_rule(open, get_open_value(node), ctx)
      let content_tokens = format_rule(content, get_content_value(node), ctx)
      let close_tokens = format_rule(close, get_close_value(node), ctx)
      Ok(open_tokens ++ content_tokens ++ close_tokens)
    }

    Expression { atoms, operators } -> {
      // Format an expression AST node back to tokens.
      // Uses the operator precedence to determine parenthesization.
      format_expression(node, atoms, operators, ctx)
    }

    Constructor { constructor, destructors, format_hint } -> {
      // This rule wraps parsed results in an AST constructor.
      // For formatting, we need to deconstruct the AST node to get
      // the parts that correspond to the inner rules.
      // This is the key challenge: we need to know how to destructure
      // the AST to feed to each sub-rule's formatter.
      format_constructor(node, destructors, rules, ctx)
    }
  }
}

/// Format a Pratt expression, adding parentheses only when needed.
fn format_expression(node: ast, atoms, operators, ctx)
  -> Result(List(Token), FormatError) {
  case node {
    Literal(n) -> Ok([Token(int_to_string(n), None)])
    Variable(name) -> Ok([Token(name, None)])
    Op(op_type, lhs, rhs) -> {
      let op_prec = operator_precedence(op_type, operators)
      let needs_parens = op_prec < ctx.parent_prec

      let lhs_tokens = format_expression(lhs, atoms, operators,
        { parent_prec: op_prec })
      let rhs_tokens = format_expression(rhs, atoms, operators,
        { parent_prec: op_prec })

      let op_str = operator_symbol(op_type, operators)
      let inner = lhs_tokens ++ [Token(" " <> op_str <> " ", None)] ++ rhs_tokens

      case needs_parens {
        True -> Ok([Token("(", None)] ++ inner ++ [Token(")", None)])
        False -> Ok(inner)
      }
    }
    PrefixOp(op_type, operand) -> {
      let op_prec = operator_precedence(op_type, operators)
      let needs_parens = op_prec < ctx.parent_prec
      let operand_tokens = format_expression(operand, atoms, operators,
        { parent_prec: op_prec })
      let op_str = operator_symbol(op_type, operators)
      let inner = [Token(op_str, None)] ++ operand_tokens
      case needs_parens {
        True -> Ok([Token("(", None)] ++ inner ++ [Token(")", None)])
        False -> Ok(inner)
      }
    }
    PostfixOp(op_type, operand) -> { ... }
    Paren(inner) -> format_expression(*inner, atoms, operators, ctx)
  }
}

/// Format a choice: try each formatter until one succeeds.
fn format_choice(rules: List(Rule(ast)), node: ast, ctx)
  -> Result(List(Token), FormatError) {
  // This is the expensive part. We try each rule's formatter.
  // To optimize, we can use the AST constructor tags to narrow down
  // which rule(s) could match.
  case rules {
    [] -> Error(FormatError("no choice matched", node))
    [first, ..rest] -> {
      case format_rule(first, node, ctx) {
        Ok(tokens) -> Ok(tokens)
        Error(_) -> format_choice(rest, node, ctx)
      }
    }
  }
}
```

## 6. The Key Challenge: AST Destructuring

The hardest part: **how does the formatter know how to destructure the AST?**

When formatting a `Sequence([Rule1, Rule2, Rule3])`, the formatter needs to know:
- Which part of the AST corresponds to Rule1?
- Which part corresponds to Rule2?
- Which part corresponds to Rule3?

This is where the AST constructor/destructor pattern comes in.

### Approach A: Explicit Destructors

The user provides destructors for each AST constructor:

```gleam
/// User provides: for each AST constructor, how to destructure it.
pub type AstDestructors(ast) {
  AstDestructors(
    destruct: fn(ast) -> List(#(String, ast)),  // (field_name, field_value)
  )
}
```

### Approach B: Pattern-Based Destructors (My Preference)

The grammar rule encodes the destructuring pattern:

```gleam
/// A rule that wraps results in an AST constructor.
/// The user provides:
///   - the constructor function
///   - a pattern describing how to destructure the AST
Constructor {
  constructor: fn(field1: T1, field2: T2) -> ast,
  /// Pattern for destructuring: which AST fields map to which inner rules
  field_mapping: List(#(String, Int)),  // (field_name, rule_index)
  format_hint: String,
}
```

### Approach C: Macro/Compile-Time Generation (Gleam 2.0+)

With Gleam 2.0's `@extern` and potentially better metaprogramming:

```gleam
// The compiler generates destructors from the AST type definition.
#[grammar(ast_type = Expr)]
pub type Expr {
  Literal(Int)
  Variable(String)
  Add(Expr, Expr)
  Mul(Expr, Expr)
}
```

## 7. Complete User-Facing API

```gleam
// === User defines their AST ===
pub type Expr {
  Literal(Int)
  Variable(String)
  Add(Expr, Expr)
  Mul(Expr, Expr)
  Parens(Expr)
}

// === User defines the grammar ===
import grammar/derive.{parser, formatter}
import grammar/rule.{lit, ident, expression, infix, prefix, sequence, choice}

let precedence = precedence.new()
  |> precedence.infix(4, "+", Assoc.Left)
  |> precedence.infix(6, "*", Assoc.Left)
  |> precedence.infix(8, "^", Assoc.Right)
  |> precedence.prefix(7, "-")

let expr_rule = expression(
  atoms = choice([
    sequence([ident()], fn(name) -> Variable(name)),
    sequence([lit("("), expr_rule, lit(")")], fn(_, inner, _) -> Parens(inner)),
  ]),
  operators = [
    infix("+", 4, Left, fn(l, r) -> Add(l, r)),
    infix("*", 6, Left, fn(l, r) -> Mul(l, r)),
    prefix("-", 7, fn(r) -> Neg(r)),
  ],
  precedence = precedence,
)

// === User derives parser and formatter ===
let parse = parser(expr_rule)
let format = formatter(expr_rule)

// === User uses them ===
let assert Ok(ast) = parse("3 + 4 * 2")
let assert Ok(formatted) = format(ast)
// formatted == "3 + 4 * 2"
```

## 8. Derivation Process

```
Grammar Rule
    │
    ▼
┌─────────────────────────────────────────┐
│  derive_parser(grammar)                 │
│  ┌───────────────────────────────────┐  │
│  │ For each rule variant:            │  │
│  │   Literal(s)   → emit token match │  │
│  │   Identifier   → emit token match │  │
│  │   Sequence     → compose parsers  │  │
│  │   Choice       → compose parsers  │  │
│  │   Expression   → Pratt algorithm  │  │
│  │   Constructor  → apply fn         │  │
│  └───────────────────────────────────┘  │
│  Returns: fn(List(Token)) -> Result(AST)│
└─────────────────────────────────────────┘
    │
    ▼
┌─────────────────────────────────────────┐
│  derive_formatter(grammar)              │
│  ┌───────────────────────────────────┐  │
│  │ For each rule variant:            │  │
│  │   Literal(s)   → emit literal tok │  │
│  │   Identifier   → extract + emit   │  │
│  │   Sequence     → destructure +    │  │
│  │                  compose formatters│  │
│  │   Choice       → try each option  │  │
│  │   Expression   → recurse + paren  │  │
│  │   Constructor  → destructure +    │  │
│  │                  compose formatters│  │
│  └───────────────────────────────────┘  │
│  Returns: fn(AST) -> Result(List(Token))│
└─────────────────────────────────────────┘
```

**Both functions are derived from the same grammar. They share the same structure.**

## 9. Key Design Decisions

### Why Not Hand-Written Parse/Format?

- **Duplication**: User writes the same logic twice
- **Drift**: One gets updated, the other doesn't
- **Complexity**: Pratt formatting is non-trivial; writing it manually is error-prone

### Why Not FormatParser's Approach?

FormatParser embeds parse+format in the same function. In Gleam, this is awkward
because:
1. Gleam doesn't have Haskell's bidirectional pattern matching
2. The `Iso` type is boilerplate-heavy
3. It doesn't solve the AST destructuring problem

### Why Derivation?

- **Single source of truth**: Grammar is the only thing the user writes
- **Automatic sync**: Changing grammar changes both parser and formatter
- **Less boilerplate**: User doesn't write Iso bridges or destructors
- **Pratt formatting**: The derived formatter knows about precedence from the grammar

### The Tradeoff

The cost: the derivation must handle AST destructuring. This requires:
1. User-provided field mappings, OR
2. Compile-time generation (Gleam 2.0+), OR
3. Runtime introspection (limited in Gleam)

## 10. Comparison

| Aspect | Hand-Written (v2) | Derived (v3) |
|--------|-------------------|--------------|
| **Grammar is single source** | ❌ No (parse + format) | ✅ Yes |
| **Sync guaranteed** | ❌ Manual | ✅ By construction |
| **Boilerplate** | High (Iso bridges, destructors) | Low (just AST + grammar) |
| **Flexibility** | High (hand-tuned format) | Medium (derived format) |
| **Pratt formatting** | User writes it | Library derives it |
| **Choice handling** | User handles | Library tries all branches |
| **Performance** | Optimal | May be slower (choice branches) |
