# Core Language Implementation Plan - Revised

> **Goal**: Single grammar definition generates both parser AND formatter
> **Status**: Implementation in progress
> **Date**: March 2025

---

## Core Principle

**The grammar is the single source of truth.** It should define:
1. What to parse (patterns)
2. How to construct AST from parsed values (constructors)
3. **How to deconstruct AST back to values (deconstructors)** ← This was missing!
4. How to format values back to source (layout hints)

---

## Grammar Structure

Each grammar rule needs **bidirectional** information:

```gleam
pub type Rule(a) {
  Rule(
    name: String,
    alternatives: List(Alternative(a)),
    precedence: Int,
  )
}

pub type Alternative(a) {
  Alternative(
    pattern: Pattern(a),
    constructor: fn(List(Value(a))) -> a,      // Parse: values → AST
    deconstructor: fn(a) -> List(Value(a)),    // Format: AST → values
  )
}
```

### Example: Application Rule

```gleam
// Grammar rule for application: f(x)
grammar.rule("App", [
  grammar.alt(
    grammar.seq_with_layout([
      #(grammar.ref("Atom"), NoSeparator),
      #(grammar.token("LParen"), NoSeparator),
      #(grammar.ref("Arg"), SoftBreak),
      #(grammar.token("RParen"), NoSeparator),
    ]),
    // Constructor: build App from parsed values
    fn(values) {
      case values {
        [AstValue(fun), _, AstValue(arg), _] => Term(App(fun, arg), span())
        _ => panic as "Invalid app"
      }
    },
    // Deconstructor: extract values from App term
    fn(term) {
      case term.data {
        App(fun, arg) => [
          AstValue(fun),
          TokenValue(lp_token),  // Need to create dummy tokens for formatting
          AstValue(arg),
          TokenValue(rp_token),
        ]
        _ => panic as "Expected App"
      }
    },
  ),
])
```

---

## Formatter Generation Algorithm

The generic formatter works as follows:

```
format_ast(grammar, ast, parent_prec):
  1. Find which rule/alternative produced this AST
     - Try each rule's deconstructor until one succeeds
     
  2. Deconstruct AST into values
     - values = alternative.deconstructor(ast)
     
  3. Format each value based on pattern
     - For TokenValue: output the token text
     - For AstValue(child): recursively format_ast(child, child_prec)
     
  4. Join formatted values with layout hints from pattern
     - Use SoftBreak/HardBreak/Space from SeqWithLayout
     
  5. Add parentheses if precedence requires
```

### Key Functions

```gleam
// In syntax/grammar.gleam

/// Format an AST using grammar rules
pub fn format_ast<A>(
  grammar: Grammar(A),
  ast: A,
  parent_prec: Int,
) -> Doc {
  case find_matching_alternative(grammar, ast) {
    Some(#(rule, alt)) -> {
      let values = alt.deconstructor(ast)
      format_pattern(alt.pattern, values, parent_prec, rule.precedence)
    }
    None -> formatter.text("<unknown>")
  }
}

/// Find which alternative matches this AST
fn find_matching_alternative<A>(
  grammar: Grammar(A),
  ast: A,
) -> Option(#(Rule(A), Alternative(A))) {
  // Try each rule's alternatives
  // Return first one whose deconstructor succeeds
}

/// Format values according to pattern with layout hints
fn format_pattern<A>(
  pattern: Pattern(A),
  values: List(Value(A)),
  parent_prec: Int,
  rule_prec: Int,
) -> Doc {
  case pattern {
    SeqWithLayout(items) -> format_seq_with_layout(items, values, parent_prec, rule_prec)
    // ... other patterns
  }
}
```

---

## Implementation Steps

### Step 1: Update Grammar Types

Add deconstructor to Alternative:

```gleam
pub type Alternative(a) {
  Alternative(
    pattern: Pattern(a),
    constructor: fn(List(Value(a))) -> a,
    deconstructor: fn(a) -> List(Value(a)),  // NEW
  )
}
```

### Step 2: Update Core Grammar

Add deconstructors to all rules:

```gleam
pub fn core_grammar() -> Grammar(Term) {
  use g <- grammar.define

  g
  |> grammar.rule("App", [
    grammar.alt_with_deconstructor(
      grammar.seq_with_layout([...]),
      make_app,       // constructor
      deconstruct_app, // deconstructor
    ),
  ])
}

fn deconstruct_app(term: Term) -> List(Value(Term)) {
  case term.data {
    App(fun, arg) => [
      AstValue(fun),
      TokenValue(make_lparen()),
      AstValue(arg),
      TokenValue(make_rparen()),
    ]
    _ => panic as "Expected App"
  }
}
```

### Step 3: Implement Generic Formatter

In `syntax/grammar.gleam`:

```gleam
pub fn format<A>(grammar: Grammar(A), ast: A) -> String {
  format_ast(grammar, ast, -1) |> formatter.render_default
}

fn format_ast<A>(grammar: Grammar(A), ast: A, parent_prec: Int) -> Doc {
  // Implementation as above
}
```

### Step 4: Update Core Formatter

In `core/formatter.gleam`:

```gleam
// Just a thin wrapper around grammar.format
pub fn format(term: Term) -> String {
  grammar.format(core_grammar(), term)
}
```

### Step 5: Round-Trip Tests

```gleam
pub fn roundtrip_app_test() {
  let source = "f(x)"
  let result = parser.parse(core_grammar(), source)
  let formatted = formatter.format(result.ast)
  formatted |> should.equal(source)
}
```

---

## Challenges and Solutions

### Challenge 1: Token Values in Deconstructors

**Problem**: Deconstructors need to return `TokenValue` for punctuation, but we don't have actual tokens when formatting.

**Solution**: Create "synthetic" tokens with just the text:

```gleam
fn make_lparen() -> Token {
  Token(kind: "LParen", value: "(", start: pos(0), end: pos(0))
}
```

### Challenge 2: Finding Matching Alternative

**Problem**: How to find which alternative produced an AST?

**Solution**: Try each deconstructor until one succeeds (doesn't panic):

```gleam
fn find_matching_alternative(grammar, ast) {
  list.find_map(grammar.rules, fn(rule) {
    list.find_map(rule.alternatives, fn(alt) {
      try {
        alt.deconstructor(ast)
        Some(#(rule, alt))
      } catch panic {
        None  // This alternative doesn't match
      }
    })
  })
}
```

### Challenge 3: Precedence for Complex Patterns

**Problem**: How to determine child precedence for non-operator patterns?

**Solution**: Each pattern type has a default precedence:
- Atoms: 100 (highest)
- Application: 85
- Lambda: 70
- Pi type: 65
- etc.

---

## File Structure

```
src/
├── syntax/
│   ├── grammar.gleam      # Grammar DSL + parser + formatter generators
│   ├── formatter.gleam    # Document algebra (unchanged)
│   └── lexer.gleam        # Tokenizer (unchanged)
├── core/
│   ├── core.gleam         # Term types, evaluator, type checker (unchanged)
│   ├── grammar.gleam      # Core language grammar definition ← MAIN WORK
│   ├── parser.gleam       # Thin wrapper: grammar.parse(core_grammar(), src)
│   └── formatter.gleam    # Thin wrapper: grammar.format(core_grammar(), ast)
└── ...
```

---

## Test Plan

### Parser Tests
```gleam
pub fn parse_app_test() {
  let result = parser.parse("f(x)")
  result.ast |> should.equal(Term(App(Var(0), Var(1)), _))
}
```

### Formatter Tests
```gleam
pub fn format_app_test() {
  let term = Term(App(Var(0), Var(1)), _)
  formatter.format(term) |> should.equal("f(x)")
}
```

### Round-Trip Tests
```gleam
pub fn roundtrip_app_test() {
  let source = "f(x)"
  let result = parser.parse(source)
  let formatted = formatter.format(result.ast)
  formatted |> should.equal(source)
}
```

---

## Summary

The key insight is that **both parser and formatter are generated from the same grammar**:

| Direction | Grammar Provides | Generated By |
|-----------|-----------------|--------------|
| Source → AST | Pattern + Constructor | Parser |
| AST → Source | Pattern + Deconstructor | Formatter |

The grammar is truly the single source of truth - it defines the complete round-trip.
