# Revised Generic Grammar Design

## Problem

The current approach has a fundamental flaw:
1. Parser produces generic `ParseTree` (Leaf/Node)
2. Constructors expect specific AST types (e.g., `ast.Expr.Int`)
3. No way to convert `Leaf(Token)` to `ast.Expr.Int` without knowing the AST type

## Solution: Direct Constructor Application

Instead of a two-phase approach (parse → convert), have the parser directly call constructors with proper arguments.

### New Rule Type

```gleam
pub type Rule(ast) {
  Rule(
    name: String,
    parser: fn() -> Parser(a),  // Each rule defines its own parser
  )
}
```

### Grammar Construction

```gleam
pub fn calc_grammar() -> Grammar(ast.Expr) {
  grammar.new()
  |> grammar.start("Expr")
  |> grammar.rule("Expr", fn() {
    parser.choice([
      parser.map(parser.seq([
        parser.ref("Term"),
        parser.token("Plus"),
        parser.ref("Expr"),
      ]), fn([left, _plus, right]) {
        ast.Expr.Add(left, right)
      }),
      parser.ref("Term"),
    ])
  })
  |> grammar.rule("Term", fn() {
    parser.choice([
      parser.map(parser.seq([
        parser.ref("Factor"),
        parser.token("Star"),
        parser.ref("Term"),
      ]), fn([left, _star, right]) {
        ast.Expr.Mul(left, right)
      }),
      parser.ref("Factor"),
    ])
  })
  |> grammar.rule("Factor", fn() {
    parser.choice([
      parser.map(parser.token("Int"), fn(token) {
        ast.Expr.Int(token.value)
      }),
      parser.map(parser.seq([
        parser.token("LParen"),
        parser.ref("Expr"),
        parser.token("RParen"),
      ]), fn([_, expr, _]) {
        expr
      }),
    ])
  })
}
```

### Benefits

1. **Type Safe**: Constructors receive properly typed arguments
2. **No Conversion Layer**: No need to convert ParseTree → AST
3. **Flexible**: Each rule can parse however it wants
4. **Composable**: Rules can reference other rules

### Implementation

```gleam
pub type Parser(a) {
  Parser(fn(State) -> ParseResult(a))
}

pub fn parse(g: Grammar(a), source: String) -> ParseResult(a) {
  let tokens = lexer.tokenize(source)
  let state = State(tokens: tokens, pos: 0)
  
  // Get start rule parser
  case dict.get(g.rules, g.start) {
    Ok(rule) -> rule.parser()(state)
    Error(_) -> panic as "No start rule"
  }
}
```

This approach is cleaner because:
1. Each rule knows how to parse its structure
2. Constructors are called with the right types
3. No intermediate representation needed
4. Type inference works correctly
