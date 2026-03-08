# Generic Grammar/Parser/Formatter Design

## Core Insight

The grammar, parser, and formatter should be **completely generic** over the AST type. They should know nothing about `core.Term`, `hl.Expr`, or any specific AST.

## Generic Types

### Grammar
```gleam
pub type Grammar(ast) {
  Grammar(
    start: String,
    rules: Dict(String, Rule(ast)),
    tokens: List(String),
    keywords: List(String),
  )
}
```

The grammar is parameterized by `ast` - the type it produces.

### Rule
```gleam
pub type Rule(ast) {
  Rule(
    definition: Symbol,
    constructor: fn(List(ast)) -> ast,
  )
}
```

Each rule has:
- `definition`: What to parse (Symbol tree)
- `constructor`: How to build the AST from parsed children

### Parser
```gleam
pub fn parse(grammar: Grammar(a), source: String) -> ParseResult(a)
```

The parser is generic - it works for ANY grammar that produces ANY type `a`.

### Formatter
```gleam
pub fn format(grammar: Grammar(a), ast: a) -> String
```

The formatter is also generic - it formats ANY AST type.

## How It Works

### Example: Core Language Grammar

```gleam
pub fn core_grammar() -> Grammar(core.Term) {
  grammar.new()
  |> grammar.start("Expr")
  |> grammar.rule(
    "AppExpr",
    grammar.seq([
      grammar.token("Ident"),
      grammar.token("LParen"),
      grammar.opt(grammar.sep_by(grammar.ref("Expr"), grammar.token("Comma"))),
      grammar.token("RParen"),
    ]),
    // Constructor builds core.Term
    fn([func, _lparen, args, _rparen]) {
      let args_list = extract_args(args)
      list.fold(args_list, func, fn(acc, arg) {
        core.Term(core.App(acc, arg), merge_spans([acc, arg]))
      })
    },
  )
  |> grammar.rule(
    "FnExpr",
    grammar.seq([
      grammar.keyword("fn"),
      grammar.token("LParen"),
      grammar.opt(grammar.sep_by(grammar.ref("Param"), grammar.token("Comma"))),
      grammar.token("RParen"),
      grammar.token("Arrow"),
      grammar.ref("Expr"),
    ]),
    // Constructor builds core.Term
    fn([_fn_kw, _lparen, params, _rparen, _arrow, body]) {
      let param_names = extract_param_names(params)
      construct_nested_lambdas(param_names, body)
    },
  )
  // ... more rules
}
```

### Example: High-Level Language Grammar

```gleam
pub fn high_level_grammar() -> Grammar(hl.Expr) {
  grammar.new()
  |> grammar.start("Expr")
  |> grammar.rule(
    "AppExpr",
    grammar.seq([
      grammar.token("Ident"),
      grammar.token("LParen"),
      grammar.opt(grammar.sep_by(grammar.ref("Expr"), grammar.token("Comma"))),
      grammar.token("RParen"),
    ]),
    // Constructor builds hl.Expr (different from core.Term!)
    fn([func, _lparen, args, _rparen]) {
      hl.Expr.App(func, args)
    },
  )
  // ... more rules
}
```

## Generic Parser Implementation

The parser doesn't know about specific AST types:

```gleam
pub fn parse(grammar: Grammar(a), source: String) -> ParseResult(a) {
  let tokens = lexer.tokenize(source)
  let tree = parse_to_tree(grammar, tokens)  // Generic tree
  
  case tree {
    Ok(generic_tree) -> {
      // Apply constructors from grammar
      let ast = apply_constructors(grammar, generic_tree)
      ParseResult(ast: ast, errors: [])
    }
    Error(errors) -> {
      ParseResult(ast: panic as "No AST", errors: errors)
    }
  }
}
```

## Generic Tree (Intermediate Representation)

The parser first builds a generic tree, then applies constructors:

```gleam
type GenericTree {
  Leaf(Token)
  Node(String, List(GenericTree))
}

fn parse_to_tree(grammar: Grammar(a), tokens: List(Token)) -> Result(GenericTree, List(Error)) {
  // Generic parsing logic - same for all grammars
}

fn apply_constructors(grammar: Grammar(a), tree: GenericTree) -> a {
  case tree {
    Node(rule_name, children) -> {
      let rule = dict.get(grammar.rules, rule_name)
      let child_asts = list.map(children, apply_constructors(grammar, _))
      rule.constructor(child_asts)  // Apply the constructor
    }
    Leaf(token) -> {
      // Leaf nodes are handled by the constructor
      token
    }
  }
}
```

## Generic Formatter

The formatter also works generically:

```gleam
pub fn format(grammar: Grammar(a), ast: a) -> String {
  // Use grammar rules to determine how to format
  // Each rule has a formatter function
}
```

Wait, this doesn't work - the formatter needs to know the structure of `a`.

## Better Approach: Bidirectional Grammar

Each rule specifies both how to parse AND how to format:

```gleam
pub type Rule(ast) {
  Rule(
    definition: Symbol,
    constructor: fn(List(a)) -> ast,
    deconstructor: fn(ast) -> List(a),  // For formatting
  )
}
```

Or even better, the grammar provides a separate formatter:

```gleam
pub type Grammar(ast) {
  Grammar(
    start: String,
    rules: Dict(String, Rule(ast)),
    formatter: fn(ast) -> String,
  )
}
```

## Simplest Approach: Separate Formatter

Keep parser and formatter separate but both generic:

```gleam
// Generic parser
pub fn parse(grammar: Grammar(a), source: String) -> ParseResult(a)

// Generic formatter (provided by user of grammar)
pub fn format(ast: a, formatter: Formatter(a)) -> String

// Or: grammar includes formatter
pub type Grammar(ast) {
  Grammar(
    parser: ParserConfig,
    formatter: fn(ast) -> String,
  )
}
```

## Recommended Design

### Grammar Type
```gleam
pub type Grammar(ast) {
  Grammar(
    start: String,
    rules: Dict(String, Rule(ast)),
  )
}

pub type Rule(ast) {
  Rule(
    definition: Symbol,
    constructor: fn(List(a)) -> ast,
  )
}
```

### Parser (Generic)
```gleam
pub fn parse(grammar: Grammar(a), source: String) -> ParseResult(a) {
  let tokens = lexer.tokenize(source)
  let tree = parse_symbols(tokens, grammar.rules, grammar.start)
  
  case tree {
    Ok(nodes) -> {
      let ast = apply_constructors(rules, nodes)
      ParseResult(ast: ast, errors: [])
    }
    Error(errors) -> ParseResult(ast: panic as "...", errors: errors)
  }
}
```

### Formatter (Provided by Grammar User)
```gleam
// Core language provides its own formatter
pub fn format_core_term(term: core.Term) -> String {
  case term.data {
    core.App(func, arg) -> format_core_term(func) <> "(" <> format_core_term(arg) <> ")"
    // ...
  }
}

// High-level language provides its own formatter
pub fn format_hl_expr(expr: hl.Expr) -> String {
  case expr {
    hl.Expr.App(func, args) -> // ...
  }
}
```

## Usage

### Core Language
```gleam
// Define grammar
let grammar = core_grammar()

// Parse
let result = grammar.parse(grammar, "fn(x) { x + 1 }")
// result.ast : core.Term

// Type check
let infer_result = core.infer(core.initial_state(), result.ast)

// Format (using core-specific formatter)
let formatted = core_format.format(result.ast)
```

### High-Level Language
```gleam
// Define grammar
let grammar = high_level_grammar()

// Parse
let result = grammar.parse(grammar, "fn x => x + 1")
// result.ast : hl.Expr

// Type check
let infer_result = hl.infer(hl.initial_state(), result.ast)

// Format (using HL-specific formatter)
let formatted = hl_format.format(result.ast)
```

## Benefits

1. **Truly Generic**: Parser works for ANY AST type
2. **No Duplication**: Parser logic written once
3. **Flexible**: Each language provides its own AST and formatter
4. **Type Safe**: Grammar is parameterized by AST type
5. **Composable**: Can mix and match grammars

## Implementation Order

1. Make `Grammar` generic: `Grammar(ast)`
2. Make `Rule` generic: `Rule(ast)` with constructor
3. Update `parse()` to be generic
4. Update `core/syntax.gleam` to provide constructors
5. Add `core/format.gleam` for core-specific formatting
6. Repeat for high-level language

---

## Complete Example: Calculator Language

Here's a complete end-to-end example of a simple calculator language with `Int`, `Add`, and `Mul`. This demonstrates operator precedence and the full parse → evaluate → format flow.

### Step 1: Define the AST

```gleam
// src/calc/ast.gleam
pub type Expr {
  Int(Int)
  Add(Expr, Expr)
  Mul(Expr, Expr)
}
```

### Step 2: Define the Grammar

```gleam
// src/calc/grammar.gleam
import grammar
import calc/ast

pub fn calc_grammar() -> Grammar(ast.Expr) {
  grammar.new()
  |> grammar.start("Expr")
  
  // Addition (lower precedence)
  |> grammar.rule(
    "Add",
    grammar.seq([
      grammar.ref("Term"),
      grammar.token("Plus"),
      grammar.ref("Expr"),
    ]),
    fn([left, _plus, right]) {
      ast.Expr.Add(left, right)
    },
  )
  
  // Multiplication (higher precedence)
  |> grammar.rule(
    "Mul",
    grammar.seq([
      grammar.ref("Factor"),
      grammar.token("Star"),
      grammar.ref("Term"),
    ]),
    fn([left, _star, right]) {
      ast.Expr.Mul(left, right)
    },
  )
  
  // Factor (integers, parenthesized expressions)
  |> grammar.rule(
    "Factor",
    grammar.choice([
      grammar.token("Int"),
      grammar.seq([
        grammar.token("LParen"),
        grammar.ref("Expr"),
        grammar.token("RParen"),
      ]),
    ]),
    fn([node]) {
      case node {
        grammar.Leaf(token) -> ast.Expr.Int(token.value)
        grammar.Node(_, [_lparen, expr, _rparen]) -> expr
        _ -> panic as "Invalid factor"
      }
    },
  )
}
```

### Step 3: Define the Evaluator

```gleam
// src/calc/eval.gleam
import calc/ast

pub fn eval(expr: ast.Expr) -> Int {
  case expr {
    ast.Expr.Int(n) -> n
    ast.Expr.Add(left, right) -> eval(left) + eval(right)
    ast.Expr.Mul(left, right) -> eval(left) * eval(right)
  }
}
```

### Step 4: Define the Formatter

```gleam
// src/calc/format.gleam
import calc/ast

pub fn format(expr: ast.Expr) -> String {
  case expr {
    ast.Expr.Int(n) -> int.to_string(n)
    ast.Expr.Add(left, right) -> 
      format(left) <> " + " <> format(right)
    ast.Expr.Mul(left, right) -> 
      format_group(left) <> " * " <> format_group(right)
  }
}

// Add parens around Add when it's inside Mul
fn format_group(expr: ast.Expr) -> String {
  case expr {
    ast.Expr.Add(_, _) -> "(" <> format(expr) <> ")"
    _ -> format(expr)
  }
}
```

### Step 5: Use It!

```gleam
// src/main.gleam
import calc/grammar
import calc/eval
import calc/format
import grammar

pub fn main() {
  let grammar = grammar.calc_grammar()
  
  // Parse
  let source = "2 + 3 * 4"
  let result = grammar.parse(grammar, source)
  
  case result {
    Ok(ast) -> {
      // Evaluate: 2 + (3 * 4) = 14
      let value = calc/eval.eval(ast)
      io.println(int.to_string(value))  // Prints: 14
      
      // Format back (with correct precedence)
      let formatted = calc/format.format(ast)
      io.println(formatted)  // Prints: "2 + 3 * 4"
    }
    Error(errors) -> {
      io.println("Parse error!")
    }
  }
  
  // Another example with parens
  let source2 = "(2 + 3) * 4"
  let result2 = grammar.parse(grammar, source2)
  
  case result2 {
    Ok(ast) -> {
      // Evaluate: (2 + 3) * 4 = 20
      let value = calc/eval.eval(ast)
      io.println(int.to_string(value))  // Prints: 20
      
      // Format back (preserves parens)
      let formatted = calc/format.format(ast)
      io.println(formatted)  // Prints: "(2 + 3) * 4"
    }
    Error(errors) -> {
      io.println("Parse error!")
    }
  }
}
```

### Key Points

1. **Operator Precedence**: The grammar structure enforces precedence:
   - `Expr` → `Add` → `Term` → `Mul` → `Factor`
   - `Mul` binds tighter than `Add`
   - `2 + 3 * 4` parses as `2 + (3 * 4)` = 14
   - `(2 + 3) * 4` parses as `(2 + 3) * 4` = 20

2. **Generic Parser**: The same `grammar.parse()` function works for any grammar.

3. **Language-Specific Logic**: Each language provides:
   - Its own AST type (`calc/ast.Expr`)
   - Its own constructors (in grammar rules)
   - Its own evaluator (`calc/eval.eval`)
   - Its own formatter (`calc/format.format`)

4. **Extensible**: To add subtraction:
   ```gleam
   |> grammar.rule(
     "Sub",
     grammar.seq([
       grammar.ref("Term"),
       grammar.token("Minus"),
       grammar.ref("Expr"),
     ]),
     fn([left, _minus, right]) {
       ast.Expr.Sub(left, right)
     },
   )
   ```

### Scaling to Core Language

The core language follows the same pattern, just with more constructs:

```gleam
// Core AST
pub type Term {
  Int(Int)
  Var(String)
  App(Term, Term)
  Lam(String, Term)
  Match(Term, List(Case))
  // ...
}

// Core Grammar
pub fn core_grammar() -> Grammar(core.Term) {
  grammar.new()
  |> grammar.start("Expr")
  |> grammar.rule("App", /* ... */, fn(args) { core.Term.App(...) })
  |> grammar.rule("Lam", /* ... */, fn(args) { core.Term.Lam(...) })
  // ...
}

// Core Evaluator
pub fn eval(env: Env, term: core.Term) -> core.Value {
  case term {
    core.Term.Int(n) -> core.Value.Int(n)
    core.Term.App(func, arg) -> // ...
    // ...
  }
}

// Core Formatter
pub fn format(term: core.Term) -> String {
  case term {
    core.Term.Int(n) -> int.to_string(n)
    core.Term.App(func, arg) -> // ...
    // ...
  }
}
```

The pattern is identical - just more complex AST and more grammar rules.
