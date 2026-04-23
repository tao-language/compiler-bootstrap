# Testing Strategy

## Design Philosophy

> **Tests as examples** — Every function has tests that demonstrate correct usage with example inputs/outputs.

The testing strategy is organized in layers:

1. **Unit tests** — Test each function in isolation
2. **Golden tests** — Test round-trip (parse → format → parse)
3. **Integration tests** — Test full pipeline stages
4. **End-to-end tests** — Test complete compilation from source to value

## Test Organization

```
test/
├── syntax/
│   ├── lexer_test.gleam       # Tokenizer unit tests
│   ├── grammar_test.gleam     # Parser combinator unit tests
│   ├── formatter_test.gleam   # Document algebra + layout tests
│   └── golden_test.gleam      # Parse → format → parse round-trip tests
├── core/
│   ├── ast_test.gleam         # Term/Value type construction tests
│   ├── syntax_test.gleam      # Core parser + formatter tests
│   ├── infer_test.gleam       # Bidirectional type checking tests
│   ├── eval_test.gleam        # Normalization by evaluation tests
│   ├── quote_test.gleam       # Value → Term tests
│   ├── unify_test.gleam       # Unification tests
│   ├── subst_test.gleam       # Substitution tests
│   ├── generalize_test.gleam  # Generalization tests
│   ├── exhaustiveness_test.gleam  # Pattern match coverage tests
│   ├── error_formatter_test.gleam  # Type error diagnostics tests
│   ├── state_test.gleam       # State management tests
│   ├── examples_test.gleam    # End-to-end example programs
│   └── golden_test.gleam      # Core → eval → quote → eval round-trip
├── tao/
│   ├── ast_test.gleam         # Tao AST type construction tests
│   ├── syntax_test.gleam      # Tao parser + formatter tests
│   ├── desugar_test.gleam     # Desugaring correctness tests
│   ├── compiler_test.gleam    # Multi-file compilation tests
│   ├── import_test.gleam      # Module import system tests
│   ├── examples_test.gleam    # End-to-end example programs
│   └── golden_test.gleam      # Tao → desugar → compile → format round-trip
└── integration/
    └── e2e_test.gleam         # Full pipeline tests (Tao source → Core value)
```

## Test Examples

### Unit Tests: Lexer (lexer_test.gleam)

```gleam
import gleeunit.{should, test}
import syntax/lexer.{tokenize}
import syntax/grammar.{type Span}

test "tokenize integer literal" {
  let tokens = tokenize("42")
  case tokens {
    [Token(kind: "Integer", value: "42", ..)] -> True
    _ -> False
  }
}

test "tokenize string with escape sequences" {
  let tokens = tokenize("\"hello\\nworld\"")
  case tokens {
    [Token(kind: "String", value: "hello\nworld", ..)] -> True
    _ -> False
  }
}

test "tokenize multiple tokens with correct positions" {
  let tokens = tokenize("let x = 42")
  case tokens {
    [Token(line: 1, column: 1, ..),
     Token(line: 1, column: 4, ..),
     Token(line: 1, column: 6, ..),
     Token(line: 1, column: 8, ..),
     Token(line: 1, column: 11, ..)] -> True
    _ -> False
  }
}

test "tokenize comments (single-line)" {
  let tokens = tokenize("// comment\nlet x = 42")
  // Comments should not produce tokens
  let non_comment_tokens = list.filter(tokens, fn(t) -> t.kind != "Comment")
  non_comment_tokens == list.drop(tokens, 1)  // Skip the comment token
}

test "tokenize block comments" {
  let tokens = tokenize("/* block comment */ let x = 42")
  let non_comment_tokens = list.filter(tokens, fn(t) -> t.kind != "Comment")
  non_comment_tokens.length == 4  // let, x, =, 42
}

test "tokenize operators with correct kinds" {
  let tokens = tokenize("+ - * / == != < > <= >= && ||")
  case tokens {
    [Token(kind: "Op", value: "+", ..),
     Token(kind: "Op", value: "-", ..),
     Token(kind: "Op", value: "*", ..),
     // ... all should be "Op" kind
     _] -> True
    _ -> False
  }
}

test "tokenize reserved keywords" {
  let tokens = tokenize("fn let in match type of import as")
  case tokens {
    [Token(kind: "Keyword", value: "fn", ..),
     Token(kind: "Keyword", value: "let", ..),
     // ... all should be "Keyword" kind
     _] -> True
    _ -> False
  }
}

test "handle empty input" {
  let tokens = tokenize("")
  tokens == []
}

test "handle whitespace-only input" {
  let tokens = tokenize("   \n\t  ")
  tokens == []
}

test "tokenize unicode characters" {
  let tokens = tokenize("\"こんにちは\"")
  case tokens {
    [Token(kind: "String", value: "こんにちは", ..)] -> True
    _ -> False
  }
}
```

### Unit Tests: Grammar Parser (grammar_test.gleam)

```gleam
import gleeunit.{should, test}
import syntax/grammar.{parse, alt, ref, seq, opt, many, choice, delimited}

test "parse optional pattern" {
  let result = parse(opt(ref("Name")), "foo")
  case result {
    ParseResult(ast: "foo", errors: []) -> True
    _ -> False
  }
}

test "parse many pattern" {
  let result = parse(many(ref("Name")), "foo bar baz")
  case result {
    ParseResult(ast: ["foo", "bar", "baz"], errors: []) -> True
    _ -> False
  }
}

test "parse empty many" {
  let result = parse(many(ref("Name")), "")
  case result {
    ParseResult(ast: [], errors: []) -> True
    _ -> False
  }
}

test "parse delimited list" {
  let result = parse(delimited(
    token("LParen"),
    ref("Name"),
    token("Comma"),
    token("RParen")
  ), "(a, b, c)")
  case result {
    ParseResult(ast: ["a", "b", "c"], errors: []) -> True
    _ -> False
  }
}

test "parse empty delimited list" {
  let result = parse(delimited(
    token("LParen"),
    ref("Name"),
    token("Comma"),
    token("RParen")
  ), "()")
  case result {
    ParseResult(ast: [], errors: []) -> True
    _ -> False
  }
}

test "accumulate multiple parse errors" {
  let grammar = Grammar(
    name: "test",
    start: "Expr",
    rules: [
      Rule(
        name: "Expr",
        alternatives: [
          Alternative(
            pattern: seq([ref("Name"), token("Op"), ref("Name")]),
            constructor: fn(_) -> "binary_op",
          ),
        ],
        precedence: 0,
      ),
    ],
    keywords: ["fn", "let", "in"],
    operators: [],
  )
  
  let result = parse(grammar, "foo + bar + baz", "error_node")
  case result {
    ParseResult(_, errors: [e1, e2, e3]) if errors.length >= 2 -> True
    _ -> False
  }
}

test "produce accurate spans from tokens" {
  let grammar = simple_grammar()
  let result = parse(grammar, "let x = 42", "error_node")
  case result {
    ParseResult(ast: _, errors: []) -> {
      // Check that the AST has spans from the actual tokens
      span_start(result.ast) == Span("test", 1, 1, 1, 3)  // "let"
      span_end(result.ast) == Span("test", 1, 1, 1, 12)   // "42"
    }
    _ -> False
  }
}
```

### Unit Tests: Formatter (formatter_test.gleam)

```gleam
import gleeunit.{should, test}
import syntax/formatter.{render, concat, text, line, nest, group, join, space_sep, comma_sep, parens}

test "join with comma separator" {
  let doc = join(concat([text(","), line()]), [text("a"), text("b"), text("c")])
  render(doc, 80) == "a,\nb,\nc"
}

test "space-separated list" {
  let doc = space_sep([text("a"), text("b"), text("c")])
  render(doc, 80) == "a b c"
}

test "parenthesize when too long" {
  let doc = group(concat([text("this is a very long expression that should wrap"), text(" and continue")]))
  case render(doc, 20) {
    "(" <> _ <> ")" -> True
    _ -> False
  }
}

test "nest increases indentation" {
  let doc = nest(2, concat([text("  a"), line(), text("  b")]))
  render(doc, 80) == "  a\n  b"
}

test "empty text produces empty doc" {
  let doc = text("")
  render(doc, 80) == ""
}
```

### Unit Tests: Core Infer (infer_test.gleam)

```gleam
import gleeunit.{should, test}
import core/ast.{Term, Var, Lam, Pi, App, Hole, Typ, Unit}
import core/eval.{Value, VLam, VPi, VNeut, HVar, HHole}
import core/infer.{infer, check}
import core/state.{State, initial_state}

test "infer identity function type" {
  // fn(x: a) -> a
  let body = Var(0, "x")
  let lam = Lam(("x", Hole(-1)), body)
  
  let state = initial_state([], [], "", "")
  let result = infer(state, lam)
  
  // Should produce: ∀a. a → a
  case result {
    State(errors: [], ctrs: _) -> True
    _ -> False
  }
}

test "check lambda with correct type annotation" {
  // (fn(x) { x } : ∀a. a → a)
  let body = Var(0, "x")
  let lam = Lam(("x", Hole(-1)), body)
  let ann = Ann(lam, Hole(-1))
  
  let state = initial_state([], [], "", "")
  let result = check(state, ann, VPi([], "a", [], VNeut(HHole(1), []), Var(0, "a")))
  
  case result {
    State(errors: [], ctrs: _) -> True
    _ -> False
  }
}

test "infer type mismatch accumulates error" {
  // let x: Int = "hello"
  let state = initial_state([], [], "", "")
  let result = check(state, Lit(String("hello")), VLit(I32(0)))
  
  case result {
    State(errors: [TypeMismatch(_, _, _, _)], _) -> True
    _ -> False
  }
}

test "infer application of identity function" {
  // (fn(x) { x }) 42
  let body = Var(0, "x")
  let lam = Lam(("x", Hole(-1)), body)
  let app = App(lam, Lit(I32(42)))
  
  let state = initial_state([], [], "", "")
  let result = infer(state, app)
  
  case result {
    State(errors: [], ctrs: _) -> True
    _ -> False
  }
}

test "handle undefined variable error" {
  let state = initial_state([], [], "", "")
  let result = infer(state, Var(5, "x"))  // Var(5) is out of scope
  
  case result {
    State(errors: [VarUndefined(5, _)], _) -> True
    _ -> False
  }
}

test "infer pi type construction" {
  // Πx:a. b (dependent function type)
  let domain = Var(0, "a")
  let codomain = Var(1, "b")  // b is from outer scope
  let pi = Pi(domain, codomain)
  
  let state = initial_state([], [], "", "")
  let result = infer(state, pi)
  
  case result {
    State(errors: [], ctrs: _) -> True
    _ -> False
  }
}

test "handle constructor undefined error" {
  let state = initial_state([], [], "", "")
  let result = infer(state, Ctr("UndefinedCtor", Hole(-1)))
  
  case result {
    State(errors: [CtrUndefined("UndefinedCtor", _)], _) -> True
    _ -> False
  }
}

test "infer let binding" {
  // let x = 42; x
  let let_term = Let("x", Lit(I32(42)), Var(0, "x"))
  let state = initial_state([], [], "", "")
  let result = infer(state, let_term)
  
  case result {
    State(errors: [], ctrs: _) -> True
    _ -> False
  }
}

test "handle infinite type error" {
  // x : ∀x. x → x (infinite type)
  let state = initial_state([], [], "", "")
  let result = check(state, Hole(-1), VPi([], "x", [], Var(0, "x"), Hole(-1)))
  
  case result {
    State(errors: [InfiniteType(_, _, _, _)], _) -> True
    _ -> False
  }
}
```

### Unit Tests: Core Eval (eval_test.gleam)

```gleam
import gleeunit.{should, test}
import core/ast.{Term, Var, Lam, App, Lit, I32}
import core/eval.{evaluate, Value, VLit, I32T}

test "evaluate identity function application" {
  // (fn(x) { x }) 42 → 42
  let body = Var(0, "x")
  let lam = Lam(("x", Hole(-1)), body)
  let app = App(lam, Lit(I32(42)))
  
  let result = evaluate(app)
  case result {
    VLit(I32(42)) -> True
    _ -> False
  }
}

test "evaluate constant" {
  // 42 → 42
  let result = evaluate(Lit(I32(42)))
  case result {
    VLit(I32(42)) -> True
    _ -> False
  }
}

test "evaluate nested lambda" {
  // (fn(x) { fn(y) { x + y }}) 1 2 → 3
  let body = App(App(Var(0, "+"), Var(1, "x")), Var(0, "y"))
  let inner_lam = Lam(("y", Hole(-1)), body)
  let outer_lam = Lam(("x", Hole(-1)), inner_lam)
  let app1 = App(outer_lam, Lit(I32(1)))
  let app2 = App(app1, Lit(I32(2)))
  
  let result = evaluate(app2)
  case result {
    VLit(I32(3)) -> True
    _ -> False
  }
}

test "evaluate Church numeral 2" {
  // λf.λx.f (f x) → λf.λx.f (f x) (already a value)
  let f_x = App(Var(1, "f"), App(Var(0, "f"), Var(0, "x")))
  let body = Lam(("x", Hole(-1)), f_x)
  let result = evaluate(Lam(("f", Hole(-1)), body))
  
  // Should be a lambda value
  case result {
    VLam(..) -> True
    _ -> False
  }
}

test "evaluate addition FFI" {
  // +(42, 1) → 43
  let add = Call("add", [Lit(I32(42)), Lit(I32(1))], Hole(-1))
  let state = initial_state([], tao_ffis(), "True", "False")
  let result = evaluate_with_ffi(state.ffi, add)
  
  case result {
    VLit(I32(43)) -> True
    _ -> False
  }
}

test "handle step limit error" {
  // Infinite loop: fix x -> x x
  let fix = Fix("x", Call("x", []))
  let result = evaluate_with_step_limit(fix, 10)
  
  case result {
    VErr -> True
    _ -> False
  }
}
```

### Unit Tests: Core Quote (quote_test.gleam)

```gleam
import gleeunit.{should, test}
import core/ast.{Term, Var, Lam, App, Lit, I32}
import core/eval.{Value, VLam, VLit, VNeut, HVar}
import core/quote.{quote}

test "quote lambda value back to term" {
  let body = Var(0, "x")
  let lam = Lam(("x", Hole(-1)), body)
  let value = VLam([], "x", [VNeut(HVar(0), [])], lam)
  
  let result = quote(value)
  case result {
    Lam(("x", _), body, _) if body == Var(0, "x") -> True
    _ -> False
  }
}

test "quote literal value" {
  let value = VLit(I32(42))
  let result = quote(value)
  case result {
    Lit(I32(42)) -> True
    _ -> False
  }
}

test "quote nested lambda" {
  // (fn(x) { fn(y) { x }}) 1 → λx.λy.x
  let inner_body = Var(1, "x")
  let inner_lam = Lam(("y", Hole(-1)), inner_body)
  let outer_lam = Lam(("x", Hole(-1)), inner_lam)
  
  let inner_value = VLam([], "y", [VNeut(HVar(0), []), VNeut(HVar(1), [])], inner_lam)
  let outer_value = VLam([], "x", [VNeut(HVar(0), [])], outer_lam)
  
  let result = quote(outer_value)
  case result {
    Lam(("x", _), Lam(("y", _), Var(0, "x"), _), _) -> True
    _ -> False
  }
}

test "quote does not evaluate" {
  // Quote should NOT call eval — this is a critical invariant
  let called_eval = ref(False)
  let value = VLam([], "x", [], Lam(("x", Hole(-1)), Var(0, "x")))
  
  let result = quote_with_trace(value, fn() -> called_eval = True)
  called_eval == False  // eval should never be called
}
```

### Unit Tests: Core Unify (unify_test.gleam)

```gleam
import gleeunit.{should, test}
import core/ast.{Term, Hole, Var, Lit, I32}
import core/eval.{Value, VLit, VNeut, HHole, I32T}
import core/unify.{unify}
import core/state.{State}

test "unify two identical values" {
  let state = initial_state([], [], "", "")
  let result = unify(state, VLit(I32(42)), VLit(I32(42)))
  case result {
    State(errors: [], _) -> True
    _ -> False
  }
}

test "unify hole with concrete type" {
  let state = initial_state([], [], "", "")
  let result = unify(state, VNeut(HHole(1), []), VLit(I32T))
  case result {
    State(errors: [], subst: _) -> True
    _ -> False
  }
}

test "unify incompatible types produces error" {
  let state = initial_state([], [], "", "")
  let result = unify(state, VLit(I32T), VLit(F64T))
  case result {
    State(errors: [TypeMismatch(_, _, _, _)], _) -> True
    _ -> False
  }
}

test "unify pi types with matching domains and codomains" {
  let state = initial_state([], [], "", "")
  let dom = VNeut(HHole(1), [])
  let codom1 = VNeut(HVar(0), [])
  let codom2 = VNeut(HVar(0), [])
  let result = unify(state, VPi([], "a", [], dom, codom1), VPi([], "a", [], dom, codom2))
  case result {
    State(errors: [], _) -> True
    _ -> False
  }
}

test "handle occurs check (should allow recursive types)" {
  let state = initial_state([], [], "", "")
  let result = unify(state, VNeut(HHole(1), []), VPi([], "a", [], VNeut(HHole(1), []), VNeut(HVar(0), [])))
  case result {
    State(errors: [], _) -> True  // Should not error (we allow recursive types)
    _ -> False
  }
}
```

### Integration Tests: Compiler (compiler_test.gleam)

```gleam
import gleeunit.{should, test}
import tao/compiler.{compile_tao}
import core/eval.{Value, VLit, I32}

test "compile simple addition" {
  let source = "let x = 42 + 1; x"
  let result = compile_tao(source, "test.tao")
  result.errors == []
  result.value == VLit(I32(43))
}

test "compile function definition and call" {
  let source = """
    fn add(a, b) { a + b }
    add(1, 2)
  """
  let result = compile_tao(source, "test.tao")
  result.errors == []
  result.value == VLit(I32(3))
}

test "compile fibonacci" {
  let source = """
    fn fib(n) {
      mut a = 0
      mut b = 1
      mut i = 0
      while i < n {
        let temp = a
        a = b
        b = temp + b
        i = i + 1
      }
      a
    }
    fib(6)
  """
  let result = compile_tao(source, "test.tao")
  result.errors == []
  result.value == VLit(I32(8))
}

test "compile with parse errors accumulates errors" {
  let source = """
    fn foo(x
    let bar = 
    type Baz
  """
  let result = compile_tao(source, "test.tao")
  result.errors.length >= 3
}

test "compile with type errors accumulates errors" {
  let source = """
    let x: Int = "hello"
    let y: String = 42
  """
  let result = compile_tao(source, "test.tao")
  result.errors.length >= 2
}

test "compile imported module" {
  let modules = [
    #("math.tao", "fn add(a, b) { a + b }"),
    #("main.tao", "import math { add }; add(1, 2)"),
  ]
  let result = compile_multi_module(modules, "main.tao")
  result.errors == []
  result.value == VLit(I32(3))
}

test "detect circular import" {
  let modules = [
    #("a.tao", "import b { foo }"),
    #("b.tao", "import a { bar }"),
  ]
  let result = compile_multi_module(modules, "a.tao")
  case result {
    Error(CircularImport(_, _, _)) -> True
    _ -> False
  }
}
```

### Golden Tests: Round-Trip (golden_test.gleam)

```gleam
import gleeunit.{should, test}

test "Tao: parse → format → parse produces same AST" {
  let source = """
    fn add(a, b) { a + b }
    let x = add(1, 2)
  """
  let parsed = tao_syntax.parse(source)
  let formatted = tao_syntax.format(parsed.ast)
  let reparsed = tao_syntax.parse(formatted)
  
  parsed.ast == reparsed.ast
}

test "Core: term → eval → quote → term produces structurally equal term" {
  let source = "let x = 42; x"
  let parsed = core_syntax.parse(source)
  let quoted = core_quote.quote(core_eval.evaluate(parsed.ast))
  
  // quoted should be structurally equivalent to parsed
  structural_equal(parsed.ast, quoted)
}

test "Core: parse → format → parse produces same term" {
  let source = "let x = 42; x"
  let parsed = core_syntax.parse(source)
  let formatted = core_syntax.format(parsed.ast)
  let reparsed = core_syntax.parse(formatted)
  
  parsed.ast == reparsed.ast
}

test "Tao → Core: desugar → format produces valid Core" {
  let source = "fn add(a, b) { a + b }"
  let tao_expr = tao_syntax.parse(source)
  let core_term = tao_desugar.desugar(tao_expr.ast)
  let core_formatted = core_syntax.format(core_term)
  
  // Should parse back as a valid Core term
  let reparsed = core_syntax.parse(core_formatted)
  reparsed.errors == []
}
```

### End-to-End Tests (e2e_test.gleam)

```gleam
import gleeunit.{should, test}

test "complete pipeline: fib(10) = 55" {
  let source = """
    fn fib(n) {
      mut a = 0
      mut b = 1
      mut i = 0
      while i < n {
        let temp = a
        a = b
        b = temp + b
        i = i + 1
      }
      a
    }
    fib(10)
  """
  let result = compile_tao(source, "fib.tao")
  result.errors == []
  result.value == VLit(I32(55))
}

test "complete pipeline: map and filter" {
  let source = """
    fn map(f, xs) {
      match xs {
        | [] -> []
        | [h, ..t] -> [f(h), ..map(f, t)]
      }
    }
    
    fn filter(p, xs) {
      match xs {
        | [] -> []
        | [h, ..t] ->
          if p(h) {
            [h, ..filter(p, t)]
          } else {
            filter(p, t)
          }
      }
    }
    
    let nums = [1, 2, 3, 4, 5]
    let doubled = map(\x -> x * 2, nums)
    let evens = filter(\x -> x == 0, doubled)
    evens
  """
  let result = compile_tao(source, "map_filter.tao")
  result.errors == []
  // evens should be [2, 4]
  result.value == VList([VLit(I32(2)), VLit(I32(4))])
}

test "complete pipeline: generator stream" {
  let source = """
    type Stream(a) = Cons(head: a, tail: Stream(a)) | Empty
    
    fn range(start, end) {
      if start >= end {
        Stream.empty()
      } else {
        Stream.cons(start, range(start + 1, end))
      }
    }
    
    let nums = range(1, 3)
    Stream.to_list(nums)
  """
  let result = compile_tao(source, "stream.tao")
  result.errors == []
  result.value == VList([VLit(I32(1)), VLit(I32(2)), VLit(I32(3))])
}
```

## Test Coverage Requirements

| Component | Minimum Coverage | Notes |
|-----------|-----------------|-------|
| `syntax/lexer` | 100% | Every token type, every edge case |
| `syntax/grammar` | 100% | Every combinator, every pattern type |
| `syntax/formatter` | 100% | Every document operation, every layout |
| `core/ast` | 100% | Every type constructor |
| `core/infer` | 100% | Every term form, every error case |
| `core/eval` | 100% | Every value form, step limit, FFI |
| `core/quote` | 100% | Every value form |
| `core/unify` | 100% | Every type pair, occurs check |
| `core/generalize` | 100% | Every quantification case |
| `core/exhaustiveness` | 100% | Every pattern combination |
| `tao/desugar` | 100% | Every statement form, every high-level feature |
| `tao/compiler` | 95% | Every file combination, import variants |
| `tao/import` | 95% | Every import variant, circular detection |
| Integration | 90% | Every end-to-end example |

## Running Tests

```bash
# Run all tests
gleam test

# Run specific test file
gleam test test/core/infer_test.gleam

# Run specific test
gleam test test/core/infer_test.gleam --name "infer_identity_function_type"

# Watch mode (continuous testing)
fswatch -or src test | xargs -n1 -I{} gleam test

# Run only golden tests
gleam test --tag golden

# Run only unit tests
gleam test --tag unit
```
