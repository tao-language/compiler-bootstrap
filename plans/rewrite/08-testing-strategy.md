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
│   ├── test_api_test.gleam    # Test framework (REPL-style extraction)
│   ├── examples_test.gleam    # End-to-end example programs
│   └── golden_test.gleam      # Tao → desugar → compile → format round-trip
├── cli/
│   ├── run_test.gleam         # Run mode tests
│   ├── check_test.gleam       # Check mode tests
│   └── test_test.gleam        # Test mode tests (run test statements)
└── integration/
    └── e2e_test.gleam         # Full pipeline tests (Tao source → Core value)
```

## Testing Convention: Assert-Based Testing

> **Tests must use `assert` statements** — Every test must verify correctness using `assert`, not just return `True`/`False`.

GleeUnit 1.x requires tests to use `assert expr == expected` to actually verify correctness. Returning `True` or `False` from a case expression passes the test regardless of the actual result.

### ✅ Correct: Assert-Based Testing

```gleam
pub fn tokenize_integer_literal_test() {
  let tokens = tokenize("42")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Integer", value: "42", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn infer_identity_function_test() {
  let state = initial_state([], "True")
  let result = infer(state, lam)
  assert result.errors == []
}

pub fn check_type_mismatch_test() {
  let result = check(state, lit, val)
  case result {
    State(errors: [TypeMismatch(..)], _) -> True
    _ -> False
  }
}
```

### ❌ Incorrect: Silent Pass

```gleam
// This passes regardless of the actual result!
pub fn tokenize_integer_literal_test() {
  let tokens = tokenize("42")
  case tokens {
    [Token(kind: "Integer", value: "42", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}
```

**Key rules:**

1. Use `assert` to verify actual values and results
2. Use `assert case ... -> True` when pattern matching on results
3. Use `assert result.errors == []` for error checking
4. Test functions must be `pub` and end with `_test` (GleeUnit 1.x requirement)
5. Always check `list.length` before pattern matching for better error messages

## Test Examples

### Unit Tests: Lexer (lexer_test.gleam)

```gleam
import gleeunit
import syntax/lexer.{tokenize, tokenize_with_filename, Token}
import gleam/list
import gleam/int

pub fn main() {
  gleeunit.main()
}

pub fn tokenize_integer_literal_test() {
  let tokens = tokenize("42")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Integer", value: "42", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_string_with_escape_sequences_test() {
  let tokens = tokenize("\"hello\\nworld\"")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "String", value: "hello\nworld", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_multiple_tokens_with_correct_positions_test() {
  let tokens = tokenize("let x = 42")
  assert list.length(tokens) == 5
}

pub fn tokenize_comments_single_line_test() {
  let tokens = tokenize("// comment\nlet x = 42")
  assert list.length(tokens) == 5
}

pub fn tokenize_block_comments_test() {
  let tokens = tokenize("/* block comment */ let x = 42")
  assert list.length(tokens) == 4  // let, x, =, 42
}

pub fn tokenize_operators_with_correct_kinds_test() {
  let tokens = tokenize("+ - * / == != < > <= >= && ||")
  assert list.length(tokens) == 14  // 13 operators + Eof
}

pub fn tokenize_reserved_keywords_test() {
  let tokens = tokenize("fn let in match type of import as")
  assert list.length(tokens) == 9  // 8 keywords + Eof
}

pub fn handle_empty_input_test() {
  let tokens = tokenize("")
  assert list.length(tokens) == 1  // Only Eof
}

pub fn handle_whitespace_only_input_test() {
  let tokens = tokenize("   \n\t  ")
  assert list.length(tokens) == 1  // Only Eof
}

pub fn tokenize_unicode_characters_test() {
  let tokens = tokenize("\"こんにちは\"")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "String", value: "こんにちは", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}
```

### Unit Tests: Grammar Parser (grammar_test.gleam)

```gleam
import gleeunit
import syntax/grammar.{parse, alt, ref, seq, opt, many, choice, delimited}
import core/ast.{type Span}

pub fn parse_optional_pattern_test() {
  let result = parse(opt(ref("Name")), "foo")
  case result {
    ParseResult(ast: "foo", errors: []) -> True
    _ -> False
  }
}

pub fn parse_many_pattern_test() {
  let result = parse(many(ref("Name")), "foo bar baz")
  case result {
    ParseResult(ast: ["foo", "bar", "baz"], errors: []) -> True
    _ -> False
  }
}

pub fn parse_empty_many_test() {
  let result = parse(many(ref("Name")), "")
  assert result.errors == []
}

pub fn parse_delimited_list_test() {
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

pub fn parse_empty_delimited_list_test() {
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

pub fn accumulate_multiple_parse_errors_test() {
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
  assert result.errors.length >= 2
}

pub fn produce_accurate_spans_from_tokens_test() {
  let grammar = simple_grammar()
  let result = parse(grammar, "let x = 42", "error_node")
  case result {
    ParseResult(ast: _, errors: []) -> {
      // Check that the AST has spans from the actual tokens
      let start = span_start(result.ast)
      let end = span_end(result.ast)
      assert start == Span("test", 1, 1, 1, 3)  // "let"
      assert end == Span("test", 1, 1, 1, 12)   // "42"
    }
    _ -> False
  }
}
```

### Unit Tests: Formatter (formatter_test.gleam)

```gleam
import gleeunit
import syntax/formatter.{render, concat, text, line, nest, group, join, space_sep, comma_sep, parens}

pub fn join_with_comma_separator_test() {
  let doc = join(concat([text(","), line()]), [text("a"), text("b"), text("c")])
  assert render(doc, 80) == "a,\nb,\nc"
}

pub fn space_separated_list_test() {
  let doc = space_sep([text("a"), text("b"), text("c")])
  assert render(doc, 80) == "a b c"
}

pub fn parenthesize_when_too_long_test() {
  let doc = group(concat([text("this is a very long expression that should wrap"), text(" and continue")]))
  let rendered = render(doc, 20)
  assert case rendered {
    "(" <> _ <> ")" -> True
    _ -> False
  }
}

pub fn nest_increases_indentation_test() {
  let doc = nest(2, concat([text("  a"), line(), text("  b")]))
  assert render(doc, 80) == "  a\n  b"
}

pub fn empty_text_produces_empty_doc_test() {
  let doc = text("")
  assert render(doc, 80) == ""
}
```

### Unit Tests: Core Infer (infer_test.gleam)

```gleam
import gleeunit
import core/ast.{Term, Var, Lam, Pi, App, Hole, Typ, Unit}
import core/eval.{Value, VLam, VPi, VNeut, HVar, HHole}
import core/infer.{infer, check}
import core/state.{State, initial_state}

pub fn infer_identity_function_type_test() {
  // fn(x: a) -> a
  let body = Var(0, "x")
  let lam = Lam(("x", Hole(-1)), body)

  let state = initial_state([], "True")
  let result = infer(state, lam)

  // Should produce: ∀a. a → a
  assert result.errors == []
}

pub fn check_lambda_with_correct_type_annotation_test() {
  // (fn(x) { x } : ∀a. a → a)
  let body = Var(0, "x")
  let lam = Lam(("x", Hole(-1)), body)
  let ann = Ann(lam, Hole(-1))

  let state = initial_state([], "True")
  let result = check(state, ann, VPi([], "a", [], VNeut(HHole(1), []), Var(0, "a")))

  assert result.errors == []
}

pub fn infer_type_mismatch_accumulates_error_test() {
  // let x: Int = "hello"
  let state = initial_state([], "True")
  let result = check(state, Lit(String("hello")), VLit(ILit(0)))

  case result {
    State(errors: [TypeMismatch(_, _, _, _)], _) -> True
    _ -> False
  }
}

pub fn infer_application_of_identity_function_test() {
  // (fn(x) { x }) 42
  let body = Var(0, "x")
  let lam = Lam(("x", Hole(-1)), body)
  let app = App(lam, Lit(ILit(42)))

  let state = initial_state([], "True")
  let result = infer(state, app)

  assert result.errors == []
}

pub fn handle_undefined_variable_error_test() {
  let state = initial_state([], "True")
  let result = infer(state, Var(5, "x"))  // Var(5) is out of scope

  case result {
    State(errors: [VarUndefined(5, _)], _) -> True
    _ -> False
  }
}

pub fn infer_pi_type_construction_test() {
  // Πx:a. b (dependent function type)
  let domain = Var(0, "a")
  let codomain = Var(1, "b")  // b is from outer scope
  let pi = Pi(domain, codomain)

  let state = initial_state([], "True")
  let result = infer(state, pi)

  assert result.errors == []
}

pub fn handle_constructor_undefined_error_test() {
  let state = initial_state([], "True")
  let result = infer(state, Ctr("UndefinedCtor", Hole(-1)))

  case result {
    State(errors: [CtrUndefined("UndefinedCtor", _)], _) -> True
    _ -> False
  }
}

pub fn infer_let_binding_test() {
  // let x = 42; x
  let let_term = Let("x", Lit(ILit(42)), Var(0, "x"))
  let state = initial_state([], "True")
  let result = infer(state, let_term)

  assert result.errors == []
}

pub fn handle_infinite_type_error_test() {
  // x : ∀x. x → x (infinite type)
  let state = initial_state([], "True")
  let result = check(state, Hole(-1), VPi([], "x", [], Var(0, "x"), Hole(-1)))

  case result {
    State(errors: [InfiniteType(_, _, _, _)], _) -> True
    _ -> False
  }
}
```

### Unit Tests: Core Eval (eval_test.gleam)

```gleam
import gleeunit
import core/ast.{Term, Var, Lam, App, Lit}
import core/eval.{evaluate, Value, VLit}

pub fn evaluate_identity_function_application_test() {
  // (fn(x) { x }) 42 → 42
  let body = Var(0, "x")
  let lam = Lam(("x", Hole(-1)), body)
  let app = App(lam, Lit(ILit(42)))

  let result = evaluate(app)
  case result {
    VLit(ILit(42)) -> True
    _ -> False
  }
}

pub fn evaluate_constant_test() {
  // 42 → 42
  let result = evaluate(Lit(ILit(42)))
  case result {
    VLit(ILit(42)) -> True
    _ -> False
  }
}

pub fn evaluate_nested_lambda_test() {
  // (fn(x) { fn(y) { x + y }}) 1 2 → 3
  let body = App(App(Var(0, "+"), Var(1, "x")), Var(0, "y"))
  let inner_lam = Lam(("y", Hole(-1)), body)
  let outer_lam = Lam(("x", Hole(-1)), inner_lam)
  let app1 = App(outer_lam, Lit(ILit(1)))
  let app2 = App(app1, Lit(ILit(2)))

  let result = evaluate(app2)
  case result {
    VLit(ILit(3)) -> True
    _ -> False
  }
}

pub fn evaluate_church_numeral_2_test() {
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

pub fn evaluate_addition_ffi_test() {
  // +(42, 1) → 43
  let add = Call("add", [Lit(ILit(42)), Lit(ILit(1))], Hole(-1))
  let state = initial_state([], tao_ffis(), "True", "False")
  let result = evaluate_with_ffi(state.ffi, add)

  case result {
    VLit(ILit(43)) -> True
    _ -> False
  }
}

pub fn handle_step_limit_error_test() {
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
import gleeunit
import core/ast.{Term, Var, Lam, App, Lit}
import core/eval.{Value, VLam, VLit, VNeut, HVar}
import core/quote.{quote}

pub fn quote_lambda_value_back_to_term_test() {
  let body = Var(0, "x")
  let lam = Lam(("x", Hole(-1)), body)
  let value = VLam([], "x", [VNeut(HVar(0), [])], lam)

  let result = quote(value)
  case result {
    Lam(("x", _), body, _) if body == Var(0, "x") -> True
    _ -> False
  }
}

pub fn quote_literal_value_test() {
  let value = VLit(ILit(42))
  let result = quote(value)
  case result {
    Lit(ILit(42)) -> True
    _ -> False
  }
}

pub fn quote_nested_lambda_test() {
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

pub fn quote_does_not_evaluate_test() {
  // Quote should NOT call eval — this is a critical invariant
  let called_eval = ref(False)
  let value = VLam([], "x", [], Lam(("x", Hole(-1)), Var(0, "x")))

  let result = quote_with_trace(value, fn() -> called_eval = True)
  assert called_eval == False  // eval should never be called
}
```

### Unit Tests: Core Unify (unify_test.gleam)

```gleam
import gleeunit
import core/ast.{Term, Hole, Var, Lit}
import core/eval.{Value, VLit, VNeut, HHole}
import core/unify.{unify}
import core/state.{State, initial_state}

pub fn unify_two_identical_values_test() {
  let state = initial_state([], "True")
  let result = unify(state, VLit(ILit(42)), VLit(ILit(42)))
  assert result.errors == []
}

pub fn unify_hole_with_concrete_type_test() {
  let state = initial_state([], "True")
  let result = unify(state, VNeut(HHole(1), []), VLit(I32T))
  assert result.errors == []
}

pub fn unify_incompatible_types_produces_error_test() {
  let state = initial_state([], "True")
  let result = unify(state, VLit(I32T), VLit(F64T))
  case result {
    State(errors: [TypeMismatch(_, _, _, _)], _) -> True
    _ -> False
  }
}

pub fn unify_pi_types_with_matching_domains_and_codomains_test() {
  let state = initial_state([], "True")
  let dom = VNeut(HHole(1), [])
  let codom1 = VNeut(HVar(0), [])
  let codom2 = VNeut(HVar(0), [])
  let result = unify(state, VPi([], "a", [], dom, codom1), VPi([], "a", [], dom, codom2))
  assert result.errors == []
}

pub fn handle_occurs_check_should_allow_recursive_types_test() {
  let state = initial_state([], "True")
  let result = unify(state, VNeut(HHole(1), []), VPi([], "a", [], VNeut(HHole(1), []), VNeut(HVar(0), [])))
  assert result.errors == []  // Should not error (we allow recursive types)
}
```

### Integration Tests: Compiler (compiler_test.gleam)

```gleam
import gleeunit
import tao/compiler.{compile_tao}
import core/eval.{Value, VLit}

pub fn compile_simple_addition_test() {
  let source = "let x = 42 + 1; x"
  let result = compile_tao(source, "test.tao")
  assert result.errors == []
  assert result.value == VLit(ILit(43))
}

pub fn compile_function_definition_and_call_test() {
  let source = """
    fn add(a, b) { a + b }
    add(1, 2)
  """
  let result = compile_tao(source, "test.tao")
  assert result.errors == []
  assert result.value == VLit(ILit(3))
}

pub fn compile_fibonacci_test() {
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
  assert result.errors == []
  assert result.value == VLit(ILit(8))
}

pub fn compile_with_parse_errors_accumulates_errors_test() {
  let source = """
    fn foo(x
    let bar = 
    type Baz
  """
  let result = compile_tao(source, "test.tao")
  assert result.errors.length >= 3
}

pub fn compile_with_type_errors_accumulates_errors_test() {
  let source = """
    let x: Int = "hello"
    let y: String = 42
  """
  let result = compile_tao(source, "test.tao")
  assert result.errors.length >= 2
}

pub fn compile_imported_module_test() {
  let modules = [
    #("math.tao", "fn add(a, b) { a + b }"),
    #("main.tao", "import math { add }; add(1, 2)"),
  ]
  let result = compile_multi_module(modules, "main.tao")
  assert result.errors == []
  assert result.value == VLit(ILit(3))
}

pub fn module_not_found_creates_empty_bindings_test() {
  let modules = [
    #("a.tao", "import nonexistent { foo }\nlet x = foo"),
  ]
  let result = compile_multi_module(modules, "a.tao")
  case result {
    State(errors: [ImportError.ModuleNotFound(_, _)], _) -> True  // Error accumulated in state
    _ -> False
  }
}

pub fn name_not_found_deferred_to_type_checker_test() {
  let modules = [
    #("a.tao", "import b { undefined_name }"),
  ]
  let result = compile_multi_module(modules, "a.tao")
  case result {
    State(errors: [TypeError.VarUndefined(_, _)], _) -> True  // Type checker catches undefined name
    _ -> False
  }
}
```

### Golden Tests: Round-Trip (golden_test.gleam)

```gleam
import gleeunit
import tao/syntax.{type TaoSyntax}
import core/syntax.{type CoreSyntax}
import core/quote
import core/eval

pub fn tao_parse_format_parse_produces_same_ast_test() {
  let source = """
    fn add(a, b) { a + b }
    let x = add(1, 2)
  """
  let parsed = TaoSyntax.parse(source)
  let formatted = TaoSyntax.format(parsed.ast)
  let reparsed = TaoSyntax.parse(formatted)

  assert parsed.ast == reparsed.ast
}

pub fn core_term_eval_quote_term_produces_structurally_equal_term_test() {
  let source = "let x = 42; x"
  let parsed = CoreSyntax.parse(source)
  let quoted = quote.quote(eval.evaluate(parsed.ast))

  // quoted should be structurally equivalent to parsed
  assert structural_equal(parsed.ast, quoted)
}

pub fn core_parse_format_parse_produces_same_term_test() {
  let source = "let x = 42; x"
  let parsed = CoreSyntax.parse(source)
  let formatted = CoreSyntax.format(parsed.ast)
  let reparsed = CoreSyntax.parse(formatted)

  assert parsed.ast == reparsed.ast
}

pub fn tao_to_core_desugar_format_produces_valid_core_test() {
  let source = "fn add(a, b) { a + b }"
  let tao_expr = TaoSyntax.parse(source)
  let core_term = tao_desugar.desugar(tao_expr.ast)
  let core_formatted = CoreSyntax.format(core_term)

  // Should parse back as a valid Core term
  let reparsed = CoreSyntax.parse(core_formatted)
  assert reparsed.errors == []
}
```

### End-to-End Tests (e2e_test.gleam)

```gleam
import gleeunit
import tao/compiler.{compile_tao}
import core/eval.{Value, VLit}

pub fn complete_pipeline_fib_10_equals_55_test() {
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
  assert result.errors == []
  assert result.value == VLit(ILit(55))
}

pub fn complete_pipeline_map_and_filter_test() {
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
  assert result.errors == []
  // evens should be [2, 4]
  assert result.value == VList([VLit(ILit(2)), VLit(ILit(4))])
}

pub fn complete_pipeline_generator_stream_test() {
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
  assert result.errors == []
  assert result.value == VList([VLit(ILit(1)), VLit(ILit(2)), VLit(ILit(3))])
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

## Tao Test Framework (REPL Style)

Tests in Tao source files use a REPL-style syntax with `///` doc comments:

```tao
// Example: test statements in a Tao file

/// > 1 + 2 ~> 3
/// > "hello" <> " world" ~> "hello world"
/// > fib(10) ~> 55

fn fib(n) {
  // ...
}
```

**How it works:**
1. The Tao parser extracts `/// > expr ~> expected` from doc comments
2. Each line becomes a `TestStatement` in the AST
3. The test framework compiles and evaluates each expression
4. The result is compared against the expected value

**Test framework in `test_api.gleam`:**
- `extract_tests(source)` → List(TestStatement)
- `run_tests(tests, context)` → List(TestResult)
- `run_tests_in_file(path, context)` → List(TestResult)

**CLI `tao test` command:**
- Scans source files for test statements
- Runs each test
- Reports: pass count, fail count, total
- Failed tests show expected vs. actual values

**Test result format:**
```gleam
pub type TestResult {
  Pass(test_name: Option(String))
  Fail(test_name: Option(String), expected: Value, actual: Value)
  Skipped(test_name: Option(String), reason: String)
}
```

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

# Run Tao tests (test statements in source files)
tao test main.tao
tao test --filter "addition"  # Run only tests matching "addition"
tao test --list               # List all test names
```
