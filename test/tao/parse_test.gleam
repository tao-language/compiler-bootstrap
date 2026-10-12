/// Tests for the Tao language parser (type definitions).
import core/error.{type Error, ExpectedToken, SyntaxError, Error as CompileError}
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/result.{try}
import gleam/string
import syntax/span.{type Span, Span}
import tao/ast as tao
import tao/parse as p

const filename = "parse_test"

fn s(r1: Int, c1: Int, r2: Int, c2: Int) -> Span {
  Span(filename, r1, c1, r2, c2)
}

fn lex(source: String) -> Result(List(p.Token), Error) {
  use tokens <- try(p.lex(filename, source))
  Ok(list.map(tokens, fn(tok) { tok.value }))
}

fn parse_stmts(source: String) -> Result(List(tao.Stmt), Error) {
  p.statements(filename, source)
}

fn parse_expr(source: String) -> Result(tao.Expr, Error) {
  p.expression(filename, source)
}

pub fn lex_type_test() {
  assert lex("type") == Ok([p.KwType])
  assert lex("type Bool") == Ok([p.KwType, p.Name("Bool")])
  assert lex("types") == Ok([p.Name("types")])
}

// ============================================================================
// Regression: leading-underscore names
//
// `is_tag_name` used to recurse on its *unchanged* input whenever the name
// started with `_`, so any source containing a name like `_and` (a function
// definition, a variable reference, a test expression) made the parser loop
// forever instead of returning.
// ============================================================================

pub fn lex_underscore_name_test() {
  assert lex("_and") == Ok([p.Name("_and")])
}

pub fn parse_underscore_var_test() {
  let src = "_and"
  assert case parse_expr(src) {
    Ok(tao.Expr(tao.Var(name), _)) -> name == "_and"
    _ -> False
  }
}

pub fn parse_underscore_app_test() {
  let src = "_and(True, True)"
  assert case parse_expr(src) {
    Ok(tao.Expr(tao.App(tao.Expr(tao.Var(name), _), args, _), _)) ->
      name == "_and" && list.length(args) == 2
    _ -> False
  }
}

pub fn parse_underscore_fn_def_test() {
  let src =
    "fn _and(a, b) -> Bool = match a, b { | True, True => True | _, _ => False }"
  assert case parse_stmts(src) {
    Ok([tao.Stmt(tao.FnDef(name, _, _, _, _), _)]) -> name == "_and"
    _ -> False
  }
}

pub fn parse_underscore_test_stmt_test() {
  let src = ">>> _and(True, True) True"
  assert case parse_stmts(src) {
    Ok([
      tao.Stmt(
        tao.Test(
          _,
          tao.Expr(tao.App(tao.Expr(tao.Var(name), _), _, _), _),
          _,
        ),
        _,
      ),
    ])
    -> name == "_and"
    _ -> False
  }
}

pub fn parse_type_def_bool_test() {
  let src = "type Bool { | True | False }"
  let expected =
    Ok([
      tao.Stmt(
        tao.TypeDef(
          "Bool",
          tao.TypeDefinition([], [
            tao.Variant("True", [], [], tao.ctr("Bool", [], s(1, 11, 1, 12))),
            tao.Variant("False", [], [], tao.ctr("Bool", [], s(1, 15, 1, 19))),
          ]),
        ),
        s(1, 1, 1, 29),
      ),
    ])
  assert parse_stmts(src) == expected
}

pub fn parse_type_def_option_test() {
  let src = "type Option(a) { | Some(a) | None }"
  let expected =
    Ok([
      tao.Stmt(
        tao.TypeDef(
          "Option",
          tao.TypeDefinition([#("a", None)], [
            tao.Variant(
              "Some",
              [],
              [#("", tao.var("a", s(1, 24, 1, 26)))],
              tao.ctr(
                "Option",
                [#("a", tao.var("a", s(1, 16, 1, 17)))],
                s(1, 16, 1, 17),
              ),
            ),
            tao.Variant(
              "None",
              [],
              [],
              tao.ctr(
                "Option",
                [#("a", tao.var("a", s(1, 26, 1, 27)))],
                s(1, 26, 1, 27),
              ),
            ),
          ]),
        ),
        s(1, 1, 1, 36),
      ),
    ])
  assert parse_stmts(src) == expected
}

pub fn parse_type_def_list_test() {
  let src = "type List(a: Type) { | Cons(x: a, xs: List(a)) | Nil }"
  let expected =
    Ok([
      tao.Stmt(
        tao.TypeDef(
          "List",
          tao.TypeDefinition(
            [#("a", Some(tao.ctr("Type", [], s(1, 12, 1, 18))))],
            [
              tao.Variant(
                "Cons",
                [],
                [
                  #("x", tao.var("a", s(1, 30, 1, 33))),
                  #(
                    "xs",
                    tao.ctr(
                      "List",
                      [#("", tao.var("a", s(1, 43, 1, 45)))],
                      s(1, 37, 1, 46),
                    ),
                  ),
                ],
                tao.ctr(
                  "List",
                  [#("a", tao.var("a", s(1, 20, 1, 21)))],
                  s(1, 20, 1, 21),
                ),
              ),
              tao.Variant(
                "Nil",
                [],
                [],
                tao.ctr(
                  "List",
                  [#("a", tao.var("a", s(1, 46, 1, 47)))],
                  s(1, 46, 1, 47),
                ),
              ),
            ],
          ),
        ),
        s(1, 1, 1, 55),
      ),
    ])
  assert parse_stmts(src) == expected
}

// ============================================================================
// Named operators (and/or/is/in)
// ============================================================================

pub fn lex_named_operators_test() {
  assert lex("and") == Ok([p.And])
  assert lex("or") == Ok([p.Or])
  assert lex("is") == Ok([p.Is])
  assert lex("in") == Ok([p.In])
  // Longer identifiers are unaffected: the keyword rules require a
  // non-word boundary, and reserved names are exact matches only.
  assert lex("andy") == Ok([p.Name("andy")])
  assert lex("inline") == Ok([p.Name("inline")])
}

pub fn parse_infix_operator_precedence_test() {
  // `or` < `and` < `is`/`in` < `+`/`-` < `*`/`/`
  let src = "1 + 2 * 3 and 4 - 1 is Int or True"
  let expected = Ok(
    tao.op2(
      tao.Or,
      tao.op2(
        tao.And,
        tao.op2(
          tao.Add,
          tao.int(1, s(1, 1, 1, 2)),
          tao.op2(
            tao.Mul,
            tao.int(2, s(1, 3, 1, 6)),
            tao.int(3, s(1, 7, 1, 10)),
            s(1, 3, 1, 10),
          ),
          s(1, 1, 1, 10),
        ),
        tao.op2(
          tao.Is,
          tao.op2(
            tao.Sub,
            tao.int(4, s(1, 11, 1, 16)),
            tao.int(1, s(1, 17, 1, 20)),
            s(1, 11, 1, 20),
          ),
          tao.ctr("Int", [], s(1, 21, 1, 27)),
          s(1, 11, 1, 27),
        ),
        s(1, 1, 1, 27),
      ),
      tao.ctr("True", [], s(1, 28, 1, 35)),
      s(1, 1, 1, 35),
    ),
  )
  assert parse_expr(src) == expected
}

pub fn parse_fn_named_operator_test() {
  let src = "fn (and)(a, b) = a"
  let expected = Ok([
    tao.Stmt(
      tao.FnDef(
        "and",
        [],
        #(
          [
            #(
              tao.pvar("a", s(1, 9, 1, 11)),
              #(None, None),
            ),
            #(
              tao.pvar("b", s(1, 11, 1, 14)),
              #(None, None),
            ),
          ],
          None,
        ),
        None,
        tao.var("a", s(1, 16, 1, 19)),
      ),
      s(1, 1, 1, 19),
    ),
  ])
  assert parse_stmts(src) == expected
}

// ============================================================================
// Field access (dot) and module-qualified names
// ============================================================================

pub fn parse_dot_access_test() {
  // `bool._and` is a Dot expression: the base is a variable, the field a
  // name (including leading-underscore names).
  let src = "bool._and"
  assert case parse_expr(src) {
    Ok(tao.Expr(tao.Dot(base, field), _)) ->
      field == "_and"
      && case base {
        tao.Expr(tao.Var(name), _) -> name == "bool"
        _ -> False
      }
    _ -> False
  }
}

pub fn parse_dot_chained_test() {
  // Dots chain left-associatively: `a.b.c` is `Dot(Dot(a, b), c)`.
  let src = "a.b.c"
  assert case parse_expr(src) {
    Ok(tao.Expr(tao.Dot(inner, "c"), _)) ->
      case inner {
        tao.Expr(tao.Dot(base, "b"), _) ->
          case base {
            tao.Expr(tao.Var(name), _) -> name == "a"
            _ -> False
          }
        _ -> False
      }
    _ -> False
  }
}

pub fn parse_dot_after_app_test() {
  // Application and field access interleave: `f(x).field`.
  let src = "f(x).field"
  assert case parse_expr(src) {
    Ok(tao.Expr(tao.Dot(inner, "field"), _)) ->
      case inner {
        tao.Expr(tao.App(tao.Expr(tao.Var(name), _), args, _), _) ->
          name == "f" && list.length(args) == 1
        _ -> False
      }
    _ -> False
  }
}

pub fn parse_let_operator_module_access_test() {
  // `let (and) = bool._and`: an operator name (parenthesized, since
  // `and` is a keyword) bound to a module-qualified definition.
  let src = "let (and) = bool._and"
  assert case parse_stmts(src) {
    Ok([tao.Stmt(tao.LetVar(name, _, value), _)]) ->
      name == "and"
      && case value {
        tao.Expr(tao.Dot(_, "_and"), _) -> True
        _ -> False
      }
    _ -> False
  }
}

// ============================================================================
// Match tuple sugar: `match a, b { | p, q => ... }`
// ============================================================================

pub fn parse_match_single_arg_test() {
  // A single argument is not wrapped in a Tuple.
  let src = "match a { | x => x }"
  let expected = Ok(
    tao.match(
      tao.var("a", s(1, 1, 1, 8)),
      [tao.Case(tao.pvar("x", s(1, 11, 1, 14)), None, tao.var("x", s(1, 15, 1, 19)))],
      s(1, 1, 1, 21),
    ),
  )
  assert parse_expr(src) == expected
}

pub fn parse_match_tuple_args_test() {
  // A comma-separated argument list is one Tuple expression, and a
  // comma-separated pattern list is one PTuple pattern.
  let src = "match a, b { | x, y => x }"
  let expected = Ok(
    tao.match(
      tao.tuple(
        [tao.var("a", s(1, 1, 1, 8)), tao.var("b", s(1, 8, 1, 11))],
        s(1, 1, 1, 11),
      ),
      [
        tao.Case(
          tao.ptuple(
            [tao.pvar("x", s(1, 14, 1, 17)), tao.pvar("y", s(1, 17, 1, 20))],
            s(1, 14, 1, 20),
          ),
          None,
          tao.var("x", s(1, 21, 1, 25)),
        ),
      ],
      s(1, 1, 1, 27),
    ),
  )
  assert parse_expr(src) == expected
}

// ============================================================================
// Relative imports
// ============================================================================

pub fn parse_import_relative_dot_test() {
  let src = "import ./bool"
  assert case parse_stmts(src) {
    Ok([tao.Stmt(tao.Import(path, alias, _), _)]) ->
      path == "./bool" && alias == "bool"
    _ -> False
  }
}

pub fn parse_import_relative_parent_test() {
  let src = "import ../bool"
  assert case parse_stmts(src) {
    Ok([tao.Stmt(tao.Import(path, alias, _), _)]) ->
      path == "../bool" && alias == "bool"
    _ -> False
  }
}

pub fn parse_import_relative_grandparent_test() {
  let src = "import ../../bool"
  assert case parse_stmts(src) {
    Ok([tao.Stmt(tao.Import(path, alias, _), _)]) ->
      path == "../../bool" && alias == "bool"
    _ -> False
  }
}

pub fn parse_import_relative_subdir_test() {
  let src = "import ./sub/bool"
  assert case parse_stmts(src) {
    Ok([tao.Stmt(tao.Import(path, alias, _), _)]) ->
      path == "./sub/bool" && alias == "bool"
    _ -> False
  }
}

pub fn parse_import_relative_parent_subdir_test() {
  let src = "import ../sub/bool"
  assert case parse_stmts(src) {
    Ok([tao.Stmt(tao.Import(path, alias, _), _)]) ->
      path == "../sub/bool" && alias == "bool"
    _ -> False
  }
}

pub fn parse_import_absolute_unchanged_test() {
  let src = "import prelude/bool"
  assert case parse_stmts(src) {
    Ok([tao.Stmt(tao.Import(path, alias, _), _)]) ->
      path == "/prelude/bool" && alias == "bool"
    _ -> False
  }
}

pub fn parse_import_relative_with_alias_test() {
  let src = "import ../bool as b"
  assert case parse_stmts(src) {
    Ok([tao.Stmt(tao.Import(path, alias, _), _)]) ->
      path == "../bool" && alias == "b"
    _ -> False
  }
}

pub fn parse_import_relative_with_scope_test() {
  let src = "import ./bool {True, False}"
  assert case parse_stmts(src) {
    Ok([tao.Stmt(tao.Import(path, alias, tao.ImportSome(names)), _)]) ->
      path == "./bool"
      && alias == "bool"
      && list.length(names) == 2
    _ -> False
  }
}

pub fn parse_import_operator_name_test() {
  // Operators are named with parentheses in imports, like `fn (*)` and
  // `let (and) = ...`: `import prelude/operators/mul {(*)}`.
  let src = "import prelude/operators/mul {(*)}"
  assert case parse_stmts(src) {
    Ok([tao.Stmt(tao.Import(path, alias, tao.ImportSome(names)), _)]) ->
      path == "/prelude/operators/mul"
      && alias == "mul"
      && names == [#("*", "*")]
    _ -> False
  }
}

// ============================================================================
// Error localization
//
// A `one_of` records a dead end for every alternative it tried. The parser
// must report the one that made the most progress (the furthest position),
// not the first alternative that gave up. Otherwise a `fn` definition with a
// bad body is misreported as "expected import" at the `fn` token.
// ============================================================================

pub fn parse_fn_type_now_parses_test() {
  // Function types are valid syntax: `fn f(g: fn(x: Int) -> Num) = 1` parses,
  // and the parameter type is a `FnT` (a function from `Int` to `Num`).
  let src = "fn f(g: fn(x: Int) -> Num) = 1"
  assert case parse_stmts(src) {
    Ok([tao.Stmt(tao.FnDef("f", _, params, _, _), _)]) ->
      case params {
        #([#(_, #(Some(tao.Expr(tao.FnT(_, _, _), _)), _)), ..], _) -> True
        _ -> False
      }
    _ -> False
  }
}

pub fn parse_fn_type_error_localized_test() {
  // A bare arrow is not a type: in `fn f(g: Int ->) = 1` the parameter type
  // is just `Int`, and the `->` is an unexpected token, localized to it
  // (col 13), not to the `fn` token (col 1) where the `import`/`fn`
  // alternatives first gave up.
  let src = "fn f(g: Int ->) = 1"
  assert case parse_stmts(src) {
    Ok(_) -> False
    Error(CompileError(_problem, span, _trace)) ->
      span.start_line == 1 && span.start_col >= 13
  }
}

pub fn parse_misplaced_token_general_test() {
  // A `}` in the middle of a parameter type. Localized to the `}`, proving the
  // fix is general and not a special case for `->`.
  let src = "fn f(x: Int } Num) = 1"
  assert case parse_stmts(src) {
    Ok(_) -> False
    Error(CompileError(ExpectedToken(")", "}"), span, _trace)) ->
      span.start_line == 1 && span.start_col == 13
    _ -> False
  }
}

pub fn parse_type_def_gadt_test() {
  let src =
    "type Vec(n: Int, a: Type) { | VCons<m>(x: a, xs: Vec(m, a)) -> Vec(m + 1, a) | VNil -> Vec(0, a) }"
  let expected =
    Ok([
      tao.Stmt(
        tao.TypeDef(
          "Vec",
          tao.TypeDefinition(
            [
              #("n", Some(tao.ctr("Int", [], s(1, 11, 1, 16)))),
              #("a", Some(tao.ctr("Type", [], s(1, 19, 1, 25)))),
            ],
            [
              tao.Variant(
                "VCons",
                [#("m", None)],
                [
                  #("x", tao.var("a", s(1, 41, 1, 44))),
                  #(
                    "xs",
                    tao.ctr(
                      "Vec",
                      [
                        #("", tao.var("m", s(1, 53, 1, 55))),
                        #("", tao.var("a", s(1, 55, 1, 58))),
                      ],
                      s(1, 48, 1, 59),
                    ),
                  ),
                ],
                tao.ctr(
                  "Vec",
                  [
                    #(
                      "",
                      tao.op2(
                        tao.Add,
                        tao.var("m", s(1, 67, 1, 69)),
                        tao.int(1, s(1, 70, 1, 73)),
                        s(1, 67, 1, 73),
                      ),
                    ),
                    #("", tao.var("a", s(1, 73, 1, 76))),
                  ],
                  s(1, 61, 1, 77),
                ),
              ),
              tao.Variant(
                "VNil",
                [],
                [],
                tao.ctr(
                  "Vec",
                  [
                    #("", tao.int(0, s(1, 91, 1, 93))),
                    #("", tao.var("a", s(1, 93, 1, 96))),
                  ],
                  s(1, 85, 1, 97),
                ),
              ),
            ],
          ),
        ),
        s(1, 1, 1, 99),
      ),
    ])
  assert parse_stmts(src) == expected
}

// ============================================================================
// Function types and anonymous functions
//
// Types are values in Tao, so function types live in the expression grammar.
// Both forms require the `fn` prefix: `fn(I)(P) -> R` is a function type,
// `fn(I)(P) -> R = B` (or `fn(I)(P) = B`) an anonymous function. A bare
// arrow (`A -> B`) is not a type.
// ============================================================================

pub fn parse_bare_arrow_is_error_test() {
  // `Int -> Num` is not a type: function types require the `fn` prefix.
  assert case parse_expr("Int -> Num") {
    Ok(_) -> False
    Error(_) -> True
  }
}

pub fn parse_fn_type_unnamed_param_test() {
  // `fn(a) -> b`: unannotated parameters are types, so this is a function
  // from type `a` to type `b` (not an anonymous function: there is no body).
  let e = parse_expr("fn(a) -> b")
  assert case e {
    Ok(tao.Expr(tao.FnT([], #([p], None), ret), _)) ->
      case p, ret.data {
        #(
          tao.Pattern(tao.PAny, _),
          #(Some(ptype), _)
        ),
        tao.Var(r)
        if r == "b" ->
          case ptype.data {
            tao.Var(v) -> v == "a"
            _ -> False
          }
        _, _ -> False
      }
    _ -> False
  }
}

pub fn parse_fn_type_named_param_test() {
  // `fn(x: a) -> b`: the named parameter is bound so the return type may
  // depend on it.
  let e = parse_expr("fn(x: a) -> b")
  assert case e {
    Ok(tao.Expr(tao.FnT([], #([p], None), ret), _)) ->
      case p, ret.data {
        #(
          tao.Pattern(tao.PVar(name), _),
          #(Some(ptype), _)
        ),
        tao.Var(r)
        if name == "x" && r == "b" ->
          case ptype.data {
            tao.Var(v) -> v == "a"
            _ -> False
          }
        _, _ -> False
      }
    _ -> False
  }
}

pub fn parse_fn_type_multi_param_test() {
  // `fn<a, b>(c, d) -> e`: two implicits, two (unannotated) type parameters.
  let e = parse_expr("fn<a, b>(c, d) -> e")
  assert case e {
    Ok(tao.Expr(tao.FnT(implicits, #([p1, p2], None), ret), _)) ->
      case implicits, ret.data {
        [#("a", None), #("b", None)],
        tao.Var(r)
        if r == "e" ->
          case p1, p2 {
            #(_, #(Some(t1), _)), #(_, #(Some(t2), _)) ->
              case t1.data, t2.data {
                tao.Var(v1), tao.Var(v2) -> v1 == "c" && v2 == "d"
                _, _ -> False
              }
            _, _ -> False
          }
        _, _ -> False
      }
    _ -> False
  }
}

pub fn parse_fn_type_nested_test() {
  // `fn(f: fn(x: Int) -> Int) -> Bool`: a function type as a parameter type.
  let e = parse_expr("fn(f: fn(x: Int) -> Int) -> Bool")
  assert case e {
    Ok(tao.Expr(tao.FnT([], #([p], None), ret), _)) ->
      case p, ret.data {
        #(_, #(Some(inner), _)),
        tao.Ctr("Bool", _, _)
        ->
          case inner.data {
            tao.FnT([], #([ip], None), iret) ->
              case ip, iret.data {
                #(_, #(Some(it), _)), tao.Ctr("Int", _, _) ->
                  case it.data {
                    tao.Ctr("Int", _, _) -> True
                    _ -> False
                  }
                _, _ -> False
              }
            _ -> False
          }
        _, _ -> False
      }
    _ -> False
  }
}

pub fn parse_fn_type_missing_body_is_error_test() {
  // `fn(x: a)` with neither `->` nor `=` is not a complete expression.
  assert case parse_expr("fn(x: a)") {
    Ok(_) -> False
    Error(_) -> True
  }
}

pub fn parse_fn_type_implicit_test() {
  // `fn<a>(a) -> a`: an unannotated implicit type variable.
  let e = parse_expr("fn<a>(a) -> a")
  assert case e {
    Ok(tao.Expr(tao.FnT(implicits, _, _), _)) ->
      case implicits {
        [#("a", None)] -> True
        _ -> False
      }
    _ -> False
  }
}

pub fn parse_fn_type_typed_implicit_test() {
  // `fn<a: t>(x: a) -> t`: a typed implicit; the param and return reference it.
  let e = parse_expr("fn<a: t>(x: a) -> t")
  assert case e {
    Ok(tao.Expr(tao.FnT(implicits, params, ret), _)) -> {
      let imp = case implicits {
        [#("a", Some(t)), ..] -> Some(t)
        _ -> None
      }
      let par = case params {
        #([pp], _) -> Some(pp)
        _ -> None
      }
      case imp, par {
        Some(imp_t), Some(pp) -> {
          let imp_ref = case imp_t.data {
            tao.Var(v) -> v == "t"
            _ -> False
          }
          let param_ref = case pp {
            #(_, #(Some(t), _)) ->
              case t.data {
                tao.Var(v) -> v == "a"
                _ -> False
              }
            _ -> False
          }
          let ret_ref = case ret.data {
            tao.Var(v) -> v == "t"
            _ -> False
          }
          imp_ref && param_ref && ret_ref
        }
        _, _ -> False
      }
    }
    _ -> False
  }
}

// ============================================================================
// Anonymous functions (`fn(x) = y` and friends)
// ============================================================================

/// A parsed expression is an anonymous `Fn` with the given implicits and
/// exactly `n` parameters (structure only, ignoring spans and the body).
fn is_anon_fn(implicits: List(#(String, Option(tao.Expr))), n: Int, e: tao.Expr) -> Bool {
  case e.data {
    tao.Fn(None, imps, #(ps, None), _, _body) ->
      list.length(ps) == n
      && list.length(imps) == list.length(implicits)
      && list.all(
        list.zip(imps, implicits),
        fn(pair) {
          case pair {
            #(a, b) if a.0 == b.0 -> True
            _ -> False
          }
        },
      )
    _ -> False
  }
}

pub fn parse_fn_anon_simple_test() {
  // `fn(x) = y`: an anonymous function of one unannotated parameter.
  let e = parse_expr("fn(x) = y")
  assert case e {
    Ok(expr) -> is_anon_fn([], 1, expr)
    _ -> False
  }
}

pub fn parse_fn_anon_typed_test() {
  // `fn(x: a) = y`.
  let e = parse_expr("fn(x: a) = y")
  assert case e {
    Ok(tao.Expr(tao.Fn(None, [], #([p], None), None, body), _)) ->
      case p, body.data {
        #(
          tao.Pattern(tao.PVar(name), _),
          #(Some(t), _)
        ),
        tao.Var(r)
        if name == "x" && r == "y" ->
          case t.data {
            tao.Var(v) -> v == "a"
            _ -> False
          }
        _, _ -> False
      }
    _ -> False
  }
}

pub fn parse_fn_anon_return_test() {
  // `fn(x: a) -> b = y`: an explicit return type.
  let e = parse_expr("fn(x: a) -> b = y")
  assert case e {
    Ok(tao.Expr(tao.Fn(None, [], _, Some(ret), body), _)) ->
      case ret.data, body.data {
        tao.Var(r), tao.Var(b) if r == "b" && b == "y" -> True
        _, _ -> False
      }
    _ -> False
  }
}

pub fn parse_fn_anon_implicit_test() {
  // `fn<a>(x: a) -> b = y`: an unannotated implicit.
  let e = parse_expr("fn<a>(x: a) -> b = y")
  assert case e {
    Ok(expr) -> is_anon_fn([#("a", None)], 1, expr)
    _ -> False
  }
}

pub fn parse_fn_anon_typed_implicit_test() {
  // `fn<a: T>(x: a) -> b = y`: a typed implicit.
  let e = parse_expr("fn<a: T>(x: a) -> b = y")
  assert case e {
    Ok(tao.Expr(tao.Fn(None, [#("a", Some(t))], _, _, _), _)) ->
      case t.data {
        tao.Ctr("T", _, _) -> True
        _ -> False
      }
    _ -> False
  }
}

pub fn parse_fn_anon_multi_implicit_test() {
  // `fn<a, b>(x, y) -> b = z`: two implicits, two parameters.
  let e = parse_expr("fn<a, b>(x, y) -> b = z")
  assert case e {
    Ok(expr) -> is_anon_fn([#("a", None), #("b", None)], 2, expr)
    _ -> False
  }
}

pub fn parse_fn_anon_block_test() {
  // `fn(x) { let y = x }`: a block body (a `Do`).
  let e = parse_expr("fn(x) { let y = x }")
  assert case e {
    Ok(tao.Expr(tao.Fn(None, [], #([_], None), None, body), _)) ->
      case body.data {
        tao.Do([tao.Stmt(tao.LetVar("y", _, _), _)]) -> True
        _ -> False
      }
    _ -> False
  }
}

pub fn parse_fn_anon_zero_params_test() {
  // `fn() = y`: zero parameters.
  let e = parse_expr("fn() = y")
  assert case e {
    Ok(expr) -> is_anon_fn([], 0, expr)
    _ -> False
  }
}

pub fn parse_fn_type_zero_params_test() {
  // `fn() -> a`: a zero-parameter function type.
  let e = parse_expr("fn() -> a")
  assert case e {
    Ok(tao.Expr(tao.FnT([], #([], None), ret), _)) ->
      case ret.data {
        tao.Var(r) -> r == "a"
        _ -> False
      }
    _ -> False
  }
}

pub fn parse_let_fn_type_paren_test() {
  // `let t: (fn(x: a) -> b) = c`: a parenthesized function type annotation.
  let src = "let t: (fn(x: a) -> b) = c"
  assert case parse_stmts(src) {
    Ok([tao.Stmt(tao.LetVar("t", Some(tao.Expr(tao.FnT(_, _, _), _)), tao.Expr(tao.Var(v), _)), _)])
    -> v == "c"
    _ -> False
  }
}

pub fn parse_let_fn_type_ambiguous_test() {
  // `let t: fn(x: a) -> b = c` is ambiguous: the `fn` form is parsed as an
  // anonymous function (its body swallows `= c`), so the let's `=` is missing
  // and the source is a parse error. The parenthesized form is the escape
  // hatch (see `parse_let_fn_type_paren_test`).
  let src = "let t: fn(x: a) -> b = c"
  assert case parse_stmts(src) {
    Ok(_) -> False
    Error(_) -> True
  }
}

// ============================================================================
// Placeholders (`_`, `_N`): anonymous-function arguments
//
// A placeholder expression is desugared at parse time to an anonymous `Fn` whose
// parameters are the placeholders (1-indexed; `_` is `_1`), each replaced by the
// corresponding parameter variable.
// ============================================================================

/// A parsed expression is an anonymous `Fn` with exactly `n` parameters.
fn is_ph_fn(n: Int, e: tao.Expr) -> Bool {
  case e.data {
    tao.Fn(None, [], #(ps, None), None, _body) ->
      list.length(ps) == n
    _ -> False
  }
}

pub fn parse_placeholder_single_test() {
  // `_ + 1` -> `fn(x1) = x1 + 1`.
  let e = parse_expr("_ + 1")
  assert case e {
    Ok(expr) -> is_ph_fn(1, expr)
    _ -> False
  }
}

pub fn parse_placeholder_reversed_test() {
  // `1 / _` -> `fn(x1) = 1 / x1`.
  let e = parse_expr("1 / _")
  assert case e {
    Ok(expr) -> is_ph_fn(1, expr)
    _ -> False
  }
}

pub fn parse_placeholder_numbered_test() {
  // `_1 + _2` -> `fn(x1, x2) = x1 + x2` (two parameters).
  let e = parse_expr("_1 + _2")
  assert case e {
    Ok(expr) -> is_ph_fn(2, expr)
    _ -> False
  }
}

pub fn parse_placeholder_high_index_test() {
  // `_3` alone -> a three-parameter function returning its third argument.
  let e = parse_expr("_3")
  assert case e {
    Ok(expr) -> is_ph_fn(3, expr)
    _ -> False
  }
}

pub fn parse_placeholder_zero_is_error_test() {
  // `_0` is not a valid position (positions are 1-based): a clear syntax error.
  assert case parse_expr("_0") {
    Ok(_) -> False
    Error(_) -> True
  }
}

pub fn parse_placeholder_too_large_test() {
  // `_N` desugars to an N-parameter function, so N is capped (100):
  // `_101` is a syntax error, `_100` parses.
  assert case parse_expr("_101") {
    Ok(_) -> False
    Error(CompileError(SyntaxError(msg), _, _)) ->
      string.contains(msg, "too large")
    _ -> False
  }
  assert case parse_expr("_100") {
    Ok(expr) -> is_ph_fn(100, expr)
    _ -> False
  }
}

pub fn parse_let_underscore_test() {
  // `let _ = 1` is a wildcard binding: `_` is a `Placeholder` token (not a
  // name), so `let_var` accepts it and keeps it under the name `"_"`.
  let src = "let _ = 1"
  assert case parse_stmts(src) {
    Ok([tao.Stmt(tao.LetVar(name, _, tao.Expr(tao.Lit(_), _)), _)]) ->
      name == "_"
    _ -> False
  }
}

pub fn parse_let_numbered_underscore_test() {
  // `let _1 = 1` is also a wildcard binding (a numbered placeholder is not a
  // let name either).
  let src = "let _1 = 1"
  assert case parse_stmts(src) {
    Ok([tao.Stmt(tao.LetVar(name, _, _), _)]) -> name == "_"
    _ -> False
  }
}

pub fn lex_placeholder_test() {
  // `_`, `_1`, `_2` are placeholder tokens; `_and`, `_1a`, `_1_` are names.
  assert lex("_") == Ok([p.Placeholder(None)])
  assert lex("_1") == Ok([p.Placeholder(Some(1))])
  assert lex("_2") == Ok([p.Placeholder(Some(2))])
  assert lex("_and") == Ok([p.Name("_and")])
  assert lex("_1a") == Ok([p.Name("_1a")])
  assert lex("_1_") == Ok([p.Name("_1_")])
}

pub fn parse_placeholder_underscore_still_wildcard_test() {
  // `_` in a pattern is still the wildcard (a `PAny`), not a placeholder.
  let src = "match x { | _ => 1 }"
  assert case parse_expr(src) {
    Ok(tao.Expr(tao.Match(_, cases), _)) ->
      case cases {
        [tao.Case(tao.Pattern(tao.PAny, _), _, _)] -> True
        _ -> False
      }
    _ -> False
  }
}

pub fn parse_stmts_semicolon_separated_test() {
  // Statements may be separated by `;` as well as newlines.
  let stmts = parse_stmts("let x = 1; let y = 2")
  assert case stmts {
    Ok([tao.Stmt(tao.LetVar("x", _, _), _), tao.Stmt(tao.LetVar("y", _, _), _)]) -> True
    _ -> False
  }
}

pub fn parse_stmts_trailing_semicolon_test() {
  // A trailing `;` after the last statement is allowed.
  let stmts = parse_stmts("let x = 1;")
  assert case stmts {
    Ok([tao.Stmt(tao.LetVar("x", _, _), _)]) -> True
    _ -> False
  }
}

pub fn parse_stmts_mixed_separators_test() {
  // Newline and `;` separation may be mixed.
  let stmts = parse_stmts("let x = 1\nlet y = 2; let z = 3")
  assert case stmts {
    Ok([tao.Stmt(tao.LetVar("x", _, _), _), tao.Stmt(tao.LetVar("y", _, _), _), tao.Stmt(tao.LetVar("z", _, _), _)]) ->
      True
    _ -> False
  }
}

pub fn parse_fn_block_semicolon_test() {
  // A block body accepts `;` after statements too.
  let e = parse_expr("fn(x) { let y = x; let z = y }")
  assert case e {
    Ok(tao.Expr(tao.Fn(None, [], #([_], None), None, body), _)) ->
      case body.data {
        tao.Do([tao.Stmt(tao.LetVar("y", _, _), _), tao.Stmt(tao.LetVar("z", _, _), _)]) ->
          True
        _ -> False
      }
    _ -> False
  }
}
