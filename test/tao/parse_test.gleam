/// Tests for the Tao language parser (type definitions).
import core/error.{type Error}
import gleam/list
import gleam/option.{None, Some}
import gleam/result.{try}
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
        #([], None),
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
