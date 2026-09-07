/// Tests for the Tao language parser (type definitions).
import core/error.{type Error}
import gleam/list
import gleam/option.{None, Some}
import gleam/result.{try}
import syntax/span.{type Span, Span}
import tao/parse as p
import tao/ast as tao

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

pub fn lex_type_test() {
  assert lex("type") == Ok([p.KwType])
  assert lex("type Bool")
    == Ok([p.KwType, p.Name("Bool")])
  assert lex("types") == Ok([p.Name("types")])
}

pub fn parse_type_def_bool_test() {
  let src = "type Bool { | True | False }"
  let expected =
    Ok([
      tao.Stmt(
        tao.TypeDef(
          "Bool",
          tao.TypeDefinition([], [
            tao.Variant(
              "True",
              [],
              [],
              tao.ctr("Bool", [], s(1, 11, 1, 12)),
            ),
            tao.Variant(
              "False",
              [],
              [],
              tao.ctr("Bool", [], s(1, 15, 1, 19)),
            ),
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
          tao.TypeDefinition(
            [#("a", None)],
            [
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
            ],
          ),
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

pub fn parse_type_def_gadt_test() {
  let src = "type Vec(n: Int, a: Type) { | VCons<m>(x: a, xs: Vec(m, a)) -> Vec(m + 1, a) | VNil -> Vec(0, a) }"
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
                      [#("", tao.var("m", s(1, 53, 1, 55))), #("", tao.var("a", s(1, 55, 1, 58)))],
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
                  [#("", tao.int(0, s(1, 91, 1, 93))), #("", tao.var("a", s(1, 93, 1, 96)))],
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
