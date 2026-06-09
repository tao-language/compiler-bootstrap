import core/ast.{type AST}
import core/parse.{parse}
import gleam/option.{type Option, None, Some}
import gleeunit
import syntax/span.{Span}

pub fn main() {
  gleeunit.main()
}

const s = Span("", 0, 0, 0, 0)

fn p(source: String) -> Option(AST) {
  case parse(source) {
    Ok(ast) -> Some(ast)
    Error(_) -> None
  }
}

pub fn parse_error_empty_test() {
  assert p("") == None
}

pub fn parse_typ_test() {
  assert p("%Type ") == Some(ast.typ(0, s))
}
// pub fn parse_hole_test() { todo }
// pub fn parse_lit_test() { todo }
// pub fn parse_litt_test() { todo }
// pub fn parse_var_test() { todo }
// pub fn parse_ctr_test() { todo }
// pub fn parse_rcd_test() { todo }
// pub fn parse_rcdt_test() { todo }
// pub fn parse_ann_test() { todo }
// pub fn parse_lam_test() { todo }
// pub fn parse_pi_test() { todo }
// pub fn parse_fix_test() { todo }
// pub fn parse_app_test() { todo }
// pub fn parse_typedef_test() { todo }
// pub fn parse_let_test() { todo }
// pub fn parse_match_test() { todo }
// pub fn parse_call_test() { todo }
// pub fn parse_err_test() { todo }
