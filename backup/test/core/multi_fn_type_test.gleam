import gleeunit/should
import gleam/list
import syntax/grammar.{Span}
import tao/syntax.{parse_module as tao_parse_module}
import tao/test_api.{strip_test_lines, exprs_to_stmts}
import tao/ast.{Module}
import tao/desugar.{desugar_module}
import tao/global_context.{new_context, with_prelude}
import core/infer.{infer}
import core/state as st
import gleeunit

pub fn main() {
  gleeunit.main()
}

/// Helper: desugar and type-check a module, return errors.
fn check_module(source: String, filename: String) -> List(st.Error) {
  let code = strip_test_lines(source)
  let parse_result = tao_parse_module(code, filename)
  case parse_result.errors {
    [_, ..] -> parse_result.errors |> list.map(fn(_) { st.SyntaxError(Span(filename, 0, 0, 0, 0), "parse", "error", filename) })
    [] -> {
      let body = exprs_to_stmts(parse_result.ast)
      let module_ = Module(filename, body, Span(filename, 0, 0, 0, 0))
      let ctx = new_context() |> with_prelude()
      let #(core_term, dc) = desugar_module(module_, ctx)
      let merged_ctrs = list.append(dc.ctrs, st.initial_state.ctrs)
      let s = st.State(..st.initial_state, ctrs: merged_ctrs)
      let #(_, _, final_state) = infer(s, core_term)
      final_state.errors
    }
  }
}

/// Single function with match — baseline
pub fn single_fn_match_test() {
  let source = "
type Bool = True | False

fn not(b: Bool) -> Bool {
  match b {
    | True -> False
    | False -> True
  }
}
"
  let errors = check_module(source, "test.tao")
  case errors {
    [] -> should.equal(True, True)
    _ -> should.equal(True, False)
  }
}

/// Two functions, NO cross-reference — should pass
pub fn two_fn_no_xref_test() {
  let source = "
type Bool = True | False

fn not(b: Bool) -> Bool {
  match b {
    | True -> False
    | False -> True
  }
}

fn id(b: Bool) -> Bool {
  b
}
"
  let errors = check_module(source, "test.tao")
  case errors {
    [] -> should.equal(True, True)
    _ -> should.equal(True, False)
  }
}

/// Two functions, second references first — the minimal failing case
pub fn two_fn_xref_test() {
  let source = "
type Bool = True | False

fn not(b: Bool) -> Bool {
  match b {
    | True -> False
    | False -> True
  }
}

fn double_not(b: Bool) -> Bool {
  not(not(b))
}
"
  let errors = check_module(source, "test.tao")
  case errors {
    [] -> should.equal(True, True)
    _ -> should.equal(True, False)
  }
}

/// Two functions, both with match, second references first
pub fn two_fn_match_xref_test() {
  let source = "
type Bool = True | False

fn not(b: Bool) -> Bool {
  match b {
    | True -> False
    | False -> True
  }
}

fn flip(b: Bool) -> Bool {
  match not(b) {
    | True -> False
    | False -> True
  }
}
"
  let errors = check_module(source, "test.tao")
  case errors {
    [] -> should.equal(True, True)
    _ -> should.equal(True, False)
  }
}

/// Three functions, chain cross-reference
pub fn three_fn_chain_xref_test() {
  let source = "
type Bool = True | False

fn not(b: Bool) -> Bool {
  match b {
    | True -> False
    | False -> True
  }
}

fn id(b: Bool) -> Bool {
  not(not(b))
}

fn flip(b: Bool) -> Bool {
  match id(b) {
    | True -> False
    | False -> True
  }
}
"
  let errors = check_module(source, "test.tao")
  case errors {
    [] -> should.equal(True, True)
    _ -> should.equal(True, False)
  }
}
