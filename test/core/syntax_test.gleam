/// Round-trip tests: parse -> format -> same source
///
/// These tests verify that the parser and formatter work correctly together
/// by checking that format(parse(source), 80, 2) == source for various inputs.
import core/ast.{type Term}
import core/format.{format}
import core/parse as p
import gleam/list
import gleam/string

const filename = "syntax_test"

fn parse(src: String) -> Term {
  case p.parse(filename, src) {
    Ok(ast) -> ast
    Error(e) -> {
      let msg = string.inspect(e)
      panic as msg
    }
  }
}

// ============================================================================
// Simple values
// ============================================================================

pub fn roundtrip_int_test() {
  let source = "42"
  assert format(parse(source), 80, 2) == source
}

pub fn roundtrip_float_test() {
  let source = "3.14"
  assert format(parse(source), 80, 2) == source
}

pub fn roundtrip_var_test() {
  let source = "x"
  assert format(parse(source), 80, 2) == source
}

pub fn roundtrip_hole_test() {
  let source = "?"
  assert format(parse(source), 80, 2) == source

  let source2 = "?<42>"
  assert format(parse(source2), 80, 2) == source2
}

pub fn roundtrip_type_test() {
  let source1 = "%Type"
  assert format(parse(source1), 80, 2) == source1

  let source2 = "%Type<42>"
  assert format(parse(source2), 80, 2) == source2
}

// ============================================================================
// Literals types
// ============================================================================

pub fn roundtrip_lit_type_test() {
  let sources = [
    "%Int",
    "%Float",
    "%I8",
    "%I16",
    "%I32",
    "%I64",
    "%U8",
    "%U16",
    "%U32",
    "%U64",
    "%F16",
    "%F32",
    "%F64",
  ]
  sources
  |> list.each(fn(src) {
    assert format(parse(src), 80, 2) == src
  })
}

// ============================================================================
// Records
// ============================================================================

pub fn roundtrip_rcd_empty_test() {
  let source = "{}"
  assert format(parse(source), 80, 2) == source
}

pub fn roundtrip_rcd_single_test() {
  let source = "{a: x}"
  assert format(parse(source), 80, 2) == source
}

pub fn roundtrip_rcdt_empty_test() {
  let source = "%{}"
  assert format(parse(source), 80, 2) == source
}

pub fn roundtrip_rcdt_single_test() {
  let source = "%{a: x}"
  assert format(parse(source), 80, 2) == source
}

pub fn roundtrip_rcdt_with_default_test() {
  let source = "%{a: x = 42}"
  assert format(parse(source), 80, 2) == source
}

// ============================================================================
// Annotations
// ============================================================================

pub fn roundtrip_ann_test() {
  let source = "%(x: y)"
  assert format(parse(source), 80, 2) == source
}

// ============================================================================
// Lambdas
// ============================================================================

pub fn roundtrip_lam_explicit_test() {
  let source = "%lam(x: y) => z"
  assert format(parse(source), 80, 2) == source
}

pub fn roundtrip_lam_implicit_test() {
  let source = "%lam<x: y> => z"
  assert format(parse(source), 80, 2) == source
}

// ============================================================================
// Pi types
// ============================================================================

pub fn roundtrip_pi_explicit_test() {
  let source = "%pi(x: y) -> z"
  assert format(parse(source), 80, 2) == source
}

pub fn roundtrip_pi_implicit_test() {
  let source = "%pi<x: y> -> z"
  assert format(parse(source), 80, 2) == source
}

// ============================================================================
// Fixpoint
// ============================================================================

pub fn roundtrip_fix_test() {
  let source = "%fix f. f"
  assert format(parse(source), 80, 2) == source
}

// ============================================================================
// Applications
// ============================================================================

pub fn roundtrip_app_explicit_test() {
  let source = "f(x)"
  assert format(parse(source), 80, 2) == source
}

pub fn roundtrip_app_implicit_test() {
  let source = "f<x>"
  assert format(parse(source), 80, 2) == source
}

// ============================================================================
// Let bindings
// ============================================================================

pub fn roundtrip_let_test() {
  let source = "%let x: a = y\nz"
  assert format(parse(source), 80, 2) == source
}

// ============================================================================
// Constructor
// ============================================================================

pub fn roundtrip_ctr_test() {
  let source = "#A(x)"
  assert format(parse(source), 80, 2) == source
}
