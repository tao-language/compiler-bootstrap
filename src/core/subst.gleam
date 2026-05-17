import core/ast
import core/state.{type FFI, type Subst}

pub fn subst_term(ffi: FFI, sub: Subst, term: ast.Term) -> ast.Term {
  todo
}

pub fn subst_value(ffi: FFI, sub: Subst, value: ast.Value) -> ast.Value {
  todo
}

pub fn subst_pattern(
  ffi: FFI,
  sub: Subst,
  pattern: ast.Pattern,
) -> ast.Pattern {
  todo
}

pub fn subst_case(ffi: FFI, sub: Subst, case_: ast.Case) -> ast.Case {
  todo
}
