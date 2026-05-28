/// Quote — Convert Values back to Terms
///
/// The `quote` module reifies evaluateuated values (De Bruijn levels) back into
/// syntax terms (De Bruijn indices). This is used for:
/// - Displaying inferred types as readable terms
/// - Normalization by evaluateuation results
/// - Error message generation
///
/// ## How Quoting Works
///
/// Values use De Bruijn levels where `HVar(0)` is the innermost binder.
/// Terms use De Bruijn indices where `Var(0)` is the innermost binder.
///
/// When quoting a value, we need to know the number of binders above the
/// value's scope to convert levels to indices correctly.
///
/// Because both values and terms use **innermost-first** ordering, the
/// conversion is: `index = lvl - 1 - absolute_level`.
///
/// `lvl` tracks the depth of binders in the quoting context. When entering
/// a lambda body or Pi codomain, `lvl` is incremented by 1.
import core/ast
import core/evaluate.{evaluate}
import core/state.{type FFI}
import gleam/int
import gleam/list
import gleam/option
import syntax/span.{type Span}

pub fn quote(ffi: FFI, size: Int, value: ast.Value, span: Span) -> ast.Term {
  case value {
    ast.VTyp(universe) -> ast.Typ(universe, span)
    ast.VLit(lit) -> ast.Lit(lit, span)
    ast.VLitT(lit) -> ast.LitT(lit, span)
    ast.VCtr(tag, arg_val) ->
      ast.Ctr(tag, quote(ffi, size, arg_val, span), span)
    ast.VRcd(fields_val) -> {
      let fields =
        list.map(fields_val, fn(field) {
          let #(name, value) = field
          #(name, quote(ffi, size, value, span))
        })
      ast.Rcd(fields, span)
    }
    ast.VRcdT(fields_val) -> {
      let fields =
        list.map(fields_val, fn(field) {
          let #(name, value, default_val) = field
          let default =
            option.map(default_val, fn(v) { quote(ffi, size, v, span) })
          #(name, quote(ffi, size, value, span), default)
        })
      ast.RcdT(fields, span)
    }
    ast.VNeut(neut) -> quote_neut(ffi, size, neut, span)
    ast.VLam(implicit, #(name, param_val), #(env, body)) -> {
      let param = quote(ffi, size, param_val, span)
      let body_val = evaluate(ffi, [param_val, ..env], body)
      let body = quote(ffi, size, body_val, span)
      ast.Lam(implicit, #(name, param), body, span)
    }
    ast.VPi(implicit, #(name, param_val), #(env, body)) -> {
      let param = quote(ffi, size, param_val, span)
      let body_val = evaluate(ffi, [param_val, ..env], body)
      let body = quote(ffi, size, body_val, span)
      ast.Pi(implicit, #(name, param), body, span)
    }
    ast.VFix(name, #(env, body)) -> {
      todo
    }
    ast.VUnion(variants) -> {
      todo
    }
    ast.VErr -> ast.Err(span)
  }
}

fn quote_neut(ffi: FFI, size: Int, neut: ast.Neut, span: Span) -> ast.Term {
  case neut {
    ast.NVar(level) -> ast.Var(size - level - 1, span)
    ast.NHole(id) -> ast.Hole(id, span)
    _ -> {
      echo neut
      todo
    }
  }
}
