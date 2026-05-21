/// Quote — Convert Values back to Terms
///
/// The `quote` module reifies evaluated values (De Bruijn levels) back into
/// syntax terms (De Bruijn indices). This is used for:
/// - Displaying inferred types as readable terms
/// - Normalization by evaluation results
/// - Error message generation
///
/// ## How Quoting Works
///
/// Values use De Bruijn levels where `HVar(0)` is the innermost binder.
/// Terms use De Bruijn indices where `Var(0)` is the innermost binder.
///
/// When quoting a value, we need to know the number of binders above the
/// value's scope to convert levels to indices correctly.
import core/ast
import core/state.{type FFI}
import gleam/list
import gleam/option
import syntax/span.{type Span}

pub fn quote(ffi: FFI, lvl: Int, value: ast.Value, span: Span) -> ast.Term {
  case value {
    ast.VTyp(universe) -> ast.Typ(universe, span)
    ast.VLit(lit) -> ast.Lit(lit, span)
    ast.VLitT(lit) -> ast.LitT(lit, span)
    ast.VCtr(tag, arg_val) -> ast.Ctr(tag, quote(ffi, lvl, arg_val, span), span)
    ast.VRcd(fields_val) -> {
      let fields =
        list.map(fields_val, fn(field) {
          let #(name, value) = field
          #(name, quote(ffi, lvl, value, span))
        })
      ast.Rcd(fields, span)
    }
    ast.VRcdT(fields_val) -> {
      let fields =
        list.map(fields_val, fn(field) {
          let #(name, value, default_val) = field
          let default = option.map(default_val, quote(ffi, lvl, _, span))
          #(name, quote(ffi, lvl, value, span), default)
        })
      ast.RcdT(fields, span)
    }
    ast.VNeut(head, spine) -> {
      let base = quote_head(ffi, lvl, head, span)
      quote_spine(ffi, lvl, base, spine, span)
    }
    // VLam( env: Env, implicits: List(#(String, Value)), param: #(String, Value), body: Term, )
    ast.VPi(_, implicits_val, #(name, domain_val), codomain) -> {
      let implicits =
        list.map(implicits_val, fn(param) {
          let #(name, implicit_val) = param
          #(name, quote(ffi, lvl, implicit_val, span))
        })
      let domain = quote(ffi, lvl, domain_val, span)
      ast.Pi(implicits, #(name, domain), codomain, span)
    }
    // VTypeDef( params: List(#(String, Value)), constructors: List(#(String, #(List(String), Value, Term))), )
    ast.VErr -> ast.Err(span)
    _ -> {
      echo value
      todo
    }
  }
}

fn quote_head(ffi: FFI, lvl: Int, head: ast.Head, span: Span) -> ast.Term {
  case head {
    ast.HVar(absolute_level) -> {
      // HVar uses absolute De Bruijn levels. Convert to relative Var index.
      let index = lvl - absolute_level - 1
      ast.Var(index, span)
    }
    ast.HHole(id) -> ast.Hole(id, span)
    _ -> {
      echo head
      todo
    }
  }
}

fn quote_elim(
  ffi: FFI,
  lvl: Int,
  base: ast.Term,
  elim: ast.Elim,
  span: Span,
) -> ast.Term {
  case elim {
    _ -> {
      echo elim
      todo
    }
  }
}

fn quote_spine(
  ffi: FFI,
  lvl: Int,
  base: ast.Term,
  spine: List(ast.Elim),
  span: Span,
) -> ast.Term {
  case spine {
    [] -> base
    [elim, ..spine] -> {
      let base = quote_elim(ffi, lvl, base, elim, span)
      quote_spine(ffi, lvl, base, spine, span)
    }
  }
}
