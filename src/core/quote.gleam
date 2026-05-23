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
    ast.VPi(_, implicit_env, domain, codomain) -> {
      // Convert implicit_env back to implicits for the Pi term.
      // The type values in implicit_env need to be quoted to Terms.
      let implicits =
        list.map(implicit_env, fn(imp) {
          let #(name, _, type_val) = imp
          #(name, quote(ffi, lvl, type_val, span))
        })
      ast.Pi(implicits, domain, codomain, span)
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
      // Convert De Bruijn level (absolute env position) to De Bruijn index
      // (relative binder count).
      //
      // Because state.vars is ordered innermost-first (most-recently-pushed
      // at index 0), levels and indices use the same counting convention:
      //   level 0 = env index 0 = innermost binder = Var(0)
      //   level 1 = env index 1 = next binder out    = Var(1)
      //   ...
      //
      // So the conversion is the identity: index = level.
      //
      // CAUTION: If the env ordering ever changes to outermost-first,
      // this formula must change to: index = lvl - 1 - absolute_level
      let index = absolute_level
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
