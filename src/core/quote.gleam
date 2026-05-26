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
///
/// Because both values and terms use **innermost-first** ordering, the
/// conversion is: `index = lvl - 1 - absolute_level`.
///
/// `lvl` tracks the depth of binders in the quoting context. When entering
/// a lambda body or Pi codomain, `lvl` is incremented by 1.
import core/ast
import core/eval.{eval}
import core/shift
import core/state.{type FFI}
import gleam/int
import gleam/list
import gleam/option
import syntax/span.{type Span}

pub fn quote(ffi: FFI, value: ast.Value, span: Span) -> ast.Term {
  case value {
    ast.VTyp(universe) -> ast.Typ(universe, span)
    ast.VLit(lit) -> ast.Lit(lit, span)
    ast.VLitT(lit) -> ast.LitT(lit, span)
    ast.VErr -> ast.Err(span)

    ast.VCtr(tag, arg_val) -> ast.Ctr(tag, quote(ffi, arg_val, span), span)

    ast.VRcd(fields_val) -> {
      let fields =
        list.map(fields_val, fn(field) {
          let #(name, value) = field
          #(name, quote(ffi, value, span))
        })
      ast.Rcd(fields, span)
    }

    ast.VRcdT(fields_val) -> {
      let fields =
        list.map(fields_val, fn(field) {
          let #(name, value, default_val) = field
          let default = option.map(default_val, fn(v) { quote(ffi, v, span) })
          #(name, quote(ffi, value, span), default)
        })
      ast.RcdT(fields, span)
    }

    ast.VNeut(head, spine) -> {
      let base = quote_head(ffi, head, span)
      quote_spine(ffi, base, spine, span)
    }

    ast.VLam(env, implicits_val, param_val, body) -> {
      let implicits = list.map(implicits_val, quote_param(ffi, _, span))
      let param = quote_param(ffi, param_val, span)
      let params =
        int.range(
          from: list.length(implicits) + 1,
          to: 0,
          with: [],
          run: list.prepend,
        )
      let env = list.append(list.map(params, ast.vvar(_, [])), env)
      let body = quote(ffi, eval(ffi, env, body), span)
      ast.Lam(implicits, param, body, span)
    }

    ast.VPi(implicits, domain, codomain) -> {
      todo
    }

    ast.VTypeDef(params, constructors) -> {
      todo
    }
  }
}

fn quote_param(
  ffi: FFI,
  param: #(String, ast.Value),
  span: Span,
) -> #(String, ast.Term) {
  let #(name, term) = param
  #(name, quote(ffi, term, span))
}

/// Quote a neutral term head to a term.
fn quote_head(ffi: FFI, head: ast.Head, span: Span) -> ast.Term {
  case head {
    ast.HVar(level) -> ast.Var(level, span)
    ast.HHole(id) -> ast.Hole(id, span)
    ast.HCall(name, args) -> {
      // HCall is a neutral application; we can't reconstruct a Call
      // directly because the head is neutral (not a value).
      // This represents a partially applied builtin whose function
      // position is a neutral term. For now, return Err.
      ast.Err(span)
    }
  }
}

/// Quote a spine of eliminators, building up an application chain.
fn quote_spine(
  ffi: FFI,
  base: ast.Term,
  spine: List(ast.Elim),
  span: Span,
) -> ast.Term {
  case spine {
    [] -> base
    [elim, ..rest] -> {
      let base = quote_elim(ffi, base, elim, span)
      quote_spine(ffi, base, rest, span)
    }
  }
}

/// Quote a single eliminator onto a base term.
fn quote_elim(
  ffi: FFI,
  base: ast.Term,
  elim: ast.Elim,
  span: Span,
) -> ast.Term {
  case elim {
    ast.EApp(arg, elim_span) -> {
      let arg_term = quote(ffi, arg, elim_span)
      ast.App(base, arg_term, span)
    }

    ast.EFix(env, body) -> {
      // EFix doesn't store the fixpoint name. We reconstruct a Fix
      // using the body directly. The name is lost at the value level.
      // This is a limitation — consider storing the name in EFix.
      // let body_term = quote(ffi, lvl + 1, body)
      // Use a placeholder name; the original name is not recoverable.
      // ast.Fix("<fix>", body_term, span)
      todo
    }

    ast.EMatch(env, cases, elim_span) -> {
      // EMatch: the matched value is `base`, cases have patterns and bodies.
      // The bodies are Terms (already in indices).
      let quoted_cases =
        list.map(cases, fn(c) { ast.Case(c.pattern, c.guard, c.body, c.span) })
      ast.Match(base, quoted_cases, span)
    }
  }
}
