// ============================================================================
// CORE QUOTE - Reification (Value to Term)
// ============================================================================
import gleam/list

import syntax/grammar.{type Span}
import core/ast as ast
import core/state as state
import core/eval as eval

// ============================================================================
// NORMALIZATION
// ============================================================================

pub fn normalize(ffi: state.FFI, env: ast.Env, term: ast.Term, s: Span) -> ast.Term {
  let value = eval.eval(ffi, env, term)
  quote(ffi, 0, value, s)
}

// ============================================================================
// QUOTE (VALUE TO TERM)
// ============================================================================

pub fn quote(ffi: state.FFI, lvl: Int, value: ast.Value, s: Span) -> ast.Term {
  quote_loop(ffi, lvl, value, s, 100)
}

fn quote_loop(ffi: state.FFI, lvl: Int, value: ast.Value, s: Span, steps: Int) -> ast.Term {
  case steps <= 0 {
    True -> ast.Hole(0, s)
    False -> quote_loop_impl(ffi, lvl, value, s, steps)
  }
}

fn quote_loop_impl(ffi: state.FFI, lvl: Int, value: ast.Value, s: Span, steps: Int) -> ast.Term {
  case value {
    ast.VTyp(universe) -> ast.Typ(universe, s)
    ast.VLit(literal) -> ast.Lit(literal, s)
    ast.VLitT(literal_type) -> ast.LitT(literal_type, s)
    ast.VNeut(head, spine) -> quote_neut(ffi, lvl, head, spine, s, steps)
    ast.VRcd(fields) -> {
      let terms = list.map(fields, fn(f) { #(f.0, quote_loop(ffi, lvl, f.1, s, steps - 1)) })
      ast.Rcd(terms, s)
    }
    ast.VLam(implicit, name, env, body) -> {
      // Add a fresh HVar to represent the bound variable
      let extended_env = list.append(env, [ast.VNeut(ast.HVar(lvl), [])])
      let body_term = quote_term_in_env(ffi, lvl + 1, extended_env, body, s, steps - 1)
      // Quote the parameter type from the bound variable
      let param_ty = quote_loop(ffi, lvl, ast.VNeut(ast.HVar(lvl), []), s, steps - 1)
      ast.Lam(implicit, #(name, param_ty), body_term, s)
    }
    ast.VPi(implicit, name, env, in_val, out_term) -> {
      let in_term = quote_loop(ffi, lvl, in_val, s, steps - 1)
      // Add a fresh HVar to represent the bound variable
      let extended_env = list.append(env, [ast.VNeut(ast.HVar(lvl), [])])
      let out_term_quoted = quote_term_in_env(ffi, lvl + 1, extended_env, out_term, s, steps - 1)
      ast.Pi(implicit, name, in_term, out_term_quoted, s)
    }
    ast.VRecord(fields) -> {
      let terms = list.map(fields, fn(f) { #(f.0, quote_loop(ffi, lvl, f.1, s, steps - 1)) })
      ast.Rcd(terms, s)
    }
    ast.VCall(name, args, ret) -> {
      let ret_term = quote_loop(ffi, lvl, ret, s, steps - 1)
      // For VCall, we don't have explicit typed args from evaluation,
      // so we wrap the args in type annotations
      let arg_pairs = list.map(args, fn(arg_val) {
        let arg_term = quote_loop(ffi, lvl, arg_val, s, steps - 1)
        #(arg_term, ret_term)
      })
      ast.Call(name, arg_pairs, ret_term, s)
    }
    ast.VFix(name, env, body) -> {
      // Add a fresh HVar to represent the recursive function
      let extended_env = list.append(env, [ast.VNeut(ast.HVar(lvl), [])])
      let body_term = quote_term_in_env(ffi, lvl, extended_env, body, s, steps - 1)
      ast.Fix(name, body_term, s)
    }
    ast.VCtrValue(ast.VCtr(tag, arg)) -> {
      ast.Ctr(tag, quote_loop(ffi, lvl, arg, s, steps - 1), s)
    }
    ast.VUnit -> ast.Unit(s)
    ast.VErr -> ast.Hole(-1, s)  // Quote VErr as a special hole
  }
}

fn quote_neut(
  ffi: state.FFI,
  lvl: Int,
  head: ast.Head,
  spine: List(ast.Elim),
  s: Span,
  steps: Int,
) -> ast.Term {
  let base = case head {
    ast.HVar(level) -> {
      // HVar uses absolute De Bruijn levels. Convert to relative Var index.
      // index = lvl - level - 1 (standard De Bruijn conversion)
      let index = lvl - level - 1
      ast.Var(index, s)
    }
    ast.HHole(id) -> ast.Hole(id, s)
    ast.HStepLimit -> ast.Hole(0, s)
  }

  quote_spine(ffi, lvl, base, spine, s, steps)
}

fn quote_spine(
  ffi: state.FFI,
  lvl: Int,
  base: ast.Term,
  spine: List(ast.Elim),
  s: Span,
  steps: Int,
) -> ast.Term {
  case spine {
    [] -> base
    [first, ..rest] -> {
      let applied = case first {
        ast.EDot(name) -> ast.Dot(base, name, s)
        ast.EApp(arg) -> ast.App(base, [], quote_loop(ffi, lvl, arg, s, steps - 1), s)
        ast.EAppImplicit(_) -> base
        ast.EMatch(_env, motive, cases) -> {
          let arg_term = quote_loop(ffi, lvl, motive, s, steps - 1)
          let cases_quoted = quote_cases(ffi, lvl, cases, s, steps - 1)
          ast.Match(base, arg_term, cases_quoted, s)
        }
      }
      quote_spine(ffi, lvl, applied, rest, s, steps - 1)
    }
  }
}

fn quote_cases(
  ffi: state.FFI,
  lvl: Int,
  cases: List(ast.Case),
  s: Span,
  steps: Int,
) -> List(ast.Case) {
  list.map(cases, fn(c) {
    ast.Case(c.pattern, quote_term_in_env(ffi, lvl, [], c.body, s, steps - 1), c.guard, c.span)
  })
}

fn quote_term_in_env(
  ffi: state.FFI,
  lvl: Int,
  env: ast.Env,
  term: ast.Term,
  s: Span,
  steps: Int,
) -> ast.Term {
  let value = eval.eval(ffi, env, term)
  quote_loop(ffi, lvl, value, s, steps)
}

// ============================================================================
// QUOTE DOMAIN WITH IMPLICIT
// ============================================================================

pub fn quote_domain_with_implicit(
  implicit: List(String),
  domain: ast.Term,
  s: Span,
) -> ast.Term {
  case implicit {
    [] -> domain
    [name, ..rest] -> {
      let inner = quote_domain_with_implicit(rest, domain, s)
      ast.Pi([], name, ast.Typ(0, s), inner, s)
    }
  }
}
