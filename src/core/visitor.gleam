// ============================================================================
// CORE VISITOR - Generic AST Traversal for Terms
// ============================================================================
/// Provides a generic term visitor that eliminates duplication across subst,
/// generalize, quote, and other core modules.
///
/// Instead of writing recursive `case` matches for each traversal, use
/// `visit_term` with transformation callbacks passed positionally.
///
/// Example - replace all holes with vars:
///   visit_term(
///     term,
///     fn(i, s) { ast.Var(i, s) },           // var
///     fn(id, s) { ast.Var(id, s) },          // hole
///     fn(i, p, b, s) { ast.Lam(i, p, b, s) }, // lam
///     ...
///   )
///
/// Each callback receives the children (already visited recursively) and
/// returns the rebuilt node. The visitor handles all recursion.

import gleam/list
import syntax/grammar.{type Span}
import core/ast as ast

// ============================================================================
// TERM TRAVERSAL
// ============================================================================

/// Visit a term with 20 positional callbacks (one per constructor).
/// Children are visited recursively before the parent callback runs.
pub fn visit_term(
  term: ast.Term,
  var: fn(Int, Span) -> ast.Term,
  hole: fn(Int, Span) -> ast.Term,
  lam: fn(List(String), #(String, ast.Term), ast.Term, Span) -> ast.Term,
  pi: fn(List(String), String, ast.Term, ast.Term, Span) -> ast.Term,
  app: fn(ast.Term, List(ast.Term), ast.Term, Span) -> ast.Term,
  match: fn(ast.Term, ast.Term, List(ast.Case), Span) -> ast.Term,
  ctr: fn(String, ast.Term, Span) -> ast.Term,
  rcd: fn(List(#(String, ast.Term)), Span) -> ast.Term,
  dot: fn(ast.Term, String, Span) -> ast.Term,
  ann: fn(ast.Term, ast.Term, Span) -> ast.Term,
  call: fn(String, List(#(ast.Term, ast.Term)), ast.Term, Span) -> ast.Term,
  comptime: fn(ast.Term, Span) -> ast.Term,
  fix: fn(String, ast.Term, Span) -> ast.Term,
  let_: fn(String, ast.Term, ast.Term, Span) -> ast.Term,
  typ: fn(Int, Span) -> ast.Term,
  lit: fn(ast.Literal, Span) -> ast.Term,
  lit_t: fn(ast.LiteralType, Span) -> ast.Term,
  unit: fn(Span) -> ast.Term,
  err: fn(String, Span) -> ast.Term,
) -> ast.Term {
  case term {
    ast.Var(idx, span) -> var(idx, span)
    ast.Hole(id, span) -> hole(id, span)
    ast.Lam(implicit, param, body, span) ->
      lam(implicit, param, visit_term(body, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err), span)
    ast.Pi(implicit, name, in_t, out_t, span) ->
      pi(implicit, name,
        visit_term(in_t, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
        visit_term(out_t, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
        span)
    ast.App(fun, implicit, arg, span) ->
      app(
        visit_term(fun, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
        list.map(implicit, fn(t) { visit_term(t, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err) }),
        visit_term(arg, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
        span)
    ast.Match(arg, motive, cases, span) ->
      match(
        visit_term(arg, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
        visit_term(motive, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
        list.map(cases, fn(c) {
          ast.Case(
            pattern: visit_pattern(c.pattern, fn(t, p, s) { ast.PCtr(t, p, s) }, fn(fs, s) { ast.PRcd(fs, s) }),
            body: visit_term(c.body, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
            guard: c.guard,
            span: c.span,
          )
        }),
        span)
    ast.Ctr(tag, arg, span) ->
      ctr(tag, visit_term(arg, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err), span)
    ast.Rcd(fields, span) ->
      rcd(list.map(fields, fn(f) { #(f.0, visit_term(f.1, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err)) }), span)
    ast.Dot(arg, name, span) ->
      dot(visit_term(arg, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err), name, span)
    ast.Ann(inner, type_term, span) ->
      ann(
        visit_term(inner, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
        visit_term(type_term, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
        span)
    ast.Call(name, typed_args, ret, span) ->
      call(
        name,
        list.map(typed_args, fn(pair) {
          #(
            visit_term(pair.0, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
            visit_term(pair.1, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
          )
        }),
        visit_term(ret, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
        span,
      )
    ast.Comptime(inner, span) ->
      comptime(visit_term(inner, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err), span)
    ast.Fix(name, body, span) ->
      fix(name, visit_term(body, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err), span)
    ast.Let(name, value, body, span) ->
      let_(
        name,
        visit_term(value, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
        visit_term(body, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
        span)
    ast.Typ(univ, span) -> typ(univ, span)
    ast.Lit(value, span) -> lit(value, span)
    ast.LitT(lt, span) -> lit_t(lt, span)
    ast.Unit(span) -> unit(span)
    ast.Err(msg, span) -> err(msg, span)
  }
}

// ============================================================================
// PATTERN TRAVERSAL
// ============================================================================

/// Visit a pattern with callbacks for constructors that may contain sub-patterns.
pub fn visit_pattern(
  pattern: ast.Pattern,
  p_ctr: fn(String, ast.Pattern, Span) -> ast.Pattern,
  p_rcd: fn(List(#(String, ast.Pattern)), Span) -> ast.Pattern,
) -> ast.Pattern {
  visit_pattern_inner(pattern, p_ctr, p_rcd)
}

fn visit_pattern_inner(
  pattern: ast.Pattern,
  p_ctr: fn(String, ast.Pattern, Span) -> ast.Pattern,
  p_rcd: fn(List(#(String, ast.Pattern)), Span) -> ast.Pattern,
) -> ast.Pattern {
  case pattern {
    ast.PAny(span) -> ast.PAny(span)
    ast.PAs(inner, name, span) -> ast.PAs(visit_pattern_inner(inner, p_ctr, p_rcd), name, span)
    ast.PTyp(univ, span) -> ast.PTyp(univ, span)
    ast.PLit(lit, span) -> ast.PLit(lit, span)
    ast.PLitT(lit_t, span) -> ast.PLitT(lit_t, span)
    ast.PRcd(fields, span) -> p_rcd(list.map(fields, fn(f) { #(f.0, visit_pattern_inner(f.1, p_ctr, p_rcd)) }), span)
    ast.PCtr(tag, arg, span) -> p_ctr(tag, visit_pattern_inner(arg, p_ctr, p_rcd), span)
    ast.PUnit(span) -> ast.PUnit(span)
  }
}
