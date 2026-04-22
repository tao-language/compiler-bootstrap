// ============================================================================
// CORE VISITOR - Generic AST Traversal for Terms
// ============================================================================
/// Provides a generic term visitor that eliminates duplication across subst,
/// generalize, quote, and other core modules.
///
/// Instead of writing recursive `case` matches for each traversal, use
/// `visit_term` with transformation callbacks. Each callback receives the
/// children (already visited) and returns the rebuilt node.
///
/// Example - replace all holes with vars:
///   visit_term(
///     term,
///     var: fn(i, s) { ast.Var(i, s) },
///     hole: fn(id, s) { ast.Var(id, s) },  // replace hole id with var id
///     lam: fn(i, p, body, s) { ast.Lam(i, p, body, s) },
///     ..
///   )

import gleam/list
import syntax/grammar.{type Span}
import core/ast as ast
import core/state as state

// ============================================================================
// TERM TRAVERSAL
// ============================================================================

/// Visit a term with explicit transformation callbacks for each constructor.
/// All children are already visited (recursively).
///
/// Parameters:
///   term       - the term to visit
///   var        - fn(idx: Int, span: Span) -> Term  (default: identity)
///   hole       - fn(id: Int, span: Span) -> Term   (default: identity)
///   lam        - fn(implicit, param, body, span) -> Term  (body already visited)
///   pi         - fn(implicit, name, in_term, out_term, span) -> Term
///   app        - fn(fun, implicit, arg, span) -> Term  (children already visited)
///   match      - fn(arg, motive, cases, span) -> Term  (children already visited)
///   ctr        - fn(tag, arg, span) -> Term  (arg already visited)
///   rcd        - fn(fields, span) -> Term  (fields already visited)
///   dot        - fn(arg, name, span) -> Term  (arg already visited)
///   ann        - fn(inner, typ, span) -> Term  (children already visited)
///   call       - fn(name, typed_args, ret, span) -> Term
///   comptime   - fn(inner, span) -> Term  (inner already visited)
///   fix        - fn(name, body, span) -> Term  (body already visited)
///   let        - fn(name, value, body, span) -> Term  (children already visited)
///   typ        - fn(universe, span) -> Term  (default: identity)
///   lit        - fn(value, span) -> Term  (default: identity)
///   lit_t      - fn(typ, span) -> Term  (default: identity)
///   unit       - fn(span) -> Term  (default: identity)
///   err        - fn(message, span) -> Term  (default: identity)
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
      lam(implicit, param, visit_term_body(body, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err), span)
    ast.Pi(implicit, name, in_t, out_t, span) ->
      pi(implicit, name,
        visit_term_body(in_t, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
        visit_term_body(out_t, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
        span)
    ast.App(fun, implicit, arg, span) ->
      app(
        visit_term_body(fun, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
        list.map(implicit, fn(t) { visit_term_body(t, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err) }),
        visit_term_body(arg, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
        span)
    ast.Match(arg, motive, cases, span) ->
      match(
        visit_term_body(arg, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
        visit_term_body(motive, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
        list.map(cases, fn(c) {
          ast.Case(
            pattern: visit_pattern(c.pattern, fn(t, p) { ast.PCtr(t, p) }, fn(fs) { ast.PRcd(fs) }),
            body: visit_term_body(c.body, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
            guard: c.guard,
            span: c.span,
          )
        }),
        span)
    ast.Ctr(tag, arg, span) ->
      ctr(tag, visit_term_body(arg, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err), span)
    ast.Rcd(fields, span) ->
      rcd(list.map(fields, fn(f) { #(f.0, visit_term_body(f.1, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err)) }), span)
    ast.Dot(arg, name, span) ->
      dot(visit_term_body(arg, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err), name, span)
    ast.Ann(inner, type_term, span) ->
      ann(
        visit_term_body(inner, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
        visit_term_body(type_term, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
        span)
    ast.Call(name, typed_args, ret, span) -> {
      let shifted_args = list.map(typed_args, fn(pair) {
        #(
          visit_term_body(pair.0, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
          visit_term_body(pair.1, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
        )
      })
      ast.Call(name, shifted_args, visit_term_body(ret, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err), span)
    }
    ast.Comptime(inner, span) ->
      comptime(visit_term_body(inner, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err), span)
    ast.Fix(name, body, span) ->
      fix(name, visit_term_body(body, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err), span)
    ast.Let(name, value, body, span) ->
      let_(
        name,
        visit_term_body(value, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
        visit_term_body(body, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err),
        span)
    ast.Typ(univ, span) -> typ(univ, span)
    ast.Lit(value, span) -> lit(value, span)
    ast.LitT(lt, span) -> lit_t(lt, span)
    ast.Unit(span) -> unit(span)
    ast.Err(msg, span) -> err(msg, span)
  }
}

/// Recursive helper that visits a term and passes the result to the callback.
/// Used by all the parent callbacks so children are visited before the parent.
fn visit_term_body(
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
  visit_term(term, var, hole, lam, pi, app, match, ctr, rcd, dot, ann, call, comptime, fix, let_, typ, lit, lit_t, unit, err)
}

// ============================================================================
// PATTERN TRAVERSAL
// ============================================================================

/// Visit a pattern with callbacks for constructors that may contain sub-patterns.
fn visit_pattern(
  pattern: ast.Pattern,
  p_ctr: fn(String, ast.Pattern) -> ast.Pattern,
  p_rcd: fn(List(#(String, ast.Pattern))) -> ast.Pattern,
) -> ast.Pattern {
  visit_pattern_inner(pattern, p_ctr, p_rcd)
}

fn visit_pattern_inner(
  pattern: ast.Pattern,
  p_ctr: fn(String, ast.Pattern) -> ast.Pattern,
  p_rcd: fn(List(#(String, ast.Pattern))) -> ast.Pattern,
) -> ast.Pattern {
  case pattern {
    ast.PAny -> ast.PAny
    ast.PAs(inner, name) -> ast.PAs(visit_pattern_inner(inner, p_ctr, p_rcd), name)
    ast.PTyp(univ) -> ast.PTyp(univ)
    ast.PLit(lit) -> ast.PLit(lit)
    ast.PLitT(lit_t) -> ast.PLitT(lit_t)
    ast.PRcd(fields) -> p_rcd(list.map(fields, fn(f) { #(f.0, visit_pattern_inner(f.1, p_ctr, p_rcd)) }))
    ast.PCtr(tag, arg) -> p_ctr(tag, visit_pattern_inner(arg, p_ctr, p_rcd))
    ast.PUnit -> ast.PUnit
  }
}
