// ============================================================================
// CORE GENERALIZE - Hole Generalization for Lambda Inference
// ============================================================================
/// Generalization converts inferred holes in lambda bodies into implicit
/// type parameters. This enables polymorphic lambda inference.
import gleam/int
import gleam/list
import syntax/grammar.{type Span}
import core/ast as ast
import core/state as state
import core/eval as eval
import core/quote as quote
import core/visitor as visitor

pub fn generalize_holes(
  holes: List(Int),
  existing_implicit: List(String),
  domain: ast.Value,
  codomain: ast.Type,
  _s: state.State,
  ffi: state.FFI,
  lvl: Int,
  span: Span,
) -> #(List(String), ast.Value, ast.Term) {
  let base_index = list.length(existing_implicit)
  let hole_subst = create_hole_to_var_subst(holes, base_index)

  // KEY FIX: Do NOT generalize the domain. The domain hole should remain as a hole
  // so it can be unified during application. Only generalize the codomain.
  let generalized_domain = domain

  case holes {
    [] -> #(
      existing_implicit,
      generalized_domain,
      quote.quote(ffi, lvl, codomain, span),
    )
    _ -> {
      let codomain_term = quote.quote(ffi, lvl, codomain, span)
      let existing_names = collect_existing_names(existing_implicit, codomain_term)
      let new_names = generate_unique_names(list.length(holes), existing_names, 0)
      let generalized_codomain_val = subst_value_with_hole_vars(hole_subst, codomain)
      let num_new_implicit = list.length(holes)
      let generalized_codomain = quote_domain_with_implicit(ffi, num_new_implicit, generalized_codomain_val, span, 100_000)
      #(
        list.append(existing_implicit, new_names),
        generalized_domain,
        generalized_codomain,
      )
    }
  }
}

fn collect_existing_names(implicit: List(String), term: ast.Term) -> List(String) {
  list.append(implicit, collect_names_from_term(term))
}

fn collect_names_from_term(term: ast.Term) -> List(String) {
  collect_names_from_term_acc(term, [])
}

/// Collect all variable names from a term, accumulating in the given list.
fn collect_names_from_term_acc(term: ast.Term, acc: List(String)) -> List(String) {
  case term {
    ast.Typ(_, _) | ast.Lit(_, _) | ast.LitT(_, _) | ast.Var(_, _) | ast.Hole(_, _) | ast.Err(_, _) | ast.Unit(_) -> acc
    ast.Rcd(fields, _) -> collect_names_from_fields_acc(fields, acc)
    ast.Ctr(_, arg, _) -> collect_names_from_term_acc(arg, acc)
    ast.Dot(arg, _, _) -> collect_names_from_term_acc(arg, acc)
    ast.Ann(term, typ, _) -> collect_names_from_term_acc(typ, collect_names_from_term_acc(term, acc))
    ast.Lam(_, param, body, _) -> collect_names_from_term_acc(body, [param.0, ..acc])
    ast.Pi(_, name, in_term, out_term, _) -> collect_names_from_term_acc(out_term, [name, ..collect_names_from_term_acc(in_term, acc)])
    ast.App(fun, _implicit, arg, _) -> collect_names_from_term_acc(arg, collect_names_from_term_acc(fun, acc))
    ast.Match(arg, motive, cases, _) -> collect_names_from_cases_acc(cases, collect_names_from_term_acc(motive, collect_names_from_term_acc(arg, acc)))
    ast.Call(_, typed_args, ret, _) -> collect_names_from_term_acc(ret, collect_names_from_typed_args_acc(typed_args, acc))
    ast.Comptime(inner, _) -> collect_names_from_term_acc(inner, acc)
    ast.Fix(name, body, _) -> collect_names_from_term_acc(body, [name, ..acc])
    ast.Let(name, value, body, _) -> collect_names_from_term_acc(body, [name, ..collect_names_from_term_acc(value, acc)])
  }
}

fn collect_names_from_fields_acc(fields: List(#(String, ast.Term)), acc: List(String)) -> List(String) {
  list.fold(fields, acc, fn(acc, pair) {
    collect_names_from_term_acc(pair.1, [pair.0, ..acc])
  })
}

fn collect_names_from_cases_acc(cases: List(ast.Case), acc: List(String)) -> List(String) {
  list.fold(cases, acc, fn(acc, c) {
    collect_names_from_term_acc(c.body, acc)
  })
}

fn collect_names_from_typed_args_acc(args: List(#(ast.Term, ast.Term)), acc: List(String)) -> List(String) {
  list.fold(args, acc, fn(acc, pair) {
    collect_names_from_term_acc(pair.1, collect_names_from_term_acc(pair.0, acc))
  })
}

fn generate_unique_names(n: Int, existing: List(String), counter: Int) -> List(String) {
  case n <= 0 {
    True -> []
    False -> {
      let name = "_" <> int.to_string(counter)
      case list.contains(existing, name) {
        True -> generate_unique_names(n, existing, counter + 1)
        False -> [name, ..generate_unique_names(n - 1, existing, counter + 1)]
      }
    }
  }
}

fn create_hole_to_var_subst(holes: List(Int), base_index: Int) -> List(#(Int, Int)) {
  create_hole_to_var_subst_loop(holes, base_index, [])
}

fn create_hole_to_var_subst_loop(
  holes: List(Int),
  index: Int,
  acc: List(#(Int, Int)),
) -> List(#(Int, Int)) {
  case holes {
    [] -> list.reverse(acc)
    [hole, ..rest] ->
      create_hole_to_var_subst_loop(rest, index + 1, [#(hole, index), ..acc])
  }
}

fn subst_value_with_hole_vars(subst: List(#(Int, Int)), value: ast.Value) -> ast.Value {
  case value {
    ast.VNeut(ast.HHole(id), []) -> {
      case list.key_find(subst, id) {
        Ok(index) -> ast.VNeut(ast.HVar(index), [])
        Error(Nil) -> value
      }
    }
    ast.VNeut(ast.HHole(id), spine) -> {
      case list.key_find(subst, id) {
        Ok(index) ->
          ast.VNeut(
            ast.HVar(index),
            list.map(spine, fn(e) { subst_elim_with_hole_vars(subst, e) }),
          )
        Error(Nil) ->
          ast.VNeut(ast.HHole(id), list.map(spine, fn(e) { subst_elim_with_hole_vars(subst, e) }))
      }
    }
    ast.VNeut(ast.HStepLimit, spine) ->
      ast.VNeut(ast.HStepLimit, list.map(spine, fn(e) { subst_elim_with_hole_vars(subst, e) }))
    ast.VNeut(head, spine) ->
      ast.VNeut(head, list.map(spine, fn(e) { subst_elim_with_hole_vars(subst, e) }))
    ast.VRcd(fields) ->
      ast.VRcd(
        list.map(fields, fn(kv) {
          #(kv.0, subst_value_with_hole_vars(subst, kv.1))
        }),
      )
    ast.VCtrValue(ast.VCtr(tag, arg)) ->
      ast.VCtrValue(ast.VCtr(tag, subst_value_with_hole_vars(subst, arg)))
    ast.VLam(impl, name, env, body) ->
      ast.VLam(impl, name, env, subst_term_with_hole_vars(subst, body))
    ast.VPi(impl, name, env, in_val, out) ->
      ast.VPi(
        impl,
        name,
        env,
        subst_value_with_hole_vars(subst, in_val),
        subst_term_with_hole_vars(subst, out),
      )
    ast.VCall(name, args, ret) ->
      ast.VCall(
        name: name,
        args: list.map(args, fn(a) { subst_value_with_hole_vars(subst, a) }),
        ret: subst_value_with_hole_vars(subst, ret),
      )
    ast.VFix(name, env, body) ->
      ast.VFix(name, env, subst_term_with_hole_vars(subst, body))
    ast.VRecord(fields) ->
      ast.VRecord(
        list.map(fields, fn(kv) {
          #(kv.0, subst_value_with_hole_vars(subst, kv.1))
        }),
      )
    _ -> value
  }
}

fn subst_elim_with_hole_vars(subst: List(#(Int, Int)), elim: ast.Elim) -> ast.Elim {
  case elim {
    ast.EDot(name) -> ast.EDot(name)
    ast.EApp(arg) -> ast.EApp(subst_value_with_hole_vars(subst, arg))
    ast.EAppImplicit(arg) -> ast.EAppImplicit(subst_value_with_hole_vars(subst, arg))
    ast.EMatch(env, motive, cases) ->
      ast.EMatch(env, subst_value_with_hole_vars(subst, motive), cases)
  }
}

/// Replace holes with variables using the substitution map.
/// Uses the generic visitor to avoid ~50 lines of recursive pattern matching.
fn subst_term_with_hole_vars(subst: List(#(Int, Int)), term: ast.Term) -> ast.Term {
  visitor.visit_term(
    term,
    // var: identity
    fn(idx, span) { ast.Var(idx, span) },
    // hole: look up in substitution, replace with Var or keep as Hole
    fn(id, span) {
      case list.key_find(subst, id) {
        Ok(index) -> ast.Var(index, span)
        Error(Nil) -> ast.Hole(id, span)
      }
    },
    // lam: visit body
    fn(implicit, param, body, span) { ast.Lam(implicit, param, body, span) },
    // pi: visit both in and out
    fn(implicit, name, in_t, out_t, span) { ast.Pi(implicit, name, in_t, out_t, span) },
    // app: visit fun, implicit args, and arg
    fn(fun, impl, arg, span) { ast.App(fun, impl, arg, span) },
    // match: visit arg, motive, and each case body
    fn(arg, motive, cases, span) {
      ast.Match(
        arg,
        motive,
        list.map(cases, fn(c) {
          ast.Case(
            pattern: visitor.visit_pattern(c.pattern,
              fn(t, p) { ast.PCtr(t, p) },
              fn(fs) { ast.PRcd(fs) },
            ),
            body: c.body,
            guard: c.guard,
            span: c.span,
          )
        }),
        span,
      )
    },
    // ctr: visit arg
    fn(tag, arg, span) { ast.Ctr(tag, arg, span) },
    // rcd: visit field terms
    fn(fields, span) { ast.Rcd(fields, span) },
    // dot: visit arg
    fn(arg, name, span) { ast.Dot(arg, name, span) },
    // ann: visit inner and type
    fn(inner, ty, span) { ast.Ann(inner, ty, span) },
    // call: visit typed args and return type
    fn(name, typed_args, ret, span) { ast.Call(name, typed_args, ret, span) },
    // comptime: visit inner
    fn(inner, span) { ast.Comptime(inner, span) },
    // fix: visit body
    fn(name, body, span) { ast.Fix(name, body, span) },
    // let: visit value and body
    fn(name, value, body, span) { ast.Let(name, value, body, span) },
    // typ: identity
    fn(univ, span) { ast.Typ(univ, span) },
    // lit: identity
    fn(value, span) { ast.Lit(value, span) },
    // lit_t: identity
    fn(lt, span) { ast.LitT(lt, span) },
    // unit: identity
    fn(span) { ast.Unit(span) },
    // err: identity
    fn(msg, span) { ast.Err(msg, span) },
  )
}

fn quote_domain_with_implicit(
  ffi: state.FFI,
  num_implicit: Int,
  value: ast.Value,
  s: Span,
  steps: Int,
) -> ast.Term {
  quote_with_implicit_loop(ffi, num_implicit, value, s, 0, steps)
}

fn quote_with_implicit_loop(
  ffi: state.FFI,
  num_implicit: Int,
  value: ast.Value,
  s: Span,
  lvl: Int,
  steps: Int,
) -> ast.Term {
  case steps <= 0 {
    True -> ast.Err("Step limit exceeded", s)
    False -> case value {
      ast.VNeut(ast.HVar(index), []) if index < num_implicit -> ast.Var(index, s)
      ast.VNeut(ast.HVar(index), _spine) if index < num_implicit -> {
        ast.Var(index, s)
      }
      ast.VTyp(k) -> ast.Typ(k, s)
      ast.VLit(lit) -> ast.Lit(lit, s)
      ast.VLitT(lit_t) -> ast.LitT(lit_t, s)
      ast.VUnit -> ast.Unit(s)
      ast.VRcd(fields) -> {
        ast.Rcd(list.map(fields, fn(kv) {
          #(kv.0, quote_with_implicit_loop(ffi, num_implicit, kv.1, s, lvl + 1, steps - 1))
        }), s)
      }
      ast.VCtrValue(ast.VCtr(tag, arg)) -> {
        ast.Ctr(tag, quote_with_implicit_loop(ffi, num_implicit, arg, s, lvl + 1, steps - 1), s)
      }
      ast.VPi(implicit, name, env, in_val, out_term) -> {
        let in_term = quote_with_implicit_loop(ffi, num_implicit, in_val, s, lvl + 1, steps - 1)
        // Extend environment with the bound variable
        let extended_env = list.append(env, [ast.VNeut(ast.HVar(lvl), [])])
        let out_term_quoted = quote_term_in_env_with_implicit(ffi, num_implicit, lvl + 1, extended_env, out_term, s, steps - 1)
        ast.Pi(implicit, name, in_term, out_term_quoted, s)
      }
      ast.VNeut(head, spine) -> {
        quote_spine_with_implicit(ffi, num_implicit, head, spine, s, lvl, steps)
      }
      _ -> ast.Err("Cannot quote value", s)
    }
  }
}

fn quote_spine_with_implicit(
  ffi: state.FFI,
  num_implicit: Int,
  head: ast.Head,
  spine: List(ast.Elim),
  s: Span,
  lvl: Int,
  steps: Int,
) -> ast.Term {
  case spine {
    [] -> {
      case head {
        ast.HVar(index) -> ast.Var(index, s)
        ast.HHole(id) -> ast.Hole(id, s)
        ast.HStepLimit -> ast.Err("Step limit", s)
      }
    }
    [ast.EDot(name), ..rest] -> {
      let base = quote_spine_with_implicit(ffi, num_implicit, head, rest, s, lvl, steps - 1)
      ast.Dot(base, name, s)
    }
    [ast.EApp(arg), ..rest] -> {
      let base = quote_spine_with_implicit(ffi, num_implicit, head, rest, s, lvl + 1, steps - 1)
      let arg_term = quote_with_implicit_loop(ffi, num_implicit, arg, s, lvl, steps - 1)
      ast.App(base, [], arg_term, s)
    }
    [ast.EAppImplicit(arg), ..rest] -> {
      let base = quote_spine_with_implicit(ffi, num_implicit, head, rest, s, lvl, steps - 1)
      let arg_term = quote_with_implicit_loop(ffi, num_implicit, arg, s, lvl, steps - 1)
      ast.App(base, [arg_term], ast.Unit(s), s)
    }
    [ast.EMatch(_env, motive, cases), ..rest] -> {
      let base = quote_spine_with_implicit(ffi, num_implicit, head, rest, s, lvl, steps - 1)
      let motive_term = quote_with_implicit_loop(ffi, num_implicit, motive, s, lvl, steps - 1)
      ast.Match(base, motive_term, cases, s)
    }
  }
}

fn quote_term_in_env_with_implicit(
  ffi: state.FFI,
  num_implicit: Int,
  lvl: Int,
  env: ast.Env,
  term: ast.Term,
  s: Span,
  steps: Int,
) -> ast.Term {
  let value = eval.eval(ffi, env, term)
  quote_with_implicit_loop(ffi, num_implicit, value, s, lvl, steps)
}
