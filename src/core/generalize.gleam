// ============================================================================
// CORE GENERALIZE - Hole Generalization for Lambda Inference
// ============================================================================
/// Generalization converts inferred holes in lambda bodies into implicit
/// type parameters. This enables polymorphic lambda inference.
import gleam/int
import gleam/list
import syntax/grammar.{type Span, Span}
import core/ast as ast
import core/state as state
import core/eval as eval
import core/quote as quote
import core/subst as subst

pub fn generalize_holes(
  holes: List(Int),
  existing_implicit: List(String),
  domain: ast.Value,
  codomain: ast.Type,
  s: state.State,
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

fn collect_names_from_term_acc(term: ast.Term, acc: List(String)) -> List(String) {
  case term {
    ast.Typ(_, _) | ast.Lit(_, _) | ast.LitT(_, _) | ast.Var(_, _) | ast.Hole(_, _) | ast.Err(_, _) | ast.Unit(_) -> acc
    ast.Rcd(fields, _) -> collect_names_from_fields_acc(fields, acc)
    ast.Ctr(_, arg, _) -> collect_names_from_term_acc(arg, acc)
    ast.Dot(arg, _, _) -> collect_names_from_term_acc(arg, acc)
    ast.Ann(term, typ, _) -> {
      collect_names_from_term_acc(typ, collect_names_from_term_acc(term, acc))
    }
    ast.Lam(_, param, body, _) -> {
      let #(name, _) = param
      collect_names_from_term_acc(body, [name, ..acc])
    }
    ast.Pi(_, name, in_term, out_term, _) -> {
      collect_names_from_term_acc(out_term, [name, ..collect_names_from_term_acc(in_term, acc)])
    }
    ast.App(fun, implicit, arg, _) -> {
      collect_names_from_term_acc(arg, collect_names_from_term_acc(fun, acc))
    }
    ast.Match(arg, motive, cases, _) -> {
      collect_names_from_cases_acc(cases, collect_names_from_term_acc(motive, collect_names_from_term_acc(arg, acc)))
    }
    ast.Call(_, args, _) -> collect_names_from_terms_acc(args, acc)
    ast.Comptime(inner, _) -> collect_names_from_term_acc(inner, acc)
    ast.Fix(name, body, _) -> collect_names_from_term_acc(body, [name, ..acc])
  }
}

fn collect_names_from_fields_acc(fields: List(#(String, ast.Term)), acc: List(String)) -> List(String) {
  case fields {
    [] -> acc
    [#(name, term), ..rest] -> collect_names_from_fields_acc(rest, [name, ..collect_names_from_term_acc(term, acc)])
  }
}

fn collect_names_from_cases_acc(cases: List(ast.Case), acc: List(String)) -> List(String) {
  case cases {
    [] -> acc
    [c, ..rest] -> {
      collect_names_from_cases_acc(rest, collect_names_from_term_acc(c.body, acc))
    }
  }
}

fn collect_names_from_terms_acc(terms: List(ast.Term), acc: List(String)) -> List(String) {
  case terms {
    [] -> acc
    [term, ..rest] -> collect_names_from_terms_acc(rest, collect_names_from_term_acc(term, acc))
  }
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
    ast.VCall(name, args) ->
      ast.VCall(name, list.map(args, fn(a) { subst_value_with_hole_vars(subst, a) }))
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

fn subst_term_with_hole_vars(subst: List(#(Int, Int)), term: ast.Term) -> ast.Term {
  case term {
    ast.Hole(id, span) -> {
      case list.key_find(subst, id) {
        Ok(index) -> ast.Var(index, span)
        Error(Nil) -> ast.Hole(id, span)
      }
    }
    ast.App(fun, impl, arg, span) ->
      ast.App(
        subst_term_with_hole_vars(subst, fun),
        list.map(impl, fn(t) { subst_term_with_hole_vars(subst, t) }),
        subst_term_with_hole_vars(subst, arg),
        span,
      )
    ast.Pi(impl, name, in_t, out_t, span) ->
      ast.Pi(
        impl,
        name,
        subst_term_with_hole_vars(subst, in_t),
        subst_term_with_hole_vars(subst, out_t),
        span,
      )
    ast.Lam(impl, param, body, span) ->
      ast.Lam(impl, param, subst_term_with_hole_vars(subst, body), span)
    ast.Ann(inner, ty, span) ->
      ast.Ann(subst_term_with_hole_vars(subst, inner), subst_term_with_hole_vars(subst, ty), span)
    ast.Rcd(fields, span) ->
      ast.Rcd(list.map(fields, fn(kv) { #(kv.0, subst_term_with_hole_vars(subst, kv.1)) }), span)
    ast.Ctr(tag, arg, span) ->
      ast.Ctr(tag, subst_term_with_hole_vars(subst, arg), span)
    ast.Dot(arg, name, span) ->
      ast.Dot(subst_term_with_hole_vars(subst, arg), name, span)
    ast.Match(arg, motive, cases, span) ->
      ast.Match(
        subst_term_with_hole_vars(subst, arg),
        subst_term_with_hole_vars(subst, motive),
        list.map(cases, fn(c) {
          ast.Case(
            pattern: subst_pattern_with_hole_vars(subst, c.pattern),
            body: subst_term_with_hole_vars(subst, c.body),
            guard: c.guard,
            span: c.span
          )
        }),
        span,
      )
    ast.Call(name, args, span) ->
      ast.Call(name, list.map(args, fn(a) { subst_term_with_hole_vars(subst, a) }), span)
    ast.Comptime(inner, span) ->
      ast.Comptime(subst_term_with_hole_vars(subst, inner), span)
    ast.Fix(name, body, span) ->
      ast.Fix(name, subst_term_with_hole_vars(subst, body), span)
    ast.Typ(_, _) | ast.Lit(_, _) | ast.LitT(_, _) | ast.Var(_, _) | ast.Unit(_) | ast.Err(_, _) -> term
  }
}


fn subst_pattern_with_hole_vars(subst: List(#(Int, Int)), pattern: ast.Pattern) -> ast.Pattern {
  case pattern {
    ast.PAs(inner, name) -> ast.PAs(subst_pattern_with_hole_vars(subst, inner), name)
    ast.PCtr(tag, arg) -> ast.PCtr(tag, subst_pattern_with_hole_vars(subst, arg))
    ast.PLit(_) -> pattern
    ast.PLitT(_) -> pattern
    ast.PTyp(_) -> pattern
    ast.PRcd(fields) -> ast.PRcd(list.map(fields, fn(pair) {
      #(pair.0, subst_pattern_with_hole_vars(subst, pair.1))
    }))
    ast.PUnit -> pattern
    ast.PAny -> pattern
  }
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
      ast.VNeut(ast.HVar(index), spine) if index < num_implicit -> {
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
    [ast.EMatch(env, motive, cases), ..rest] -> {
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
