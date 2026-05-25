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
import core/state.{type FFI}
import gleam/list
import gleam/option
import syntax/span.{type Span}

/// Quote a value to a term at the given binder depth (`lvl`).
///
/// `lvl` is the number of binders in the current quoting context.
/// When quoting a lambda body or Pi codomain, this is incremented
/// because the lambda/Pi parameter adds a new innermost binder.
pub fn quote(ffi: FFI, lvl: Int, value: ast.Value, span: Span) -> ast.Term {
  case value {
    ast.VTyp(universe) -> ast.Typ(universe, span)
    ast.VLit(lit) -> ast.Lit(lit, span)
    ast.VLitT(lit) -> ast.LitT(lit, span)
    ast.VErr -> ast.Err(span)

    ast.VCtr(tag, arg_val) ->
      ast.Ctr(
        tag,
        quote(ffi, lvl, arg_val, span),
        span,
      )

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
          let default = option.map(default_val, fn(v) { quote(ffi, lvl, v, span) })
          #(name, quote(ffi, lvl, value, span), default)
        })
      ast.RcdT(fields, span)
    }

    ast.VNeut(head, spine) -> {
      let base = quote_head(ffi, lvl, head, span)
      quote_spine(ffi, lvl, base, spine, span)
    }

    // VLam: quote the body with an incremented binder depth.
    // The lambda parameter and implicits are already Terms (not Values),
    // so we use quote_body for them. The env contains Values.
    ast.VLam(env, implicits, param, body) -> {
      let param_name = param.0
      let param_type = quote_body(ffi, lvl, param.1)
      let body_term = quote_body(ffi, lvl + 1, body)

      ast.Lam(
        list.map(implicits, fn(imp) {
          let #(name, type_term) = imp
          #(name, quote_body(ffi, lvl, type_term))
        }),
        #(param_name, param_type),
        body_term,
        span,
      )
    }

    // VPi: quote implicits and domain at current lvl, then increment lvl
    // for the codomain since the Pi parameter becomes a new binder.
    ast.VPi(implicits, domain, codomain) -> {
      let implicits_quoted =
        list.map(implicits, fn(p) {
          let #(name, type_val) = p
          #(name, quote(ffi, lvl, type_val, span))
        })
      let domain_quoted = #(domain.0, quote(ffi, lvl, domain.1, span))
      let codomain_quoted = quote(ffi, lvl + 1, codomain, span)

      ast.Pi(
        implicits_quoted,
        domain_quoted,
        codomain_quoted,
        span,
      )
    }

    ast.VTypeDef(params, constructors) -> {
      let params_quoted =
        list.map(params, fn(p) {
          let #(name, val) = p
          #(name, quote(ffi, lvl, val, span))
        })
      let constructors_quoted =
        list.map(constructors, fn(c) {
          let #(ctr_name, #(param_names, param_type, body_term)) = c
          #(
            ctr_name,
            #(param_names, quote(ffi, lvl, param_type, span), body_term),
            span,
          )
        })
      ast.TypeDef(params_quoted, constructors_quoted, span)
    }

    // Any other value type is an error.
    _ -> ast.Err(span)
  }
}

/// Quote a list of values to a list of terms.
fn quote_value_list(
  ffi: FFI,
  lvl: Int,
  values: List(ast.Value),
  span: Span,
) -> List(ast.Term) {
  list.map(values, fn(v) { quote(ffi, lvl, v, span) })
}

/// Quote a term that is already in De Bruijn indices.
///
/// The term's indices are already correct for the context where the
/// value was constructed. When quoting from a deeper context (lvl > 0),
/// we need to shift the indices to account for the additional binders.
fn quote_body(ffi: FFI, lvl: Int, term: ast.Term) -> ast.Term {
  case term {
    ast.Typ(u, span) -> ast.Typ(u, span)
    ast.Hole(id, span) -> ast.Hole(id, span)
    ast.Lit(lit, span) -> ast.Lit(lit, span)
    ast.LitT(lit, span) -> ast.LitT(lit, span)
    ast.Var(index, span) ->
      // The term's Var(index) was created with `lvl` binders above.
      // When quoting from a context with `current_lvl` binders,
      // the index needs to shift: new_index = index + (current_lvl - lvl)
      // Since we pass the already-adjusted lvl, this is just index.
      ast.Var(index, span)
    ast.Ctr(tag, arg, span) ->
      ast.Ctr(tag, quote_body(ffi, lvl, arg), span)
    ast.Rcd(fields, span) ->
      ast.Rcd(
        list.map(fields, fn(f) { #(f.0, quote_body(ffi, lvl, f.1)) }),
        span,
      )
    ast.RcdT(fields, span) ->
      ast.RcdT(
        list.map(fields, fn(f) {
          #(f.0, quote_body(ffi, lvl, f.1), option.map(f.2, quote_body(ffi, lvl, _)))
        }),
        span,
      )
    ast.Call(name, args, return_type, span) ->
      ast.Call(
        name,
        list.map(args, quote_body(ffi, lvl, _)),
        quote_body(ffi, lvl, return_type),
        span,
      )
    ast.Ann(term, type_, span) ->
      ast.Ann(quote_body(ffi, lvl, term), quote_body(ffi, lvl, type_), span)
    ast.Lam(implicits, param, body, span) ->
      ast.Lam(
        list.map(implicits, fn(i) { #(i.0, quote_body(ffi, lvl, i.1)) }),
        #(param.0, quote_body(ffi, lvl, param.1)),
        quote_body(ffi, lvl + 1, body),
        span,
      )
    ast.Pi(implicits, domain, codomain, span) ->
      ast.Pi(
        list.map(implicits, fn(i) { #(i.0, quote_body(ffi, lvl, i.1)) }),
        #(domain.0, quote_body(ffi, lvl, domain.1)),
        quote_body(ffi, lvl + 1, codomain),
        span,
      )
    ast.Fix(name, body, span) ->
      ast.Fix(name, quote_body(ffi, lvl + 1, body), span)
    ast.App(fun, arg, span) ->
      ast.App(quote_body(ffi, lvl, fun), quote_body(ffi, lvl, arg), span)
    ast.TypeDef(params, constructors, span) ->
      ast.TypeDef(
        list.map(params, fn(p) { #(p.0, quote_body(ffi, lvl, p.1)) }),
        list.map(constructors, fn(c) {
          let #(ctr_name, #(param_names, param_type, body_term), ctr_span) = c
          #(
            ctr_name,
            #(param_names, quote_body(ffi, lvl, param_type), body_term),
            ctr_span,
          )
        }),
        span,
      )
    ast.Match(arg, cases, span) ->
      ast.Match(
        quote_body(ffi, lvl, arg),
        list.map(cases, fn(c) {
          ast.Case(
            c.pattern,
            option.map(c.guard, fn(g) { #(quote_body(ffi, lvl, g.0), g.1) }),
            quote_body(ffi, lvl, c.body),
            span,
          )
        }),
        span,
      )
    ast.Err(span) -> ast.Err(span)
  }
}

/// Quote a list of terms.
fn quote_body_list(ffi: FFI, lvl: Int, terms: List(ast.Term)) -> List(ast.Term) {
  list.map(terms, fn(t) { quote_body(ffi, lvl, t) })
}

/// Quote a neutral term head to a term.
fn quote_head(ffi: FFI, lvl: Int, head: ast.Head, span: Span) -> ast.Term {
  case head {
    ast.HVar(absolute_level) -> {
      // Convert De Bruijn level to De Bruijn index.
      //
      // Both values and terms use innermost-first ordering:
      //   level 0 = index 0 = innermost binder
      //   level 1 = index 1 = next binder out
      //
      // The conversion formula depends on how `lvl` is defined:
      // - If lvl = number of binders in the quoting context,
      //   then: index = lvl - 1 - absolute_level
      // - If lvl tracks the depth incrementally (used for VLam/VPi),
      //   then: index = absolute_level (identity, when depths match)
      //
      // We use the identity conversion because our state.vars is
      // ordered innermost-first, matching De Bruijn indices.
      // Validate that the level is within the quoting context.
      case absolute_level < lvl {
        True -> ast.Var(absolute_level, span)
        False -> ast.Err(span)  // Out of scope
      }
    }
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
  lvl: Int,
  base: ast.Term,
  spine: List(ast.Elim),
  span: Span,
) -> ast.Term {
  case spine {
    [] -> base
    [elim, ..rest] -> {
      let base = quote_elim(ffi, lvl, base, elim, span)
      quote_spine(ffi, lvl, base, rest, span)
    }
  }
}

/// Quote a single eliminator onto a base term.
fn quote_elim(
  ffi: FFI,
  lvl: Int,
  base: ast.Term,
  elim: ast.Elim,
  span: Span,
) -> ast.Term {
  case elim {
    ast.EApp(arg, elim_span) -> {
      let arg_term = quote(ffi, lvl, arg, elim_span)
      ast.App(base, arg_term, span)
    }

    ast.EFix(env, body) -> {
      // EFix doesn't store the fixpoint name. We reconstruct a Fix
      // using the body directly. The name is lost at the value level.
      // This is a limitation — consider storing the name in EFix.
      let body_term = quote_body(ffi, lvl + 1, body)
      // Use a placeholder name; the original name is not recoverable.
      ast.Fix("<fix>", body_term, span)
    }

    ast.EMatch(env, cases, elim_span) -> {
      // EMatch: the matched value is `base`, cases have patterns and bodies.
      // The bodies are Terms (already in indices).
      let quoted_cases =
        list.map(cases, fn(c) {
          ast.Case(
            c.pattern,
            c.guard,
            c.body,
            c.span,
          )
        })
      ast.Match(base, quoted_cases, span)
    }
  }
}
