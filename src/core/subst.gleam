import core/ast
import core/state.{type FFI, type Subst}
import core/utils
import gleam/list
import gleam/option.{None, Some}

/// Force all holes in a value by substituting from the substitution
/// list. Recursively forces holes in sub-values but does NOT perform
/// β-reduction (that requires apply_spine/apply_elim, which are handled
/// separately in eval).
///
/// This normalizes values to the extent possible by resolving unbound
/// metavariables (HHole) to their types from the substitution list.
pub fn force_value(ffi: FFI, sub: Subst, value: ast.Value) -> ast.Value {
  case value {
    ast.VTyp(u) -> ast.VTyp(u)
    ast.VLit(lit) -> ast.VLit(lit)
    ast.VLitT(t) -> ast.VLitT(t)
    ast.VErr -> ast.VErr

    ast.VCtr(tag, arg) ->
      ast.VCtr(tag, force_value(ffi, sub, arg))

    ast.VRcd(fields) ->
      ast.VRcd(
        list.map(fields, fn(f) { #(f.0, force_value(ffi, sub, f.1)) }),
      )

    ast.VRcdT(fields) ->
      ast.VRcdT(
        list.map(fields, fn(f) {
          #(f.0, force_value(ffi, sub, f.1), option.map(f.2, force_value(ffi, sub, _)))
        }),
      )

    ast.VPi(implicits, domain, codomain) -> {
      let forced_implicits = list.map(implicits, fn(imp) {
        let #(name, val) = imp
        #(name, force_value(ffi, sub, val))
      })
      let forced_domain = #(domain.0, force_value(ffi, sub, domain.1))
      let forced_codomain = force_value(ffi, sub, codomain)
      ast.VPi(forced_implicits, forced_domain, forced_codomain)
    }

    ast.VLam(env, implicits, param, body) ->
      ast.VLam(
        list.map(env, force_value(ffi, sub, _)),
        implicits,
        param,
        body,
      )

    ast.VTypeDef(params, constructors) ->
      ast.VTypeDef(
        list.map(params, fn(p) { #(p.0, force_value(ffi, sub, p.1)) }),
        constructors,
      )

    ast.VNeut(head, spine) ->
      case head {
        ast.HHole(id) ->
          case utils.list_lookup(sub, id) {
            Some(solution) -> {
              let resolved = force_value(ffi, sub, solution)
              case resolved {
                ast.VNeut(solved_head, solved_spine) ->
                  ast.VNeut(solved_head, list.append(solved_spine, spine))
                _ -> resolved
              }
            }
            None -> ast.VNeut(ast.HHole(id), spine)
          }

        _ -> {
          let forced_head = force_head(ffi, sub, head)
          let forced_spine = force_spine(ffi, sub, spine)
          ast.VNeut(forced_head, forced_spine)
        }
      }
  }
}

/// Force holes in a neutral term head that is NOT a HHole.
fn force_head(ffi: FFI, sub: Subst, head: ast.Head) -> ast.Head {
  case head {
    ast.HVar(level) -> ast.HVar(level)

    ast.HHole(_) ->
      // Should not reach here; HHole is handled in force_value's VNeut case.
      head

    ast.HCall(name, args) -> {
      let forced_args = list.map(args, force_value(ffi, sub, _))
      ast.HCall(name, forced_args)
    }
  }
}

/// Force holes in a spine (list of eliminators).
fn force_spine(
  ffi: FFI,
  sub: Subst,
  spine: List(ast.Elim),
) -> List(ast.Elim) {
  case spine {
    [] -> []
    [elim, ..rest] ->
      [force_elim(ffi, sub, elim), ..force_spine(ffi, sub, rest)]
  }
}

/// Force holes in a single eliminator.
fn force_elim(
  ffi: FFI,
  sub: Subst,
  elim: ast.Elim,
) -> ast.Elim {
  case elim {
    ast.EApp(arg, span) ->
      ast.EApp(force_value(ffi, sub, arg), span)

    ast.EMatch(env, cases, span) -> {
      let forced_env = list.map(env, force_value(ffi, sub, _))
      let forced_cases = list.map(cases, fn(c) {
        ast.Case(
          c.pattern,
          c.guard,
          c.body,
          span,
        )
      })
      ast.EMatch(forced_env, forced_cases, span)
    }

    ast.EFix(env, body) -> {
      let forced_env = list.map(env, force_value(ffi, sub, _))
      ast.EFix(forced_env, body)
    }
  }
}
