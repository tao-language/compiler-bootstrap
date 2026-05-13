/// Generalization — Hole collection and hole-to-variable substitution.
///
/// The `generalize` module handles two operations used during type inference:
///
/// 1. **`free_holes`** — Collects all free hole IDs from a value. These are
///    holes that are not bound by enclosing lambdas or pi types.
///
/// 2. **`replace_holes_with_vars`** — Replaces hole heads in a value with
///    De Bruijn variable references. This is used to convert holes into
///    universal type parameters during lambda generalization.
///
/// ## Why Generalization Matters
///
/// When inferring the type of a lambda like `fn(x) => x`, the inferred
/// type might contain holes (e.g., `?0 -> ?0`). Generalization collects
/// these free holes and converts them into bound variables, producing
/// a polymorphic type like `∀a. a -> a`.
///
/// ## Hole Collection
///
/// Holes are collected by walking the value's structure. Since VLam has
/// a Term body (not Value body), both value and term traversal are needed.
///
/// Results are unique and sorted by descending ID (highest hole gets
/// De Bruijn index 0).
import core/ast.{
  type Head, type Term, type Value, Ann, App, Call, Case, Ctr, EApp, EMatch, Err, Fix, HHole, HFix,
  HVar, Hole, Lam, Lit, Match, Pi, Rcd, RcdT, Typ, VCtr, VCall, VFix, VErr, VLam, VLit, VNeut, VPi,
  VRcd, VRcdT, VTyp, VTypeDef, TypeDef, Var, VLitT, LitT,
}
import gleam/option.{None, Some}
import gleam/int
import gleam/list

// ============================================================================
// HOLE COLLECTION (Value)
// ============================================================================

/// Collect all free hole IDs from a value.
///
/// Returns a sorted list (descending by ID). Each ID appears only once.
///
/// ## Example
///
/// ```
/// // A value with one free hole
/// free_holes(VNeut(HHole(42), [])) -> [42]
///
/// // A value with multiple holes
/// free_holes(VPi(VNeut(HHole(1), []), VNeut(HHole(2), []))) -> [2, 1]
/// ```
pub fn free_holes(value: Value) -> List(Int) {
  let holes = free_holes_from(value, 0)
  list.sort(list.unique(holes), fn(a, b) { int.compare(b, a) })
}

fn free_holes_from(value: Value, binding: Int) -> List(Int) {
  case value {
    VNeut(head, spine) -> {
      let holes = head_holes(head)
      let spine_holes =
        list.fold(spine, [], fn(acc, elim) {
          case elim {
            EApp(arg) -> list.append(acc, free_holes_from(arg, binding))
            EMatch(_env, cases) -> list.append(acc, list.fold(cases, [], fn(acc, c) {
              list.append(acc, free_holes_from_term(c.body, binding))
            }))
          }
        })
      list.append(holes, spine_holes)
    }
    VLam(_env, implicits, #(_name, param), body) -> {
      let implicit_holes = list.fold(implicits, [], fn(acc, i) {
        list.append(acc, free_holes_from(i.1, binding + 1))
      })
      let param_holes = free_holes_from(param, binding + 1)
      let body_holes = free_holes_term(body, binding + 1)
      list.append(list.append(implicit_holes, param_holes), body_holes)
    }
    VPi(_env, implicits, domain, codomain) -> {
      let implicit_holes = list.fold(implicits, [], fn(acc, i) {
        list.append(acc, free_holes_from(i.1, binding))
      })
      let domain_holes = free_holes_from(domain.1, binding)
      let codomain_holes = free_holes_from(codomain, binding)
      list.append(list.append(implicit_holes, domain_holes), codomain_holes)
    }
    VLit(_) -> []
    VCtr(_, arg) -> free_holes_from(arg, binding)
    VRcd(fields) -> {
      list.fold(fields, [], fn(acc, f) {
        list.append(acc, free_holes_from(f.1, binding))
      })
    }
    VRcdT(fields) -> {
      list.fold(fields, [], fn(acc, f) {
        let acc2 = list.append(acc, free_holes_from(f.1, binding))
        case f.2 {
          Some(d) -> list.append(acc2, free_holes_from(d, binding))
          None -> acc2
        }
      })
    }
    VTypeDef(name: _, params: _, constructors: _) -> []
    VTyp(_) -> []
    VLitT(_) -> []
    VFix(_, env, body) -> {
      let env_holes = list.fold(env, [], fn(acc, v) {
        list.append(acc, free_holes_from(v, binding))
      })
      list.append(env_holes, free_holes_term(body, binding))
    }
    VCall(_, args, _) -> {
      list.fold(args, [], fn(acc, ta) {
        let val_h = free_holes_from(ta.0, binding)
        let type_h = free_holes_from(ta.1, binding)
        list.append(list.append(acc, val_h), type_h)
      })
    }
    VErr -> []
  }
}

/// Collect free holes from a term body (used for EMatch cases).
fn free_holes_from_term(term: Term, binding: Int) -> List(Int) {
  free_holes_term(term, binding)
}

fn head_holes(head: Head) -> List(Int) {
  case head {
    HVar(_) -> []
    HHole(id) -> [id]
    HFix(_name, _env) -> []
  }
}

// ============================================================================
// HOLE COLLECTION (Term) — for VLam.body, VPi.codomain, Lam.body, Pi.codomain
// ============================================================================

fn free_holes_term(term: Term, binding: Int) -> List(Int) {
  case term {
    Var(_, _) -> []
    Hole(id, _) -> [id]
    Lam(implicits, param, body, _) -> {
      let implicit_holes = list.fold(implicits, [], fn(acc, i) {
        list.append(acc, free_holes_term(i.1, binding + 1))
      })
      let param_holes = free_holes_term(param.1, binding + 1)
      let body_holes = free_holes_term(body, binding + 1)
      list.append(list.append(implicit_holes, param_holes), body_holes)
    }
    App(fun, arg, _) -> {
      let fun_holes = free_holes_term(fun, binding)
      let arg_holes = free_holes_term(arg, binding)
      list.append(fun_holes, arg_holes)
    }
    Pi(implicits, domain, codomain, _) -> {
      let implicit_holes = list.fold(implicits, [], fn(acc, i) {
        list.append(acc, free_holes_term(i.1, binding))
      })
      let domain_holes = free_holes_term(domain.1, binding)
      let codomain_holes = free_holes_term(codomain, binding + 1)
      list.append(list.append(implicit_holes, domain_holes), codomain_holes)
    }
    Lit(_, _) -> []
    Ctr(_, arg, _) -> free_holes_term(arg, binding)
    Match(arg, cases, _) -> {
      let arg_holes = free_holes_term(arg, binding)
      let case_holes =
        list.fold(cases, [], fn(acc, c) {
          list.append(acc, free_holes_term(c.body, binding))
        })
      list.append(arg_holes, case_holes)
    }
    Ann(term, type_, _) -> {
      let term_holes = free_holes_term(term, binding)
      let type_holes = free_holes_term(type_, binding)
      list.append(term_holes, type_holes)
    }
    Call(_, args, return_type, _) -> {
      let arg_holes = list.fold(args, [], fn(acc, ta) {
        let term_h = free_holes_term(ta.0, binding)
        let type_h = free_holes_term(ta.1, binding)
        list.append(list.append(acc, term_h), type_h)
      })
      let ret_holes = free_holes_term(return_type, binding)
      list.append(arg_holes, ret_holes)
    }
    Rcd(fields, _) -> {
      list.fold(fields, [], fn(acc, f) {
        list.append(acc, free_holes_term(f.1, binding))
      })
    }
    RcdT(fields, _) -> {
      list.fold(fields, [], fn(acc, f) {
        let acc2 = list.append(acc, free_holes_term(f.1, binding))
        case f.2 {
          Some(t) -> list.append(acc2, free_holes_term(t, binding))
          None -> acc2
        }
      })
    }
    Typ(_, _) -> []
    TypeDef(_, _, constructors, _) -> {
      list.fold(constructors, [], fn(acc, c) {
        let acc2 = list.append(acc, free_holes_term(c.2, binding))
        list.append(acc2, free_holes_term(c.3, binding))
      })
    }
    LitT(_, _) -> []
    Fix(_, body, _) -> free_holes_term(body, binding)
    Err(_, _) -> []
  }
}

// ============================================================================
// FREE LEVELS (De Bruijn level analysis)
// ============================================================================

/// Collect free De Bruijn level indices referenced by a value.
///
/// A level is "free" if it refers to a binder outside the current scope.
/// `HVar(level)` is free when `level < binding`.
///
/// Returns levels in ascending order, unique.
pub fn collect_free_levels(value: Value) -> List(Int) {
  let levels = free_levels_from(value, 0)
  list.sort(list.unique(levels), int.compare)
}

fn free_levels_from(value: Value, binding: Int) -> List(Int) {
  case value {
    VNeut(head, spine) -> {
      let levels = head_level(head, binding)
      let spine_levels =
        list.fold(spine, [], fn(acc, elim) {
          case elim {
            EApp(arg) -> list.append(acc, free_levels_from(arg, binding))
            EMatch(_env, cases) -> list.append(acc, list.fold(cases, [], fn(acc, c) {
              list.append(acc, free_levels_from_term(c.body, binding))
            }))
          }
        })
      list.append(levels, spine_levels)
    }
    VLam(_env, implicits, param, body) -> {
      let implicit_levels = list.fold(implicits, [], fn(acc, i) {
        list.append(acc, free_levels_from(i.1, binding + 1))
      })
      let param_levels = free_levels_from(param.1, binding + 1)
      let body_levels = free_levels_term(body, binding + 1)
      list.append(list.append(implicit_levels, param_levels), body_levels)
    }
    VPi(_env, implicits, domain, codomain) -> {
      let implicit_levels = list.fold(implicits, [], fn(acc, i) {
        list.append(acc, free_levels_from(i.1, binding))
      })
      let domain_levels = free_levels_from(domain.1, binding)
      let codomain_levels = free_levels_from(codomain, binding)
      list.append(list.append(implicit_levels, domain_levels), codomain_levels)
    }
    VLit(_) -> []
    VCtr(_, arg) -> free_levels_from(arg, binding)
    VRcd(fields) -> {
      list.fold(fields, [], fn(acc, f) {
        list.append(acc, free_levels_from(f.1, binding))
      })
    }
    VRcdT(fields) -> {
      list.fold(fields, [], fn(acc, f) {
        let acc2 = list.append(acc, free_levels_from(f.1, binding))
        case f.2 {
          Some(d) -> list.append(acc2, free_levels_from(d, binding))
          None -> acc2
        }
      })
    }
    VTypeDef(name: _, params: _, constructors: _) -> []
    VTyp(_) -> []
    VLitT(_) -> []
    VFix(_, env, body) -> {
      let env_levels = list.fold(env, [], fn(acc, v) {
        list.append(acc, free_levels_from(v, binding))
      })
      list.append(env_levels, free_levels_term(body, binding))
    }
    ast.VCall(_, args, _) -> {
      list.fold(args, [], fn(acc, ta) {
        list.append(acc, free_levels_from(ta.0, binding))
      })
    }
    VErr -> []
  }
}

/// Collect free levels from a term body (used for EMatch cases).
fn free_levels_from_term(term: Term, binding: Int) -> List(Int) {
  free_levels_term(term, binding)
}

fn head_level(head: Head, binding: Int) -> List(Int) {
  case head {
    HVar(level) ->
      case level >= binding {
        True -> [level]
        False -> []
      }
    HHole(_) -> []
    HFix(_name, _env) -> []
  }
}

fn free_levels_term(term: Term, binding: Int) -> List(Int) {
  case term {
    Var(i, _) ->
      case i >= binding {
        True -> [i]
        False -> []
      }
    Hole(_, _) -> []
    Lam(implicits, param, body, _) -> {
      let implicit_levels = list.fold(implicits, [], fn(acc, i) {
        list.append(acc, free_levels_term(i.1, binding + 1))
      })
      let param_levels = free_levels_term(param.1, binding + 1)
      let body_levels = free_levels_term(body, binding + 1)
      list.append(list.append(implicit_levels, param_levels), body_levels)
    }
    App(fun, arg, _) -> {
      let fun_levels = free_levels_term(fun, binding)
      let arg_levels = free_levels_term(arg, binding)
      list.append(fun_levels, arg_levels)
    }
    Pi(implicits, domain, codomain, _) -> {
      let implicit_levels = list.fold(implicits, [], fn(acc, i) {
        list.append(acc, free_levels_term(i.1, binding))
      })
      let domain_levels = free_levels_term(domain.1, binding)
      let codomain_levels = free_levels_term(codomain, binding + 1)
      list.append(list.append(implicit_levels, domain_levels), codomain_levels)
    }
    Lit(_, _) -> []
    Ctr(_, arg, _) -> free_levels_term(arg, binding)
    Match(arg, cases, _) -> {
      let arg_levels = free_levels_term(arg, binding)
      let case_levels =
        list.fold(cases, [], fn(acc, c) {
          list.append(acc, free_levels_term(c.body, binding))
        })
      list.append(arg_levels, case_levels)
    }
    Ann(term, type_, _) -> {
      let term_levels = free_levels_term(term, binding)
      let type_levels = free_levels_term(type_, binding)
      list.append(term_levels, type_levels)
    }
    Call(_, args, return_type, _) -> {
      let arg_levels = list.fold(args, [], fn(acc, ta) {
        let term_l = free_levels_term(ta.0, binding)
        let type_l = free_levels_term(ta.1, binding)
        list.append(list.append(acc, term_l), type_l)
      })
      let ret_levels = free_levels_term(return_type, binding)
      list.append(arg_levels, ret_levels)
    }
    Rcd(fields, _) -> {
      list.fold(fields, [], fn(acc, f) {
        list.append(acc, free_levels_term(f.1, binding))
      })
    }
    RcdT(fields, _) -> {
      list.fold(fields, [], fn(acc, f) {
        let acc2 = list.append(acc, free_levels_term(f.1, binding))
        case f.2 {
          Some(t) -> list.append(acc2, free_levels_term(t, binding))
          None -> acc2
        }
      })
    }
    Typ(_, _) -> []
    TypeDef(_, _, constructors, _) -> {
      list.fold(constructors, [], fn(acc, c) {
        let acc2 = list.append(acc, free_levels_term(c.2, binding))
        list.append(acc2, free_levels_term(c.3, binding))
      })
    }
    LitT(_, _) -> []
    Fix(_, body, _) -> free_levels_term(body, binding)
    Err(_, _) -> []
  }
}

// ============================================================================
// HOLE → VARIABLE SUBSTITUTION
// ============================================================================

/// Create a substitution mapping: maps hole IDs to De Bruijn variable indices.
///
/// Hole IDs are assigned indices starting from `base`. The highest-numbered
/// hole gets the lowest index (base). This ensures that the most recently
/// inferred hole appears first in the implicit parameter list.
///
/// ## Example
///
/// ```
/// create_hole_subst([2, 1], 0) -> [ #(2, 0), #(1, 1) ]
/// create_hole_subst([3, 1], 1) -> [ #(3, 1), #(1, 2) ]
/// ```
pub fn create_hole_subst(holes: List(Int), base: Int) -> List(#(Int, Int)) {
  // Deduplicate, sort ascending, reverse so highest hole gets lowest index
  let unique = list.unique(holes)
  let sorted = list.sort(unique, int.compare)
  let rev = fn(acc: List(Int), id: Int) -> List(Int) { [id, ..acc] }
  let rev_sorted = list.fold(sorted, [], rev)
  let assign = fn(acc: List(#(Int, Int)), id: Int) -> List(#(Int, Int)) {
    let n = list.length(acc)
    [#(id, base + n), ..acc]
  }
  list.fold(rev_sorted, [], assign)
}

/// Replace holes in a value with De Bruijn variable references.
///
/// Given a hole-to-DeBruijn mapping, this transforms every `HHole(id)` in the
/// value's head to `HVar(idx)` where `idx` comes from the mapping.
///
/// ## Example
///
/// ```
/// let subst = create_hole_subst([0], 0)  // #(0, 0)
/// let val = VNeut(HHole(0), [])
/// replace_holes_with_vars(val, subst)
/// // -> VNeut(HVar(0), [])
/// ```
pub fn replace_holes_with_vars(
  value: Value,
  subst: List(#(Int, Int)),
) -> Value {
  subst_holes(value, subst)
}

fn subst_holes(value: Value, subst: List(#(Int, Int))) -> Value {
  case value {
    VNeut(head, spine) -> {
      let new_head = subst_head(head, subst)
      let new_spine =
        list.map(spine, fn(elim) {
          case elim {
            EApp(arg) -> EApp(subst_values(arg, subst))
            EMatch(env, cases) -> EMatch(env, list.map(cases, fn(c) {
              Case(pattern: c.pattern, guard: c.guard, body: subst_holes_term(c.body, subst), span: c.span)
            }))
          }
        })
      VNeut(new_head, new_spine)
    }
    VLam(env, implicits, #(name, param_type), body) ->
      VLam(env, implicits, #(name, subst_holes(param_type, subst)), subst_holes_term(body, subst))
    VPi(env, implicits, domain, codomain) ->
      VPi(env, implicits, #(domain.0, subst_holes(domain.1, subst)), subst_holes(codomain, subst))
    VLit(lit) -> VLit(lit)
    VCtr(tag, arg) -> VCtr(tag, subst_holes(arg, subst))
    VRcd(fields) ->
      VRcd(list.map(fields, fn(f) { #(f.0, subst_holes(f.1, subst)) }))
    VRcdT(fields) ->
      VRcdT(list.map(fields, fn(f) {
        let new_default = case f.2 {
          Some(d) -> Some(subst_holes(d, subst))
          None -> None
        }
        #(f.0, subst_holes(f.1, subst), new_default)
      }))
    VCall(name, args, return_type) ->
      VCall(
        name,
        list.map(args, fn(a) {
          #(subst_holes(a.0, subst), subst_holes(a.1, subst))
        }),
        subst_holes(return_type, subst),
      )
    VFix(name, env, body) ->
      VFix(name, env, subst_holes_term(body, subst))
    VTypeDef(name: n, params: p, constructors: c) -> VTypeDef(
      name: n,
      params: p,
      constructors: c,
    )
    VTyp(level) -> VTyp(level)
    VLitT(ltype) -> VLitT(ltype)
    VErr -> VErr
  }
}

fn subst_holes_term(term: Term, subst: List(#(Int, Int))) -> Term {
  case term {
    Var(i, span) -> Var(i, span)
    Hole(id, span) -> {
      case list.find(subst, fn(pair) { pair.0 == id }) {
        Ok(#(_, idx)) -> Var(idx, span)
        Error(_) -> Hole(id, span)
      }
    }
    Lam(implicits, #(name, param), body, span) ->
      Lam(
        list.map(implicits, fn(i) { #(i.0, subst_holes_term(i.1, subst)) }),
        #(name, subst_holes_term(param, subst)),
        subst_holes_term(body, subst),
        span,
      )
    App(fun, arg, span) ->
      App(subst_holes_term(fun, subst), subst_holes_term(arg, subst), span)
    Pi(implicits, #(name, domain), codomain, span) ->
      Pi(
        list.map(implicits, fn(i) { #(i.0, subst_holes_term(i.1, subst)) }),
        #(name, subst_holes_term(domain, subst)),
        subst_holes_term(codomain, subst),
        span,
      )
    Lit(value, span) -> Lit(value, span)
    Ctr(tag, arg, span) -> Ctr(tag, subst_holes_term(arg, subst), span)
    Match(arg, cases, span) ->
      Match(
        subst_holes_term(arg, subst),
        list.map(cases, fn(c) {
          Case(c.pattern, c.guard, subst_holes_term(c.body, subst), c.span)
        }),
        span,
      )
    Ann(term, type_, span) ->
      Ann(subst_holes_term(term, subst), subst_holes_term(type_, subst), span)
    Call(name, args, return_type, span) ->
      Call(
        name,
        list.map(args, fn(ta) {
          #(subst_holes_term(ta.0, subst), subst_holes_term(ta.1, subst))
        }),
        subst_holes_term(return_type, subst),
        span,
      )
    Rcd(fields, span) ->
      Rcd(
        list.map(fields, fn(f) { #(f.0, subst_holes_term(f.1, subst)) }),
        span,
      )
    RcdT(fields, span) ->
      RcdT(
        list.map(
          fields,
          fn(f: #(String, ast.Term, option.Option(ast.Term))) {
            let new_default: option.Option(ast.Term) = case f.2 {
              Some(t) -> Some(subst_holes_term(t, subst))
              None -> None
            }
            #(f.0, subst_holes_term(f.1, subst), new_default)
          },
        ),
        span,
      )
    Typ(level, span) -> Typ(level, span)
    TypeDef(name: name, params: params, constructors: constructors, span: span) -> {
      let shift_cons = fn(ctor) {
        case ctor {
          #(tag, bindings, self_ty, result, c_span) -> {
            let new_self = subst_holes_term(self_ty, subst)
            let new_result = subst_holes_term(result, subst)
            #(tag, bindings, new_self, new_result, c_span)
          }
        }
      }
      TypeDef(
        name: name,
        params: params,
        constructors: list.map(constructors, shift_cons),
        span: span,
      )
    }
    LitT(ltype, span) -> LitT(ltype, span)
    Fix(name, body, span) -> Fix(name, subst_holes_term(body, subst), span)
    Err(msg, span) -> Err(msg, span)
  }
}

fn subst_head(head: Head, subst: List(#(Int, Int))) -> Head {
  case head {
    HHole(id) -> {
      case list.find(subst, fn(pair) { pair.0 == id }) {
        Ok(#(_, idx)) -> HVar(idx)
        Error(_) -> HHole(id)
      }
    }
    HVar(level) -> HVar(level)
    HFix(name, env) -> HFix(name, env)
  }
}

fn subst_values(value: Value, subst: List(#(Int, Int))) -> Value {
  subst_holes(value, subst)
}

// ============================================================================
// STRING REPRESENTATION (Debug)
// ============================================================================

/// Format a list of free holes as a debug string.
pub fn holes_to_string(holes: List(Int)) -> String {
  case holes {
    [] -> "<no holes>"
    _ ->
      "["
      <> list.fold(holes, "", fn(acc, id) {
        case acc {
          "" -> "hole(" <> int.to_string(id) <> ")"
          _ -> acc <> ", hole(" <> int.to_string(id) <> ")"
        }
      })
      <> "]"
  }
}
