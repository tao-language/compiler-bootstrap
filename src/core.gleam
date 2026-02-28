import gleam/int
import gleam/io
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/result

pub type Term {
  Term(data: TermData, span: Span)
}

pub type TermData {
  Typ(level: Int)
  Lit(value: Literal)
  LitT(typ: LiteralType)
  Var(index: Int)
  Hole(id: Int)
  Ctr(tag: String, arg: Term)
  Rcd(fields: List(#(String, Term)))
  Dot(arg: Term, field: String)
  Ann(term: Term, typ: Term)
  Lam(name: String, body: Term)
  Pi(name: String, in: Term, out: Term)
  App(fun: Term, arg: Term)
  Match(arg: Term, motive: Term, cases: List(Case))
}

pub type Value {
  VTyp(level: Int)
  VLit(value: Literal)
  VLitT(typ: LiteralType)
  VNeut(head: Head, spine: List(Elim))
  VCtr(tag: String, arg: Value)
  VRcd(fields: List(#(String, Value)))
  VLam(name: String, env: Env, body: Term)
  VPi(name: String, env: Env, in: Value, out: Term)
  VErr
}

pub type Type =
  Value

pub type Pattern {
  PAny
  PAs(pattern: Pattern, name: String)
  PTyp(level: Int)
  PLit(value: Literal)
  PLitT(value: LiteralType)
  PCtr(tag: String, arg: Pattern)
  PRcd(fields: List(#(String, Pattern)))
}

pub type Head {
  HVar(level: Int)
  HHole(id: Int)
}

pub type Elim {
  EDot(name: String)
  EApp(arg: Value)
  EMatch(env: Env, motive: Value, cases: List(Case))
}

pub type Case {
  Case(pattern: Pattern, body: Term, span: Span)
}

pub type Literal {
  I32(value: Int)
  I64(value: Int)
  U32(value: Int)
  U64(value: Int)
  F32(value: Float)
  F64(value: Float)
}

pub type LiteralType {
  I32T
  I64T
  U32T
  U64T
  F32T
  F64T
}

pub type Span {
  Span(file: String, row: Int, col: Int)
}

pub type CtrDef {
  CtrDef(params: List(String), arg_ty: Term, ret_ty: Term)
}

pub type TypeEnv =
  List(#(String, CtrDef))

pub type Env =
  List(Value)

pub type Context =
  List(#(String, #(Value, Type)))

pub type Subst =
  List(#(Int, Value))

pub type Error {
  // Type errors
  PatternMismatch(pattern: Pattern, expected_ty: Type, s1: Span, s2: Span)
  TypeMismatch(expected: Type, got: Type, span1: Span, span2: Span)
  TypeAnnotationNeeded(term: Term)
  NotAFunction(fun: Term, fun_ty: Value)
  VarUndefined(index: Int, span: Span)
  CtrUndefined(tag: String, span: Span)
  CtrUnsolvedParam(tag: String, ctr: CtrDef, id: Int, span: Span)
  RcdMissingFields(name: List(String), span: Span)
  DotFieldNotFound(name: String, fields: List(#(String, Value)), span: Span)
  DotOnNonCtr(value: Value, name: String, span: Span)
  MatchEmpty(arg: Term, motive: Term, span: Span)

  // Exhaustiveness errors
  NonExhaustiveMatch(missing: List(Pattern), span: Span)
  RedundantMatch(pattern: Pattern, span: Span)

  // Runtime errors
  TODO(message: String, span: Span)
  MatchUnhandledCase(value: Value, span: Span)
  AppNotFunction(value: Value)
}

pub fn eval(env: Env, term: Term) -> Value {
  case term.data {
    Typ(k) -> VTyp(k)
    Lit(k) -> VLit(k)
    LitT(k) -> VLitT(k)
    Var(i) ->
      case list_get(env, i) {
        Some(value) -> value
        None -> VErr
      }
    Hole(id) -> VNeut(HHole(id), [])
    Ctr(tag, arg) -> VCtr(tag, eval(env, arg))
    Rcd(fields) -> VRcd(list.map(fields, fn(kv) { #(kv.0, eval(env, kv.1)) }))
    Dot(arg, name) -> do_dot(eval(env, arg), name, arg.span)
    Ann(term, _) -> eval(env, term)
    Lam(name, body) -> VLam(name, env, body)
    Pi(name, in, out) -> VPi(name, env, eval(env, in), out)
    App(fun, arg) -> {
      let fun_val = eval(env, fun)
      let arg_val = eval(env, arg)
      do_app(fun_val, arg_val)
    }
    Match(arg, motive, cases) -> {
      let arg_val = eval(env, arg)
      let motive_val = eval(env, motive)
      do_match(env, arg_val, motive_val, cases)
    }
  }
}

fn do_dot(value: Value, name: String, s: Span) -> Value {
  case value {
    VNeut(head, spine) -> VNeut(head, list.append(spine, [EDot(name)]))
    VRcd(fields) ->
      case list.key_find(fields, name) {
        Ok(v) -> v
        Error(Nil) -> VErr
      }
    _ -> VErr
  }
}

pub fn do_app(fun: Value, arg: Value) -> Value {
  case fun {
    VNeut(head, spine) -> VNeut(head, list.append(spine, [EApp(arg)]))
    VLam(_, env, body) -> eval([arg, ..env], body)
    _ -> VErr
  }
}

pub fn do_match(env: Env, arg: Value, motive: Value, cases: List(Case)) -> Value {
  case arg {
    VNeut(head, spine) ->
      VNeut(head, list.append(spine, [EMatch(env, motive, cases)]))
    _ ->
      case do_match_cases(arg, cases) {
        Some(#(bindings, body)) -> eval(list.append(bindings, env), body)
        None -> VErr
      }
  }
}

pub fn do_match_cases(arg: Value, cases: List(Case)) -> Option(#(Env, Term)) {
  case cases {
    [] -> None
    [c, ..cases] ->
      case do_match_pattern(c.pattern, arg) {
        Ok(env) -> Some(#(env, c.body))
        Error(Nil) -> do_match_cases(arg, cases)
      }
  }
}

pub fn do_match_pattern(pattern: Pattern, value: Value) -> Result(Env, Nil) {
  case pattern, value {
    PAny, _ -> Ok([])
    PAs(p, x), _ -> {
      use env <- result.try(do_match_pattern(p, value))
      Ok([value, ..env])
    }
    PTyp(pk), VTyp(vk) if pk == vk -> Ok([])
    PLit(pk), VLit(vk) if pk == vk -> Ok([])
    PLitT(pk), VLitT(vk) if pk == vk -> Ok([])
    PCtr(ptag, parg), VCtr(vtag, varg) if ptag == vtag ->
      do_match_pattern(parg, varg)
    PRcd(pfields), VRcd(vfields) ->
      list.try_fold(pfields, [], fn(acc_env, pfield) {
        let #(name, p) = pfield
        use v <- result.try(list.key_find(vfields, name))
        use env <- result.try(do_match_pattern(p, v))
        Ok(list.append(acc_env, env))
      })
    _, _ -> Error(Nil)
  }
}

pub fn normalize(env: Env, term: Term, s: Span) -> Term {
  let val = eval(env, term)
  quote(list.length(env), val, s)
}

// Converts a Value (semantics) back to a Term (syntax).
pub fn quote(lvl: Int, value: Value, s: Span) -> Term {
  case value {
    VTyp(k) -> Term(Typ(k), s)
    VLit(k) -> Term(Lit(k), s)
    VLitT(k) -> Term(LitT(k), s)
    VNeut(head, spine) -> {
      let head_term = quote_head(lvl, head, s)
      quote_neut(lvl, head_term, spine, s)
    }
    VCtr(tag, arg) -> Term(Ctr(tag, quote(lvl, arg, s)), s)
    VRcd(fields) ->
      Term(Rcd(list.map(fields, fn(kv) { #(kv.0, quote(lvl, kv.1, s)) })), s)
    VLam(name, env, body) -> {
      let fresh = VNeut(HVar(lvl), [])
      let body_val = eval([fresh, ..env], body)
      let body_quote = quote(lvl + 1, body_val, body.span)
      Term(Lam(name, body_quote), s)
    }
    VPi(name, env, in_val, out_term) -> {
      let in_quote = quote(lvl, in_val, s)
      let fresh = VNeut(HVar(lvl), [])
      let out_val = eval([fresh, ..env], out_term)
      let out_quote = quote(lvl + 1, out_val, out_term.span)
      Term(Pi(name, in_quote, out_quote), s)
    }
    VErr -> Term(Hole(-1), s)
  }
}

fn quote_neut(lvl: Int, head: Term, spine: List(Elim), s: Span) -> Term {
  case spine {
    [] -> head
    [elim, ..spine] -> {
      let new_head = quote_elim(lvl, head, elim, s)
      quote_neut(lvl, new_head, spine, s)
    }
  }
}

fn quote_elim(lvl: Int, head: Term, elim: Elim, s: Span) -> Term {
  case elim {
    EDot(name) -> Term(Dot(head, name), s)
    EApp(arg) -> Term(App(head, quote(lvl, arg, s)), s)
    EMatch(env, motive, cases) ->
      Term(Match(head, quote(lvl, motive, s), cases), s)
  }
}

fn quote_head(lvl: Int, head: Head, s: Span) -> Term {
  case head {
    HVar(l) -> Term(Var(lvl - l - 1), s)
    HHole(id) -> Term(Hole(id), s)
  }
}

pub fn unify(
  lvl: Int,
  sub: Subst,
  v1: Value,
  v2: Value,
  s1: Span,
  s2: Span,
) -> Result(Subst, Error) {
  case v1, v2 {
    VTyp(k1), VTyp(k2) if k1 == k2 -> Ok(sub)
    VLit(k1), VLit(k2) if k1 == k2 -> Ok(sub)
    VLitT(k1), VLitT(k2) if k1 == k2 -> Ok(sub)
    VNeut(HHole(id), []), _ ->
      case list.key_find(sub, id) {
        Ok(v) -> unify(lvl + 1, sub, v, v2, s1, s2)
        Error(Nil) -> Ok([#(id, v2), ..sub])
      }
    _, VNeut(HHole(_), []) -> unify(lvl + 1, sub, v2, v1, s2, s1)
    VNeut(h1, spine1), VNeut(h2, spine2) if h1 == h2 ->
      unify_elim_list(lvl, sub, spine1, spine2, s1, s2)
    VCtr(k1, arg1), VCtr(k2, arg2) if k1 == k2 ->
      unify(lvl, sub, arg1, arg2, s1, s2)
    VRcd(fields1), VRcd(fields2) ->
      unify_fields(lvl, sub, fields1, fields2, s1, s2)
    VLam(_, env1, body1), VLam(_, env2, body2) -> {
      let fresh = VNeut(HVar(lvl), [])
      let a = eval([fresh, ..env1], body1)
      let b = eval([fresh, ..env2], body2)
      unify(lvl + 1, sub, a, b, s1, s2)
    }
    VPi(_, env1, in1, out1), VPi(_, env2, in2, out2) -> {
      use _ <- result.try(unify(lvl, sub, in1, in2, s1, s2))
      let fresh = VNeut(HVar(lvl), [])
      let a = eval([fresh, ..env1], out1)
      let b = eval([fresh, ..env2], out2)
      unify(lvl + 1, sub, a, b, s1, s2)
    }
    VErr, _ -> Ok(sub)
    _, VErr -> Ok(sub)
    _, _ -> Error(TypeMismatch(v1, v2, s1, s2))
  }
}

fn unify_fields(
  lvl: Int,
  sub: Subst,
  args1: List(#(String, Value)),
  args2: List(#(String, Value)),
  s1: Span,
  s2: Span,
) -> Result(Subst, Error) {
  case args1 {
    [] ->
      case list.map(args2, fn(kv) { kv.0 }) {
        [] -> Ok(sub)
        names -> Error(RcdMissingFields(names, s1))
      }
    [#(name, v1), ..args1] ->
      case list.key_pop(args2, name) {
        Error(Nil) -> {
          let names =
            list.filter(args1, fn(kv) {
              list.key_find(args2, kv.0) == Error(Nil)
            })
            |> list.map(fn(kv) { kv.0 })
          Error(RcdMissingFields([name, ..names], s2))
        }
        Ok(#(v2, args2)) -> {
          use sub <- result.try(unify(lvl, sub, v1, v2, s1, s2))
          unify_fields(lvl, sub, args1, args2, s1, s2)
        }
      }
  }
}

fn unify_elim(
  lvl: Int,
  sub: Subst,
  e1: Elim,
  e2: Elim,
  s1: Span,
  s2: Span,
) -> Result(Subst, Error) {
  case e1, e2 {
    EDot(n1), EDot(n2) if n1 == n2 -> Ok(sub)
    EApp(a1), EApp(a2) -> unify(lvl, sub, a1, a2, s1, s2)
    _, _ -> Error(TODO("Spine mismatch", s1))
  }
}

fn unify_elim_list(
  lvl: Int,
  sub: Subst,
  l1: List(Elim),
  l2: List(Elim),
  s1: Span,
  s2: Span,
) -> Result(Subst, Error) {
  case l1, l2 {
    [], [] -> Ok(sub)
    [e1, ..xs], [e2, ..ys] -> {
      use sub <- result.try(unify_elim(lvl, sub, e1, e2, s1, s2))
      unify_elim_list(lvl, sub, xs, ys, s1, s2)
    }
    _, _ -> Error(TODO("Arity mismatch", s1))
  }
}

pub fn infer(
  lvl: Int,
  ctx: Context,
  tenv: TypeEnv,
  sub: Subst,
  term: Term,
) -> #(Value, Type, Subst, List(Error)) {
  case term.data {
    Typ(k) -> #(VTyp(k), VTyp(k + 1), sub, [])
    Lit(k) -> #(VLit(k), typeof_lit(k), sub, [])
    LitT(k) -> #(VLitT(k), VTyp(0), sub, [])
    Var(i) -> {
      case list_get(ctx, i) {
        Some(#(_, #(val, ty))) -> #(val, ty, sub, [])
        None -> {
          let err = VarUndefined(i, term.span)
          #(VErr, VErr, sub, [err])
        }
      }
    }
    Hole(_) -> {
      let err = TypeAnnotationNeeded(term)
      #(VErr, VErr, sub, [err])
    }
    Ctr(tag, arg) -> {
      case list.key_find(tenv, tag) {
        Error(Nil) -> {
          let err = CtrUndefined(tag, term.span)
          #(VErr, VErr, sub, [err])
        }
        Ok(ctr) -> {
          let #(ctr_arg_ty, _, sub, ctr_errors) =
            check_ctr_def(lvl, ctx, tenv, sub, ctr)
          let #(arg_val, arg_ty, sub, arg_errors) =
            infer(lvl, ctx, tenv, sub, arg)
          let #(_, sub, arg_errors) =
            check_type(lvl, sub, arg_ty, ctr_arg_ty, arg.span, ctr.arg_ty.span)
          let #(params, param_errors) =
            ctr_solve_params(sub, ctr, tag, term.span)
          let env = list.append(params, ctx2env(ctx))
          let errors = list.flatten([ctr_errors, param_errors, arg_errors])
          #(VCtr(tag, eval(env, arg)), eval(env, ctr.ret_ty), sub, errors)
        }
      }
    }
    Rcd(fields) -> {
      let #(fields_val, fields_ty, sub, errors) =
        infer_fields(lvl, ctx, tenv, sub, fields)
      #(VRcd(fields_val), VRcd(fields_ty), sub, errors)
    }
    Dot(arg, name) -> {
      let #(arg_val, arg_ty, sub, arg_errors) = infer(lvl, ctx, tenv, sub, arg)
      let val = do_dot(arg_val, name, term.span)
      let #(ty, dot_errors) = case arg_ty {
        VRcd(fields) ->
          case list.key_find(fields, name) {
            Ok(ty) -> #(ty, [])
            Error(Nil) -> {
              let err = DotFieldNotFound(name, fields, arg.span)
              #(VErr, [err])
            }
          }
        _ -> {
          let err = DotOnNonCtr(arg_ty, name, arg.span)
          #(VErr, [err])
        }
      }
      let errors = list.append(arg_errors, dot_errors)
      #(val, ty, sub, errors)
    }
    Ann(term, term_ty) -> {
      let #(ty_val, _, sub, infer_errors) = infer(lvl, ctx, tenv, sub, term_ty)
      let #(val, sub, check_errors) =
        check(lvl, ctx, tenv, sub, term, ty_val, term_ty.span)
      let errors = list.append(infer_errors, check_errors)
      #(val, ty_val, sub, errors)
    }
    Lam(_, _) -> {
      let err = TypeAnnotationNeeded(term)
      #(VErr, VErr, sub, [err])
    }
    Pi(name, in, out) -> {
      let env = ctx2env(ctx)
      let #(in_val, _, sub, in_errors) = infer(lvl, ctx, tenv, sub, in)
      let fresh = VNeut(HVar(lvl), [])
      let ctx = [#(name, #(fresh, in_val)), ..ctx]
      let #(_, _, sub, out_errors) = infer(lvl + 1, ctx, tenv, sub, out)
      let errors = list.append(in_errors, out_errors)
      #(VPi(name, env, in_val, out), VTyp(0), sub, errors)
    }
    App(fun, arg) -> {
      let #(fun_val, fun_ty, sub, fun_errors) = infer(lvl, ctx, tenv, sub, fun)
      case fun_ty {
        VPi(_, pi_env, in, out) -> {
          let #(arg_val, sub, arg_errors) =
            check(lvl, ctx, tenv, sub, arg, in, fun.span)
          let out_val = eval([arg_val, ..pi_env], out)
          let errors = list.append(fun_errors, arg_errors)
          #(do_app(fun_val, arg_val), out_val, sub, errors)
        }
        _ -> {
          let err = NotAFunction(fun, fun_ty)
          #(VErr, VErr, sub, [err])
        }
      }
    }
    // Match(arg, []) -> #(VErr, VErr, sub, [MatchEmpty(arg, term.span)])
    // Match(arg, [Case(pattern, body, p_span), ..cases]) -> {
    //   let #(arg_val, arg_ty, sub, arg_errors) = infer(lvl, ctx, tenv, sub, arg)
    //   let #(lvl, case_ctx, sub, p1_errors) =
    //     bind_pattern(lvl, ctx, tenv, sub, pattern, arg_ty, p_span, arg.span)
    //   let #(_, body_ty, sub, b1_errors) = infer(lvl, case_ctx, tenv, sub, body)
    //   let #(lvl, sub, cases_errors) =
    //     list.fold(
    //       cases,
    //       #(lvl, sub, list.append(p1_errors, b1_errors)),
    //       fn(acc, c) {
    //         let #(lvl, sub, errors) = acc
    //         let #(s1, s2) = #(c.span, arg.span)
    //         let #(lvl, case_ctx, sub, p_errors) =
    //           bind_pattern(lvl, ctx, tenv, sub, c.pattern, arg_ty, s1, s2)
    //         let #(_, sub, b_errors) =
    //           check(lvl, case_ctx, tenv, sub, c.body, body_ty, c.body.span)
    //         let errors = list.flatten([errors, p_errors, b_errors])
    //         #(lvl, sub, errors)
    //       },
    //     )
    //   let errors = list.flatten([arg_errors, cases_errors])
    //   #(todo, body_ty, sub, errors)
    // }
    Match(arg, motive, cases) -> {
      let env = ctx2env(ctx)
      let #(arg_val, arg_ty, sub, arg_errors) = infer(lvl, ctx, tenv, sub, arg)
      let motive_ty = VPi("_", env, arg_ty, Term(Typ(0), arg.span))
      let #(motive_val, sub, motive_errors) =
        check(lvl, ctx, tenv, sub, motive, motive_ty, motive.span)
      let empty_error = case cases {
        [] -> [MatchEmpty(arg, motive, term.span)]
        _ -> []
      }
      let #(sub, cases_errors) =
        list.fold(cases, #(sub, empty_error), fn(acc, c) {
          let #(sub, acc_errors) = acc
          let #(s1, s2) = #(c.span, arg.span)
          let #(lvl, ctx, sub, pat_val, pat_errors) =
            bind_pattern(lvl, ctx, tenv, sub, c.pattern, arg_ty, s1, s2)
          let branch_ty = do_app(motive_val, pat_val)
          let #(_, sub, body_errors) =
            check(lvl, ctx, tenv, sub, c.body, branch_ty, motive.span)
          let errors = list.flatten([acc_errors, pat_errors, body_errors])
          #(sub, errors)
        })
      let result_ty = do_app(motive_val, arg_val)
      let match_val = do_match(env, arg_val, motive_val, cases)
      let errors = list.flatten([arg_errors, motive_errors, cases_errors])
      #(match_val, result_ty, sub, errors)
    }
  }
}

fn typeof_lit(lit: Literal) -> Value {
  case lit {
    I32(_) -> VLitT(I32T)
    I64(_) -> VLitT(I64T)
    U32(_) -> VLitT(U32T)
    U64(_) -> VLitT(U64T)
    F32(_) -> VLitT(F32T)
    F64(_) -> VLitT(F64T)
  }
}

fn infer_fields(
  lvl: Int,
  ctx: Context,
  tenv: TypeEnv,
  sub: Subst,
  fields: List(#(String, Term)),
) -> #(List(#(String, Value)), List(#(String, Type)), Subst, List(Error)) {
  case fields {
    [] -> #([], [], sub, [])
    [#(name, term), ..fields] -> {
      let #(val, ty, sub, errors1) = infer(lvl, ctx, tenv, sub, term)
      let #(fields_val, fields_ty, sub, errors2) =
        infer_fields(lvl, ctx, tenv, sub, fields)
      let errors = list.append(errors1, errors2)
      #([#(name, val), ..fields_val], [#(name, ty), ..fields_ty], sub, errors)
    }
  }
}

// fn infer_match(
//   lvl: Int,
//   ctx: Context,
//   tenv: TypeEnv,
//   sub: Subst,
//   arg_ty: Value,
//   cases: List(Case),
//   s: Span,
// ) -> #(Value, Subst, List(Error)) {
//   let results =
//     list.map(cases, fn(c) {
//       let s1 = c.span
//       let s2 = c.body.span
//       let #(lvl, ctx, sub, errors) =
//         bind_pattern(lvl, ctx, tenv, sub, c.pattern, arg_ty, s1, s2)
//       let body_ty = infer(lvl, ctx, tenv, c.body)
//       #(body_ty, c.body.span, errors)
//     })
//   let #(first_ty, s2) = case results {
//     [] -> #(VErr(MatchEmpty(arg_ty, s)), s)
//     [#(ty, span, _), ..] -> #(ty, span)
//   }
//   let #(final_ty, errors) =
//     list.fold(results, #(first_ty, []), fn(acc, res) {
//       let #(acc_ty, acc_errors) = acc
//       let #(body_ty, s1, p_errs) = res
//       let #(final_ty, type_errs) = case
//         unify(lvl, [], body_ty, first_ty, s1, s2)
//       {
//         // Should we apply sub to acc_ty? Is this correct or necessary?
//         Ok(sub) -> #(acc_ty, [])
//         Error(e) -> #(acc_ty, [e])
//       }
//       let errors = list.flatten([acc_errors, p_errs, type_errs])
//       #(final_ty, errors)
//     })
//   with_errors(final_ty, errors)
// }

pub fn pattern_to_value(lvl: Int, pat: Pattern) -> #(Int, Value) {
  case pat {
    PAny -> #(lvl + 1, VNeut(HVar(lvl), []))
    PAs(p, _) -> pattern_to_value(lvl, p)
    PTyp(k) -> #(lvl, VTyp(k))
    PLit(k) -> #(lvl, VLit(k))
    PLitT(k) -> #(lvl, VLitT(k))
    PCtr(tag, parg) -> {
      let #(lvl, arg) = pattern_to_value(lvl, parg)
      #(lvl, VCtr(tag, arg))
    }
    PRcd(pfields) -> {
      let #(lvl, fields) =
        list.fold(pfields, #(lvl, []), fn(acc, kv) {
          let #(lvl, fields) = acc
          let #(name, p) = kv
          let #(lvl, v) = pattern_to_value(lvl, p)
          #(lvl, [#(name, v), ..fields])
        })
      #(lvl, VRcd(list.reverse(fields)))
    }
  }
}

pub fn bind_pattern(
  lvl: Int,
  ctx: Context,
  tenv: TypeEnv,
  sub: Subst,
  pattern: Pattern,
  ret_ty: Value,
  pat_span: Span,
  ret_span: Span,
) -> #(Int, Context, Subst, Value, List(Error)) {
  case pattern {
    PAny -> {
      let fresh = VNeut(HVar(lvl), [])
      let ctx = [#("", #(fresh, ret_ty)), ..ctx]
      #(lvl + 1, ctx, sub, VNeut(HVar(lvl), []), [])
    }
    PAs(PAny, name) -> {
      let fresh = VNeut(HVar(lvl), [])
      let ctx = [#(name, #(fresh, ret_ty)), ..ctx]
      #(lvl + 1, ctx, sub, VNeut(HVar(lvl), []), [])
    }
    PAs(p, name) -> {
      let fresh = VNeut(HVar(lvl), [])
      let ctx = [#(name, #(fresh, ret_ty)), ..ctx]
      bind_pattern(lvl + 1, ctx, tenv, sub, p, ret_ty, pat_span, ret_span)
    }
    PTyp(k) -> {
      let #(_, sub, errors) =
        check(lvl, ctx, tenv, sub, Term(Typ(k), pat_span), ret_ty, ret_span)
      #(lvl, ctx, sub, VTyp(k), errors)
    }
    PLit(k) -> {
      let #(_, sub, errors) =
        check(lvl, ctx, tenv, sub, Term(Lit(k), pat_span), ret_ty, ret_span)
      #(lvl, ctx, sub, VLit(k), errors)
    }
    PLitT(k) -> {
      let #(_, sub, errors) =
        check(lvl, ctx, tenv, sub, Term(LitT(k), pat_span), ret_ty, ret_span)
      #(lvl, ctx, sub, VLitT(k), errors)
    }
    PCtr(tag, parg) -> {
      case list.key_find(tenv, tag) {
        Error(Nil) -> #(lvl, ctx, sub, VErr, [CtrUndefined(tag, pat_span)])
        Ok(ctr) -> {
          let #(_, ctr_ret_ty, sub, ctr_errors) =
            check_ctr_def(lvl, ctx, tenv, sub, ctr)
          let #(_, sub, ret_errors) =
            check_type(lvl, sub, ctr_ret_ty, ret_ty, ctr.ret_ty.span, ret_span)
          let #(params, param_errors) =
            ctr_solve_params(sub, ctr, tag, pat_span)
          let env = list.append(params, ctx2env(ctx))
          let ctr_arg_ty = eval(env, ctr.arg_ty)
          let #(s1, s2) = #(pat_span, ctr.arg_ty.span)
          let #(lvl, ctx, sub, varg, arg_errors) =
            bind_pattern(lvl, ctx, tenv, sub, parg, ctr_arg_ty, s1, s2)
          let errors =
            list.flatten([ctr_errors, param_errors, arg_errors, ret_errors])
          #(lvl, ctx, sub, VCtr(tag, varg), errors)
        }
      }
    }
    PRcd(pfields) ->
      case ret_ty {
        VRcd(vfields) -> {
          let missing =
            list.filter_map(pfields, fn(kv) {
              case list.key_find(vfields, kv.0) {
                Error(Nil) -> Ok(kv.0)
                Ok(_) -> Error(Nil)
              }
            })
          let errors = case missing {
            [] -> []
            _ -> [RcdMissingFields(missing, ret_span)]
          }
          let #(lvl, ctx, sub, fields, errors) =
            list.index_fold(
              pfields,
              #(lvl, ctx, sub, [], errors),
              fn(acc, kv, i) {
                let #(lvl, ctx, sub, fields, errors) = acc
                let #(name, p) = kv
                let ty = case list.key_find(vfields, name) {
                  Error(Nil) -> VNeut(HHole(i), [])
                  Ok(ty) -> ty
                }
                let #(lvl, ctx, sub, v, bind_errors) =
                  bind_pattern(lvl, ctx, tenv, sub, p, ty, pat_span, ret_span)
                let fields = [#(name, v), ..fields]
                let errors = list.append(errors, bind_errors)
                #(lvl, ctx, sub, fields, errors)
              },
            )
          #(lvl, ctx, sub, VRcd(fields), errors)
        }
        _ -> #(lvl, ctx, sub, VErr, [
          PatternMismatch(pattern, ret_ty, pat_span, ret_span),
        ])
      }
  }
}

pub fn check(
  lvl: Int,
  ctx: Context,
  tenv: TypeEnv,
  sub: Subst,
  term: Term,
  expected_ty: Value,
  ty_span: Span,
) -> #(Value, Subst, List(Error)) {
  case term.data, expected_ty {
    Lam(name, body), VPi(_, pi_env, in, out) -> {
      let env = ctx2env(ctx)
      let fresh = VNeut(HVar(lvl), [])
      let out_val = eval([fresh, ..pi_env], out)
      let ctx = [#(name, #(fresh, in)), ..ctx]
      let #(_, sub, errors) =
        check(lvl + 1, ctx, tenv, sub, body, out_val, ty_span)
      #(VLam(name, env, body), sub, errors)
    }
    Hole(id), _ -> #(VNeut(HHole(id), []), [], [])
    Ctr(tag, arg), _ ->
      check_ctr(lvl, ctx, tenv, sub, tag, arg, expected_ty, ty_span, term.span)
    _, _ -> {
      let #(value, inferred_ty, sub, errors) = infer(lvl, ctx, tenv, sub, term)
      case unify(lvl, sub, inferred_ty, expected_ty, term.span, ty_span) {
        Ok(sub) -> #(value, sub, errors)
        Error(e) -> #(VErr, sub, [e, ..errors])
      }
    }
  }
}

fn check_ctr(
  lvl: Int,
  ctx: Context,
  tenv: TypeEnv,
  sub: Subst,
  tag: String,
  arg: Term,
  ret_ty: Value,
  ret_span: Span,
  term_span: Span,
) -> #(Value, Subst, List(Error)) {
  case list.key_find(tenv, tag) {
    Error(Nil) -> {
      let err = CtrUndefined(tag, ret_span)
      #(VErr, [], [err])
    }
    Ok(ctr) -> {
      let #(_, ctr_ret_ty, sub, ctr_errors) =
        check_ctr_def(lvl, ctx, tenv, sub, ctr)
      let #(_, sub, ret_errors) =
        check_type(lvl, sub, ctr_ret_ty, ret_ty, ctr.ret_ty.span, ret_span)
      let #(params, param_errors) = ctr_solve_params(sub, ctr, tag, term_span)
      let env = list.append(params, ctx2env(ctx))
      let ctr_arg_ty = eval(env, ctr.arg_ty)
      let #(arg_val, sub, arg_errors) =
        check(lvl, ctx, tenv, sub, arg, ctr_arg_ty, ctr.arg_ty.span)
      let errors =
        list.flatten([ctr_errors, param_errors, arg_errors, ret_errors])
      #(VCtr(tag, arg_val), sub, errors)
    }
  }
}

fn check_ctr_def(
  lvl: Int,
  ctx: Context,
  tenv: TypeEnv,
  sub: Subst,
  ctr: CtrDef,
) -> #(Value, Value, Subst, List(Error)) {
  let params =
    list.index_map(ctr.params, fn(x, i) {
      #(x, #(VNeut(HHole(i), []), VTyp(0)))
    })
  let ctx = list.append(params, ctx)
  let #(arg_ty, _, sub, arg_errors) = infer(lvl, ctx, tenv, sub, ctr.arg_ty)
  let #(ret_ty, _, sub, ret_errors) = infer(lvl, ctx, tenv, sub, ctr.ret_ty)
  #(arg_ty, ret_ty, sub, list.append(arg_errors, ret_errors))
}

pub fn ctr_params_instantiate(ctx: Context, ctr: CtrDef) -> Env {
  let params = list.index_map(ctr.params, fn(_, i) { VNeut(HHole(i), []) })
  list.append(params, ctx2env(ctx))
}

pub fn check_type(
  lvl: Int,
  sub: Subst,
  t1: Value,
  t2: Value,
  t1_span: Span,
  t2_span: Span,
) -> #(Value, Subst, List(Error)) {
  case unify(lvl, sub, t1, t2, t1_span, t2_span) {
    Ok(sub) -> #(force(sub, t1, t1_span), sub, [])
    Error(e) -> #(t1, sub, [e])
  }
}

pub fn force(sub: Subst, value: Value, s: Span) -> Value {
  case value {
    VNeut(HVar(i), spine) ->
      case list.key_find(sub, i) {
        Ok(v) -> {
          let forced_val = apply_spine(v, spine, s)
          force(sub, forced_val, s)
        }
        Error(Nil) -> value
      }
    _ -> value
  }
}

fn apply_spine(val: Value, spine: List(Elim), s: Span) -> Value {
  list.fold(spine, val, fn(value, elimination) {
    case elimination {
      EDot(field) -> do_dot(value, field, s)
      EApp(arg) -> do_app(value, arg)
      EMatch(env, motive, cases) -> do_match(env, value, motive, cases)
    }
  })
}

pub fn ctr_solve_params(
  sub: Subst,
  ctr: CtrDef,
  tag: String,
  s: Span,
) -> #(Env, List(Error)) {
  list.index_fold(ctr.params, #([], []), fn(acc, _, i) {
    let #(acc_params, acc_errors) = acc
    case list.key_find(sub, i) {
      Ok(val) -> #(list.append(acc_params, [val]), acc_errors)
      Error(Nil) -> #(
        list.append(acc_params, [VNeut(HHole(i), [])]),
        list.append(acc_errors, [CtrUnsolvedParam(tag, ctr, i, s)]),
      )
    }
  })
}

pub fn list_get(xs: List(a), i: Int) -> Option(a) {
  case xs {
    [] -> None
    [x, ..] if i == 0 -> Some(x)
    [_, ..xs] -> list_get(xs, i - 1)
  }
}

pub fn range(start: Int, stop: Int, step: Int) -> List(Int) {
  case start < stop {
    True -> [start, ..range(start + step, stop, step)]
    False -> []
  }
}

fn show_msg(s: Span, msg: String) -> String {
  show_span(s) <> " " <> msg
}

fn show_span(s: Span) -> String {
  "["
  <> s.file
  <> ":"
  <> int.to_string(s.row)
  <> ":"
  <> int.to_string(s.col)
  <> "]"
}

fn ctx2env(ctx: Context) -> Env {
  list.map(ctx, fn(kv) { kv.1.0 })
}
