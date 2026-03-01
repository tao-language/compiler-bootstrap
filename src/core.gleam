import gleam/dict
import gleam/int
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/result
import gleam/string

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

pub type State {
  State(
    hole: Int,
    var: Int,
    tenv: TypeEnv,
    ctx: Context,
    sub: Subst,
    errors: List(Error),
  )
}

pub type Error {
  // Type errors
  PatternMismatch(pattern: Pattern, expected_ty: Type, s1: Span, s2: Span)
  TypeMismatch(expected: Type, got: Type, span1: Span, span2: Span)
  InfiniteType(hole_id: Int, ty: Type, span1: Span, span2: Span)
  TypeAnnotationNeeded(term: Term)
  NotAFunction(fun: Term, fun_ty: Value)
  VarUndefined(index: Int, span: Span)
  CtrUndefined(tag: String, span: Span)
  CtrUnsolvedParam(tag: String, ctr: CtrDef, id: Int, span: Span)
  RcdMissingFields(name: List(String), span: Span)
  DotFieldNotFound(name: String, fields: List(#(String, Value)), span: Span)
  DotOnNonCtr(value: Value, name: String, span: Span)
  MatchEmpty(arg: Term, span: Span)

  // Runtime errors
  TODO(message: String)
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
    Dot(arg, name) -> do_dot(eval(env, arg), name)
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

fn do_dot(value: Value, name: String) -> Value {
  case value {
    VNeut(head, spine) -> VNeut(head, [EDot(name), ..spine])
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
    VNeut(head, spine) -> VNeut(head, [EApp(arg), ..spine])
    VLam(_, env, body) -> eval([arg, ..env], body)
    _ -> VErr
  }
}

pub fn do_match(env: Env, arg: Value, motive: Value, cases: List(Case)) -> Value {
  case arg {
    VNeut(head, spine) -> VNeut(head, [EMatch(env, motive, cases), ..spine])
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
    PAs(p, _), _ -> {
      use env <- result.try(do_match_pattern(p, value))
      Ok(list.append(env, [value]))
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
  list.fold_right(spine, head, fn(head, elim) { quote_elim(lvl, head, elim, s) })
}

fn quote_elim(lvl: Int, head: Term, elim: Elim, s: Span) -> Term {
  case elim {
    EDot(name) -> Term(Dot(head, name), s)
    EApp(arg) -> Term(App(head, quote(lvl, arg, s)), s)
    // TODO: Is it okay to discard this env?
    EMatch(_, motive, cases) ->
      Term(Match(head, quote(lvl, motive, s), cases), s)
  }
}

fn quote_head(lvl: Int, head: Head, s: Span) -> Term {
  case head {
    HVar(l) -> Term(Var(lvl - l - 1), s)
    HHole(id) -> Term(Hole(id), s)
  }
}

pub fn occurs(sub: Subst, id: Int, value: Value) -> Bool {
  case force(sub, value) {
    VTyp(_) | VLit(_) | VLitT(_) | VErr -> False
    VNeut(HHole(hole_id), spine) ->
      id == hole_id || list.any(spine, occurs_elim(sub, id, _))
    VNeut(_, spine) -> list.any(spine, occurs_elim(sub, id, _))
    VCtr(_, arg) -> occurs(sub, id, arg)
    VRcd(fields) -> list.any(fields, fn(kv) { occurs(sub, id, kv.1) })
    VLam(_, env, _) -> list.any(env, occurs(sub, id, _))
    VPi(_, env, in, _) ->
      occurs(sub, id, in) || list.any(env, occurs(sub, id, _))
  }
}

pub fn occurs_elim(sub: Subst, id: Int, elim: Elim) -> Bool {
  case elim {
    EDot(_) -> False
    EApp(arg) -> occurs(sub, id, arg)
    EMatch(env, motive, _) ->
      occurs(sub, id, motive) || list.any(env, occurs(sub, id, _))
  }
}

pub fn unify(
  s: State,
  v1: Value,
  v2: Value,
  s1: Span,
  s2: Span,
) -> Result(State, Error) {
  case v1, v2 {
    VTyp(k1), VTyp(k2) if k1 == k2 -> Ok(s)
    VLit(k1), VLit(k2) if k1 == k2 -> Ok(s)
    VLitT(k1), VLitT(k2) if k1 == k2 -> Ok(s)
    VNeut(HHole(id), []), _ ->
      case list.key_find(s.sub, id) {
        Ok(v) -> unify(s, v, v2, s1, s2)
        Error(Nil) ->
          case occurs(s.sub, id, v2) {
            True -> Error(InfiniteType(id, v2, s1, s2))
            False -> Ok(State(..s, sub: [#(id, v2), ..s.sub]))
          }
      }
    _, VNeut(HHole(_), []) -> unify(s, v2, v1, s2, s1)
    VNeut(h1, spine1), VNeut(h2, spine2) if h1 == h2 ->
      unify_elim_list(s, spine1, spine2, s1, s2)
    VCtr(k1, arg1), VCtr(k2, arg2) if k1 == k2 -> unify(s, arg1, arg2, s1, s2)
    VRcd(fields1), VRcd(fields2) -> unify_fields(s, fields1, fields2, s1, s2)
    VLam(_, env1, body1), VLam(_, env2, body2) -> {
      let #(fresh, s) = new_var(s)
      let a = eval([fresh, ..env1], body1)
      let b = eval([fresh, ..env2], body2)
      unify(s, a, b, s1, s2)
    }
    VPi(_, env1, in1, out1), VPi(_, env2, in2, out2) -> {
      use _ <- result.try(unify(s, in1, in2, s1, s2))
      let #(fresh, s) = new_var(s)
      let a = eval([fresh, ..env1], out1)
      let b = eval([fresh, ..env2], out2)
      unify(s, a, b, s1, s2)
    }
    VErr, _ -> Ok(s)
    _, VErr -> Ok(s)
    _, _ -> Error(TypeMismatch(v1, v2, s1, s2))
  }
}

fn unify_fields(
  s: State,
  args1: List(#(String, Value)),
  args2: List(#(String, Value)),
  s1: Span,
  s2: Span,
) -> Result(State, Error) {
  case args1 {
    [] ->
      case list.map(args2, fn(kv) { kv.0 }) {
        [] -> Ok(s)
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
          use s <- result.try(unify(s, v1, v2, s1, s2))
          unify_fields(s, args1, args2, s1, s2)
        }
      }
  }
}

fn unify_elim(
  s: State,
  e1: Elim,
  e2: Elim,
  s1: Span,
  s2: Span,
) -> Result(State, Error) {
  case e1, e2 {
    EDot(n1), EDot(n2) if n1 == n2 -> Ok(s)
    EApp(a1), EApp(a2) -> unify(s, a1, a2, s1, s2)
    _, _ -> Error(TODO("Spine mismatch"))
  }
}

fn unify_elim_list(
  s: State,
  l1: List(Elim),
  l2: List(Elim),
  s1: Span,
  s2: Span,
) -> Result(State, Error) {
  case l1, l2 {
    [], [] -> Ok(s)
    [e1, ..xs], [e2, ..ys] -> {
      use s <- result.try(unify_elim(s, e1, e2, s1, s2))
      unify_elim_list(s, xs, ys, s1, s2)
    }
    _, _ -> Error(TODO("ArityMismatch"))
  }
}

pub fn with_err(s: State, err: Error) -> State {
  State(..s, errors: list.append(s.errors, [err]))
}

pub fn infer(s: State, term: Term) -> #(Value, Type, State) {
  case term.data {
    Typ(k) -> #(VTyp(k), VTyp(k + 1), s)
    Lit(k) -> #(VLit(k), typeof_lit(k), s)
    LitT(k) -> #(VLitT(k), VTyp(0), s)
    Var(i) -> {
      case list_get(s.ctx, i) {
        Some(#(_, #(val, ty))) -> #(val, ty, s)
        None -> #(VErr, VErr, with_err(s, VarUndefined(i, term.span)))
      }
    }
    Hole(id) -> {
      let #(ty, s) = new_hole(s)
      #(VNeut(HHole(id), []), ty, s)
    }
    Ctr(tag, arg) -> {
      case list.key_find(s.tenv, tag) {
        Error(Nil) -> #(VErr, VErr, with_err(s, CtrUndefined(tag, term.span)))
        Ok(ctr) -> {
          let #(params, ctr_arg_ty, _, s) = check_ctr_def(s, ctr)
          let #(_, arg_ty, s) = infer(s, arg)
          let #(_, s) =
            check_type(s, arg_ty, ctr_arg_ty, arg.span, ctr.arg_ty.span)
          let #(params, s) = ctr_solve_params(s, ctr, params, tag, term.span)
          let env = list.append(params, get_env(s))
          #(VCtr(tag, eval(env, arg)), eval(env, ctr.ret_ty), s)
        }
      }
    }
    Rcd(fields) -> {
      let #(fields_val, fields_ty, s) = infer_fields(s, fields)
      #(VRcd(fields_val), VRcd(fields_ty), s)
    }
    Dot(arg, name) -> {
      let #(arg_val, arg_ty, s) = infer(s, arg)
      let val = do_dot(arg_val, name)
      case arg_ty {
        VRcd(fields) ->
          case list.key_find(fields, name) {
            Ok(ty) -> #(val, ty, s)
            Error(Nil) -> {
              let s = with_err(s, DotFieldNotFound(name, fields, arg.span))
              #(val, VErr, s)
            }
          }
        _ -> #(val, VErr, with_err(s, DotOnNonCtr(arg_ty, name, arg.span)))
      }
    }
    Ann(term, term_ty) -> {
      let #(ty_val, _, s) = infer(s, term_ty)
      let #(val, s) = check(s, term, ty_val, term_ty.span)
      #(val, ty_val, s)
    }
    Lam(name, body) -> {
      let env = get_env(s)
      let #(t1_hole, s) = new_hole(s)
      let #(_, s) = def_var(s, name, t1_hole)
      let #(_, t2_val, s) = infer(s, body)
      let t1 = force(s.sub, t1_hole)
      let t2 = quote(list.length(env), t2_val, body.span)
      #(VLam(name, env, body), VPi(name, env, t1, t2), s)
    }
    Pi(name, in, out) -> {
      let env = get_env(s)
      let #(in_val, _, s) = infer(s, in)
      let #(_, s) = def_var(s, name, in_val)
      let #(_, _, s) = infer(s, out)
      #(VPi(name, env, in_val, out), VTyp(0), s)
    }
    App(fun, arg) -> {
      let #(fun_val, fun_ty, s) = infer(s, fun)
      case fun_ty {
        VPi(_, pi_env, in, out) -> {
          let #(arg_val, s) = check(s, arg, in, fun.span)
          let out_val = eval([arg_val, ..pi_env], out)
          #(do_app(fun_val, arg_val), out_val, s)
        }
        _ -> #(VErr, VErr, with_err(s, NotAFunction(fun, fun_ty)))
      }
    }
    Match(arg, motive, cases) -> {
      let env = get_env(s)
      let #(arg_val, arg_ty, s) = infer(s, arg)
      let motive_ty = VPi("_", env, arg_ty, Term(Typ(0), arg.span))
      let #(motive_val, s) = check(s, motive, motive_ty, motive.span)
      let s = case cases {
        [] -> with_err(s, MatchEmpty(arg, term.span))
        _ -> s
      }
      let s =
        list.fold(cases, s, fn(s, c) {
          let #(pat_val, branch_s) =
            bind_pattern(s, c.pattern, arg_ty, c.span, arg.span)
          let branch_ty = do_app(motive_val, pat_val)
          let #(_, branch_s) = check(branch_s, c.body, branch_ty, c.span)
          State(..branch_s, var: s.var, ctx: s.ctx)
        })
      let match_val = do_match(env, arg_val, motive_val, cases)
      let result_ty = do_app(motive_val, arg_val)
      #(match_val, result_ty, s)
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
  s: State,
  fields: List(#(String, Term)),
) -> #(List(#(String, Value)), List(#(String, Type)), State) {
  case fields {
    [] -> #([], [], s)
    [#(name, term), ..fields] -> {
      let #(val, ty, s) = infer(s, term)
      let #(fields_val, fields_ty, s) = infer_fields(s, fields)
      #([#(name, val), ..fields_val], [#(name, ty), ..fields_ty], s)
    }
  }
}

pub fn bind_pattern(
  s: State,
  pattern: Pattern,
  ret_ty: Value,
  pat_span: Span,
  ret_span: Span,
) -> #(Value, State) {
  case pattern {
    PAny -> new_hole(s)
    PAs(PAny, name) -> def_var(s, name, ret_ty)
    PAs(p, name) -> {
      let #(_, s) = def_var(s, name, ret_ty)
      bind_pattern(s, p, ret_ty, pat_span, ret_span)
    }
    PTyp(k) -> check(s, Term(Typ(k), pat_span), ret_ty, ret_span)
    PLit(k) -> check(s, Term(Lit(k), pat_span), ret_ty, ret_span)
    PLitT(k) -> check(s, Term(LitT(k), pat_span), ret_ty, ret_span)
    PCtr(tag, parg) -> {
      case list.key_find(s.tenv, tag) {
        Error(Nil) -> #(VErr, with_err(s, CtrUndefined(tag, pat_span)))
        Ok(ctr) -> {
          let #(params, _, ctr_ret_ty, s) = check_ctr_def(s, ctr)
          let #(_, s) =
            check_type(s, ctr_ret_ty, ret_ty, ctr.ret_ty.span, ret_span)
          let #(params, s) = ctr_solve_params(s, ctr, params, tag, pat_span)
          let env = list.append(params, get_env(s))
          let ctr_arg_ty = eval(env, ctr.arg_ty)
          let #(varg, s) =
            bind_pattern(s, parg, ctr_arg_ty, pat_span, ctr.arg_ty.span)
          #(VCtr(tag, varg), s)
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
          let s = case missing {
            [] -> s
            _ -> with_err(s, RcdMissingFields(missing, ret_span))
          }
          let #(fields, s) =
            list.fold_right(pfields, #([], s), fn(acc, kv) {
              let #(fields, s) = acc
              let #(name, p) = kv
              let #(ty, s) = case list.key_find(vfields, name) {
                Error(Nil) -> new_hole(s)
                Ok(ty) -> #(ty, s)
              }
              let #(v, s) = bind_pattern(s, p, ty, pat_span, ret_span)
              #([#(name, v), ..fields], s)
            })
          #(VRcd(fields), s)
        }
        _ -> #(
          VErr,
          with_err(s, PatternMismatch(pattern, ret_ty, pat_span, ret_span)),
        )
      }
  }
}

pub fn check(
  s: State,
  term: Term,
  expected_ty: Value,
  ty_span: Span,
) -> #(Value, State) {
  case term.data, expected_ty {
    Lam(name, body), VPi(_, pi_env, in, out) -> {
      let env = get_env(s)
      let #(fresh, s) = def_var(s, name, in)
      let out_val = eval([fresh, ..pi_env], out)
      let #(_, s) = check(s, body, out_val, ty_span)
      #(VLam(name, env, body), s)
    }
    Hole(id), _ -> {
      // TODO: add warning
      #(VNeut(HHole(id), []), s)
    }
    Ctr(tag, arg), _ -> check_ctr(s, tag, arg, expected_ty, ty_span, term.span)
    _, _ -> {
      let #(value, inferred_ty, s) = infer(s, term)
      case unify(s, inferred_ty, expected_ty, term.span, ty_span) {
        Ok(s) -> #(force(s.sub, value), s)
        Error(e) -> #(VErr, with_err(s, e))
      }
    }
  }
}

fn check_ctr(
  s: State,
  tag: String,
  arg: Term,
  ret_ty: Value,
  ret_span: Span,
  term_span: Span,
) -> #(Value, State) {
  case list.key_find(s.tenv, tag) {
    Error(Nil) -> #(VErr, with_err(s, CtrUndefined(tag, ret_span)))
    Ok(ctr) -> {
      let #(params, _, ctr_ret_ty, s) = check_ctr_def(s, ctr)
      let #(_, s) = check_type(s, ctr_ret_ty, ret_ty, ctr.ret_ty.span, ret_span)
      let #(params, s) = ctr_solve_params(s, ctr, params, tag, term_span)
      let env = list.append(params, get_env(s))
      let ctr_arg_ty = eval(env, ctr.arg_ty)
      let #(arg_val, s) = check(s, arg, ctr_arg_ty, ctr.arg_ty.span)
      #(VCtr(tag, arg_val), s)
    }
  }
}

fn check_ctr_def(s: State, ctr: CtrDef) -> #(List(Int), Value, Value, State) {
  let #(params, s) =
    list.fold(ctr.params, #([], s), fn(acc, name) {
      let #(params, s) = acc
      let id = s.hole
      let #(hole, s) = new_hole(s)
      let params = [id, ..params]
      let s = State(..s, ctx: [#(name, #(hole, VTyp(0))), ..s.ctx])
      #(params, s)
    })
  let #(arg_ty, _, s) = infer(s, ctr.arg_ty)
  let #(ret_ty, _, s) = infer(s, ctr.ret_ty)
  #(params, arg_ty, ret_ty, s)
}

pub fn check_type(
  s: State,
  t1: Value,
  t2: Value,
  t1_span: Span,
  t2_span: Span,
) -> #(Value, State) {
  case unify(s, t1, t2, t1_span, t2_span) {
    Ok(s) -> #(force(s.sub, t1), s)
    Error(e) -> #(t1, with_err(s, e))
  }
}

pub fn force(sub: Subst, value: Value) -> Value {
  case value {
    VNeut(HHole(id), spine) ->
      case list.key_find(sub, id) {
        Ok(v) -> {
          let forced_val = apply_spine(v, spine)
          force(sub, forced_val)
        }
        Error(Nil) -> value
      }
    _ -> value
  }
}

fn apply_spine(value: Value, spine: List(Elim)) -> Value {
  list.fold(spine, value, fn(value, elim) {
    case elim {
      EDot(field) -> do_dot(value, field)
      EApp(arg) -> do_app(value, arg)
      EMatch(env, motive, cases) -> do_match(env, value, motive, cases)
    }
  })
}

pub fn ctr_solve_params(
  s: State,
  ctr: CtrDef,
  params: List(Int),
  tag: String,
  span: Span,
) -> #(Env, State) {
  list.fold(params, #([], s), fn(acc, id) {
    let #(acc_params, s) = acc
    case list.key_find(s.sub, id) {
      Ok(val) -> #(list.append(acc_params, [val]), s)
      Error(Nil) -> #(
        list.append(acc_params, [VNeut(HHole(id), [])]),
        with_err(s, CtrUnsolvedParam(tag, ctr, id, span)),
      )
    }
  })
}

// -- Exhaustiveness checks -- \\
// http://moscova.inria.fr/~maranget/papers/warn/index.html

pub type Diagnostic {
  RedundantBranch(Span)
  NonExhaustiveMatch(Span, Pattern)
}

// 1. --- Pattern Abstraction --- \\
// We decouple the "Shape" of a pattern from its recursive arguments.
// This single abstraction replaces all the specialized matrix functions.

pub type PHead {
  HAny
  HCtr(String)
  HLit(Literal)
  HLitT(LiteralType)
  HTyp(Int)
  HRcd(List(String))
}

fn expand_pattern(p: Pattern) -> #(PHead, List(Pattern)) {
  case p {
    PAs(inner, _) -> expand_pattern(inner)
    PAny -> #(HAny, [])
    PLit(v) -> #(HLit(v), [])
    PLitT(t) -> #(HLitT(t), [])
    PTyp(l) -> #(HTyp(l), [])
    PCtr(name, arg) -> #(HCtr(name), [arg])
    PRcd(fields) -> {
      // Sort to ensure robust structural equality regardless of defined order
      let sorted = list.sort(fields, fn(a, b) { string.compare(a.0, b.0) })
      let keys = list.map(sorted, fn(f) { f.0 })
      let vals = list.map(sorted, fn(f) { f.1 })
      #(HRcd(keys), vals)
    }
  }
}

fn head_arity(head: PHead) -> Int {
  case head {
    HAny | HLit(_) | HLitT(_) | HTyp(_) -> 0
    HCtr(_) -> 1
    HRcd(keys) -> list.length(keys)
  }
}

fn build_pattern(head: PHead, args: List(Pattern)) -> Pattern {
  case head, args {
    HAny, _ -> PAny
    HLit(v), [] -> PLit(v)
    HLitT(t), [] -> PLitT(t)
    HTyp(l), [] -> PTyp(l)
    HCtr(name), [arg] -> PCtr(name, arg)
    HRcd(keys), _ -> PRcd(list.zip(keys, args))
    _, _ -> PAny
  }
}

// 2. --- Matrix Operations --- \\

// Replaces all specialize_matrix_* functions. Extracts rows that match the target_head.
fn specialize(
  matrix: List(List(Pattern)),
  target_head: PHead,
) -> List(List(Pattern)) {
  list.filter_map(matrix, fn(row) {
    case row {
      [] -> Error(Nil)
      [first, ..rest] -> {
        let #(head, args) = expand_pattern(first)
        case head {
          _ if head == target_head -> Ok(list.append(args, rest))
          HAny -> {
            // Wildcards match everything. Replace with N wildcards.
            let wildcards = list.repeat(PAny, head_arity(target_head))
            Ok(list.append(wildcards, rest))
          }
          _ -> Error(Nil)
        }
      }
    }
  })
}

// Extracts rows that start with a wildcard (used when evaluating a wildcard pattern).
fn default_matrix(matrix: List(List(Pattern))) -> List(List(Pattern)) {
  list.filter_map(matrix, fn(row) {
    case row {
      [first, ..rest] -> {
        case expand_pattern(first).0 {
          HAny -> Ok(rest)
          _ -> Error(Nil)
        }
      }
      [] -> Error(Nil)
    }
  })
}

// 3. --- Signature Completeness --- \\

pub type Completeness {
  Complete
  Incomplete(List(PHead))
  Unknown
}

// 1. --- Type Environment Helpers --- \\

// Pseudo-definition of what we need to extract from your State
// You will replace these with your actual TEnv lookup logic.
fn get_ctr_return_type(state: State, ctr_name: String) -> Result(Term, Nil) {
  // e.g., dict.get(state.tenv, ctr_name) |> result.map(fn(def) { def.return_type })
  Error(Nil)
}

// If you have generics/type variables, simple equality (==) is not enough.
// You must use your unifier to check if the constructor's return type 
// can unify with the target type we are matching on.
fn types_are_compatible(state: State, a: Term, b: Term) -> Bool {
  // e.g., unify(state, a, b) |> result.is_ok
  a == b
}

// 2. --- Signature Checking --- \\

fn check_signature(state: State, heads: List(PHead)) -> Completeness {
  case heads {
    [] | [HLit(_), ..] | [HLitT(_), ..] | [HTyp(_), ..] -> Unknown
    [HRcd(_), ..] -> Complete

    // Records always have exactly 1 shape
    [HCtr(first_name), ..] -> {
      // Step 1: Discover the target type of this pattern match 
      // by looking up the first constructor the user provided.
      case get_ctr_return_type(state, first_name) {
        Error(_) -> Unknown
        // Safety fallback if Ctr is missing from TEnv
        Ok(target_type) -> {
          // Step 2: Scan the ENTIRE environment for valid constructors.
          // Any constructor that returns a compatible type belongs to this signature.
          let all_possible_ctrs =
            list.fold(state.tenv, [], fn(acc, ctr) {
              let #(ctr_name, ctr_def) = ctr
              case types_are_compatible(state, ctr_def.ret_ty, target_type) {
                True -> [ctr_name, ..acc]
                False -> acc
              }
            })

          // Step 3: Extract the names of the constructors the user actually matched on.
          let known_names =
            list.filter_map(heads, fn(h) {
              case h {
                HCtr(name) -> Ok(name)
                _ -> Error(Nil)
              }
            })

          // Step 4: Find the difference.
          // If all_possible_ctrs is ["A", "B", "C"] and known_names is ["A", "B"], 
          // missing_ctrs will be ["C"].
          let missing_ctrs =
            list.filter(all_possible_ctrs, fn(c) {
              let is_known = list.contains(known_names, c)
              !is_known
              // Keep it if it is NOT known
            })

          case missing_ctrs {
            [] -> Complete
            _ -> {
              // We found specific missing constructors! 
              // Map them back to HCtr heads so the witness generator can use them.
              let missing_heads = list.map(missing_ctrs, HCtr)
              Incomplete(missing_heads)
            }
          }
        }
      }
    }

    _ -> Unknown
  }
}

fn collect_first_heads(matrix: List(List(Pattern))) -> List(PHead) {
  list.filter_map(matrix, fn(row) {
    case row {
      [first, ..] -> {
        case expand_pattern(first).0 {
          HAny -> Error(Nil)
          h -> Ok(h)
        }
      }
      [] -> Error(Nil)
    }
  })
  |> list.unique
}

// 4. --- The Core Engine --- \\

// Unified pass: returns `Ok(WitnessArgs)` if the vector covers new ground, `Error` if redundant.
fn is_useful(
  state: State,
  matrix: List(List(Pattern)),
  vector: List(Pattern),
) -> Result(List(Pattern), Nil) {
  case matrix, vector {
    [], [] -> Ok([])
    // Useful!
    _, [] -> Error(Nil)

    // Redundant
    _, [first, ..rest] -> {
      let #(target_head, target_args) = expand_pattern(first)

      case target_head {
        HAny -> {
          let present_heads = collect_first_heads(matrix)
          case check_signature(state, present_heads) {
            Complete -> {
              // Signature is complete. The wildcard is useful if it is useful 
              // for AT LEAST ONE of the known constructors.
              find_useful(state, matrix, present_heads, rest)
            }
            Incomplete([missing_head, ..]) -> {
              // We know exactly what constructor was forgotten! Generate a precise witness.
              let wildcards = list.repeat(PAny, head_arity(missing_head))
              case is_useful(state, [], list.append(wildcards, rest)) {
                Ok(w) -> {
                  let w_args = list.take(w, head_arity(missing_head))
                  let w_rest = list.drop(w, head_arity(missing_head))
                  Ok([build_pattern(missing_head, w_args), ..w_rest])
                }
                Error(Nil) -> Error(Nil)
              }
            }
            _ -> {
              // Infinite space or unknown. Wildcard is useful if default matrix is useful.
              case is_useful(state, default_matrix(matrix), rest) {
                Ok(w) -> Ok([PAny, ..w])
                Error(Nil) -> Error(Nil)
              }
            }
          }
        }

        _ -> {
          // Checking a concrete pattern (Ctr, Lit, Rcd, Typ)
          let spec_m = specialize(matrix, target_head)
          case is_useful(state, spec_m, list.append(target_args, rest)) {
            Ok(w) -> {
              let arity = list.length(target_args)
              let w_args = list.take(w, arity)
              let w_rest = list.drop(w, arity)
              Ok([build_pattern(target_head, w_args), ..w_rest])
            }
            Error(Nil) -> Error(Nil)
          }
        }
      }
    }
  }
}

// Helper to iterate over heads when the signature is complete
fn find_useful(
  state: State,
  matrix: List(List(Pattern)),
  heads: List(PHead),
  rest: List(Pattern),
) -> Result(List(Pattern), Nil) {
  case heads {
    [] -> Error(Nil)
    [head, ..tail] -> {
      let wildcards = list.repeat(PAny, head_arity(head))
      case
        is_useful(state, specialize(matrix, head), list.append(wildcards, rest))
      {
        Ok(w) -> {
          let w_args = list.take(w, head_arity(head))
          let w_rest = list.drop(w, head_arity(head))
          Ok([build_pattern(head, w_args), ..w_rest])
        }
        Error(Nil) -> find_useful(state, matrix, tail, rest)
      }
    }
  }
}

// 5. --- Public Entry --- \\

pub fn check_exhaustiveness(
  state: State,
  cases: List(Case),
  match_span: Span,
) -> List(Diagnostic) {
  // 1. Fold sequentially to find Redundant Branches
  let #(rev_matrix, diagnostics) =
    list.fold(cases, #([], []), fn(acc, case_) {
      let Case(pat, _, span) = case_
      let #(matrix, diags) = acc

      // We must reverse because `fold` stacks the newest items on top,
      // but Maranget expects the highest-priority patterns first.
      case is_useful(state, list.reverse(matrix), [pat]) {
        Ok(_) -> #([[pat], ..matrix], diags)
        Error(Nil) -> #(matrix, [RedundantBranch(span), ..diags])
      }
    })

  let matrix = list.reverse(rev_matrix)

  // 2. Check Exhaustiveness using a Wildcard
  case is_useful(state, matrix, [PAny]) {
    Ok([witness]) -> [NonExhaustiveMatch(match_span, witness), ..diagnostics]
    _ -> diagnostics
  }
}

// -- Helper functions -- \\

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

pub fn show_msg(s: Span, msg: String) -> String {
  show_span(s) <> " " <> msg
}

pub fn show_span(s: Span) -> String {
  "["
  <> s.file
  <> ":"
  <> int.to_string(s.row)
  <> ":"
  <> int.to_string(s.col)
  <> "]"
}

fn get_env(s: State) -> Env {
  list.map(s.ctx, fn(kv) { kv.1.0 })
}

fn new_var(s: State) -> #(Value, State) {
  let var = VNeut(HVar(s.var), [])
  #(var, State(..s, var: s.var + 1))
}

fn def_var(s: State, name: String, ty: Type) -> #(Value, State) {
  let name = case name {
    "" -> "$" <> int.to_string(s.var)
    _ -> name
  }
  let #(var, s) = new_var(s)
  #(var, State(..s, ctx: [#(name, #(var, ty)), ..s.ctx]))
}

fn new_hole(s: State) -> #(Value, State) {
  let hole = VNeut(HHole(s.hole), [])
  #(hole, State(..s, hole: s.hole + 1))
}
