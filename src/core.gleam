import gleam/dict
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
  Match(arg: Term, cases: List(Case))
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
  EMatch(env: Env, cases: List(Case))
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
  TypeAnnotationNeeded(term: Term)
  NotAFunction(fun: Term, fun_ty: Value)
  VarUndefined(index: Int, span: Span)
  CtrUndefined(tag: String, span: Span)
  CtrUnsolvedParam(tag: String, ctr: CtrDef, id: Int, span: Span)
  RcdMissingFields(name: List(String), span: Span)
  DotFieldNotFound(name: String, fields: List(#(String, Value)), span: Span)
  DotOnNonCtr(value: Value, name: String, span: Span)
  MatchEmpty(arg: Term, span: Span)

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
    Match(arg, cases) -> {
      let arg_val = eval(env, arg)
      do_match(env, arg_val, cases)
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

pub fn do_match(env: Env, arg: Value, cases: List(Case)) -> Value {
  case arg {
    VNeut(head, spine) -> VNeut(head, list.append(spine, [EMatch(env, cases)]))
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
    EMatch(env, cases) -> Term(Match(head, cases), s)
  }
}

fn quote_head(lvl: Int, head: Head, s: Span) -> Term {
  case head {
    HVar(l) -> Term(Var(lvl - l - 1), s)
    HHole(id) -> Term(Hole(id), s)
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
        Ok(v) -> unify(State(..s, hole: s.hole + 1), v, v2, s1, s2)
        Error(Nil) -> Ok(State(..s, sub: [#(id, v2), ..s.sub]))
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
    _, _ -> Error(TODO("Spine mismatch", s1))
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
    _, _ -> Error(TODO("Arity mismatch", s1))
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
      let val = do_dot(arg_val, name, term.span)
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
      let t1 = force(s.sub, t1_hole, term.span)
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
    Match(_, _) -> {
      let #(hole, s) = new_hole(s)
      let #(result, s) = check(s, term, hole, term.span)
      let result_ty = force(s.sub, hole, term.span)
      #(result, result_ty, s)
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
) -> State {
  case pattern {
    PAny -> s
    PAs(PAny, name) -> def_var(s, name, ret_ty).1
    PAs(p, name) -> {
      let #(_, s) = def_var(s, name, ret_ty)
      bind_pattern(s, p, ret_ty, pat_span, ret_span)
    }
    PTyp(k) -> check(s, Term(Typ(k), pat_span), ret_ty, ret_span).1
    PLit(k) -> check(s, Term(Lit(k), pat_span), ret_ty, ret_span).1
    PLitT(k) -> check(s, Term(LitT(k), pat_span), ret_ty, ret_span).1
    PCtr(tag, parg) -> {
      case list.key_find(s.tenv, tag) {
        Error(Nil) -> with_err(s, CtrUndefined(tag, pat_span))
        Ok(ctr) -> {
          let #(params, _, ctr_ret_ty, s) = check_ctr_def(s, ctr)
          let #(_, s) =
            check_type(s, ctr_ret_ty, ret_ty, ctr.ret_ty.span, ret_span)
          let #(params, s) = ctr_solve_params(s, ctr, params, tag, pat_span)
          let env = list.append(params, get_env(s))
          let ctr_arg_ty = eval(env, ctr.arg_ty)
          bind_pattern(s, parg, ctr_arg_ty, pat_span, ctr.arg_ty.span)
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
          list.fold(pfields, s, fn(s, kv) {
            let #(name, p) = kv
            let #(ty, s) = case list.key_find(vfields, name) {
              Error(Nil) -> new_hole(s)
              Ok(ty) -> #(ty, s)
            }
            bind_pattern(s, p, ty, pat_span, ret_span)
          })
        }
        _ -> with_err(s, PatternMismatch(pattern, ret_ty, pat_span, ret_span))
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
    Match(arg, cases), _ -> {
      let env = get_env(s)
      let #(arg_val, arg_ty, s) = infer(s, arg)
      let s = case cases {
        [] -> with_err(s, MatchEmpty(arg, term.span))
        _ -> s
      }
      let s =
        list.fold(cases, s, fn(s, c) {
          let s = bind_pattern(s, c.pattern, arg_ty, c.span, arg.span)
          check(s, c.body, expected_ty, ty_span).1
        })
      let match_val = do_match(env, arg_val, cases)
      #(match_val, s)
    }
    _, _ -> {
      let #(value, inferred_ty, s) = infer(s, term)
      case unify(s, inferred_ty, expected_ty, term.span, ty_span) {
        Ok(s) -> #(force(s.sub, value, term.span), s)
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
    Ok(s) -> #(force(s.sub, t1, t1_span), s)
    Error(e) -> #(t1, with_err(s, e))
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
      EMatch(env, cases) -> do_match(env, value, cases)
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
