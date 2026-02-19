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
  Ctr(tag: String, args: List(Term))
  Ann(term: Term, typ: Term)
  Lam(name: String, body: Term)
  Pi(name: String, in: Term, out: Term)
  App(fun: Term, arg: Term)
  Match(arg: Term, cases: List(Case))
  Err(err: Error)
}

pub type Value {
  VTyp(level: Int)
  VLit(value: Literal)
  VLitT(typ: LiteralType)
  VNeut(head: Head, args: List(Value))
  VCtr(tag: String, args: List(Value))
  VLam(name: String, env: Env, body: Term)
  VPi(name: String, env: Env, in_ty: Value, out_ty: Term)
  VErr(err: Error)
}

pub type Pattern {
  PAny
  PVar(name: String)
  PCtr(tag: String, args: List(Pattern))
}

pub type Head {
  // De Bruijn Level (Absolute)
  HVar(level: Int)
  HMeta(id: Int)
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
  CtrDef(tag: String, num_params: Int, args: List(Term), ret_ty: Term)
}

pub type TypeEnv =
  List(#(String, CtrDef))

pub type Env =
  List(Value)

pub type Context =
  List(#(String, Value))

pub type Subst =
  List(#(Int, Value))

pub type Error {
  // Type errors
  TypeMismatch(expected: Value, got: Value, span: Span)
  TypeAnnotationNeeded(term: Term)
  NotAFunction(got: Value, span: Span)
  UnboundVar(index: Int, span: Span)

  // Exhaustiveness errors
  NonExhaustiveMatch(missing: List(Pattern), span: Span)
  RedundantMatch(pattern: Pattern, span: Span)

  // Runtime errors
  TODO(message: String, span: Span)
  MatchUnhandledCase(value: Value, span: Span)
}

pub fn app(fun: Term, args: List(Term), s: Span) -> Term {
  list.fold(args, fun, fn(fun, arg) { Term(App(fun, arg), s) })
}

pub fn eval(env: Env, term: Term) -> Value {
  case term.data {
    Typ(k) -> VTyp(k)
    Lit(k) -> VLit(k)
    LitT(k) -> VLitT(k)
    Var(i) ->
      case list_get(env, i) {
        Some(value) -> value
        None -> VErr(UnboundVar(i, term.span))
      }
    Ctr(tag, args) -> VCtr(tag, list.map(args, eval(env, _)))
    Ann(term, _) -> eval(env, term)
    Lam(name, body) -> VLam(name, env, body)
    Pi(name, in, out) -> VPi(name, env, eval(env, in), out)
    App(fun, arg) -> {
      let fun_val = eval(env, fun)
      let arg_val = eval(env, arg)
      case eval_apply(fun_val, arg_val) {
        Some(result) -> result
        None -> VErr(NotAFunction(fun_val, fun.span))
      }
    }
    Match(arg, cases) -> {
      let arg_val = eval(env, arg)
      case eval_match(env, arg_val, cases) {
        Some(result) -> result
        None -> VErr(MatchUnhandledCase(arg_val, arg.span))
      }
    }
    Err(e) -> VErr(e)
  }
}

fn eval_apply(fun: Value, arg: Value) -> Option(Value) {
  case fun {
    VLam(_, env, body) -> Some(eval([arg, ..env], body))
    VNeut(head, args) -> Some(VNeut(head, list.append(args, [arg])))
    VErr(e) -> Some(VErr(e))
    _ -> None
  }
}

fn eval_match(env: Env, arg: Value, cases: List(Case)) -> Option(Value) {
  case cases {
    [] -> None
    [c, ..cases] -> {
      case match_pattern(c.pattern, arg) {
        Ok(bindings) -> Some(eval(list.append(bindings, env), c.body))
        Error(Nil) -> eval_match(env, arg, cases)
      }
    }
  }
}

fn match_pattern(pattern: Pattern, value: Value) -> Result(Env, Nil) {
  case pattern, value {
    PAny, _ -> Ok([])
    PVar(_), _ -> Ok([value])
    PCtr(tag_p, args_p), VCtr(tag_v, args_v) if tag_p == tag_v ->
      match_pattern_list(args_p, args_v)
    PCtr(_, _), _ -> Error(Nil)
  }
}

pub fn match_pattern_list(
  ps: List(Pattern),
  vs: List(Value),
) -> Result(Env, Nil) {
  case ps, vs {
    [], [] -> Ok([])
    [p, ..ps], [v, ..vs] -> {
      use bindings_first <- result.try(match_pattern(p, v))
      use bindings_rest <- result.try(match_pattern_list(ps, vs))
      Ok(list.append(bindings_first, bindings_rest))
    }
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
    VCtr(tag, args) -> Term(Ctr(tag, list.map(args, quote(lvl, _, s))), s)
    VNeut(HVar(l), args_val) -> {
      let fun = Term(Var(lvl - l - 1), s)
      let args = list.map(args_val, quote(lvl, _, s))
      app(fun, args, s)
    }
    VNeut(HMeta(id), args_val) -> todo
    VLam(name, env, body) -> {
      let fresh = VNeut(HVar(lvl), [])
      let body_val = eval([fresh, ..env], body)
      let body_quote = quote(lvl + 1, body_val, body.span)
      Term(Lam(name, body_quote), s)
    }
    VPi(name, env, in_val, out_term) -> {
      let in_quote = quote(lvl, in_val, s)
      let fresh = VNeut(HVar(lvl + 1), [])
      let out_val = eval([fresh, ..env], out_term)
      let out_quote = quote(lvl + 1, out_val, out_term.span)
      Term(Pi(name, in_quote, out_quote), s)
    }
    VErr(e) -> Term(Err(e), s)
  }
}

pub fn unify(
  lvl: Int,
  sub: Subst,
  v1: Value,
  v2: Value,
  s: Span,
) -> Result(Subst, Error) {
  case v1, v2 {
    VTyp(k1), VTyp(k2) if k1 == k2 -> Ok(sub)
    VLit(k1), VLit(k2) if k1 == k2 -> Ok(sub)
    VLitT(k1), VLitT(k2) if k1 == k2 -> Ok(sub)
    VNeut(HMeta(id), []), _ ->
      case list.key_find(sub, id) {
        Ok(v) -> unify(lvl + 1, sub, v, v2, s)
        Error(Nil) -> Ok([#(id, v2), ..sub])
      }
    _, VNeut(HMeta(_), []) -> unify(lvl + 1, sub, v2, v1, s)
    VNeut(h1, args1), VNeut(h2, args2) if h1 == h2 ->
      unify_list(lvl, sub, args1, args2, s)
    VCtr(k1, args1), VCtr(k2, args2) if k1 == k2 ->
      unify_list(lvl, sub, args1, args2, s)
    VLam(_, env1, body1), VLam(_, env2, body2) -> {
      let fresh = VNeut(HVar(lvl), [])
      let a = eval([fresh, ..env1], body1)
      let b = eval([fresh, ..env2], body2)
      unify(lvl + 1, sub, a, b, s)
    }
    VPi(_, env1, in1, out1), VPi(_, env2, in2, out2) -> {
      use _ <- result.try(unify(lvl, sub, in1, in2, s))
      let fresh = VNeut(HVar(lvl), [])
      let a = eval([fresh, ..env1], out1)
      let b = eval([fresh, ..env2], out2)
      unify(lvl + 1, sub, a, b, s)
    }
    // On errors, succeed to prevent cascading noise
    VErr(_), _ -> Ok(sub)
    _, VErr(_) -> Ok(sub)
    _, _ -> Error(TypeMismatch(v1, v2, s))
  }
}

fn unify_list(
  lvl: Int,
  sub: Subst,
  l1: List(Value),
  l2: List(Value),
  s: Span,
) -> Result(Subst, Error) {
  case l1, l2 {
    [], [] -> Ok(sub)
    [x, ..xs], [y, ..ys] -> {
      use sub <- result.try(unify(lvl, sub, x, y, s))
      unify_list(lvl, sub, xs, ys, s)
    }
    _, _ -> Error(TODO("Arity mismatch", s))
  }
}

// // Checks if two values are equal.
// pub fn is_convertible(lvl: Int, v1: Value, v2: Value) -> Bool {
//   case v1, v2 {
//     VTyp(k1), VTyp(k2) -> k1 == k2
//     VLit(v1), VLit(v2) -> v1 == v2
//     VLitT(t1), VLitT(t2) -> t1 == t2
//     VNeut(HVar(l1), args1), VNeut(HVar(l2), args2) -> {
//       l1 == l2 && is_convertible_list(lvl, args1, args2)
//     }
//     VCtr(tag1, args1), VCtr(tag2, args2) -> {
//       tag1 == tag2 && is_convertible_list(lvl, args1, args2)
//     }
//     VLam(_, _, _), other -> {
//       let fresh = VNeut(HVar(lvl), [])
//       case eval_apply(v1, fresh), eval_apply(other, fresh) {
//         Some(b1), Some(b2) -> is_convertible(lvl + 1, b1, b2)
//         _, _ -> False
//       }
//     }
//     _, VLam(_, _, _) -> is_convertible(lvl, v2, v1)
//     VPi(_, env1, in1, out1), VPi(_, env2, in2, out2) -> {
//       // 1. Check Domains
//       let domain_ok = is_convertible(lvl, in1, in2)
//       // 2. Check Ranges, with fresh var
//       let fresh = VNeut(HVar(lvl), [])
//       let range1 = eval([fresh, ..env1], out1)
//       let range2 = eval([fresh, ..env2], out2)
//       let range_ok = is_convertible(lvl + 1, range1, range2)
//       domain_ok && range_ok
//     }
//     VErr(_), _ -> True
//     _, VErr(_) -> True
//     _, _ -> False
//   }
// }

// fn is_convertible_list(lvl: Int, l1: List(Value), l2: List(Value)) -> Bool {
//   case l1, l2 {
//     [], [] -> True
//     [x, ..xs], [y, ..ys] ->
//       is_convertible(lvl, x, y) && is_convertible_list(lvl, xs, ys)
//     _, _ -> False
//   }
// }

pub fn infer(
  lvl: Int,
  ctx: Context,
  env: Env,
  tenv: TypeEnv,
  term: Term,
) -> Value {
  case term.data {
    Typ(k) -> VTyp(k + 1)
    Lit(k) -> infer_lit(k)
    LitT(_) -> VTyp(0)
    Var(i) -> {
      case list_get(ctx, i) {
        Some(#(_, ty)) -> ty
        None -> VErr(UnboundVar(i, term.span))
      }
    }
    // Ctr(tag, args) -> VCtr(tag, list.map(args, infer(lvl, ctx, env, tenv, _)))
    Ctr(_, _) -> VErr(TypeAnnotationNeeded(term))
    Ann(term, ty) -> {
      // Ensure annotation is a type
      // TODO: check(lvl, ctx, ty, VTyp(0))
      let ty_val = eval(ctx_to_env(ctx), ty)
      check(lvl, ctx, env, tenv, term, ty_val)
    }
    Lam(_, _) -> VErr(TypeAnnotationNeeded(term))
    Pi(name, in, out) -> {
      check(lvl, ctx, env, tenv, in, VTyp(0))
      let fresh = VNeut(HVar(lvl), [])
      let new_ctx = [#(name, eval(env, in)), ..ctx]
      infer(lvl + 1, new_ctx, [fresh, ..env], tenv, out)
      VTyp(0)
    }
    App(fun, arg) -> {
      case infer(lvl, ctx, env, tenv, fun) {
        VPi(_, pi_env, in_ty, out_ty) -> {
          check(lvl, ctx, env, tenv, arg, in_ty)
          let arg_val = eval(env, arg)
          eval([arg_val, ..pi_env], out_ty)
        }
        VErr(e) -> VErr(e)
        fun_ty -> VErr(NotAFunction(fun_ty, term.span))
      }
    }
    Match(arg, cases) -> {
      let arg_ty = infer(lvl, ctx, env, tenv, arg)
      case cases {
        [] -> {
          // Empty matches are only valid for "Void" types
          // TODO: replace this with a more specific error.
          let err = Err(TODO("match without any cases", term.span))
          infer(lvl, ctx, env, tenv, Term(err, term.span))
        }
        [first, ..cases] -> {
          let #(lvl_f, ctx_f) = bind_pattern(lvl, ctx, first.pattern, arg_ty)
          let return_ty = infer(lvl_f, ctx_f, env, tenv, first.body)
          list.each(cases, fn(c) {
            let #(lvl_c, ctx_c) = bind_pattern(lvl, ctx, c.pattern, arg_ty)
            check(lvl_c, ctx_c, env, tenv, c.body, return_ty)
          })
          return_ty
        }
      }
    }
    Err(e) -> VErr(e)
  }
}

pub fn bind_pattern(
  lvl: Int,
  ctx: Context,
  pattern: Pattern,
  expected_ty: Value,
) -> #(Int, Context) {
  case pattern {
    PAny -> #(lvl, ctx)
    PVar(name) -> #(lvl + 1, [#(name, expected_ty), ..ctx])
    PCtr(tag, p_args) -> {
      // let sig = get_signature(tag)

      // // 2. Simple check: Is the tag valid for the expected type?
      // // (In a real impl, you'd check sig.parent_type == expected_ty)

      // // 3. Recursively bind arguments
      // // This assumes sig.args (Terms) are evaluated into Values
      // list.fold(list.zip(p_args, sig.args), #(lvl, ctx), fn(acc, pair) {
      //   let #(p, arg_tm) = pair
      //   let #(current_lvl, current_ctx) = acc
      //   let arg_ty = eval(ctx_to_env(current_ctx), arg_tm)
      //   bind_pattern(current_lvl, current_ctx, p, arg_ty)
      // })
      todo
    }
  }
}

pub fn infer_lit(lit: Literal) -> Value {
  case lit {
    I32(_) -> VLitT(I32T)
    I64(_) -> VLitT(I64T)
    U32(_) -> VLitT(U32T)
    U64(_) -> VLitT(U64T)
    F32(_) -> VLitT(F32T)
    F64(_) -> VLitT(F64T)
  }
}

pub fn check(
  lvl: Int,
  ctx: Context,
  env: Env,
  tenv: TypeEnv,
  term: Term,
  expected_ty: Value,
) -> Value {
  case term.data, expected_ty {
    Lam(name, body), VPi(_, pi_env, in, out) -> {
      let fresh = VNeut(HVar(lvl), [])
      let out_val = eval([fresh, ..pi_env], out)
      let new_ctx = [#(name, in), ..ctx]
      check(lvl + 1, new_ctx, [fresh, ..env], tenv, body, out_val)
    }
    Ctr(tag, args), _ ->
      case check_ctr(lvl, ctx, env, tenv, tag, args, expected_ty, term.span) {
        Ok(ty) -> ty
        Error(Nil) -> VErr(TODO("Unknown constructor", term.span))
      }
    // Holes are always valid types (but warn)
    Err(TODO(msg, s)), _ -> {
      io.print_error(
        "["
        <> s.file
        <> ":"
        <> int.to_string(s.row)
        <> ":"
        <> int.to_string(s.col)
        <> "] TODO: "
        <> msg,
      )
      expected_ty
    }
    _, _ -> {
      let inferred_ty = infer(lvl, ctx, env, tenv, term)
      case unify(lvl, [], inferred_ty, expected_ty, term.span) {
        Ok(sub) -> inferred_ty
        Error(e) -> VErr(e)
      }
    }
  }
}

fn check_ctr(
  lvl: Int,
  ctx: Context,
  env: Env,
  tenv: TypeEnv,
  tag: String,
  args: List(Term),
  expected_ty: Value,
  s: Span,
) -> Result(Value, Nil) {
  use ctr <- result.try(list.key_find(tenv, tag))
  let param_vals =
    list.range(0, ctr.num_params - 1)
    |> list.map(fn(i) { VNeut(HMeta(i), []) })
  let ctr_ret_ty = eval(list.append(param_vals, env), ctr.ret_ty)
  case unify(lvl, [], ctr_ret_ty, expected_ty, s) {
    Ok(sub) -> todo
    Error(e) -> Ok(VErr(e))
  }
}

// // --- 3. EXHAUSTIVENESS (The Safety Net) ---
// fn check_exhaustiveness(cases: List(Case), span: Span) -> Result(Nil, Error) {
//   // A "Matrix" is a list of rows, where each row is a list of Patterns
//   let patterns = list.map(cases, fn(c) { c.pattern })

//   case is_useful(patterns, PAny) {
//     True ->
//       // If the Wildcard is still "useful" after all user cases, 
//       // it means the user missed something.
//       // In a real implementation, 'witness' would be the missing constructor.
//       Error(NonExhaustiveMatch([PAny], span))
//     False -> Ok(Nil)
//   }
// }

// // The core "Is this pattern covered?" logic (Simplified)
// fn is_useful(matrix: List(Pattern), target: Pattern) -> Bool {
//   case matrix {
//     [] -> True
//     // Nothing covers the target, so it is useful
//     [row, ..rest] -> {
//       case covers(row, target) {
//         True ->
//           // Covered by a previous row -> Not useful
//           False
//         False -> is_useful(rest, target)
//       }
//     }
//   }
// }

// fn covers(p1: Pattern, p2: Pattern) -> Bool {
//   case p1, p2 {
//     PAny, _ -> True
//     PVar(_), _ -> True
//     PCtr(n1, _), PCtr(n2, _) -> n1 == n2
//     _, _ -> False
//   }
// }

// fn infer_case(lvl: Int, ctx: Context, c: Case, scrut_ty: Value) -> Value {
//   // 1. Unify pattern with scrutinee type to get new bindings
//   // 2. Add bindings to context
//   // 3. Infer body
//   // infer(lvl + 1, ctx, c.body)
//   // simplified
//   todo
// }

fn ctx_to_env(ctx: Context) -> Env {
  let len = list.length(ctx)
  list.index_map(ctx, fn(_, i) {
    // Map Index 'i' to Level 'len - 1 - i'
    VNeut(HVar(len - 1 - i), [])
  })
}

pub fn list_get(xs: List(a), i: Int) -> Option(a) {
  case xs {
    [] -> None
    [x, ..] if i == 0 -> Some(x)
    [_, ..xs] -> list_get(xs, i - 1)
  }
}
