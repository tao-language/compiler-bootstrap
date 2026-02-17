import gleam/int
import gleam/io
import gleam/list
import gleam/option.{type Option, None, Some}

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
  Pi(name: String, in_ty: Term, out_ty: Term)
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

pub type Env =
  List(Value)

pub type Context =
  List(#(String, Value))

pub type CtrSignature {
  CtrSignature(
    name: String,
    parent: String,
    params: List(String),
    args: List(Term),
  )
}

pub type Error {
  // Type errors
  TypeMismatch(expected: Value, got: Value, span: Span, context: Option(String))
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
    Typ(l) -> VTyp(l)
    Lit(v) -> VLit(v)
    LitT(t) -> VLitT(t)
    Var(i) ->
      case list_get(env, i) {
        Some(value) -> value
        None -> VErr(UnboundVar(i, term.span))
      }
    Ctr(tag, args) -> VCtr(tag, list.map(args, fn(arg) { eval(env, arg) }))
    Ann(term, _) -> eval(env, term)
    Lam(name, body) -> VLam(name, env, body)
    Pi(name, in_ty, out_ty) -> VPi(name, env, eval(env, in_ty), out_ty)
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

pub fn eval_apply(fun: Value, arg: Value) -> Option(Value) {
  case fun {
    VLam(_, env, body) -> Some(eval([arg, ..env], body))
    VNeut(head, args) -> Some(VNeut(head, list.append(args, [arg])))
    _ -> None
  }
}

pub fn eval_match(env: Env, arg: Value, cases: List(Case)) -> Option(Value) {
  case cases {
    [] -> None
    [head, ..cases] -> {
      case matches(head.pattern, arg) {
        Some(bindings) -> Some(eval(list.append(bindings, env), head.body))
        None -> eval_match(env, arg, cases)
      }
    }
  }
}

// Returns bindings (in reverse order) if match succeeds
fn matches(pattern: Pattern, value: Value) -> Option(List(Value)) {
  case pattern {
    PAny -> Some([])
    PVar(_) -> Some([value])
    PCtr(tag_p, args_p) -> matches_ctr(tag_p, args_p, value)
  }
}

pub fn matches_ctr(tag_p: String, args_p: List(Pattern), value: Value) {
  case value {
    VCtr(tag_v, args_v) ->
      case tag_p == tag_v && list.length(args_p) == list.length(args_v) {
        True -> {
          // Zip args and recursively match. 
          let zipped = list.zip(args_p, args_v)
          let results =
            list.map(zipped, fn(pv) {
              let #(p, v) = pv
              matches(p, v)
            })
          // Check if all matches succeeded
          let bindings =
            list.fold(results, Some([]), fn(match_result, acc) {
              case match_result, acc {
                Some(bindings), Some(acc_bindings) ->
                  Some(list.append(bindings, acc_bindings))
                _, _ -> None
              }
            })
          case bindings {
            Some(bindings) -> Some(bindings)
            None -> None
          }
        }
        False -> None
      }
    _ -> None
  }
}

// Converts a Value (semantics) back to a Term (syntax).
pub fn quote(lvl: Int, value: Value, s: Span) -> Term {
  case value {
    VTyp(l) -> Term(Typ(l), s)
    VLit(v) -> Term(Lit(v), s)
    VLitT(t) -> Term(LitT(t), s)
    VCtr(tag, args) ->
      Term(Ctr(tag, list.map(args, fn(arg) { quote(lvl, arg, s) })), s)
    VNeut(HVar(l), args) -> {
      // Convert Absolute Level (l) back to Relative Index
      // Index = Current_Depth - Definition_Depth - 1
      let i = lvl - 1 - l
      let fun = Term(Var(i), s)
      app(fun, list.map(args, fn(arg) { quote(lvl, arg, s) }), s)
    }
    VLam(name, env, body) -> {
      let fresh = VNeut(HVar(lvl), [])
      let body_val = eval([fresh, ..env], body)
      let body_quote = quote(lvl + 1, body_val, body.span)
      Term(Lam(name, body_quote), s)
    }
    VPi(name, env, in_val, out_term) -> {
      // Input type doesn't depend on the fresh variable.
      let in_quote = quote(lvl, in_val, s)
      let fresh = VNeut(HVar(lvl + 1), [])
      let out_val = eval([fresh, ..env], out_term)
      let out_quote = quote(lvl + 1, out_val, out_term.span)
      Term(Pi(name, in_quote, out_quote), s)
    }
    VErr(e) -> Term(Err(e), s)
  }
}

// Checks if two values are equal.
pub fn is_convertible(lvl: Int, v1: Value, v2: Value) -> Bool {
  case v1, v2 {
    VTyp(k1), VTyp(k2) -> k1 == k2
    VLit(v1), VLit(v2) -> v1 == v2
    VLitT(t1), VLitT(t2) -> t1 == t2
    VNeut(HVar(l1), args1), VNeut(HVar(l2), args2) -> {
      l1 == l2 && is_convertible_list(lvl, args1, args2)
    }
    VCtr(tag1, args1), VCtr(tag2, args2) -> {
      tag1 == tag2 && is_convertible_list(lvl, args1, args2)
    }
    VLam(_, _, _), other -> {
      let fresh = VNeut(HVar(lvl), [])
      case eval_apply(v1, fresh), eval_apply(other, fresh) {
        Some(b1), Some(b2) -> is_convertible(lvl + 1, b1, b2)
        _, _ -> False
      }
    }
    _, VLam(_, _, _) -> is_convertible(lvl, v2, v1)
    VPi(_, env1, in1, out1), VPi(_, env2, in2, out2) -> {
      // 1. Check Domains
      let domain_ok = is_convertible(lvl, in1, in2)
      // 2. Check Ranges, with fresh var
      let fresh = VNeut(HVar(lvl), [])
      let range1 = eval([fresh, ..env1], out1)
      let range2 = eval([fresh, ..env2], out2)
      let range_ok = is_convertible(lvl + 1, range1, range2)
      domain_ok && range_ok
    }
    // Errors match everything to prevent cascading error messages
    VErr(_), _ -> True
    _, VErr(_) -> True
    _, _ -> False
  }
}

fn is_convertible_list(lvl: Int, l1: List(Value), l2: List(Value)) -> Bool {
  case l1, l2 {
    [], [] -> True
    [x, ..xs], [y, ..ys] ->
      is_convertible(lvl, x, y) && is_convertible_list(lvl, xs, ys)
    _, _ -> False
  }
}

pub fn normalize(env: Env, term: Term, s: Span) -> Term {
  let val = eval(env, term)
  quote(list.length(env), val, s)
}

fn ctx_to_env(ctx: Context) -> Env {
  let len = list.length(ctx)
  list.index_map(ctx, fn(_, i) {
    // Map Index 'i' to Level 'len - 1 - i'
    VNeut(HVar(len - 1 - i), [])
  })
}

pub fn infer(lvl: Int, ctx: Context, term: Term) -> Value {
  case term.data {
    Typ(l) -> VTyp(l + 1)
    Lit(v) -> infer_lit(v)
    LitT(_) -> VTyp(0)
    Var(i) -> {
      case list_get(ctx, i) {
        Some(#(_, ty)) -> ty
        None -> VErr(UnboundVar(i, term.span))
      }
    }
    Ctr(tag, args) -> infer_ctr(lvl, ctx, tag, args, term.span)
    Ann(term, ty) -> {
      // Ensure annotation is a type
      // TODO: check(lvl, ctx, ty, VTyp(0))
      let ty_val = eval(ctx_to_env(ctx), ty)
      check(lvl, ctx, term, ty_val)
    }
    Lam(_, _) -> VErr(TypeAnnotationNeeded(term))
    Pi(name, in_ty, out_ty) -> {
      check(lvl, ctx, in_ty, VTyp(0))
      let in_val = eval(ctx_to_env(ctx), in_ty)
      let new_ctx = [#(name, in_val), ..ctx]
      check(lvl + 1, new_ctx, out_ty, VTyp(0))
      VTyp(0)
    }
    App(fun, arg) -> {
      case infer(lvl, ctx, fun) {
        VPi(_, env, in_ty, out_ty) -> {
          check(lvl, ctx, arg, in_ty)
          let arg_val = eval(ctx_to_env(ctx), arg)
          eval([arg_val, ..env], out_ty)
        }
        fun_ty -> VErr(NotAFunction(fun_ty, term.span))
      }
    }
    Match(arg, cases) -> {
      let arg_ty = infer(lvl, ctx, arg)
      case cases {
        [] -> {
          // Empty matches are only valid for "Void" types
          // TODO: replace this with a more specific error.
          let err = Err(TODO("match without any cases", term.span))
          infer(lvl, ctx, Term(err, term.span))
        }

        [head, ..cases] -> {
          let #(lvl_f, ctx_f) = bind_pattern(lvl, ctx, head.pattern, arg_ty)
          let return_ty = infer(lvl_f, ctx_f, head.body)
          list.each(cases, fn(c) {
            let #(lvl_c, ctx_c) = bind_pattern(lvl, ctx, c.pattern, arg_ty)
            check(lvl_c, ctx_c, c.body, return_ty)
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

fn infer_ctr(
  lvl: Int,
  ctx: Context,
  tag: String,
  args: List(Term),
  span: Span,
) -> Value {
  // if list.length(args) != list.length(sig.args) {
  //    return Error(TypeMismatch(..., Some("Arity mismatch")))
  // }

  // // 2. Check arguments and resolve parameters
  // // Example: Just(5). Sig: a -> Maybe(a). Arg: Int.
  // // We need to realize 'a' is 'Int'.

  // // This is tricky in pure inference without HM variables.
  // // STRATEGY: 
  // // If the constructor is generic (like Just), fail inference and ask for annotation.
  // // If the constructor is concrete (like True), return Bool.

  // if list.is_empty(sig.params) {
  //   // Simple case: True : Bool
  //   Ok(eval_type(sig.parent_type)) 
  // } else {
  //   // Complex case: Just(5)
  //   // For a simple compiler, reject this! 
  //   // Force the user to write: (Just(5) : Maybe(Int))
  //   // Or use 'check' mode.
  //   Error(TypeMismatch(..., Some("Cannot infer generic constructor. Use an annotation.")))
  // }
  todo
}

pub fn check(lvl: Int, ctx: Context, term: Term, expected_ty: Value) -> Value {
  case term.data, expected_ty {
    Lam(name, body), VPi(_, env, in_ty, out_ty) -> {
      let fresh = VNeut(HVar(lvl), [])
      let out_val = eval([fresh, ..env], out_ty)
      check(lvl + 1, [#(name, in_ty), ..ctx], body, out_val)
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
      let term_ty = infer(lvl, ctx, term)
      case is_convertible(lvl, term_ty, expected_ty) {
        True -> expected_ty
        False -> VErr(TypeMismatch(expected_ty, term_ty, term.span, None))
      }
    }
  }
}

// --- 3. EXHAUSTIVENESS (The Safety Net) ---
fn check_exhaustiveness(cases: List(Case), span: Span) -> Result(Nil, Error) {
  // A "Matrix" is a list of rows, where each row is a list of Patterns
  let patterns = list.map(cases, fn(c) { c.pattern })

  case is_useful(patterns, PAny) {
    True ->
      // If the Wildcard is still "useful" after all user cases, 
      // it means the user missed something.
      // In a real implementation, 'witness' would be the missing constructor.
      Error(NonExhaustiveMatch([PAny], span))
    False -> Ok(Nil)
  }
}

// The core "Is this pattern covered?" logic (Simplified)
fn is_useful(matrix: List(Pattern), target: Pattern) -> Bool {
  case matrix {
    [] -> True
    // Nothing covers the target, so it is useful
    [row, ..rest] -> {
      case covers(row, target) {
        True ->
          // Covered by a previous row -> Not useful
          False
        False -> is_useful(rest, target)
      }
    }
  }
}

fn covers(p1: Pattern, p2: Pattern) -> Bool {
  case p1, p2 {
    PAny, _ -> True
    PVar(_), _ -> True
    PCtr(n1, _), PCtr(n2, _) -> n1 == n2
    _, _ -> False
  }
}

fn infer_case(lvl: Int, ctx: Context, c: Case, scrut_ty: Value) -> Value {
  // 1. Unify pattern with scrutinee type to get new bindings
  // 2. Add bindings to context
  // 3. Infer body
  // infer(lvl + 1, ctx, c.body)
  // simplified
  todo
}

pub fn list_get(xs: List(a), i: Int) -> Option(a) {
  case xs {
    [] -> None
    [x, ..] if i == 0 -> Some(x)
    [_, ..xs] -> list_get(xs, i - 1)
  }
}
