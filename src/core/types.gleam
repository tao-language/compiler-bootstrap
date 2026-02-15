import core/ast.{
  type Case, type Pattern, type Span, type Term, type Value, Ann, App, Ctr, HVar,
  Hole, Lam, Match, PAny, PCtr, PVar, Pi, Typ, VCtr, VLam, VNeut, VPi, VTyp, Var,
}
import core/error.{type TypeError}
import core/eval
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/result

pub type Context =
  List(#(String, Value))

pub type CtrSignature {
  CtrSignature(
    name: String,
    parent_type: String,
    params: List(String),
    args: List(ast.Term),
  )
}

pub fn ctx_get(ctx: Context, i: Int) -> Option(#(String, Value)) {
  case ctx {
    [] -> None
    [x, ..] if i == 0 -> Some(x)
    [_, ..ctx] -> ctx_get(ctx, i - 1)
  }
}

// --- 1. INFERENCE (Synthesize a type) ---
pub fn infer(lvl: Int, ctx: Context, term: Term) -> Result(Value, TypeError) {
  case term.data {
    Var(i) -> {
      case ctx_get(ctx, i) {
        Some(#(_, ty)) -> Ok(ty)
        None -> Error(error.UnboundVariable(i, term.span))
      }
    }

    Ann(tm, ty) -> {
      use _ <- result.try(check(lvl, ctx, ty, VTyp(0)))
      // Ensure annotation is a type
      let ty_val = eval.eval(ctx_to_env(ctx), ty)
      use _ <- result.try(check(lvl, ctx, tm, ty_val))
      Ok(ty_val)
    }

    Typ(k) -> Ok(VTyp(k + 1))

    App(f, arg) -> {
      use f_ty <- result.try(infer(lvl, ctx, f))
      case f_ty {
        VPi(_, input_ty, output_closure) -> {
          use _ <- result.try(check(lvl, ctx, arg, input_ty))
          let arg_val = eval.eval(ctx_to_env(ctx), arg)
          Ok(output_closure(arg_val))
        }
        _ -> Error(error.NotAFunction(f_ty, term.span))
      }
    }

    Match(scrutinee, cases) -> {
      // 1. Infer type of scrutinee
      use scrutinee_ty <- result.try(infer(lvl, ctx, scrutinee))
      // 2. Check Exhaustiveness (The Matrix Check)
      use _ <- result.try(check_exhaustiveness(cases, term.span))
      // 3. Infer type of the first branch to establish expected type
      // (Simplified: In a real compiler, we join types of all branches)
      case cases {
        [] -> Ok(VTyp(0))
        // Empty match (Void)
        [first, ..] -> infer_case(lvl, ctx, first, scrutinee_ty)
      }
    }

    _ ->
      Error(error.Mismatch(
        expected: VTyp(0),
        // Placeholder
        got: VTyp(0),
        span: term.span,
        context: option.Some("Cannot infer type; try adding an annotation."),
      ))
  }
}

// --- 2. CHECKING (Validate against a type) ---
pub fn check(
  lvl: Int,
  ctx: Context,
  term: Term,
  expected: Value,
) -> Result(Nil, TypeError) {
  case term.data, expected {
    Lam(name, body), VPi(_, domain, range_closure) -> {
      let var = VNeut(HVar(lvl), [])
      let new_ctx = [#(name, domain), ..ctx]
      check(lvl + 1, new_ctx, body, range_closure(var))
    }

    Hole, _ -> Ok(Nil)

    // Holes are always valid types (but warn)
    _, _ -> {
      // Switch mode: Infer and Compare
      use inferred <- result_map(infer(lvl, ctx, term))
      case is_convertible(lvl, inferred, expected) {
        True -> Ok(Nil)
        False -> Error(error.Mismatch(expected, inferred, term.span, None))
      }
    }
  }
}

// --- 3. EXHAUSTIVENESS (The Safety Net) ---
fn check_exhaustiveness(cases: List(Case), span: Span) -> Result(Nil, TypeError) {
  // A "Matrix" is a list of rows, where each row is a list of Patterns
  let patterns = list.map(cases, fn(c) { c.pattern })

  case is_useful(patterns, PAny) {
    True ->
      // If the Wildcard is still "useful" after all user cases, 
      // it means the user missed something.
      // In a real implementation, 'witness' would be the missing constructor.
      Error(error.NonExhaustiveMatch([PAny], span))
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

// --- HELPERS ---

fn ctx_to_env(ctx: Context) -> eval.Env {
  // Convert type context to value environment (dummies for checking)
  list.map(ctx, fn(_) { VNeut(HVar(0), []) })
  // Simplified
}

fn result_map(res: Result(a, e), f: fn(a) -> Result(b, e)) -> Result(b, e) {
  case res {
    Ok(x) -> f(x)
    Error(e) -> Error(e)
  }
}

// NbE Equality Check
pub fn is_convertible(lvl: Int, v1: Value, v2: Value) -> Bool {
  case v1, v2 {
    // 1. Universes: Simply compare levels
    VTyp(k1), VTyp(k2) -> k1 == k2

    // 2. Constructors: Names and arguments must match
    VCtr(n1, args1), VCtr(n2, args2) -> {
      n1 == n2 && is_convertible_list(lvl, args1, args2)
    }

    // 3. Neutral Terms (Variables/Applications): 
    // Heads (the variable) and all applied arguments must match
    VNeut(ast.HVar(h1), args1), VNeut(ast.HVar(h2), args2) -> {
      h1 == h2 && is_convertible_list(lvl, args1, args2)
    }

    // 4. Pi Types (Functions Types): 
    // Inputs must match, and outputs must match for a fresh variable
    VPi(_, in1, out1), VPi(_, in2, out2) -> {
      let fresh = VNeut(HVar(lvl), [])
      is_convertible(lvl, in1, in2)
      && is_convertible(lvl + 1, out1(fresh), out2(fresh))
    }

    // 5. Lambdas:
    // Compare bodies by applying a fresh variable to both
    VLam(_, body1), VLam(_, body2) -> {
      let fresh = VNeut(HVar(lvl), [])
      is_convertible(lvl + 1, body1(fresh), body2(fresh))
    }

    // Eta-Expansion (Advanced): 
    // Allows a lambda to be equal to a neutral term if they behave the same
    VLam(_, body), other | other, VLam(_, body) -> {
      let fresh = VNeut(HVar(lvl), [])
      is_convertible(lvl + 1, body(fresh), eval.eval_apply(other, fresh))
    }

    // Fallback: If types are different, they are not convertible
    _, _ -> False
  }
}

// Helper to compare lists of values
fn is_convertible_list(lvl: Int, l1: List(Value), l2: List(Value)) -> Bool {
  case l1, l2 {
    [], [] -> True
    [x, ..xs], [y, ..ys] ->
      is_convertible(lvl, x, y) && is_convertible_list(lvl, xs, ys)
    _, _ -> False
  }
}

fn infer_case(
  lvl: Int,
  ctx: Context,
  c: Case,
  scrut_ty: Value,
) -> Result(Value, TypeError) {
  // 1. Unify pattern with scrutinee type to get new bindings
  // 2. Add bindings to context
  // 3. Infer body
  infer(lvl + 1, ctx, c.body)
  // simplified
}
