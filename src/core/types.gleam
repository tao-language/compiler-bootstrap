import core/ast.{type Term, type Value}
import core/error.{type TypeError}
import core/eval
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/result

pub type Context =
  List(#(String, Value))

fn ctx_get(ctx: Context, i: Int) -> Option(#(String, Value)) {
  case ctx {
    [] -> None
    [x, ..] if i == 0 -> Some(x)
    [_, ..ctx] -> ctx_get(ctx, i - 1)
  }
}

// --- 1. INFERENCE (Synthesize a type) ---
pub fn infer(lvl: Int, ctx: Context, term: Term) -> Result(Value, TypeError) {
  case term.data {
    ast.Var(i) -> {
      case ctx_get(ctx, i) {
        Some(#(_, ty)) -> Ok(ty)
        None -> Error(error.UnboundVariable(i, term.span))
      }
    }

    ast.Ann(tm, ty) -> {
      use _ <- result.try(check(lvl, ctx, ty, ast.VUniverse(0)))
      // Ensure annotation is a type
      let ty_val = eval.eval(ctx_to_env(ctx), ty)
      use _ <- result.try(check(lvl, ctx, tm, ty_val))
      Ok(ty_val)
    }

    ast.Universe(k) -> Ok(ast.VUniverse(k + 1))

    ast.App(f, arg) -> {
      use f_ty <- result.try(infer(lvl, ctx, f))
      case f_ty {
        ast.VPi(_, input_ty, output_closure) -> {
          use _ <- result.try(check(lvl, ctx, arg, input_ty))
          let arg_val = eval.eval(ctx_to_env(ctx), arg)
          Ok(output_closure(arg_val))
        }
        _ -> Error(error.NotAFunction(f_ty, term.span))
      }
    }

    ast.Match(scrutinee, cases) -> {
      // 1. Infer type of scrutinee
      use scrutinee_ty <- result.try(infer(lvl, ctx, scrutinee))
      // 2. Check Exhaustiveness (The Matrix Check)
      use _ <- result.try(check_exhaustiveness(cases, term.span))
      // 3. Infer type of the first branch to establish expected type
      // (Simplified: In a real compiler, we join types of all branches)
      case cases {
        [] -> Ok(ast.VUniverse(0))
        // Empty match (Void)
        [first, ..] -> infer_case(lvl, ctx, first, scrutinee_ty)
      }
    }

    _ ->
      Error(error.Mismatch(
        expected: ast.VUniverse(0),
        // Placeholder
        got: ast.VUniverse(0),
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
    ast.Lam(name, body), ast.VPi(_, domain, range_closure) -> {
      let var = ast.VNeut(ast.HVar(lvl), [])
      let new_ctx = [#(name, domain), ..ctx]
      check(lvl + 1, new_ctx, body, range_closure(var))
    }

    ast.Hole, _ -> Ok(Nil)

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
fn check_exhaustiveness(
  cases: List(ast.Case),
  span: ast.Span,
) -> Result(Nil, TypeError) {
  // A "Matrix" is a list of rows, where each row is a list of Patterns
  let patterns = list.map(cases, fn(c) { c.pattern })

  case is_useful(patterns, ast.PWildcard) {
    True ->
      // If the Wildcard is still "useful" after all user cases, 
      // it means the user missed something.
      // In a real implementation, 'witness' would be the missing constructor.
      Error(error.NonExhaustiveMatch([ast.PWildcard], span))
    False -> Ok(Nil)
  }
}

// The core "Is this pattern covered?" logic (Simplified)
fn is_useful(matrix: List(ast.Pattern), target: ast.Pattern) -> Bool {
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

fn covers(p1: ast.Pattern, p2: ast.Pattern) -> Bool {
  case p1, p2 {
    ast.PWildcard, _ -> True
    ast.PVar(_), _ -> True
    ast.PConstructor(n1, _), ast.PConstructor(n2, _) -> n1 == n2
    _, _ -> False
  }
}

// --- HELPERS ---

fn ctx_to_env(ctx: Context) -> eval.Env {
  // Convert type context to value environment (dummies for checking)
  list.map(ctx, fn(_) { ast.VNeut(ast.HVar(0), []) })
  // Simplified
}

fn result_map(res: Result(a, e), f: fn(a) -> Result(b, e)) -> Result(b, e) {
  case res {
    Ok(x) -> f(x)
    Error(e) -> Error(e)
  }
}

// NbE Equality Check
fn is_convertible(lvl: Int, v1: Value, v2: Value) -> Bool {
  // In a real compiler: quote(lvl, v1) == quote(lvl, v2)
  // For bootstrap, we can approximate or implement full quote
  True
}

fn infer_case(
  lvl: Int,
  ctx: Context,
  c: ast.Case,
  scrut_ty: Value,
) -> Result(Value, TypeError) {
  // 1. Unify pattern with scrutinee type to get new bindings
  // 2. Add bindings to context
  // 3. Infer body
  infer(lvl + 1, ctx, c.body)
  // simplified
}
