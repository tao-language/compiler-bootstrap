import core/ast.{
  type Case, type Env, type Pattern, type Span, type Term, type Value, Ann, App,
  Ctr, HVar, Hole, Lam, Lit, Match, PAny, PCtr, PVar, Pi, Typ, VCtr, VErr, VLam,
  VLit, VNeut, VPi, VTyp, Var,
}
import gleam/list
import gleam/option.{type Option, None, Some}

pub fn env_get(env: Env, i: Int) -> Option(Value) {
  case env {
    [] -> None
    [x, ..] if i == 0 -> Some(x)
    [_, ..env] -> env_get(env, i - 1)
  }
}

pub fn eval(env: Env, term: Term) -> Value {
  case term.data {
    Typ(k) -> VTyp(k)
    Lit(v) -> VLit(v)
    Var(i) ->
      case env_get(env, i) {
        Some(val) -> val
        // None -> VNeut(HVar(i), [])
        None -> VErr(ast.UnboundVar(i, term.span))
      }

    // Closures capture the environment 'env'
    Pi(name, in, out) ->
      VPi(name, eval(env, in), fn(x) { eval([x, ..env], out) })

    Lam(name, body) -> VLam(name, fn(x) { eval([x, ..env], body) })

    App(f, arg) -> {
      let vf = eval(env, f)
      let va = eval(env, arg)
      case eval_apply(vf, va) {
        Some(result) -> result
        None -> VErr(ast.NotAFunction(vf, f.span))
      }
    }

    Ann(t, _) -> eval(env, t)

    Ctr(name, args) -> VCtr(name, list.map(args, fn(a) { eval(env, a) }))

    Match(scrutinee, cases) -> {
      let val = eval(env, scrutinee)
      eval_match(val, cases, env)
    }

    Hole -> VErr(ast.EvalHole(term.span))
  }
}

pub fn eval_apply(vf: Value, va: Value) -> Option(Value) {
  case vf {
    VLam(_, closure) -> Some(closure(va))
    VNeut(head, args) -> Some(VNeut(head, list.append(args, [va])))
    _ -> None
  }
}

pub fn eval_match(val: Value, cases: List(Case), env: Env) -> Value {
  case cases {
    [] -> panic as "Runtime Error: Non-exhaustive match hit at runtime"
    [first, ..rest] -> {
      case matches(val, first.pattern) {
        Some(bindings) -> eval(list.append(bindings, env), first.body)
        None -> eval_match(val, rest, env)
      }
    }
  }
}

// Returns bindings (in reverse order) if match succeeds
fn matches(val: Value, pat: Pattern) -> Option(List(Value)) {
  case val, pat {
    // First, check for wildcard patterns
    _, PAny -> Some([])
    // Next, handle variable patterns before constructor patterns
    v, PVar(_) -> Some([v])
    // Finally, attempt to match constructor patterns
    VCtr(n1, args1), PCtr(n2, args2) ->
      case n1 == n2 && list.length(args1) == list.length(args2) {
        True -> {
          // Zip args and recursively match. 
          let zipped = list.zip(args1, args2)
          let results =
            list.map(zipped, fn(kv) {
              let #(a, b) = kv
              matches(a, b)
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
    // If none of the above cases match, return None
    _, _ -> None
  }
}
