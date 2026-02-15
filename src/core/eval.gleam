import core/ast.{
  type Case, type Pattern, type Span, type Term, type Value, Ann, App, Ctr, HVar,
  Hole, Lam, Match, PAny, PCtr, PVar, Pi, Typ, VCtr, VLam, VNeut, VPi, VTyp, Var,
}
import gleam/list
import gleam/option.{type Option, None, Some}

// The Environment maps De Bruijn Indices (relative) to Values
pub type Env =
  List(Value)

fn env_get(env: Env, i: Int) -> Option(Value) {
  case env {
    [] -> None
    [x, ..] if i == 0 -> Some(x)
    [_, ..env] -> env_get(env, i - 1)
  }
}

pub fn eval(env: Env, term: Term) -> Value {
  case term.data {
    Var(i) ->
      case env_get(env, i) {
        Some(val) -> val
        None ->
          // panic as "Compiler error: Index out of bounds in eval. Type checker failed."
          VNeut(HVar(i), [])
      }

    Typ(k) -> VTyp(k)

    // Closures capture the environment 'env'
    Pi(name, in, out) ->
      VPi(name, eval(env, in), fn(x) { eval([x, ..env], out) })

    Lam(name, body) -> VLam(name, fn(x) { eval([x, ..env], body) })

    App(f, arg) -> {
      let vf = eval(env, f)
      let va = eval(env, arg)
      eval_apply(vf, va)
    }

    Ann(t, _) -> eval(env, t)

    Ctr(name, args) -> VCtr(name, list.map(args, fn(a) { eval(env, a) }))

    Match(scrutinee, cases) -> {
      let val = eval(env, scrutinee)
      eval_match(val, cases, env)
    }

    Hole -> panic as "Runtime Error: Cannot evaluate a Hole"
  }
}

pub fn eval_apply(f: Value, arg: Value) -> Value {
  case f {
    VLam(_, closure) -> closure(arg)
    VNeut(head, args) -> VNeut(head, list.append(args, [arg]))
    _ -> panic as "Runtime Error: Applied non-function"
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
