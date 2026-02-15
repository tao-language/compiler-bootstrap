import core/ast.{type Term, type Value}
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
    ast.Var(i) ->
      case env_get(env, i) {
        Some(val) -> val
        None ->
          // panic as "Compiler error: Index out of bounds in eval. Type checker failed."
          ast.VNeut(ast.HVar(i), [])
      }

    ast.Universe(k) -> ast.VUniverse(k)

    // Closures capture the environment 'env'
    ast.Pi(name, in, out) ->
      ast.VPi(name, eval(env, in), fn(x) { eval([x, ..env], out) })

    ast.Lam(name, body) -> ast.VLam(name, fn(x) { eval([x, ..env], body) })

    ast.App(f, arg) -> {
      let vf = eval(env, f)
      let va = eval(env, arg)
      eval_apply(vf, va)
    }

    ast.Ann(t, _) -> eval(env, t)

    ast.Constructor(name, args) ->
      ast.VConstructor(name, list.map(args, fn(a) { eval(env, a) }))

    ast.Match(scrutinee, cases) -> {
      let val = eval(env, scrutinee)
      eval_match(val, cases, env)
    }

    ast.Hole -> panic as "Runtime Error: Cannot evaluate a Hole"
  }
}

fn eval_apply(f: Value, arg: Value) -> Value {
  case f {
    ast.VLam(_, closure) -> closure(arg)
    ast.VNeut(head, args) -> ast.VNeut(head, list.append(args, [arg]))
    _ -> panic as "Runtime Error: Applied non-function"
  }
}

fn eval_match(val: Value, cases: List(ast.Case), env: Env) -> Value {
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
fn matches(val: Value, pat: ast.Pattern) -> Option(List(Value)) {
  case val, pat {
    _, ast.PWildcard -> Some([])
    v, ast.PVar(_) -> Some([v])
    // Bind variable
    ast.VConstructor(n1, args1), ast.PConstructor(n2, args2) ->
      case n1 == n2 && list.length(args1) == list.length(args2) {
        True -> {
          // Zip args and recursively match. 
          // Note: Real implementation needs to flatten the list of results correctly
          // Placeholder for brevity
          // Some([])
          panic as "TODO: Implement variable binding logic here"
        }
        False -> {
          None
        }
      }
    _, _ -> None
  }
}
