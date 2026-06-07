import core/context.{type FFI, type Subst}
import core/quote.{quote}
import core/term.{type Case, type Term} as tm
import gleam/list
import gleam/option.{None, Some}

pub fn resolve(ffi: FFI, subst: Subst, size: Int, term: Term) -> Term {
  case term {
    tm.Typ(_) -> term
    tm.Hole(id) ->
      case list.key_find(subst, id) {
        Error(Nil) -> term
        Ok(value) -> {
          let term = quote(ffi, size, value)
          resolve(ffi, subst, size, term)
        }
      }
    tm.Lit(_) -> term
    tm.LitT(_) -> term
    tm.Var(_) -> term
    tm.Ctr(tag, arg) -> tm.Ctr(tag, resolve(ffi, subst, size, arg))
    tm.Rcd(fields) -> {
      let fields =
        list.map(fields, fn(field) {
          let #(name, term) = field
          #(name, resolve(ffi, subst, size, term))
        })
      tm.Rcd(fields)
    }
    tm.RcdT(fields) -> todo
    tm.Call(name, args) ->
      tm.Call(name, list.map(args, resolve(ffi, subst, size, _)))
    tm.Ann(term, _) -> todo
    tm.Lam(param, body) -> todo
    tm.Pi(implicit, domain, codomain) -> todo
    tm.Fix(name, body) -> todo
    tm.App(fun, arg) -> todo
    tm.TypeDef(type_def) -> todo
    tm.Match(arg, cases) -> todo
    tm.Err -> term
  }
}

pub fn resolve_case(ffi: FFI, subst: Subst, size: Int, c: Case) -> Case {
  let size = size + list.length(tm.bindings(c.pattern))
  let #(guard, size) = case c.guard {
    Some(#(g_term, g_pattern)) -> {
      let size = size + list.length(tm.bindings(g_pattern))
      let g_term = resolve(ffi, subst, size, g_term)
      #(Some(#(g_term, g_pattern)), size)
    }
    None -> #(None, size)
  }
  tm.Case(c.pattern, guard, resolve(ffi, subst, size, c.body))
}
