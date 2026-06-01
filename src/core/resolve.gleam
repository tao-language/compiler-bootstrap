import core/context.{type Subst}
import core/term.{type Term} as tm
import gleam/list

pub fn resolve(subst: Subst, term: Term) -> Term {
  case term {
    tm.Typ(_) -> term
    tm.Hole(id) -> todo
    tm.Lit(_) -> term
    tm.LitT(_) -> term
    tm.Var(_) -> term
    tm.Ctr(tag, arg) -> tm.Ctr(tag, resolve(subst, arg))
    tm.Rcd(fields) -> {
      let fields =
        list.map(fields, fn(field) {
          let #(name, term) = field
          #(name, resolve(subst, term))
        })
      tm.Rcd(fields)
    }
    tm.RcdT(fields) -> todo
    tm.Call(name, args) -> tm.Call(name, list.map(args, resolve(subst, _)))
    tm.Ann(term, _) -> todo
    tm.Lam(implicit, param, body) -> todo
    tm.Pi(implicit, domain, codomain) -> todo
    tm.Fix(name, body) -> todo
    tm.App(fun, arg) -> todo
    tm.TypeDef(type_def) -> todo
    tm.Match(arg, cases) -> todo
    tm.Err -> term
  }
}
