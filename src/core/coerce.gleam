import core/literals.{type Literal, type LiteralType} as lit
import core/term.{type Term} as tm
import core/value.{type Value} as v

pub fn coerce(term: Term, type_: Value) -> Term {
  case term, type_ {
    tm.Lit(lit), v.LitT(ty) -> tm.Lit(coerce_lit(lit, ty))
    _, _ -> term
  }
}

fn coerce_lit(lit: Literal, type_: LiteralType) -> Literal {
  case lit, type_ {
    _, _ -> lit
  }
}
