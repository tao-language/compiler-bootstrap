import core/term.{type Term}
import core/value.{type Value}

pub fn coerce(term: Term, type_: Value) -> Term {
  case term, type_ {
    // TODO: Rcd default values
    _, _ -> term
  }
}
