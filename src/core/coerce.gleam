import core/term.{type Term}
import core/value.{type Value}

/// Adjust an inferred term to its expected type. Currently a no-op;
/// intended to fill missing record fields with their type-level defaults.
pub fn coerce(term: Term, type_: Value) -> Term {
  case term, type_ {
    // TODO: Rcd default values
    _, _ -> term
  }
}
