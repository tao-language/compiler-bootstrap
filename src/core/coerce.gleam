import core/literals.{type Literal, type LiteralType} as lit
import core/term.{type Term} as tm
import core/value.{type Value} as v
import gleam/int

pub fn coerce(term: Term, type_: Value) -> Term {
  case term, type_ {
    tm.Lit(lit), v.LitT(ty) -> tm.Lit(coerce_lit(lit, ty))
    _, _ -> term
  }
}

fn coerce_lit(lit: Literal, ty: LiteralType) -> Literal {
  case lit {
    // lit.Int(k)
    //   if ty == lit.FloatT || ty == lit.F16 || ty == lit.F32 || ty == lit.F64
    // -> lit.Float(int.to_float(k))
    _ -> lit
  }
}
