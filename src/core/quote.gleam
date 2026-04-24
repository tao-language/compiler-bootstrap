// Core quote - Value -> Term conversion
// Quotes a value back to a term (syntax).
// Does NOT call eval - quote transforms a Value back to a Term by re-wrapping
// evaluated lambdas.

import core/ast.{type Value, type Term, Closure, IntVal, FloatVal, StringVal, CtrVal, LitVal, HoleVal, ErrVal, Lam, Ctr, Lit, Hole, Err, LInt, LFloat, LString}

/// Quote a value to a term
pub fn quote(val: Value) -> Term {
  case val {
    Closure(param, body, _) -> Lam(param: param, body: body)
    IntVal(n) -> Lit(LInt(n))
    FloatVal(n) -> Lit(LFloat(n))
    StringVal(s) -> Lit(LString(s))
    CtrVal(tag, arg) -> Ctr(tag: tag, args: [quote(arg)])
    LitVal(lit) -> Lit(lit)
    HoleVal(id) -> Hole(id)
    ErrVal -> Err(message: "quote error")
  }
}
