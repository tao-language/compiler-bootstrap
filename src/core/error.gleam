import core/term.{type Term}
import core/value.{type Neut, type Value, type Variant}
import gleam/string
import syntax/span.{type Span}

pub type Error {
  UnexpectedToken(token: String, span: Span)
  VarUndefined(name: String, span: Span)
  TypeMismatch(#(Value, Span), #(Value, Span))
  NeutralTypeMismatch(#(Neut, Span), #(Neut, Span))
  RcdFieldsMismatch(#(List(String), Span), #(List(String), Span))
  CallArityMismatch(#(Int, Span), #(Int, Span))
  InfiniteType(hole_id: Int, type_: Value, span: Span)
  NotAFunction(fun: Term, fun_type: Value, span: Span)
  AppExpectedExplicitArg(fun_type: Value, span: Span)
  TypeVariantUndefined(
    tag: #(String, Span),
    variants: #(List(#(String, Variant)), Span),
  )
  MatchMissing(patterns: List(String), covered: List(String), span: Span)
  MatchRedundant(span: Span)
  StepLimitExceeded(steps: Int, span: Span)
  CtorArgTypeMismatch(
    tag: String,
    expected_pattern: Value,
    actual_type: Value,
    span: Span,
  )
  CtorNotFound(tag: String, span: Span)
}

pub fn display(err: Error) -> String {
  // TODO: human-friendly error message display
  // TODO: code snippet with ascii art showing location
  // TODO: colored output
  string.inspect(err)
}
