import core/ast.{type Pattern, type Span, type Value}
import gleam/option.{type Option}

pub type TypeError {
  Mismatch(expected: Value, got: Value, span: Span, context: Option(String))
  NotAFunction(got: Value, span: Span)
  UnboundVariable(index: Int, span: Span)
  UnknownConstructor(name: String, span: Span)

  // Exhaustiveness Errors
  NonExhaustiveMatch(missing: List(Pattern), span: Span)
  RedundantMatch(pattern: Pattern, span: Span)
}
