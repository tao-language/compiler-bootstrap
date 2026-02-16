import gleam/option.{type Option}

pub type Span {
  Span(start: Int, end: Int, file: String)
}

pub type Term {
  Term(data: TermData, span: Span)
}

pub type TermData {
  // Type, Type1, ...
  Typ(level: Int)

  // De Bruijn Index
  Var(index: Int)

  // Functions
  Pi(name: String, input: Term, output: Term)
  Lam(name: String, body: Term)
  App(fun: Term, arg: Term)

  // Annotation
  Ann(val: Term, type_: Term)

  // Data & Matching
  Ctr(name: String, args: List(Term))
  Match(scrutinee: Term, cases: List(Case))

  // '?' for incomplete code
  Hole
}

pub type Case {
  Case(pattern: Pattern, body: Term, span: Span)
}

pub type Pattern {
  PAny
  PVar(name: String)
  PCtr(name: String, args: List(Pattern))
}

pub type Value {
  VTyp(level: Int)
  VPi(name: String, input: Value, output: fn(Value) -> Value)
  VLam(name: String, body: fn(Value) -> Value)
  VNeut(head: Head, args: List(Value))
  VCtr(name: String, args: List(Value))
  VErr(err: Error)
}

pub type Head {
  // De Bruijn Level (Absolute)
  HVar(level: Int)
}

pub type Env =
  List(Value)

pub type Error {
  // Type errors
  TypeMismatch(expected: Value, got: Value, span: Span, context: Option(String))
  NotAFunction(got: Value, span: Span)
  UnboundVar(index: Int, span: Span)

  // Exhaustiveness errors
  NonExhaustiveMatch(missing: List(Pattern), span: Span)
  RedundantMatch(pattern: Pattern, span: Span)

  // Runtime errors
  EvalHole(span: Span)
}
