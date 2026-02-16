import gleam/option.{type Option}

pub type Span {
  Span(start: Int, end: Int, file: String)
}

pub type Term {
  Term(data: TermData, span: Span)
}

pub type TermData {
  Typ(level: Int)
  Lit(value: Literal)
  Var(index: Int)
  Pi(name: String, input: Term, output: Term)
  Lam(name: String, body: Term)
  Ann(term: Term, typ: Term)
  Ctr(name: String, args: List(Term))
  App(fun: Term, arg: Term)
  Match(arg: Term, cases: List(Case))
  Hole
}

pub type Literal {
  I32(value: Int)
  I64(value: Int)
  U32(value: Int)
  U64(value: Int)
  F32(value: Float)
  F64(value: Float)
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
  VLit(value: Literal)
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
