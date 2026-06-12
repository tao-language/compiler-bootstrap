import core/literals.{type Literal}
import gleam/option.{type Option}
import syntax/span.{type Span}

pub type Expr {
  Expr(data: ExprData, span: Span)
}

pub type Type =
  Expr

pub type ExprData {
  Hole(id: Int)
  Lit(value: Literal)
  Var(name: String)
  Ctr(tag: Label, args: List(Arg))
  Rcd(fields: List(Arg))
  RcdT(fields: List(Param))
  Ann(value: Expr, type_: Type)
  Fn(implicits: List(Param), params: List(Param), body: Expr)
  FnT(implicits: List(Param), params: List(Param), body: Expr)
  App(fun: Expr, implicits: List(Arg), args: List(Arg))
  TypeDef(type_def: TypeDefinition)
  Match(arg: Expr, cases: List(Case))
  Call(name: Label, ret: Type, args: List(Expr))
  Let(def: #(Pattern, Option(Type), Expr), body: Expr)
  Err
}

pub type Label =
  #(String, Span)

pub type Arg =
  #(Label, Expr)

pub type Param =
  // (name, (type, default_value))
  #(Label, #(Option(Type), Option(Expr)))

pub type TypeDefinition {
  TypeDefinition(params: List(Param), variants: List(Variant))
}

pub type Variant {
  Variant(tag: Label, params: List(Param), args: List(Arg), returns: Type)
}

pub type Pattern {
  Pattern(data: PatternData, span: Span)
}

pub type PatternData

pub type Case {
  Case(pattern: Pattern, body: Expr)
  CaseIf(pattern: Pattern, guard: Expr, body: Expr)
  CaseMatch(pattern: Pattern, guard: #(Expr, Pattern), body: Expr)
}

// Syntax sugar

pub fn err(span: Span) {
  Expr(Err, span)
}
