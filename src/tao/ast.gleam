import core/literals.{type Literal, type LiteralType} as lit
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
  RcdT(fields: List(ArgT))
  Ann(value: Expr, type_: Type)
  Fn(
    implicits: List(Param),
    params: List(Param),
    returns: Option(Type),
    body: Expr,
  )
  FnT(implicits: List(Param), params: List(Param), body: Expr)
  App(fun: Expr, implicits: List(Arg), args: List(Arg))
  Match(arg: Expr, cases: List(Case))
  Call(name: Label, ret: Type, args: List(Expr))
  Do(List(Stmt))
  Err
}

pub type Stmt {
  Stmt(data: StmtData, span: Span)
}

pub type StmtData {
  Let(pattern: Pattern, type_: Option(Type), value: Expr)
  LetMut(name: String, type_: Option(Type), value: Expr)
  FnDef(
    name: Label,
    implicits: List(Param),
    params: List(Param),
    returns: Option(Type),
    body: Expr,
  )
  TypeDef(type_def: TypeDefinition)
  For(iterator: Pattern, range: Expr, body: Expr)
  While(condition: Expr, body: Expr)
  Return(Expr)
  Break
  Continue
}

pub type Label =
  // TODO: #(String, Span)
  String

pub type Arg =
  #(Label, Expr)

pub type ArgT =
  // (name, (type, default_value))
  #(Label, #(Option(Type), Option(Expr)))

pub type Param =
  // (pattern, (type, default_value))
  #(Pattern, #(Option(Type), Option(Expr)))

pub type TypeDefinition {
  TypeDefinition(params: List(ArgT), variants: List(Variant))
}

pub type Variant {
  Variant(tag: Label, params: List(ArgT), args: List(Arg), returns: Type)
}

pub type Pattern {
  Pattern(data: PatternData, span: Span)
}

pub type PatternData {
  PAny
  PVar(name: String)
  PLit(lit: Literal)
  PLitT(lit_t: LiteralType)
  PCtr(tag: Label, args: List(PArg))
}

pub type PArg =
  #(Label, Pattern)

pub type Case {
  Case(pattern: Pattern, body: Expr)
  CaseIf(pattern: Pattern, guard: Expr, body: Expr)
  CaseIfMatch(pattern: Pattern, guard: #(Expr, Pattern), body: Expr)
}

// Syntax sugar

pub fn int(value: Int, span: Span) {
  Expr(Lit(lit.Int(value)), span)
}

pub fn float(value: Float, span: Span) {
  Expr(Lit(lit.Float(value)), span)
}

pub fn int_t(span: Span) {
  Expr(Ctr("Int", []), span)
}

pub fn var(name: String, span: Span) {
  Expr(Var(name), span)
}

pub fn app(fun: Expr, args: List(Arg), span: Span) {
  Expr(App(fun, [], args), span)
}

pub fn match(arg: Expr, cases: List(Case), span: Span) {
  Expr(Match(arg, cases), span)
}

pub fn call(name: Label, ret: Type, args: List(Expr), span: Span) {
  Expr(Call(name, ret, args), span)
}

pub fn do(stmts: List(Stmt), span: Span) {
  Expr(Do(stmts), span)
}

pub fn err(span: Span) {
  Expr(Err, span)
}

pub fn pany(span: Span) {
  Pattern(PAny, span)
}

pub fn pvar(name: String, span: Span) {
  Pattern(PVar(name), span)
}

pub fn pint(value: Int, span: Span) {
  Pattern(PLit(lit.Int(value)), span)
}

pub fn pfloat(value: Float, span: Span) {
  Pattern(PLit(lit.Float(value)), span)
}

pub fn return(expr: Expr, span: Span) {
  Stmt(Return(expr), span)
}
