import core/literals.{type Literal, type LiteralType} as lit
import gleam/option.{type Option}
import syntax/span.{type Span}

pub type Expr {
  Expr(data: ExprData, span: Span)
}

pub type Type =
  Expr

pub type ExprData {
  Hole(id: Option(Int))
  Lit(value: Literal)
  Var(name: String)
  Ctr(tag: String, args: List(#(String, Expr)))
  Rcd(fields: List(#(String, Expr)))
  RcdT(fields: List(#(String, #(Option(Type), Option(Expr)))))
  Ann(value: Expr, type_: Type)
  Fn(
    implicits: List(Param),
    params: List(Param),
    returns: Option(Type),
    body: Expr,
  )
  FnT(implicits: List(Param), params: List(Param), body: Expr)
  App(fun: Expr, implicits: List(#(String, Expr)), args: List(#(String, Expr)))
  Match(arg: Expr, cases: List(Case))
  Call(name: String, ret: Type, args: List(Expr))
  Do(Block)
  Err
}

pub type Block =
  List(Stmt)

pub type Stmt {
  Stmt(data: StmtData, span: Span)
}

pub type StmtData {
  Let(pattern: Pattern, opt_type: Option(Type), value: Expr)
  LetMut(name: String, opt_type: Option(Type), value: Expr)
  Mut(name: String, value: Expr)
  FnDef(
    name: String,
    implicits: List(Param),
    params: List(Param),
    returns: Option(Type),
    body: Expr,
  )
  TypeDef(type_def: TypeDefinition)
  For(iterator: Pattern, range: Expr, body: Expr)
  While(condition: Expr, body: Expr)
  Return(expr: Expr)
  Break
  Continue
}

pub type Param =
  // (pattern, (type, default_value))
  #(Pattern, #(Option(Type), Option(Expr)))

pub type TypeDefinition {
  TypeDefinition(
    params: List(#(String, #(Option(Type), Option(Expr)))),
    variants: List(Variant),
  )
}

pub type Variant {
  Variant(
    tag: String,
    params: List(#(String, #(Option(Type), Option(Expr)))),
    args: List(#(String, Expr)),
    returns: Type,
  )
}

pub type Pattern {
  Pattern(data: PatternData, span: Span)
}

pub type PatternData {
  PAny
  PVar(name: String)
  PLit(lit: Literal)
  PLitT(lit_t: LiteralType)
  PCtr(tag: String, args: List(PArg))
}

pub type PArg =
  #(String, Pattern)

pub type Case {
  Case(pattern: Pattern, body: Expr)
  CaseIf(pattern: Pattern, guard: Expr, body: Expr)
  CaseIfMatch(pattern: Pattern, guard: #(Expr, Pattern), body: Expr)
}

// Syntax sugar

pub fn true(span: Span) {
  ctr0("True", span)
}

pub fn false(span: Span) {
  ctr0("False", span)
}

pub fn bool(span: Span) {
  ctr0("Bool", span)
}

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

pub fn ctr(tag: String, args: List(#(String, Expr)), span: Span) {
  Expr(Ctr(tag, args), span)
}

pub fn ctr0(tag: String, span: Span) {
  ctr(tag, [], span)
}

pub fn ann(expr: Expr, type_: Type, span: Span) {
  Expr(Ann(expr, type_), span)
}

pub fn app(fun: Expr, args: List(#(String, Expr)), span: Span) {
  Expr(App(fun, [], args), span)
}

pub fn match(arg: Expr, cases: List(Case), span: Span) {
  Expr(Match(arg, cases), span)
}

pub fn call(name: String, ret: Type, args: List(Expr), span: Span) {
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

pub fn pctr(tag: String, args: List(#(String, Pattern)), span: Span) {
  Pattern(PCtr(tag, args), span)
}

pub fn return(expr: Expr, span: Span) {
  Stmt(Return(expr), span)
}
