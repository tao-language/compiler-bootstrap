import core/literals.{type Literal, type LiteralType} as lit
import gleam/list
import gleam/option.{type Option, None, Some}
import syntax/span.{type Span}

pub type Module =
  #(String, List(Stmt))

pub type Expr {
  Expr(data: ExprData, span: Span)
}

pub type Type =
  Expr

pub type ExprData {
  Hole(id: Option(Int))
  Lit(value: Literal)
  Var(name: String)
  Ctr(tag: String, args: List(#(String, Expr)), tail: Option(Expr))
  Rcd(fields: List(#(String, Option(Expr))), tail: Option(Expr))
  RcdT(
    fields: List(#(String, #(Option(Type), Option(Expr)))),
    tail: Option(Expr),
  )
  Ann(value: Expr, type_: Type)
  Fn(
    implicits: List(Param),
    implicits_tail: Option(Type),
    params: List(Param),
    params_tail: Option(Type),
    returns: Option(Type),
    body: Expr,
  )
  FnT(implicits: List(Param), params: List(Param), body: Expr)
  App(
    implicit: Bool,
    fun: Expr,
    args: List(#(String, Expr)),
    tail: Option(Expr),
  )
  Match(arg: Expr, cases: List(Case))
  Op1(op: UnaryOp, expr: Expr)
  Op2(op: BinaryOp, lhs: Expr, rhs: Expr)
  Call(name: String, ret: Type, args: List(Expr))
  Do(Block)
  Err
}

pub type UnaryOp {
  Neg
}

pub type BinaryOp {
  Add
  Sub
  Mul
  Div
}

pub fn binop_name(op: BinaryOp) -> String {
  case op {
    Add -> "+"
    Sub -> "-"
    Mul -> "*"
    Div -> "/"
  }
}

pub type Block =
  List(Stmt)

pub type Stmt {
  Stmt(data: StmtData, span: Span)
}

pub type StmtData {
  Import(
    path: String,
    alias: Option(String),
    names: List(#(String, Option(String))),
  )
  Let(pattern: Pattern, opt_type: Option(Type), value: Expr)
  LetMut(name: String, opt_type: Option(Type), value: Expr)
  Mut(name: String, value: Expr)
  Test(name: String, expr: Expr, expect: Pattern)
  FnDef(
    name: String,
    implicits: List(Param),
    implicits_tail: Option(Type),
    params: List(Param),
    params_tail: Option(Type),
    returns: Option(Type),
    body: Expr,
  )
  FnOverload(name: String, choices: List(OverloadChoice))
  TypeDef(type_def: TypeDefinition)
  For(iterator: Pattern, range: Expr, body: Expr)
  While(condition: Expr, body: Expr)
  Return(expr: Expr)
  Break
  Continue
}

pub type OverloadChoice {
  OverloadChoice(
    module: Option(String),
    name: String,
    args: List(#(String, Pattern)),
    guard: Option(#(Expr, Option(Pattern))),
    span: Span,
  )
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
  PRcd(fields: List(#(String, Pattern)), tail: Option(Pattern))
  PCtr(tag: String, args: List(#(String, Pattern)), tail: Option(Pattern))
}

pub type Case {
  Case(pattern: Pattern, guard: Option(#(Expr, Option(Pattern))), body: Expr)
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

pub fn hole(id: Option(Int), span: Span) {
  Expr(Hole(id), span)
}

pub fn int(value: Int, span: Span) {
  Expr(Lit(lit.Int(value)), span)
}

pub fn float(value: Float, span: Span) {
  Expr(Lit(lit.Float(value)), span)
}

pub fn int_t(span: Span) {
  ctr0("Int", span)
}

pub fn var(name: String, span: Span) {
  Expr(Var(name), span)
}

pub fn rcd(
  fields: List(#(String, Option(Expr))),
  tail: Option(Expr),
  span: Span,
) {
  Expr(Rcd(fields, tail), span)
}

pub fn rcd_vars(vars: List(String), tail: Option(Expr), span: Span) {
  let fields = list.map(vars, fn(name) { #(name, Some(var(name, span))) })
  rcd(fields, tail, span)
}

pub fn rcd_t(
  fields: List(#(String, #(Option(Type), Option(Expr)))),
  tail: Option(Expr),
  span: Span,
) {
  Expr(RcdT(fields, tail), span)
}

pub fn ctr(tag: String, args: List(#(String, Expr)), span: Span) {
  ctr_open(tag, args, None, span)
}

pub fn ctr_open(
  tag: String,
  args: List(#(String, Expr)),
  tail: Option(Expr),
  span: Span,
) {
  Expr(Ctr(tag, args, tail), span)
}

pub fn ctr0(tag: String, span: Span) {
  ctr(tag, [], span)
}

pub fn ann(expr: Expr, type_: Type, span: Span) {
  Expr(Ann(expr, type_), span)
}

pub fn app(implicit: Bool, fun: Expr, args: List(#(String, Expr)), span: Span) {
  app_open(implicit, fun, args, None, span)
}

pub fn app_open(
  implicit: Bool,
  fun: Expr,
  args: List(#(String, Expr)),
  args_tail: Option(Expr),
  span: Span,
) {
  Expr(App(implicit, fun, args, args_tail), span)
}

pub fn app_explicit(fun: Expr, args: List(#(String, Expr)), span: Span) {
  app(False, fun, args, span)
}

pub fn app_implicit(fun: Expr, args: List(#(String, Expr)), span: Span) {
  app(True, fun, args, span)
}

pub fn match(arg: Expr, cases: List(Case), span: Span) {
  Expr(Match(arg, cases), span)
}

pub fn op1(op: UnaryOp, expr: Expr, span: Span) {
  Expr(Op1(op, expr), span)
}

pub fn neg(expr: Expr, span: Span) {
  op1(Neg, expr, span)
}

pub fn op2(op: BinaryOp, lhs: Expr, rhs: Expr, span: Span) {
  Expr(Op2(op, lhs, rhs), span)
}

pub fn add(lhs: Expr, rhs: Expr, span: Span) {
  op2(Add, lhs, rhs, span)
}

pub fn sub(lhs: Expr, rhs: Expr, span: Span) {
  op2(Sub, lhs, rhs, span)
}

pub fn mul(lhs: Expr, rhs: Expr, span: Span) {
  op2(Mul, lhs, rhs, span)
}

pub fn div(lhs: Expr, rhs: Expr, span: Span) {
  op2(Div, lhs, rhs, span)
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

pub fn prcd(fields: List(#(String, Pattern)), span: Span) {
  prcd_open(fields, Some(pany(span)), span)
}

pub fn prcd_strict(fields: List(#(String, Pattern)), span: Span) {
  prcd_open(fields, None, span)
}

pub fn prcd_open(
  fields: List(#(String, Pattern)),
  tail: Option(Pattern),
  span: Span,
) {
  Pattern(PRcd(fields, tail), span)
}

pub fn pctr(tag: String, args: List(#(String, Pattern)), span: Span) {
  Pattern(PCtr(tag, args, None), span)
}

pub fn pctr_open(
  tag: String,
  args: List(#(String, Pattern)),
  tail: Option(Pattern),
  span: Span,
) {
  Pattern(PCtr(tag, args, tail), span)
}

pub fn import_(
  path: String,
  alias: Option(String),
  names: List(#(String, Option(String))),
  span: Span,
) {
  Stmt(Import(path, alias, names), span)
}

pub fn let_(pattern: Pattern, opt_type: Option(Type), value: Expr, span: Span) {
  Stmt(Let(pattern, opt_type, value), span)
}

pub fn fn_def(
  name: String,
  implicits: List(Param),
  params: List(Param),
  returns: Option(Type),
  body: Expr,
  span: Span,
) {
  fn_def_open(name, implicits, None, params, None, returns, body, span)
}

pub fn fn_def_open(
  name: String,
  implicits: List(Param),
  implicits_tail: Option(Type),
  params: List(Param),
  params_tail: Option(Type),
  returns: Option(Type),
  body: Expr,
  span: Span,
) {
  Stmt(
    FnDef(name, implicits, implicits_tail, params, params_tail, returns, body),
    span,
  )
}

pub fn fn_overload(name: String, choices: List(OverloadChoice), span: Span) {
  Stmt(FnOverload(name, choices), span)
}

pub fn test_(name: String, expr: Expr, expect: Pattern, span: Span) {
  Stmt(Test(name, expr, expect), span)
}

pub fn return(expr: Expr, span: Span) {
  Stmt(Return(expr), span)
}
