/// Type checking of user-defined types (ADTs and GADTs) through the
/// full Tao pipeline (parse → declare → define → resolve).
///
/// These are the regression targets for the pipeline wiring of
/// `lookup_type_def`: type definitions are stored as concrete values in
/// phase 1, and constructor tags (which are not variables) resolve
/// through the module records.
import core/context.{Context, new_ctx}
import core/error.{display, display_syntax}
import core/ffi
import gleam/list
import tao/ast.{type Module}
import tao/compile
import tao/parse as p

const nl = "\n"

/// A monomorphic ADT: matching on it is well typed.
pub fn adt_color_test() {
  let src =
    "type Color { | Red | Blue }"
    <> nl
    <> "fn f(c: Color) -> Int ="
    <> nl
    <> "match c {"
    <> nl
    <> "| Red => 1"
    <> nl
    <> "| Blue => 2"
    <> nl
    <> "}"
  assert check(src) == []
}

/// A polymorphic ADT with a parameterized constructor.
pub fn adt_option_test() {
  let src =
    "type Option(a) { | Some(a) | None }"
    <> nl
    <> "fn f(o: Option(Int)) -> Int ="
    <> nl
    <> "match o {"
    <> nl
    <> "| Some(x) => x"
    <> nl
    <> "| None => 0"
    <> nl
    <> "}"
  assert check(src) == []
}

/// A recursive ADT: the self-reference is a constructor tag, so it
/// resolves through the module record at unification time.
pub fn adt_list_test() {
  let src =
    "type List(a: Type) { | Cons(x: a, xs: List(a)) | Nil }"
    <> nl
    <> "fn f(l: List(Int)) -> Bool ="
    <> nl
    <> "match l {"
    <> nl
    <> "| Cons(h, t) => True"
    <> nl
    <> "| Nil => False"
    <> nl
    <> "}"
  assert check(src) == []
}

/// A GADT: a `LitInt` case against `Expr(Int)` is well typed.
pub fn gadt_expr_test() {
  let src =
    expr_type
    <> nl
    <> "fn f(e: Expr(Int)) -> Int ="
    <> nl
    <> "match e {"
    <> nl
    <> "| LitInt(n) => n"
    <> nl
    <> "| _ => 0"
    <> nl
    <> "}"
  assert check(src) == []
}

/// A GADT: a `LitInt` case against `Expr(Bool)` is impossible — the
/// variant's return type `Expr(Int)` conflicts with the expected
/// `Expr(Bool)`.
pub fn gadt_impossible_case_test() {
  let src =
    expr_type
    <> nl
    <> "fn f(e: Expr(Bool)) -> Int ="
    <> nl
    <> "match e {"
    <> nl
    <> "| LitInt(n) => n"
    <> nl
    <> "| _ => 0"
    <> nl
    <> "}"
  assert check(src) != []
}

const expr_type = "type Expr(a) { | LitInt(Int) -> Expr(Int) | LitBool(Bool) -> Expr(Bool) | IsZero(Expr(Int)) -> Expr(Bool) }"

/// A function whose parameter annotation mentions a sibling parameter
/// (`expr: Expr(a)`) must not panic in the definition phase, and an
/// evaluator over the GADT is well typed.
pub fn gadt_sibling_param_test() {
  let src =
    expr_type
    <> nl
    <> "fn eval(a: Type, e: Expr(a)) -> Int ="
    <> nl
    <> "match e {"
    <> nl
    <> "| LitInt(n) => n"
    <> nl
    <> "| _ => 0"
    <> nl
    <> "}"
  assert check(src) == []
}

/// Unannotated parameters (inferred types) still work, alone and
/// mixed with annotations.
pub fn fn_unannotated_params_test() {
  let src = "fn f(x) = x" <> nl <> "fn g(x: Int, y) = y"
  assert check(src) == []
}

/// Compile an in-memory module and return its reported errors (or a
/// parse error message).
fn check(source: String) -> List(String) {
  case p.statements("scratch", source) {
    Ok(stmts) -> {
      let mods: List(Module) = [#("scratch", stmts)]
      let ctx =
        Context(..new_ctx, ffi: ffi.build)
        |> compile.modules(mods)
      list.map(ctx.errors, fn(err) { display(ffi.build, ctx.types, err) })
    }
    Error(err) -> ["PARSE: " <> display_syntax(err)]
  }
}
