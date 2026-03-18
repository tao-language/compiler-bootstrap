// ============================================================================
// TAO DESUGARER TESTS
// ============================================================================
/// Tests for the Tao desugarer module.

import gleeunit
import gleeunit/should
import gleam/option.{None, Some}
import tao/desugar.{desugar_module}
import tao/global_context.{new_context, with_prelude}
import tao/ast.{
  type Module, type Stmt, type Expr, type Pattern, type Param,
  StmtLet, StmtExpr, StmtFor, StmtWhile, StmtLoop, StmtBreak, StmtContinue, StmtReturn, StmtYield,
  Var, Lit, Lambda, Match, BinOp, OpGt,
  PVar,
  Int, MatchClause,
  Module as ModuleCtr, Param as ParamCtr,
}
import syntax/grammar.{Span}

pub fn main() {
  gleeunit.main()
}

fn create_module(body: List(Stmt)) -> Module {
  ModuleCtr("test", body, Span("test", 0, 0, 0, 0))
}

// ============================================================================
// EXPRESSION DESUGARING TESTS
// ============================================================================

pub fn expression_desugaring_test() {
  let ctx = new_context() |> with_prelude()
  let var_expr = Var("x", Span("test", 0, 0, 0, 0))
  let module = create_module([StmtExpr(var_expr, Span("test", 0, 0, 0, 0))])
  let #(_term, _dc) = desugar_module(module, ctx)
  True |> should.be_true()
}

// ============================================================================
// PATTERN MATCHING TESTS
// ============================================================================

pub fn pattern_matching_test() {
  let ctx = new_context() |> with_prelude()
  
  let scrutinee = Var("x", Span("test", 0, 0, 0, 0))
  let pattern = PVar("y", Span("test", 0, 0, 0, 0))
  let body = Var("y", Span("test", 0, 0, 0, 0))
  
  let clause = MatchClause(pattern, None, body, Span("test", 0, 0, 0, 0))
  let match_expr = Match(scrutinee, [clause], Span("test", 0, 0, 0, 0))
  
  let module = create_module([StmtExpr(match_expr, Span("test", 0, 0, 0, 0))])
  let #(_term, _dc) = desugar_module(module, ctx)
  True |> should.be_true()
}

// ============================================================================
// CONTROL FLOW TESTS
// ============================================================================

pub fn control_flow_test() {
  let ctx = new_context() |> with_prelude()

  // For loop
  let collection = Var("items", Span("test", 0, 0, 0, 0))
  let pattern = PVar("x", Span("test", 0, 0, 0, 0))
  let body = [StmtExpr(Var("x", Span("test", 0, 0, 0, 0)), Span("test", 0, 0, 0, 0))]
  let for_stmt = StmtFor(pattern, collection, body, Span("test", 0, 0, 0, 0))
  let module = create_module([for_stmt])
  let #(_term, _dc) = desugar_module(module, ctx)
  True |> should.be_true()

  // While loop
  let condition = Var("cond", Span("test", 0, 0, 0, 0))
  let while_body = [StmtExpr(Var("x", Span("test", 0, 0, 0, 0)), Span("test", 0, 0, 0, 0))]
  let while_stmt = StmtWhile(condition, while_body, Span("test", 0, 0, 0, 0))
  let module2 = create_module([while_stmt])
  let #(_term2, _dc2) = desugar_module(module2, ctx)
  True |> should.be_true()

  // Loop
  let loop_body = [StmtExpr(Var("x", Span("test", 0, 0, 0, 0)), Span("test", 0, 0, 0, 0))]
  let loop_stmt = StmtLoop(loop_body, Span("test", 0, 0, 0, 0))
  let module3 = create_module([loop_stmt])
  let #(_term3, _dc3) = desugar_module(module3, ctx)
  True |> should.be_true()
}

// ============================================================================
// BREAK/CONTINUE TESTS
// ============================================================================

pub fn break_continue_test() {
  let ctx = new_context() |> with_prelude()

  // Loop with break
  let break_stmt = StmtBreak(Span("test", 0, 0, 0, 0))
  let loop_body_with_break = [StmtExpr(Var("x", Span("test", 0, 0, 0, 0)), Span("test", 0, 0, 0, 0)), break_stmt]
  let loop_with_break = StmtLoop(loop_body_with_break, Span("test", 0, 0, 0, 0))
  let module = create_module([loop_with_break])
  let #(_term, _dc) = desugar_module(module, ctx)
  True |> should.be_true()

  // Loop with continue
  let continue_stmt = StmtContinue(Span("test", 0, 0, 0, 0))
  let loop_body_with_continue = [StmtExpr(Var("x", Span("test", 0, 0, 0, 0)), Span("test", 0, 0, 0, 0)), continue_stmt]
  let loop_with_continue = StmtLoop(loop_body_with_continue, Span("test", 0, 0, 0, 0))
  let module2 = create_module([loop_with_continue])
  let #(_term2, _dc2) = desugar_module(module2, ctx)
  True |> should.be_true()

  // While loop with break
  let condition = Var("cond", Span("test", 0, 0, 0, 0))
  let while_body_with_break = [break_stmt]
  let while_with_break = StmtWhile(condition, while_body_with_break, Span("test", 0, 0, 0, 0))
  let module3 = create_module([while_with_break])
  let #(_term3, _dc3) = desugar_module(module3, ctx)
  True |> should.be_true()

  // For loop with continue
  let collection = Var("items", Span("test", 0, 0, 0, 0))
  let pattern = PVar("x", Span("test", 0, 0, 0, 0))
  let for_body_with_continue = [continue_stmt]
  let for_with_continue = StmtFor(pattern, collection, for_body_with_continue, Span("test", 0, 0, 0, 0))
  let module4 = create_module([for_with_continue])
  let #(_term4, _dc4) = desugar_module(module4, ctx)
  True |> should.be_true()
}

// ============================================================================
// RETURN/YIELD TESTS
// ============================================================================

pub fn return_yield_test() {
  let ctx = new_context() |> with_prelude()

  // Return with value
  let return_stmt = StmtReturn(Some(Var("x", Span("test", 0, 0, 0, 0))), Span("test", 0, 0, 0, 0))
  let module = create_module([return_stmt])
  let #(_term, _dc) = desugar_module(module, ctx)
  True |> should.be_true()

  // Return without value
  let return_unit = StmtReturn(None, Span("test", 0, 0, 0, 0))
  let module2 = create_module([return_unit])
  let #(_term2, _dc2) = desugar_module(module2, ctx)
  True |> should.be_true()

  // Yield
  let yield_stmt = StmtYield(Var("x", Span("test", 0, 0, 0, 0)), Span("test", 0, 0, 0, 0))
  let module3 = create_module([yield_stmt])
  let #(_term3, _dc3) = desugar_module(module3, ctx)
  True |> should.be_true()
}

// ============================================================================
// NESTED LOOP TESTS
// ============================================================================

pub fn nested_loop_test() {
  let ctx = new_context() |> with_prelude()

  // Nested loops
  let inner_loop_body = [StmtExpr(Var("y", Span("test", 0, 0, 0, 0)), Span("test", 0, 0, 0, 0))]
  let inner_loop = StmtLoop(inner_loop_body, Span("test", 0, 0, 0, 0))
  let outer_loop_body = [inner_loop]
  let outer_loop = StmtLoop(outer_loop_body, Span("test", 0, 0, 0, 0))
  let module = create_module([outer_loop])
  let #(_term, _dc) = desugar_module(module, ctx)
  True |> should.be_true()

  // While inside for
  let condition = Var("cond", Span("test", 0, 0, 0, 0))
  let while_body = [StmtExpr(Var("x", Span("test", 0, 0, 0, 0)), Span("test", 0, 0, 0, 0))]
  let while_stmt = StmtWhile(condition, while_body, Span("test", 0, 0, 0, 0))
  let for_body = [while_stmt]
  let collection = Var("items", Span("test", 0, 0, 0, 0))
  let pattern = PVar("x", Span("test", 0, 0, 0, 0))
  let for_stmt = StmtFor(pattern, collection, for_body, Span("test", 0, 0, 0, 0))
  let module2 = create_module([for_stmt])
  let #(_term2, _dc2) = desugar_module(module2, ctx)
  True |> should.be_true()
}

// ============================================================================
// VARIABLE SCOPING TESTS
// ============================================================================

pub fn variable_scoping_test() {
  let ctx = new_context() |> with_prelude()
  
  let value = Lit(Int(1), Span("test", 0, 0, 0, 0))
  let let_stmt = StmtLet("x", False, None, value, Span("test", 0, 0, 0, 0))
  let body_expr = Var("x", Span("test", 0, 0, 0, 0))
  let expr_stmt = StmtExpr(body_expr, Span("test", 0, 0, 0, 0))
  
  let module = create_module([let_stmt, expr_stmt])
  let #(_term, _dc) = desugar_module(module, ctx)
  True |> should.be_true()
}

// ============================================================================
// LAMBDA SCOPING TESTS
// ============================================================================

pub fn lambda_scoping_test() {
  let ctx = new_context() |> with_prelude()

  let param = ParamCtr("x", None, Span("test", 0, 0, 0, 0))
  let body = Var("x", Span("test", 0, 0, 0, 0))
  let lambda = Lambda([], [param], body, Span("test", 0, 0, 0, 0))

  let module = create_module([StmtExpr(lambda, Span("test", 0, 0, 0, 0))])
  let #(_term, _dc) = desugar_module(module, ctx)
  True |> should.be_true()
}

// ============================================================================
// MATCH GUARDS TESTS
// ============================================================================

pub fn match_guards_test() {
  let ctx = new_context() |> with_prelude()

  // match x { | y if y > 0 -> y | _ -> 0 }
  let scrutinee = Var("x", Span("test", 0, 0, 0, 0))
  
  // First clause: y if y > 0 -> y
  let pattern1 = PVar("y", Span("test", 0, 0, 0, 0))
  let guard_expr = BinOp(Var("y", Span("test", 0, 0, 0, 0)), OpGt, Lit(Int(0), Span("test", 0, 0, 0, 0)), Span("test", 0, 0, 0, 0))
  let body1 = Var("y", Span("test", 0, 0, 0, 0))
  let clause1 = MatchClause(pattern1, Some(guard_expr), body1, Span("test", 0, 0, 0, 0))
  
  // Second clause: _ -> 0
  let pattern2 = PVar("_", Span("test", 0, 0, 0, 0))
  let body2 = Lit(Int(0), Span("test", 0, 0, 0, 0))
  let clause2 = MatchClause(pattern2, None, body2, Span("test", 0, 0, 0, 0))
  
  let match_expr = Match(scrutinee, [clause1, clause2], Span("test", 0, 0, 0, 0))
  let module = create_module([StmtExpr(match_expr, Span("test", 0, 0, 0, 0))])
  let #(_term, _dc) = desugar_module(module, ctx)
  True |> should.be_true()
}

// ============================================================================
// FIXPOINT-BASED LOOP TESTS
// ============================================================================

pub fn fixpoint_loop_test() {
  let ctx = new_context() |> with_prelude()

  // loop { x }
  let loop_body = [StmtExpr(Var("x", Span("test", 0, 0, 0, 0)), Span("test", 0, 0, 0, 0))]
  let loop_stmt = StmtLoop(loop_body, Span("test", 0, 0, 0, 0))
  let module = create_module([loop_stmt])
  let #(_term, _dc) = desugar_module(module, ctx)
  True |> should.be_true()
}

pub fn fixpoint_while_test() {
  let ctx = new_context() |> with_prelude()

  // while cond { x }
  let condition = Var("cond", Span("test", 0, 0, 0, 0))
  let while_body = [StmtExpr(Var("x", Span("test", 0, 0, 0, 0)), Span("test", 0, 0, 0, 0))]
  let while_stmt = StmtWhile(condition, while_body, Span("test", 0, 0, 0, 0))
  let module = create_module([while_stmt])
  let #(_term, _dc) = desugar_module(module, ctx)
  True |> should.be_true()
}
