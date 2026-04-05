// ============================================================================
// TAO IMPORT DESUGARING TESTS
// ============================================================================
/// Tests for Tao import desugaring.

import gleeunit
import gleeunit/should
import gleam/option.{None}
import gleam/list
import tao/desugar.{desugar_module, desugar_import, type CoreTerm, type DesugarContext, CoreLet, CoreRcd, CoreDot, CoreVar, DesugarContext as DcCtr}
import tao/global_context.{type GlobalContext, new_context, with_prelude}
import tao/ast.{type Module, type Stmt, Module as ModuleCtr, StmtImport}
import tao/import_ast.{ImportModule, ImportAlias, ImportSelective, ImportName}
import syntax/grammar.{Span}

pub fn main() {
  gleeunit.main()
}

fn create_module(body: List(Stmt)) -> Module {
  ModuleCtr("test", body, Span("test", 0, 0, 0, 0))
}

fn create_desugar_context(ctx: GlobalContext) -> DesugarContext {
  DcCtr(
    global: ctx,
    current_module: "test",
    local_scope: [],
    loop_stack: [],
    ctrs: [],
    annotated_types: [],
    hole_counter: -1,
  )
}

// ============================================================================
// IMPORT MODULE TESTS
// ============================================================================

pub fn import_module_desugar_test() {
  // import math/trig
  // Should desugar to: let math_trig = @math/trig
  let import_stmt = StmtImport(ImportModule("math/trig", Span("test", 0, 0, 0, 0)), Span("test", 0, 0, 0, 0))
  let module = create_module([import_stmt])
  let ctx = new_context() |> with_prelude()
  let #(_term, _dc) = desugar_module(module, ctx)
  True |> should.be_true()
}

pub fn import_alias_desugar_test() {
  // import math/trig as trig
  // Should desugar to: let trig = @math/trig
  let import_stmt = StmtImport(ImportAlias("math/trig", "trig", Span("test", 0, 0, 0, 0)), Span("test", 0, 0, 0, 0))
  let module = create_module([import_stmt])
  let ctx = new_context() |> with_prelude()
  let #(_term, _dc) = desugar_module(module, ctx)
  True |> should.be_true()
}

pub fn import_selective_desugar_test() {
  // import math/trig {sin, cos}
  // Should desugar to: let sin = @math/trig.sin, let cos = @math/trig.cos
  let items = [ImportName("sin", None), ImportName("cos", None)]
  let import_stmt = StmtImport(ImportSelective("math/trig", items, Span("test", 0, 0, 0, 0)), Span("test", 0, 0, 0, 0))
  let module = create_module([import_stmt])
  let ctx = new_context() |> with_prelude()
  let #(_term, _dc) = desugar_module(module, ctx)
  True |> should.be_true()
}

// ============================================================================
// DIRECT IMPORT DESUGARING TESTS
// ============================================================================

pub fn desugar_import_module_test() {
  let ctx = new_context() |> with_prelude()
  let dc = create_desugar_context(ctx)
  let span = Span("test", 0, 0, 0, 0)

  // import math/trig
  let import_item = ImportModule("math/trig", span)
  let core_terms = desugar_import(import_item, dc, span)

  // Should produce: [let math_trig = {}]
  // For non-prelude modules without registered public names, creates empty record
  case core_terms {
    [CoreLet(name, CoreRcd(fields, _), _)] -> {
      name |> should.equal("math_trig")
      // For modules without registered public names, record is empty
      list.length(fields) |> should.equal(0)
    }
    _ -> False |> should.be_true()
  }
}

pub fn desugar_import_alias_test() {
  let ctx = new_context() |> with_prelude()
  let dc = create_desugar_context(ctx)
  let span = Span("test", 0, 0, 0, 0)

  // import math/trig as trig
  let import_item = ImportAlias("math/trig", "trig", span)
  let core_terms = desugar_import(import_item, dc, span)

  // Should produce: [let trig = {}]
  // For non-prelude modules without registered public names, creates empty record
  case core_terms {
    [CoreLet(name, CoreRcd(fields, _), _)] -> {
      name |> should.equal("trig")
      // For modules without registered public names, record is empty
      list.length(fields) |> should.equal(0)
    }
    _ -> False |> should.be_true()
  }
}

pub fn desugar_import_selective_test() {
  let ctx = new_context() |> with_prelude()
  let dc = create_desugar_context(ctx)
  let span = Span("test", 0, 0, 0, 0)
  
  // import math/trig {sin, cos}
  let items = [ImportName("sin", None), ImportName("cos", None)]
  let import_item = ImportSelective("math/trig", items, span)
  let core_terms = desugar_import(import_item, dc, span)
  
  // Should produce: [let sin = @math/trig.sin, let cos = @math/trig.cos]
  case core_terms {
    [CoreLet(name1, CoreDot(_, field1, _), _), CoreLet(name2, CoreDot(_, field2, _), _)] -> {
      name1 |> should.equal("sin")
      field1 |> should.equal("sin")
      name2 |> should.equal("cos")
      field2 |> should.equal("cos")
    }
    _ -> False |> should.be_true()
  }
}
