// ============================================================================
// TAO DESUGARER
// ============================================================================
/// Desugar Tao AST to Core terms.
///
/// Converts Tao statements to Core terms:
/// - Imports → let aliases (e.g., `import math as *` → `let math = @math`)
/// - Functions → let bindings with lambdas
/// - Modules → DoBlock returning Record of public names
///
/// For detailed documentation see:
/// - [Stmt System](../../docs/plans/tao/13-stmt-system.md)
/// - [Import System](../../docs/plans/tao/12-import-system.md)

import gleam/list
import gleam/int
import gleam/float
import gleam/option.{type Option, Some, None}
import gleam/string
import syntax/grammar.{type Span, Span}
import tao/ast.{
  type Module, type Stmt, type Expr, type Param, type Pattern,
  type Literal, type BinOperator, type UnaryOperator,
  type RecordField, type MatchClause, type BlockStatement, type LetDecl,
  StmtLet, StmtFn, StmtImport, StmtExpr,
  StmtFor, StmtWhile, StmtLoop, StmtBreak, StmtContinue, StmtReturn, StmtYield,
  BlockStmtLet, BlockStmtAssign, BlockStmtExpr,
  OpAdd, OpSub, OpMul, OpDiv, OpMod, OpEq, OpNeq, OpLt, OpGt, OpLte, OpGte,
  OpAnd, OpOr, OpConcat, OpPipe, OpNegate, OpNot,
  Int, Float, String,
  RecordUpdate, OptionalChain, LetExpr,
  get_public_names, get_stmt_name, span_from_expr,
}
import tao/global_context.{
  type GlobalContext, type ModuleRef,
  get_module, has_module, get_module_public_names,
  module_base_name, is_prelude_module,
}
import tao/import_ast.{
  type Import, ImportModule, ImportAlias, ImportSelective,
  ImportSelectiveAlias, ImportWildcard,
  type ImportItem, ImportName, ImportType, ImportOperator,
}
import core/core.{type Term, Err, Var, Rcd, Dot, Lit, Unit, Call, Lam, App, Typ, I32}

// ============================================================================
// CORE TERM TYPES (simplified for desugaring)
// ============================================================================
/// Simplified Core term representation for desugaring.
/// Full Core terms are in src/core/core.gleam

pub type CoreTerm {
  /// Variable reference
  CoreVar(name: String, span: Span)
  
  /// Module reference (@path)
  CoreModuleRef(path: String, span: Span)
  
  /// Lambda abstraction
  CoreLam(param: String, body: CoreTerm, span: Span)
  
  /// Function application
  CoreApp(fun: CoreTerm, arg: CoreTerm, span: Span)
  
  /// Record construction
  CoreRcd(fields: List(#(String, CoreTerm)), span: Span)
  
  /// Field projection
  CoreDot(record: CoreTerm, field: String, span: Span)
  
  /// Let binding (in DoBlock)
  CoreLet(name: String, value: CoreTerm, span: Span)
  
  /// DoBlock (sequence of statements)
  CoreDoBlock(stmts: List(CoreTerm), result: CoreTerm, span: Span)
  
  /// Literal
  CoreLit(value: String, span: Span)
  
  /// Error placeholder
  CoreErr(message: String, span: Span)
}

// ============================================================================
// DESUGAR CONTEXT
// ============================================================================

pub type DesugarContext {
  DesugarContext(
    global: GlobalContext,
    current_module: String,
    /// Local variable bindings as a stack (for De Bruijn index conversion)
    /// The index in the list represents the De Bruijn index
    local_scope: List(String),
  )
}

/// Add a local variable to the scope.
fn add_local(dc: DesugarContext, name: String) -> DesugarContext {
  let DesugarContext(global, current_module, local_scope) = dc
  DesugarContext(global, current_module, [name, ..local_scope])
}

/// Look up a variable name and return its De Bruijn index.
fn lookup_var(dc: DesugarContext, name: String) -> Option(Int) {
  lookup_var_loop(dc.local_scope, name, 0)
}

fn lookup_var_loop(
  scope: List(String),
  name: String,
  index: Int,
) -> Option(Int) {
  case scope {
    [] -> None
    [x, ..rest] -> {
      case x == name {
        True -> Some(index)
        False -> lookup_var_loop(rest, name, index + 1)
      }
    }
  }
}

// ============================================================================
// PUBLIC API
// ============================================================================

/// Desugar a Tao module to a Core term.
pub fn desugar_module(
  module: Module,
  ctx: GlobalContext,
) -> #(Term, DesugarContext) {
  let dc = DesugarContext(
    global: ctx,
    current_module: module.path,
    local_scope: [],
  )

  // Desugar all statements
  let #(core_stmts, dc1) = desugar_stmts(module.body, dc)

  // Get public names for return record
  let public_names = get_public_names(module.body)
  let return_fields = list.map(public_names, fn(name) {
    #(name, CoreVar(name, module.span))
  })

  // Build DoBlock with Record return
  let result = CoreRcd(return_fields, module.span)
  let core_term = CoreDoBlock(core_stmts, result, module.span)
  
  // Convert to core/core.Term
  let term = core_term_to_term(core_term)

  #(term, dc1)
}

/// Desugar a list of statements.
pub fn desugar_stmts(
  stmts: List(Stmt),
  dc: DesugarContext,
) -> #(List(CoreTerm), DesugarContext) {
  desugar_stmts_loop(stmts, [], dc)
}

fn desugar_stmts_loop(
  stmts: List(Stmt),
  acc: List(CoreTerm),
  dc: DesugarContext,
) -> #(List(CoreTerm), DesugarContext) {
  case stmts {
    [] -> #(list.reverse(acc), dc)
    [stmt, ..rest] -> {
      let #(core_stmt, dc1) = desugar_stmt(stmt, dc)
      desugar_stmts_loop(rest, [core_stmt, ..acc], dc1)
    }
  }
}

/// Desugar a single statement to Core terms.
pub fn desugar_stmt(
  stmt: Stmt,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  case stmt {
    StmtLet(name, mutable, type_ann, value, span) -> {
      let #(core_value, dc1) = desugar_expr_core(value, dc)
      let core_let = CoreLet(name, core_value, span)
      let dc2 = add_local(dc1, name)
      #(core_let, dc2)
    }
    
    StmtFn(name, type_params, params, return_type, body, span) -> {
      // Function → let name = λparam1. λparam2. ... body
      let #(core_body, dc1) = desugar_expr_core(body, dc)
      let core_lam = build_lambda(params, core_body, span)
      let core_let = CoreLet(name, core_lam, span)
      let dc2 = add_local(dc1, name)
      #(core_let, dc2)
    }
    
    StmtImport(import_item, span) -> {
      // Import → let aliases
      let core_terms = desugar_import(import_item, dc, span)
      // Return first term, rest are handled separately
      case core_terms {
        [first, ..rest] -> {
          // For now, just return the first binding
          // In a full implementation, we'd handle multiple bindings
          let dc1 = add_import_bindings(dc, core_terms)
          #(first, dc1)
        }
        [] -> #(CoreErr("Empty import", span), dc)
      }
    }
    
    StmtExpr(value, span) -> {
      let #(core_expr, dc1) = desugar_expr_core(value, dc)
      #(core_expr, dc1)
    }

    StmtFor(pattern, collection, body, span) -> {
      // for pattern in collection { body... }
      // Desugar to: iterate over collection, binding pattern for each iteration
      desugar_for(pattern, collection, body, span, dc)
    }

    StmtWhile(condition, body, span) -> {
      // while condition { body... }
      // Desugar to: recursive fixpoint that checks condition and executes body
      desugar_while(condition, body, span, dc)
    }

    StmtLoop(body, span) -> {
      // loop { body... }
      // Desugar to: infinite loop using fixpoint
      desugar_loop(body, span, dc)
    }

    StmtBreak(span) -> {
      // break - exit current loop
      // Desugar to: special break marker (simplified: return unit)
      #(CoreRcd([], span), dc)
    }

    StmtContinue(span) -> {
      // continue - skip to next iteration
      // Desugar to: special continue marker (simplified: return unit)
      #(CoreRcd([], span), dc)
    }

    StmtReturn(value, span) -> {
      // return [expr] - return from function
      // Desugar to: the return value (or unit if none)
      case value {
        Some(expr) -> desugar_expr_core(expr, dc)
        None -> #(CoreRcd([], span), dc)
      }
    }

    StmtYield(value, span) -> {
      // yield expr - produce a value in a generator
      // Desugar to: the yielded expression
      desugar_expr_core(value, dc)
    }

    // Fallback for unimplemented statements
    _ -> #(CoreErr("Statement not yet implemented", get_stmt_span(stmt)), dc)
  }
}

/// Get span from any statement.
fn get_stmt_span(stmt: Stmt) -> Span {
  case stmt {
    StmtLet(_, _, _, _, span) -> span
    StmtFn(_, _, _, _, _, span) -> span
    StmtImport(_, span) -> span
    StmtExpr(_, span) -> span
    StmtFor(_, _, _, span) -> span
    StmtWhile(_, _, span) -> span
    StmtLoop(_, span) -> span
    StmtBreak(span) -> span
    StmtContinue(span) -> span
    StmtReturn(_, span) -> span
    StmtYield(_, span) -> span
    _ -> Span("unknown", 0, 0, 0, 0)
  }
}

// ============================================================================
// IMPORT DESUGARING
// ============================================================================

/// Desugar an import statement to let bindings.
pub fn desugar_import(
  import_item: Import,
  dc: DesugarContext,
  span: Span,
) -> List(CoreTerm) {
  case import_item {
    ImportModule(path, _) -> {
      // import math/trig → let math_trig = @math/trig
      let alias = path_to_alias(path)
      [CoreLet(alias, CoreModuleRef(path, span), span)]
    }
    
    ImportAlias(path, alias, _) -> {
      // import math/trig as trig → let trig = @math/trig
      [CoreLet(alias, CoreModuleRef(path, span), span)]
    }
    
    ImportSelective(path, items, _) -> {
      // import math/trig {sin, cos} → let sin = @math/trig.sin
      let module_ref = CoreModuleRef(path, span)
      list.flat_map(items, fn(item) {
        desugar_import_item(item, module_ref, path, span)
      })
    }
    
    ImportSelectiveAlias(path, alias, items, _) -> {
      // import math/trig as trig {sin, cos}
      // → let trig = @math/trig
      //   let sin = trig.sin
      //   let cos = trig.cos
      let module_binding = CoreLet(alias, CoreModuleRef(path, span), span)
      let item_bindings = list.flat_map(items, fn(item) {
        case item {
          ImportName(name, None) -> {
            [CoreLet(name, CoreDot(CoreVar(alias, span), name, span), span)]
          }
          ImportName(name, Some(item_alias)) -> {
            [CoreLet(item_alias, CoreDot(CoreVar(alias, span), name, span), span)]
          }
          _ -> []
        }
      })
      [module_binding, ..item_bindings]
    }
    
    ImportWildcard(path, _) -> {
      // import math/trig as * → let math_trig = @math/trig + all exports
      let alias = path_to_alias(path)
      let module_binding = CoreLet(alias, CoreModuleRef(path, span), span)
      
      // Get all exports from the module
      case get_module_public_names(dc.global, path) {
        Some(exports) -> {
          let export_bindings = list.map(exports, fn(name) {
            CoreLet(
              name,
              CoreDot(CoreVar(alias, span), name, span),
              span,
            )
          })
          [module_binding, ..export_bindings]
        }
        None -> [module_binding]
      }
    }
  }
}

/// Desugar a single import item.
fn desugar_import_item(
  item: ImportItem,
  module_ref: CoreTerm,
  path: String,
  span: Span,
) -> List(CoreTerm) {
  case item {
    ImportName(name, None) -> {
      [CoreLet(name, CoreDot(module_ref, name, span), span)]
    }
    ImportName(name, Some(alias)) -> {
      [CoreLet(alias, CoreDot(module_ref, name, span), span)]
    }
    ImportType(name, None) -> {
      // Type import - just bind the type
      [CoreLet(name, CoreDot(module_ref, name, span), span)]
    }
    ImportType(name, Some(alias)) -> {
      [CoreLet(alias, CoreDot(module_ref, name, span), span)]
    }
    ImportOperator(name, None) -> {
      // Operator import (e.g., "+")
      let var_name = string.replace(name, "+", "add")
      [CoreLet(var_name, CoreDot(module_ref, name, span), span)]
    }
    ImportOperator(name, Some(alias)) -> {
      [CoreLet(alias, CoreDot(module_ref, name, span), span)]
    }
  }
}

/// Convert a path to an alias.
fn path_to_alias(path: String) -> String {
  // math/trig → math_trig
  path
  |> string.replace("/", "_")
}

/// Add import bindings to context.
fn add_import_bindings(
  dc: DesugarContext,
  terms: List(CoreTerm),
) -> DesugarContext {
  list.fold(terms, dc, fn(acc, term) {
    case term {
      CoreLet(name, _, _) -> add_local(acc, name)
      _ -> acc
    }
  })
}

// ============================================================================
// CONTROL FLOW DESUGARING
// ============================================================================

/// Desugar a for loop.
fn desugar_for(
  pattern: Pattern,
  collection: Expr,
  body: List(Stmt),
  span: Span,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  // for pattern in collection { body... }
  // Desugar to: foldl/foreach over collection
  
  // Desugar the collection expression
  let #(core_collection, dc1) = desugar_expr_core(collection, dc)
  
  // Desugar the body statements
  let #(core_body_stmts, dc2) = desugar_stmts(body, dc1)
  
  // Bind the collection
  let collection_binding = CoreLet("_for_collection", core_collection, span)
  
  // For simple variable patterns, add pattern binding
  case pattern {
    ast.PVar(name, _pattern_span) -> {
      // for x in collection { body } → let x = _for_collection[i] in body
      let pattern_binding = CoreLet(name, CoreVar("_for_collection", span), span)
      let body_block = CoreDoBlock(core_body_stmts, CoreRcd([], span), span)
      let result = CoreDoBlock(
        [collection_binding, pattern_binding],
        body_block,
        span,
      )
      #(result, dc2)
    }
    ast.PAny(_pattern_span) -> {
      // for _ in collection { body } → just evaluate body
      let body_block = CoreDoBlock(core_body_stmts, CoreRcd([], span), span)
      let result = CoreDoBlock([collection_binding], body_block, span)
      #(result, dc2)
    }
    // For complex patterns, just bind collection and evaluate body
    _ -> {
      let body_block = CoreDoBlock(core_body_stmts, CoreRcd([], span), span)
      let result = CoreDoBlock([collection_binding], body_block, span)
      #(result, dc2)
    }
  }
}

/// Desugar a while loop.
fn desugar_while(
  condition: Expr,
  body: List(Stmt),
  span: Span,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  // while condition { body... }
  // Desugar to: recursive function that checks condition
  
  // Desugar the condition
  let #(core_condition, dc1) = desugar_expr_core(condition, dc)
  
  // Desugar the body statements
  let #(core_body_stmts, dc2) = desugar_stmts(body, dc1)
  
  // Bind the condition result
  let cond_binding = CoreLet("_while_cond", core_condition, span)
  
  // Body block
  let body_block = CoreDoBlock(core_body_stmts, CoreRcd([], span), span)
  
  // Simplified: just evaluate condition and body once
  // A full implementation would use fixpoint for recursion
  let result = CoreDoBlock([cond_binding], body_block, span)
  #(result, dc2)
}

/// Desugar an infinite loop.
fn desugar_loop(
  body: List(Stmt),
  span: Span,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  // loop { body... }
  // Desugar to: infinite recursion using fixpoint
  
  // Desugar the body statements
  let #(core_body_stmts, dc1) = desugar_stmts(body, dc)
  
  // Body block
  let body_block = CoreDoBlock(core_body_stmts, CoreRcd([], span), span)
  
  // Simplified: just evaluate body once
  // A full implementation would use fixpoint for infinite recursion
  #(body_block, dc1)
}

// ============================================================================
// EXPRESSION DESUGARING
// ============================================================================

/// Desugar an expression to a Core term.
pub fn desugar_expr(
  expr: Expr,
  dc: DesugarContext,
) -> #(Term, DesugarContext) {
  let #(core_term, dc1) = desugar_expr_core(expr, dc)
  #(core_term_to_term(core_term), dc1)
}

/// Desugar an expression to a CoreTerm (internal).
fn desugar_expr_core(
  expr: Expr,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  case expr {
    ast.Var(name, span) -> {
      // Variable reference - look up in scope for De Bruijn index
      case lookup_var(dc, name) {
        Some(index) -> {
          // Bound variable - use De Bruijn index
          #(CoreVar(name <> "@" <> int.to_string(index), span), dc)
        }
        None -> {
          // Free variable - keep as named variable
          #(CoreVar(name, span), dc)
        }
      }
    }
    
    ast.Lit(tao_lit, span) -> {
      // Literal - convert to Core literal
      let core_lit = literal_to_core(tao_lit, span)
      #(core_lit, dc)
    }
    
    ast.Lambda(type_params, params, body, span) -> {
      // Lambda - build nested lambdas for each param with proper scoping
      build_lambdas_with_scope(type_params, params, body, span, dc)
    }
    
    ast.Call(call_fun, call_args, span) -> {
      // Function call - desugar function and args
      let #(core_fun, dc1) = desugar_expr_core(call_fun, dc)
      let #(core_args, dc2) = desugar_exprs(call_args, dc1)
      let core_app = build_apps(core_fun, core_args, span)
      #(core_app, dc2)
    }
    
    ast.BinOp(left, op, right, span) -> {
      // Binary operator - convert to function call
      desugar_binop(left, op, right, span, dc)
    }
    
    ast.UnaryOp(op, expr, span) -> {
      // Unary operator - convert to function call
      desugar_unaryop(op, expr, span, dc)
    }
    
    ast.FieldAccess(record, field, span) -> {
      // Field access - desugar to Dot
      let #(core_record, dc1) = desugar_expr_core(record, dc)
      #(CoreDot(core_record, field, span), dc1)
    }
    
    ast.Record(fields, span) -> {
      // Record construction
      let #(core_fields, dc1) = desugar_record_fields(fields, dc)
      #(CoreRcd(core_fields, span), dc1)
    }
    
    ast.If(cond, then_expr, else_expr, span) -> {
      // If expression - convert to match on Bool
      desugar_if(cond, then_expr, else_expr, span, dc)
    }
    
    ast.Match(scrutinee, clauses, span) -> {
      // Match expression
      desugar_match(scrutinee, clauses, span, dc)
    }
    
    ast.Ctr(name, args, span) -> {
      // Constructor - convert to Ctr
      let #(core_args, dc1) = desugar_exprs(args, dc)
      let core_ctr = build_ctr(name, core_args, span)
      #(core_ctr, dc1)
    }
    
    ast.Tuple(exprs, span) -> {
      // Tuple - convert to Record with numeric fields
      desugar_tuple(exprs, span, dc)
    }
    
    ast.List(list_exprs, span) -> {
      // List - convert to nested Cons/Nil
      desugar_list(list_exprs, span, dc)
    }
    
    ast.Block(block_stmts, span) -> {
      // Block - desugar statements and return last expr
      desugar_block(block_stmts, span, dc)
    }
    
    ast.LetExpr(let_decl, body, span) -> {
      // Let expression - desugar binding and body
      desugar_let_expr(let_decl, body, span, dc)
    }
    
    ast.OptionalChain(expr, field, span) -> {
      // Optional chaining - convert to match on Option
      desugar_optional_chain(expr, field, span, dc)
    }
    
    ast.RecordUpdate(old, fields, span) -> {
      // Record update - copy old record with new fields
      desugar_record_update(old, fields, span, dc)
    }
    
    // Placeholder for unimplemented expressions
    _ -> #(CoreErr("Expression not yet implemented", get_expr_span(expr)), dc)
  }
}

/// Desugar a list of expressions.
fn desugar_exprs(
  exprs: List(Expr),
  dc: DesugarContext,
) -> #(List(CoreTerm), DesugarContext) {
  desugar_exprs_loop(exprs, [], dc)
}

fn desugar_exprs_loop(
  exprs: List(Expr),
  acc: List(CoreTerm),
  dc: DesugarContext,
) -> #(List(CoreTerm), DesugarContext) {
  case exprs {
    [] -> #(list.reverse(acc), dc)
    [expr, ..rest] -> {
      let #(core_expr, dc1) = desugar_expr_core(expr, dc)
      desugar_exprs_loop(rest, [core_expr, ..acc], dc1)
    }
  }
}

/// Convert a literal to Core.
fn literal_to_core(literal: Literal, span: Span) -> CoreTerm {
  case literal {
    Int(n) -> CoreLit(int.to_string(n), span)
    Float(f) -> CoreLit(float.to_string(f), span)
    String(s) -> CoreLit(s, span)
  }
}

/// Build nested lambdas from type params and value params.
fn build_lambdas(
  type_params: List(String),
  value_params: List(Param),
  body: CoreTerm,
  span: Span,
) -> CoreTerm {
  // For now, ignore type params (they're erased at runtime)
  build_value_lambdas(value_params, body, span)
}

fn build_value_lambdas(
  params: List(Param),
  body: CoreTerm,
  span: Span,
) -> CoreTerm {
  case params {
    [] -> body
    [param, ..rest] -> {
      let inner = build_value_lambdas(rest, body, span)
      CoreLam(param.name, inner, span)
    }
  }
}

/// Build nested lambdas with proper scope tracking for De Bruijn indices.
fn build_lambdas_with_scope(
  type_params: List(String),
  value_params: List(Param),
  body: Expr,
  span: Span,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  // For now, ignore type params (they're erased at runtime)
  build_value_lambdas_with_scope(value_params, body, span, dc)
}

fn build_value_lambdas_with_scope(
  params: List(Param),
  body: Expr,
  span: Span,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  case params {
    [] -> {
      // No more params - desugar the body
      desugar_expr_core(body, dc)
    }
    [param, ..rest] -> {
      // Add this param to scope, then build inner lambda
      let dc1 = add_local(dc, param.name)
      let #(inner_body, dc2) = build_value_lambdas_with_scope(rest, body, span, dc1)
      let core_lam = CoreLam(param.name, inner_body, span)
      #(core_lam, dc2)
    }
  }
}

/// Build function applications.
fn build_apps(
  fun: CoreTerm,
  args: List(CoreTerm),
  span: Span,
) -> CoreTerm {
  case args {
    [] -> fun
    [arg, ..rest] -> {
      let app = CoreApp(fun, arg, span)
      build_apps(app, rest, span)
    }
  }
}

/// Desugar binary operator to function call.
fn desugar_binop(
  left: Expr,
  op: BinOperator,
  right: Expr,
  span: Span,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  // Convert operator to function name
  let op_name = binop_to_name(op)
  
  // Desugar operands
  let #(core_left, dc1) = desugar_expr_core(left, dc)
  let #(core_right, dc2) = desugar_expr_core(right, dc1)
  
  // Build call: op_name(left, right)
  let op_var = CoreVar(op_name, span)
  let app1 = CoreApp(op_var, core_left, span)
  let app2 = CoreApp(app1, core_right, span)
  
  #(app2, dc2)
}

/// Convert binary operator to function name.
fn binop_to_name(op: BinOperator) -> String {
  case op {
    OpAdd -> "add"
    OpSub -> "sub"
    OpMul -> "mul"
    OpDiv -> "div"
    OpMod -> "mod"
    OpEq -> "eq"
    OpNeq -> "neq"
    OpLt -> "lt"
    OpGt -> "gt"
    OpLte -> "lte"
    OpGte -> "gte"
    OpAnd -> "and"
    OpOr -> "or"
    OpConcat -> "concat"
    OpPipe -> "pipe"
  }
}

/// Desugar unary operator to function call.
fn desugar_unaryop(
  op: UnaryOperator,
  expr: Expr,
  span: Span,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  let op_name = unaryop_to_name(op)
  let #(core_expr, dc1) = desugar_expr_core(expr, dc)
  
  let op_var = CoreVar(op_name, span)
  let app = CoreApp(op_var, core_expr, span)
  
  #(app, dc1)
}

/// Convert unary operator to function name.
fn unaryop_to_name(op: UnaryOperator) -> String {
  case op {
    OpNegate -> "negate"
    OpNot -> "not"
  }
}

/// Desugar record fields.
fn desugar_record_fields(
  fields: List(RecordField),
  dc: DesugarContext,
) -> #(List(#(String, CoreTerm)), DesugarContext) {
  desugar_record_fields_loop(fields, [], dc)
}

fn desugar_record_fields_loop(
  fields: List(RecordField),
  acc: List(#(String, CoreTerm)),
  dc: DesugarContext,
) -> #(List(#(String, CoreTerm)), DesugarContext) {
  case fields {
    [] -> #(list.reverse(acc), dc)
    [field, ..rest] -> {
      let #(core_value, dc1) = desugar_expr_core(field.value, dc)
      desugar_record_fields_loop(rest, [#(field.name, core_value), ..acc], dc1)
    }
  }
}

/// Desugar if expression to match on Bool.
fn desugar_if(
  cond: Expr,
  then_expr: Expr,
  else_expr: Option(Expr),
  span: Span,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  // if cond { then } else { else } → match cond { | True -> then | False -> else }
  let #(core_cond, dc1) = desugar_expr_core(cond, dc)
  let #(core_then, dc2) = desugar_expr_core(then_expr, dc1)
  let core_else = case else_expr {
    Some(e) -> {
      let #(core_e, dc3) = desugar_expr_core(e, dc2)
      core_e
    }
    None -> CoreRcd([], span)
  }
  
  // Build match on Bool: match cond { | True -> then | False -> else }
  // For now, simplify to: let _cond = cond in if _cond then then else else
  // A full implementation would use Core's match construct
  
  // Simple desugaring: use a conditional variable
  // Create: let bool_val = cond
  // Then return a record that selects based on bool_val
  // For now, just return the condition (placeholder until Core supports match)
  
  // Better approach: wrap in a do-block with the condition evaluated
  let cond_binding = CoreLet("_if_cond", core_cond, span)
  let result = CoreDoBlock(
    [cond_binding],
    core_then,  // In a full implementation, this would be a proper branch
    span,
  )
  #(result, dc2)
}

/// Desugar match expression with multiple clauses and guards.
fn desugar_match(
  scrutinee: Expr,
  clauses: List(MatchClause),
  span: Span,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  // match x { | pat1 if guard1 -> body1 | pat2 -> body2 }
  let #(core_scrutinee, dc1) = desugar_expr_core(scrutinee, dc)

  // Bind the scrutinee to a temporary variable
  let scrutinee_binding = CoreLet("_match_scrutinee", core_scrutinee, span)

  // Handle empty clauses
  case clauses {
    [] -> {
      // No clauses - return unit (in a full implementation, this would be a type error)
      let result = CoreDoBlock([scrutinee_binding], CoreRcd([], span), span)
      #(result, dc1)
    }
    _ -> {
      // Desugar all clauses and chain them
      let #(core_clauses, dc2) = desugar_match_clauses(clauses, scrutinee_binding, span, dc1)
      #(core_clauses, dc2)
    }
  }
}

/// Desugar a list of match clauses, chaining them with if-then-else.
fn desugar_match_clauses(
  clauses: List(MatchClause),
  scrutinee_binding: CoreTerm,
  span: Span,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  case clauses {
    [] -> {
      // No more clauses - return unit (no match)
      #(CoreRcd([], span), dc)
    }
    [clause, ..rest] -> {
      // Desugar this clause
      let #(this_clause, dc1) = desugar_single_clause(clause, scrutinee_binding, span, dc)

      // If there are more clauses, chain with if-then-else
      case rest {
        [] -> {
          // Last clause - just return it
          #(this_clause, dc1)
        }
        _rest_clauses -> {
          // More clauses - chain with if-then-else structure
          // For now, simplified: just use first matching clause
          #(this_clause, dc1)
        }
      }
    }
  }
}

/// Desugar a single match clause with pattern and optional guard.
fn desugar_single_clause(
  clause: MatchClause,
  scrutinee_binding: CoreTerm,
  span: Span,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  // Destructure the clause
  let pattern = clause.pattern
  let guard = clause.guard
  let body = clause.body

  // Desugar the body
  let #(core_body, dc1) = desugar_expr_core(body, dc)

  // Handle pattern matching
  let #(pattern_bindings, dc2) = desugar_pattern(pattern, scrutinee_binding, span, dc1)

  // Handle optional guard
  let guard_check = case guard {
    Some(guard_expr) -> {
      // Desugar guard expression
      let #(core_guard, dc3) = desugar_expr_core(guard_expr, dc2)
      // Add guard check to bindings
      let guard_binding = CoreLet("_guard_result", core_guard, span)
      #([guard_binding, ..pattern_bindings], dc3)
    }
    None -> {
      #(pattern_bindings, dc2)
    }
  }

  let #(final_bindings, dc3) = guard_check

  // Build the result block
  let result = CoreDoBlock(
    [scrutinee_binding, ..final_bindings],
    core_body,
    span,
  )
  #(result, dc3)
}

/// Desugar a pattern and return bindings.
fn desugar_pattern(
  pattern: Pattern,
  scrutinee: CoreTerm,
  span: Span,
  dc: DesugarContext,
) -> #(List(CoreTerm), DesugarContext) {
  case pattern {
    ast.PVar(name, _pattern_span) -> {
      // Variable pattern: bind scrutinee to name
      let binding = CoreLet(name, CoreVar("_match_scrutinee", span), span)
      let dc1 = add_local(dc, name)
      #([binding], dc1)
    }
    ast.PAny(_pattern_span) -> {
      // Wildcard pattern: no binding needed
      #([], dc)
    }
    ast.PLit(literal, _pattern_span) -> {
      // Literal pattern: check equality (simplified)
      let core_lit = literal_to_core(literal, span)
      let check = CoreLet("_pattern_check", core_lit, span)
      #([check], dc)
    }
    ast.PCtr(_name, _args, _pattern_span) -> {
      // Constructor pattern: check constructor and bind args
      // Simplified: just bind scrutinee
      let binding = CoreLet("_ctr_check", scrutinee, span)
      #([binding], dc)
    }
    ast.PRecord(field_names, _pattern_span) -> {
      // Record pattern: bind each field
      // Convert field names to field patterns
      let field_patterns = list.map(field_names, fn(field_name) {
        #(field_name, ast.PVar(field_name, span))
      })
      desugar_pattern_record(field_patterns, scrutinee, span, dc)
    }
    ast.PTuple(items, _pattern_span) -> {
      // Tuple pattern: bind each item
      desugar_pattern_list(items, scrutinee, span, dc)
    }
    ast.PList(items, _rest_name, _pattern_span) -> {
      // List pattern: bind each item (simplified)
      desugar_pattern_list(items, scrutinee, span, dc)
    }
    ast.POr(_patterns, _pattern_span) -> {
      // Or pattern: use first pattern (simplified)
      #([], dc)
    }
    ast.PAs(inner_pattern, alias, _pattern_span) -> {
      // As pattern: bind both alias and inner pattern
      let #(inner_bindings, dc1) = desugar_pattern(inner_pattern, scrutinee, span, dc)
      let alias_binding = CoreLet(alias, CoreVar("_match_scrutinee", span), span)
      let dc2 = add_local(dc1, alias)
      #([alias_binding, ..inner_bindings], dc2)
    }
  }
}

/// Helper for tuple/list pattern desugaring.
fn desugar_pattern_list(
  items: List(Pattern),
  scrutinee: CoreTerm,
  span: Span,
  dc: DesugarContext,
) -> #(List(CoreTerm), DesugarContext) {
  desugar_pattern_list_loop(items, scrutinee, span, dc, 0)
}

fn desugar_pattern_list_loop(
  items: List(Pattern),
  scrutinee: CoreTerm,
  span: Span,
  dc: DesugarContext,
  index: Int,
) -> #(List(CoreTerm), DesugarContext) {
  case items {
    [] -> {
      #([], dc)
    }
    [item, ..rest] -> {
      let field_name = int.to_string(index)
      let field_access = CoreDot(scrutinee, field_name, span)
      let #(item_bindings, dc1) = desugar_pattern(item, field_access, span, dc)
      let #(rest_bindings, dc2) = desugar_pattern_list_loop(rest, scrutinee, span, dc1, index + 1)
      #([item_bindings, rest_bindings] |> list.flatten, dc2)
    }
  }
}

/// Helper for record pattern desugaring.
fn desugar_pattern_record(
  fields: List(#(String, Pattern)),
  scrutinee: CoreTerm,
  span: Span,
  dc: DesugarContext,
) -> #(List(CoreTerm), DesugarContext) {
  desugar_pattern_record_loop(fields, scrutinee, span, dc)
}

fn desugar_pattern_record_loop(
  fields: List(#(String, Pattern)),
  scrutinee: CoreTerm,
  span: Span,
  dc: DesugarContext,
) -> #(List(CoreTerm), DesugarContext) {
  case fields {
    [] -> {
      #([], dc)
    }
    [#(field_name, field_pattern), ..rest] -> {
      let field_access = CoreDot(scrutinee, field_name, span)
      let #(field_bindings, dc1) = desugar_pattern(field_pattern, field_access, span, dc)
      let #(rest_bindings, dc2) = desugar_pattern_record_loop(rest, scrutinee, span, dc1)
      #([field_bindings, rest_bindings] |> list.flatten, dc2)
    }
  }
}

/// Build constructor.
fn build_ctr(
  name: String,
  args: List(CoreTerm),
  span: Span,
) -> CoreTerm {
  // Constructors are curried: #Some(x) → App(App(#Some, Unit), x)
  build_ctr_loop(name, args, span)
}

fn build_ctr_loop(
  name: String,
  args: List(CoreTerm),
  span: Span,
) -> CoreTerm {
  case args {
    [] -> {
      // Nullary constructor: #True(Unit)
      let ctr_var = CoreVar(name, span)
      CoreApp(ctr_var, CoreRcd([], span), span)
    }
    [arg, ..rest] -> {
      let inner = build_ctr_loop(name, rest, span)
      CoreApp(inner, arg, span)
    }
  }
}

/// Desugar tuple to Record.
fn desugar_tuple(
  exprs: List(Expr),
  span: Span,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  let #(core_exprs, dc1) = desugar_exprs(exprs, dc)
  let fields = list.index_map(core_exprs, fn(expr, i) {
    #(int.to_string(i), expr)
  })
  #(CoreRcd(fields, span), dc1)
}

/// Desugar list to nested Cons/Nil.
fn desugar_list(
  exprs: List(Expr),
  span: Span,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  desugar_list_loop(exprs, span, dc)
}

fn desugar_list_loop(
  exprs: List(Expr),
  span: Span,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  case exprs {
    [] -> {
      // Nil
      #(CoreVar("Nil", span), dc)
    }
    [expr, ..rest] -> {
      let #(core_expr, dc1) = desugar_expr_core(expr, dc)
      let #(core_rest, dc2) = desugar_list_loop(rest, span, dc1)
      // Cons(expr, rest)
      let cons = CoreVar("Cons", span)
      let app1 = CoreApp(cons, core_expr, span)
      let app2 = CoreApp(app1, core_rest, span)
      #(app2, dc2)
    }
  }
}

/// Desugar block.
fn desugar_block(
  stmts: List(BlockStatement),
  span: Span,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  case stmts {
    [] -> #(CoreRcd([], span), dc)
    [stmt] -> desugar_block_stmt(stmt, dc)
    [stmt, ..rest] -> {
      // Multiple statements - create a DoBlock
      let #(core_stmt, dc1) = desugar_block_stmt(stmt, dc)
      let #(core_rest, dc2) = desugar_block(rest, span, dc1)
      #(CoreDoBlock([core_stmt], core_rest, span), dc2)
    }
  }
}

/// Desugar block statement.
fn desugar_block_stmt(
  stmt: BlockStatement,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  case stmt {
    BlockStmtLet(let_decl) -> {
      desugar_let_decl(let_decl, dc)
    }
    BlockStmtAssign(name, expr) -> {
      let #(core_expr, dc1) = desugar_expr_core(expr, dc)
      // Assignment becomes a let binding
      #(CoreLet(name, core_expr, expr_span(expr)), dc1)
    }
    BlockStmtExpr(expr) -> {
      desugar_expr_core(expr, dc)
    }
  }
}

/// Desugar let declaration.
fn desugar_let_decl(
  let_decl: ast.LetDecl,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  let #(core_value, dc1) = desugar_expr_core(let_decl.value, dc)
  let core_let = CoreLet(let_decl.name, core_value, let_decl.span)
  let dc2 = add_local(dc1, let_decl.name)
  #(core_let, dc2)
}

/// Desugar let expression.
fn desugar_let_expr(
  let_decl: ast.LetDecl,
  body: Expr,
  span: Span,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  let #(core_let, dc1) = desugar_let_decl(let_decl, dc)
  let #(core_body, dc2) = desugar_expr_core(body, dc1)
  // Let expression becomes a DoBlock
  #(CoreDoBlock([core_let], core_body, span), dc2)
}

/// Desugar optional chain.
fn desugar_optional_chain(
  expr: Expr,
  field: String,
  span: Span,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  // user?.address → match user { | Some(u) -> u.address | None -> None }
  let #(core_expr, dc1) = desugar_expr_core(expr, dc)
  
  // Bind the expression
  let expr_binding = CoreLet("_opt_chain_val", core_expr, span)
  
  // For now, simplify to: field access with None check
  // A full implementation would pattern match on Option
  let field_access = CoreDot(CoreVar("_opt_chain_val", span), field, span)
  
  let result = CoreDoBlock([expr_binding], field_access, span)
  #(result, dc1)
}

/// Desugar record update.
fn desugar_record_update(
  old: Expr,
  fields: List(RecordField),
  span: Span,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  // { ..old, x: 1 } → copy old record with new fields
  let #(core_old, dc1) = desugar_expr_core(old, dc)
  let #(core_fields, dc2) = desugar_record_fields(fields, dc1)
  
  // Bind the old record
  let old_binding = CoreLet("_record_old", core_old, span)
  
  // For each field in the old record, create a field access
  // Then override with new fields
  // Simplified: just use the new fields (full implementation would merge)
  let result = CoreDoBlock([old_binding], CoreRcd(core_fields, span), span)
  #(result, dc2)
}

/// Get span from expression.
fn get_expr_span(expr: Expr) -> Span {
  span_from_expr(expr)
}

/// Get span from expression for assignment.
fn expr_span(expr: Expr) -> Span {
  span_from_expr(expr)
}

// ============================================================================
// LAMBDA BUILDING
// ============================================================================

/// Build nested lambdas from parameters.
fn build_lambda(
  params: List(Param),
  body: CoreTerm,
  span: Span,
) -> CoreTerm {
  build_lambda_loop(params, body, span)
}

fn build_lambda_loop(
  params: List(Param),
  body: CoreTerm,
  span: Span,
) -> CoreTerm {
  case params {
    [] -> body
    [param, ..rest] -> {
      let inner = build_lambda_loop(rest, body, span)
      CoreLam(param.name, inner, span)
    }
  }
}

// ============================================================================
// SCOPE MANAGEMENT
// ============================================================================

// Scope management functions (add_local, lookup_var) are defined
// in the DESUGAR CONTEXT section above

// ============================================================================
// MODULE REFERENCE HELPERS
// ============================================================================

/// Create a module reference term.
pub fn make_module_ref(path: String, span: Span) -> CoreTerm {
  CoreModuleRef(path, span)
}

/// Create a field access on a module reference.
pub fn make_module_field(
  path: String,
  field: String,
  span: Span,
) -> CoreTerm {
  CoreDot(CoreModuleRef(path, span), field, span)
}

// ============================================================================
// CORE TERM CONVERSION
// ============================================================================

/// Convert a simplified CoreTerm to core/core.Term.
pub fn core_term_to_term(term: CoreTerm) -> Term {
  core_term_to_term_loop(term)
}

fn core_term_to_term_loop(term: CoreTerm) -> Term {
  case term {
    CoreVar(_name, span) -> Var(index: 0, span: span)  // Simplified: always use index 0
    CoreModuleRef(_path, span) -> Var(index: 0, span: span)  // Simplified: module refs become vars
    CoreLam(param, body, span) -> {
      // Simplified lambda - no implicit params, no type annotation
      Lam(
        implicit: [],
        param: #(param, Typ(universe: 0, span: span)),
        body: core_term_to_term_loop(body),
        span: span,
      )
    }
    CoreApp(fun, arg, span) -> {
      App(
        fun: core_term_to_term_loop(fun),
        implicit: [],
        arg: core_term_to_term_loop(arg),
        span: span,
      )
    }
    CoreRcd(fields, span) -> {
      Rcd(
        fields: list.map(fields, fn(pair) {
          #(pair.0, core_term_to_term_loop(pair.1))
        }),
        span: span,
      )
    }
    CoreDot(record, field, span) -> {
      Dot(
        arg: core_term_to_term_loop(record),
        field: field,
        span: span,
      )
    }
    CoreLet(_name, _value, span) -> {
      // Let bindings are handled by DoBlock - return unit
      CoreRcd([], span) |> core_term_to_term_loop
    }
    CoreDoBlock(_stmts, result, _span) -> {
      // DoBlock becomes a sequence in Core (simplified: just return result)
      // A full implementation would use Fixpoint for proper sequencing
      core_term_to_term_loop(result)
    }
    CoreLit(value, span) -> {
      case int.parse(value) {
        Ok(n) -> Lit(value: I32(n), span: span)
        Error(_) -> Lit(value: I32(0), span: span)
      }
    }
    CoreErr(message, span) -> Err(message: message, span: span)
  }
}

fn value_span(term: CoreTerm) -> Span {
  case term {
    CoreVar(_, span) -> span
    CoreModuleRef(_, span) -> span
    CoreLam(_, _, span) -> span
    CoreApp(_, _, span) -> span
    CoreRcd(_, span) -> span
    CoreDot(_, _, span) -> span
    CoreLet(_, _, span) -> span
    CoreDoBlock(_, _, span) -> span
    CoreLit(_, span) -> span
    CoreErr(_, span) -> span
  }
}
