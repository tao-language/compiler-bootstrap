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
import core/core.{type Term, type Literal as CoreLiteral, type Pattern as CorePattern, type Case as CoreCaseType, Err, Var, Rcd, Dot, Lit, Unit, Call, Lam, App, Typ, I32, Match as CoreMatch, Case, Fix, PAny, PAs, PLit as PPlit, PRcd, PCtr as PPCtr, PUnit, PTyp, PLitT, Hole}

// ============================================================================
// CORE TERM TYPES (simplified for desugaring)
// ============================================================================
/// Simplified Core term representation for desugaring.
/// Full Core terms are in src/core/core.gleam

pub type CoreTerm {
  /// Variable reference
  CoreVar(name: String, span: Span)

  /// Builtin function call (add, sub, mul, etc.)
  CoreCall(name: String, args: List(CoreTerm), span: Span)

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

  /// Type universe (Typ(n) represents Type(n))
  CoreTyp(universe: Int, span: Span)

  /// Builtin type reference (e.g., "String", "Int")
  CoreBuiltinType(name: String, span: Span)

  /// Hole/metavariable for type inference
  CoreHole(id: Int, span: Span)

  /// Literal
  CoreLit(value: String, span: Span)

  /// Pattern match with cases
  CoreMatchCore(arg: CoreTerm, motive: CoreTerm, cases: List(CoreCaseType), span: Span)

  /// Fixpoint operator for recursion
  CoreFix(name: String, body: CoreTerm, span: Span)

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

  // Check if the last statement is an expression (for expression-style modules)
  let last_is_expr = is_last_stmt_expr(module.body)

  // Determine the result term
  let result = case last_is_expr {
    True -> {
      // Expression-style module - return the last expression value
      case core_stmts {
        [] -> CoreRcd([], module.span)
        _ -> {
          // Get the last statement (should be an expression)
          get_last_statement(core_stmts, CoreRcd([], module.span))
        }
      }
    }
    False -> {
      // Declaration-style module - return a record of public names
      let public_names = get_public_names(module.body)
      case public_names {
        [] -> CoreRcd([], module.span)
        names -> {
          let return_fields = list.map(names, fn(name) {
            #(name, CoreVar(name, module.span))
          })
          CoreRcd(return_fields, module.span)
        }
      }
    }
  }

  let core_term = CoreDoBlock(core_stmts, result, module.span)

  // Convert to core/core.Term
  let term = core_term_to_term(core_term)

  #(term, dc1)
}

/// Check if the last statement in a list is an expression statement.
fn is_last_stmt_expr(stmts: List(Stmt)) -> Bool {
  case stmts {
    [] -> False
    [stmt] -> {
      case stmt {
        StmtExpr(_, _) -> True
        _ -> False
      }
    }
    [_, ..rest] -> is_last_stmt_expr(rest)
  }
}

/// Get the last statement from a list, or return default if empty.
fn get_last_statement(stmts: List(CoreTerm), default: CoreTerm) -> CoreTerm {
  case stmts {
    [] -> default
    [last] -> last
    [_, ..rest] -> get_last_statement(rest, default)
  }
}

/// Build a sequential term from statements and result.
/// Each let x = e becomes a lambda application: (λx. rest) e
fn build_sequential_term(
  stmts: List(CoreTerm),
  result: CoreTerm,
  span: Span,
) -> CoreTerm {
  build_sequential_loop(stmts, result, span)
}

fn build_sequential_loop(
  stmts: List(CoreTerm),
  result: CoreTerm,
  span: Span,
) -> CoreTerm {
  case stmts {
    [] -> result
    [stmt] -> {
      // Last statement - incorporate it into the result
      case stmt {
        CoreLet(name, value, _let_span) -> {
          // let x = e as last statement  =>  (λx. result) e
          let lam = CoreLam(name, result, span)
          CoreApp(lam, value, span)
        }
        _ -> {
          // Expression statement as last statement - use it as result
          stmt
        }
      }
    }
    [stmt, ..rest] -> {
      case stmt {
        CoreLet(name, value, _let_span) -> {
          // let x = e in rest  =>  (λx. process_rest) e
          let body = build_sequential_loop(rest, result, span)
          let lam = CoreLam(name, body, span)
          CoreApp(lam, value, span)
        }
        _ -> {
          // Non-let statements in the middle are just evaluated and discarded
          build_sequential_loop(rest, result, span)
        }
      }
    }
  }
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
      // Use build_lambdas_with_scope to properly handle param scoping
      let #(core_lam, dc1) = build_lambdas_with_scope(type_params, params, body, span, dc)
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
  // Desugar to: fix loop -> match condition { | True -> body; loop () | _ -> () }
  // This ensures proper short-circuit: if condition is false, body is never executed

  // Desugar the condition
  let #(core_condition, dc1) = desugar_expr_core(condition, dc)

  // Desugar the body statements
  let #(core_body_stmts, dc2) = desugar_stmts(body, dc1)

  // Body block that ends with recursive call
  let loop_call = CoreApp(CoreVar("loop", span), CoreRcd([], span), span)
  let body_with_rec = CoreDoBlock(core_body_stmts, loop_call, span)

  // Build match on condition: match condition { | True -> body; loop () | _ -> () }
  // True clause: execute body and recurse
  let true_clause = Case(
    pattern: PPCtr("True", PUnit),
    body: core_term_to_term(body_with_rec),
    guard: None,
    span: span,
  )
  
  // Default clause: return unit (exit loop)
  let default_clause = Case(
    pattern: PAny,
    body: core_term_to_term(CoreRcd([], span)),
    guard: None,
    span: span,
  )
  
  // Match expression as CoreTerm (need to wrap Term back for fixpoint body)
  // For now, use CoreMatchCore directly with Term bodies
  // The match result type is Unit
  let match_core = CoreMatchCore(
    arg: core_condition,
    motive: CoreRcd([], span),
    cases: [true_clause, default_clause],
    span: span,
  )
  
  let fix = CoreFix("loop", match_core, span)

  #(fix, dc2)
}

/// Desugar an infinite loop.
fn desugar_loop(
  body: List(Stmt),
  span: Span,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  // loop { body... }
  // Desugar to: fixpoint that recursively executes body
  // fix loop -> (body; loop ())

  // Desugar the body statements
  let #(core_body_stmts, dc1) = desugar_stmts(body, dc)

  // Body block that ends with recursive call
  let loop_call = CoreApp(CoreVar("loop", span), CoreRcd([], span), span)
  let body_with_rec = CoreDoBlock(core_body_stmts, loop_call, span)

  // Wrap in fixpoint
  let fix = CoreFix("loop", body_with_rec, span)

  #(fix, dc1)
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
          // Bound variable - use De Bruijn index directly
          // The index is stored in the CoreVar name as "idx"
          #(CoreVar(int.to_string(index), span), dc)
        }
        None -> {
          // Free variable - keep as named variable (will be error)
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

/// Convert a Tao literal to a Core literal.
fn tao_literal_to_core_literal(literal: Literal) -> CoreLiteral {
  case literal {
    Int(n) -> core.I32(n)
    Float(f) -> core.F64(f)
    String(_s) -> core.I32(0)  // Strings not directly supported in core literals
  }
}

/// Convert a literal to Core term.
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
  // Convert operator to builtin function name
  let op_name = binop_to_name(op)

  // Desugar operands
  let #(core_left, dc1) = desugar_expr_core(left, dc)
  let #(core_right, dc2) = desugar_expr_core(right, dc1)

  // Build call: op_name(left, right) using CoreCall
  #(CoreCall(op_name, [core_left, core_right], span), dc2)
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

  // Build call: op_name(expr) using CoreCall
  #(CoreCall(op_name, [core_expr], span), dc1)
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

/// Desugar match expression with full Core Match support.
fn desugar_match(
  scrutinee: Expr,
  clauses: List(MatchClause),
  span: Span,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  // match x { | pat1 if guard1 -> body1 | pat2 -> body2 }
  let #(core_scrutinee, dc1) = desugar_expr_core(scrutinee, dc)

  // Desugar all clauses to Core Cases
  let #(core_cases, dc2) = desugar_match_clauses_to_cases(clauses, span, dc1)

  // Build Core Match term
  // For non-dependent matches, the motive is a constant function that returns the result type.
  // We use a lambda with a hole body: fn(_) -> ?ResultType
  // The hole will be unified with the result type when checking clause bodies.
  // Note: Using a negative hole ID to avoid conflicts with type checker's hole counter.
  let result_type_hole = CoreHole(-100, span)
  let motive = CoreLam("_", result_type_hole, span)
  let core_match = CoreMatchCore(core_scrutinee, motive, core_cases, span)

  #(core_match, dc2)
}

/// Desugar match clauses to Core Cases.
fn desugar_match_clauses_to_cases(
  clauses: List(MatchClause),
  span: Span,
  dc: DesugarContext,
) -> #(List(CoreCaseType), DesugarContext) {
  desugar_cases_loop(clauses, [], span, dc)
}

fn desugar_cases_loop(
  clauses: List(MatchClause),
  acc: List(CoreCaseType),
  span: Span,
  dc: DesugarContext,
) -> #(List(CoreCaseType), DesugarContext) {
  case clauses {
    [] -> #(list.reverse(acc), dc)
    [clause, ..rest] -> {
      let #(core_case, dc1) = desugar_single_case(clause, span, dc)
      desugar_cases_loop(rest, [core_case, ..acc], span, dc1)
    }
  }
}

/// Desugar a single match clause to a Core Case.
fn desugar_single_case(
  clause: MatchClause,
  span: Span,
  dc: DesugarContext,
) -> #(CoreCaseType, DesugarContext) {
  let pattern = clause.pattern
  let guard = clause.guard
  let body = clause.body

  // Desugar the body to CoreTerm
  let #(core_body, dc1) = desugar_expr_core(body, dc)

  // Convert Tao pattern to Core pattern
  let #(core_pattern, dc2) = tao_pattern_to_core_pattern(pattern, dc1)

  // Convert optional guard to Term (core/core.Case expects Option(Term))
  let core_guard = case guard {
    Some(guard_expr) -> {
      let #(core_guard_term, dc3) = desugar_expr_core(guard_expr, dc2)
      Some(core_term_to_term(core_guard_term))
    }
    None -> None
  }

  // Convert body to Term
  let core_body_term = core_term_to_term(core_body)

  let core_case = Case(core_pattern, core_body_term, core_guard, span)
  #(core_case, dc2)
}

/// Convert a Tao pattern to a Core pattern.
fn tao_pattern_to_core_pattern(
  pattern: Pattern,
  dc: DesugarContext,
) -> #(CorePattern, DesugarContext) {
  case pattern {
    ast.PVar(name, _pattern_span) -> {
      // Variable pattern: bind to as-pattern
      let core_pattern = PAs(PAny, name)
      let dc1 = add_local(dc, name)
      #(core_pattern, dc1)
    }
    ast.PAny(_pattern_span) -> {
      // Wildcard pattern
      #(PAny, dc)
    }
    ast.PLit(literal, _pattern_span) -> {
      // Literal pattern
      let core_lit = tao_literal_to_core_literal(literal)
      #(PPlit(core_lit), dc)
    }
    ast.PCtr(name, args, _pattern_span) -> {
      // Constructor pattern
      tao_ctr_pattern_to_core(name, args, dc)
    }
    ast.PRecord(field_names, _pattern_span) -> {
      // Record pattern: {x, y} → {x = x, y = y}
      let core_fields = list.map(field_names, fn(field_name) {
        #(field_name, PAs(PAny, field_name))
      })
      let dc1 = list.fold(field_names, dc, fn(acc, name) {
        add_local(acc, name)
      })
      #(PRcd(core_fields), dc1)
    }
    ast.PTuple(items, _pattern_span) -> {
      // Tuple pattern: (a, b) → record with numeric fields
      tao_tuple_pattern_to_core(items, dc)
    }
    ast.PList(items, rest_name, _pattern_span) -> {
      // List pattern: [h, ..t] or [a, b, c]
      tao_list_pattern_to_core(items, rest_name, dc)
    }
    ast.POr(_patterns, _pattern_span) -> {
      // Or pattern: simplified to PAny
      #(PAny, dc)
    }
    ast.PAs(inner_pattern, alias, _pattern_span) -> {
      // As pattern: x @ Some(_)
      let #(core_inner, dc1) = tao_pattern_to_core_pattern(inner_pattern, dc)
      let core_pattern = PAs(core_inner, alias)
      let dc2 = add_local(dc1, alias)
      #(core_pattern, dc2)
    }
  }
}

/// Convert constructor pattern to Core.
fn tao_ctr_pattern_to_core(
  name: String,
  args: List(Pattern),
  dc: DesugarContext,
) -> #(CorePattern, DesugarContext) {
  case args {
    [] -> {
      // Nullary constructor
      #(PPCtr(name, PUnit), dc)
    }
    [first, ..rest] -> {
      // Build nested constructor pattern
      tao_ctr_pattern_to_core_loop(name, [first, ..rest], dc)
    }
  }
}

fn tao_ctr_pattern_to_core_loop(
  name: String,
  args: List(Pattern),
  dc: DesugarContext,
) -> #(CorePattern, DesugarContext) {
  case args {
    [] -> {
      #(PUnit, dc)
    }
    [first] -> {
      // Last argument
      let #(core_first, dc1) = tao_pattern_to_core_pattern(first, dc)
      #(PPCtr(name, core_first), dc1)
    }
    [first, ..rest] -> {
      // Build nested pattern
      let #(core_first, dc1) = tao_pattern_to_core_pattern(first, dc)
      let #(core_rest, dc2) = tao_ctr_pattern_to_core_loop(name, rest, dc1)
      #(PPCtr(name, core_first), dc2)
    }
  }
}

/// Convert tuple pattern to Core (tuple = record with numeric fields).
fn tao_tuple_pattern_to_core(
  items: List(Pattern),
  dc: DesugarContext,
) -> #(CorePattern, DesugarContext) {
  tao_tuple_pattern_loop(items, 0, [], dc)
}

fn tao_tuple_pattern_loop(
  items: List(Pattern),
  index: Int,
  acc: List(#(String, CorePattern)),
  dc: DesugarContext,
) -> #(CorePattern, DesugarContext) {
  case items {
    [] -> {
      #(PRcd(list.reverse(acc)), dc)
    }
    [item, ..rest] -> {
      let field_name = int.to_string(index)
      let #(core_item, dc1) = tao_pattern_to_core_pattern(item, dc)
      tao_tuple_pattern_loop(rest, index + 1, [#(field_name, core_item), ..acc], dc1)
    }
  }
}

/// Convert list pattern to Core.
fn tao_list_pattern_to_core(
  items: List(Pattern),
  rest_name: Option(String),
  dc: DesugarContext,
) -> #(CorePattern, DesugarContext) {
  case items {
    [] -> {
      // Empty list: Nil
      case rest_name {
        Some(name) -> {
          // [..rest] or [] with rest
          let core_pattern = PPCtr("Nil", PUnit)
          let dc1 = add_local(dc, name)
          #(PAs(core_pattern, name), dc1)
        }
        None -> {
          #(PPCtr("Nil", PUnit), dc)
        }
      }
    }
    [first, ..rest] -> {
      // Non-empty list: Cons(h, t)
      let #(core_first, dc1) = tao_pattern_to_core_pattern(first, dc)
      let #(core_rest, dc2) = tao_list_rest_pattern_to_core(rest, rest_name, dc1)
      #(PPCtr("Cons", core_first), dc2)
    }
  }
}

fn tao_list_rest_pattern_to_core(
  rest: List(Pattern),
  rest_name: Option(String),
  dc: DesugarContext,
) -> #(CorePattern, DesugarContext) {
  case rest {
    [] -> {
      // End of list
      case rest_name {
        Some(name) -> {
          let core_pattern = PPCtr("Nil", PUnit)
          let dc1 = add_local(dc, name)
          #(PAs(core_pattern, name), dc1)
        }
        None -> {
          #(PPCtr("Nil", PUnit), dc)
        }
      }
    }
    [first, ..inner_rest] -> {
      // Continue building Cons chain
      let #(core_first, dc1) = tao_pattern_to_core_pattern(first, dc)
      let #(core_inner_rest, dc2) = tao_list_rest_pattern_to_core(inner_rest, rest_name, dc1)
      #(PPCtr("Cons", core_first), dc2)
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
  core_term_to_term_loop(term, [])
}

fn core_term_to_term_loop(term: CoreTerm, env: List(String)) -> Term {
  case term {
    CoreVar(name, span) -> {
      // Check if name is a numeric De Bruijn index
      case int.parse(name) {
        Ok(index) -> {
          // Already a De Bruijn index - use directly
          Var(index: index, span: span)
        }
        Error(_) -> {
          // Named variable - look up in environment
          case find_var_index(env, name, 0) {
            Some(index) -> Var(index: index, span: span)
            None -> Var(index: 0, span: span)  // Undefined variable
          }
        }
      }
    }
    CoreCall(name, args, span) -> {
      // Convert CoreCall to core/core.Call for FFI builtin
      Call(name, list.map(args, fn(a) { core_term_to_term_loop(a, env) }), span)
    }
    CoreModuleRef(_path, span) -> Var(index: 0, span: span)
    CoreLam(param, body, span) -> {
      // Add parameter to environment for the body
      Lam(
        implicit: [],
        param: #(param, Typ(universe: 0, span: span)),
        body: core_term_to_term_loop(body, [param, ..env]),
        span: span,
      )
    }
    CoreApp(fun, arg, span) -> {
      App(
        fun: core_term_to_term_loop(fun, env),
        implicit: [],
        arg: core_term_to_term_loop(arg, env),
        span: span,
      )
    }
    CoreRcd(fields, span) -> {
      Rcd(
        fields: list.map(fields, fn(pair) {
          #(pair.0, core_term_to_term_loop(pair.1, env))
        }),
        span: span,
      )
    }
    CoreDot(record, field, span) -> {
      Dot(
        arg: core_term_to_term_loop(record, env),
        field: field,
        span: span,
      )
    }
    CoreLet(name, value, span) -> {
      // Let bindings are handled by CoreDoBlock
      CoreRcd([], span) |> core_term_to_term_loop(env)
    }
    CoreDoBlock(stmts, result, span) -> {
      let sequential_core = build_sequential_term(stmts, result, span)
      core_term_to_term_loop(sequential_core, env)
    }
    CoreTyp(universe, span) -> {
      // Convert CoreTyp to core/core.Typ (type universe)
      Typ(universe: universe, span: span)
    }
    CoreBuiltinType(name, span) -> {
      // Convert CoreBuiltinType to a type variable
      // For now, use a hole as a placeholder
      Hole(id: -1, span: span)
    }
    CoreHole(id, span) -> {
      // Convert CoreHole to core/core.Hole (metavariable)
      Hole(id: id, span: span)
    }
    CoreLit(value, span) -> {
      case int.parse(value) {
        Ok(n) -> Lit(value: I32(n), span: span)
        Error(_) -> Lit(value: I32(0), span: span)
      }
    }
    CoreMatchCore(arg, motive, cases, span) -> {
      // Convert CoreMatchCore to core/core.Match
      // Cases are already core.Case with Term bodies
      CoreMatch(
        arg: core_term_to_term_loop(arg, env),
        motive: core_term_to_term_loop(motive, env),
        cases: cases,
        span: span,
      )
    }
    CoreFix(name, body, span) -> {
      // Convert CoreFix to core/core.Fix
      Fix(name, core_term_to_term_loop(body, [name, ..env]), span)
    }
    CoreErr(message, span) -> Err(message: message, span: span)
  }
}

/// Find the De Bruijn index of a variable name in the environment.
/// Returns the index (0 = most recent binding) or None if not found.
fn find_var_index(env: List(String), name: String, index: Int) -> Option(Int) {
  case env {
    [] -> None
    [head, ..tail] -> {
      case head == name {
        True -> Some(index)
        False -> find_var_index(tail, name, index + 1)
      }
    }
  }
}

fn value_span(term: CoreTerm) -> Span {
  case term {
    CoreVar(_, span) -> span
    CoreCall(_, _, span) -> span
    CoreModuleRef(_, span) -> span
    CoreLam(_, _, span) -> span
    CoreApp(_, _, span) -> span
    CoreRcd(_, span) -> span
    CoreDot(_, _, span) -> span
    CoreLet(_, _, span) -> span
    CoreDoBlock(_, _, span) -> span
    CoreTyp(_, span) -> span
    CoreBuiltinType(_, span) -> span
    CoreHole(_, span) -> span
    CoreLit(_, span) -> span
    CoreMatchCore(_, _, _, span) -> span
    CoreFix(_, _, span) -> span
    CoreErr(_, span) -> span
  }
}
