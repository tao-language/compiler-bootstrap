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
  type Module, type Stmt, type Expr, type Param, Param, type Pattern,
  type Literal, type BinOperator, type UnaryOperator,
  type RecordField, type MatchClause, type BlockStatement, type LetDecl,
  StmtLet, StmtFn, StmtImport, StmtExpr,
  StmtFor, StmtWhile, StmtLoop, StmtBreak, StmtContinue, StmtReturn, StmtYield,
  StmtTest, StmtRun,
  BlockStmtLet, BlockStmtAssign, BlockStmtExpr,
  OpAdd, OpSub, OpMul, OpDiv, OpMod, OpEq, OpNeq, OpLt, OpGt, OpLte, OpGte,
  OpAnd, OpOr, OpConcat, OpPipe, OpNegate, OpNot,
  Int as LitInt, Float as LitFloat, String as LitString,
  RecordUpdate, OptionalChain, LetExpr, Var as ExprVar,
  get_public_names, get_stmt_name, span_from_expr,
  type Constructor, Constructor, type ConstructorField, NamedField, UnnamedField, type TypeAst,
  TVar, TApp, TFn, TRecord, TTuple, THole,
  StmtType,
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
import core/core.{type Term, type Literal as CoreLiteral, type LiteralType, I32T, I64T, F32T, F64T, type Pattern as CorePattern, type Case as CoreCaseType, type CtrDef, CtrDef, type CtrEnv, Err, Var, Rcd, Dot, Lit, LitT, Unit, Call, Lam, App, Typ, I32, F64, Match as CoreMatch, Case, Fix, PAny, PAs, PLit as PPlit, PRcd, PCtr as PPCtr, PUnit, PTyp, PLitT, Hole, Ctr, Ann, Pi}

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

  /// Constructor (algebraic data type constructor)
  CoreCtr(tag: String, arg: CoreTerm, span: Span)

  /// Type annotation (for explicit type signatures)
  CoreAnn(term: CoreTerm, typ: CoreTerm, span: Span)

  /// Pi type (dependent function type)
  CorePi(implicit: List(String), name: String, domain: CoreTerm, codomain: CoreTerm, span: Span)

  /// Unit value
  CoreUnit(span: Span)

  /// Error placeholder
  CoreErr(message: String, span: Span)
}

// ============================================================================
// DESUGAR CONTEXT
// ============================================================================

/// Loop context for tracking break/continue targets.
pub type LoopContext {
  /// Inside a loop with a given fixpoint name.
  InLoop(fix_name: String, break_target: BreakTarget)
}

/// Where should break jump to?
pub type BreakTarget {
  /// Break exits the current loop and returns a value.
  BreakReturns
}

pub type DesugarContext {
  DesugarContext(
    global: GlobalContext,
    current_module: String,
    /// Local variable bindings as a stack (for De Bruijn index conversion)
    /// The index in the list represents the De Bruijn index
    local_scope: List(String),
    /// Stack of loop contexts (for nested loops)
    loop_stack: List(LoopContext),
    /// Constructor definitions from type declarations
    ctrs: CtrEnv,
  )
}

/// Add a local variable to the scope.
fn add_local(dc: DesugarContext, name: String) -> DesugarContext {
  let DesugarContext(global, current_module, local_scope, loop_stack, ctrs) = dc
  DesugarContext(global, current_module, [name, ..local_scope], loop_stack, ctrs)
}

/// Enter a loop context.
fn enter_loop(dc: DesugarContext, fix_name: String) -> DesugarContext {
  let DesugarContext(global, current_module, local_scope, loop_stack, ctrs) = dc
  DesugarContext(global, current_module, local_scope, [InLoop(fix_name, BreakReturns), ..loop_stack], ctrs)
}

/// Exit the current loop context.
fn exit_loop(dc: DesugarContext) -> DesugarContext {
  let DesugarContext(global, current_module, local_scope, loop_stack, ctrs) = dc
  case loop_stack {
    [] -> dc  // Should not happen if well-formed
    [_loop, ..rest] -> DesugarContext(global, current_module, local_scope, rest, ctrs)
  }
}

/// Check if we're inside a loop.
fn in_loop(dc: DesugarContext) -> Bool {
  case dc.loop_stack {
    [] -> False
    [_loop, ..] -> True
  }
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

/// Process type definitions to populate constructor environment.
fn process_type_definitions(
  stmts: List(Stmt),
  dc: DesugarContext,
) -> DesugarContext {
  list.fold(stmts, dc, fn(acc_dc, stmt) {
    case stmt {
      StmtType(name, type_params, constructors, _span) -> {
        // Add the type itself as a constructor (types are constructors of universes)
        // The type constructor has no arguments and returns Typ(0) (the universe)
        let type_ctr = #(name, CtrDef(params: type_params, arg_ty: Unit(Span("unit", 0, 0, 0, 0)), ret_ty: Typ(0, Span("type", 0, 0, 0, 0))))
        let new_ctrs = tao_type_to_core_ctrs(name, type_params, constructors)
        let all_ctrs = [type_ctr, ..new_ctrs]
        DesugarContext(..acc_dc, ctrs: list.append(acc_dc.ctrs, all_ctrs))
      }
      _ -> acc_dc
    }
  })
}

/// Convert a Tao type definition to Core constructor definitions.
fn tao_type_to_core_ctrs(
  type_name: String,
  type_params: List(String),
  constructors: List(Constructor),
) -> CtrEnv {
  list.map(constructors, fn(ctr) {
    let ctr_def = tao_constructor_to_ctr_def(type_name, type_params, ctr)
    #(ctr.name, ctr_def)
  })
}

/// Convert a Tao constructor to a Core CtrDef.
fn tao_constructor_to_ctr_def(
  type_name: String,
  type_params: List(String),
  constructor: Constructor,
) -> CtrDef {
  let Constructor(_name, fields, _span) = constructor
  
  let arg_ty = case fields {
    [] -> Unit(Span("unit", 0, 0, 0, 0))
    [field] -> constructor_field_to_type(field)
    fields -> {
      let field_types = list.index_map(fields, fn(field, index) {
        case field {
          UnnamedField(t) -> #("field_" <> int.to_string(index), type_ast_to_core(t))
          NamedField(name, t) -> #(name, type_ast_to_core(t))
        }
      })
      Rcd(field_types, Span("rcd", 0, 0, 0, 0))
    }
  }
  
  let ret_ty = build_type_app(type_name, type_params)
  
  CtrDef(params: type_params, arg_ty: arg_ty, ret_ty: ret_ty)
}

/// Convert a constructor field to a Core type.
fn constructor_field_to_type(field: ConstructorField) -> Term {
  case field {
    UnnamedField(t) -> type_ast_to_core(t)
    NamedField(_name, t) -> type_ast_to_core(t)
  }
}

/// Build type application: TypeName(param1, param2, ...)
fn build_type_app(type_name: String, type_params: List(String)) -> Term {
  let span = Span("type_app", 0, 0, 0, 0)
  case type_params {
    [] -> Ctr(type_name, Unit(span), span)
    _params -> Ctr(type_name, Unit(span), span)
  }
}

/// Convert Tao TypeAst to Core Term.
/// Note: This is a simplified version that doesn't handle type parameters.
/// Use build_core_type_from_ast for full type annotation support.
fn type_ast_to_core(t: TypeAst) -> Term {
  case t {
    TVar(name) -> {
      // Check if this is a known builtin type
      case name {
        "I32" -> LitT(I32T, Span("i32", 0, 0, 0, 0))
        "I64" -> LitT(I64T, Span("i64", 0, 0, 0, 0))
        "F32" -> LitT(F32T, Span("f32", 0, 0, 0, 0))
        "F64" -> LitT(F64T, Span("f64", 0, 0, 0, 0))
        "Bool" -> Ctr("Bool", Unit(Span("unit", 0, 0, 0, 0)), Span("bool", 0, 0, 0, 0))
        _ -> Hole(0, Span("type_var", 0, 0, 0, 0))
      }
    }
    TApp(name, _args) -> Ctr(name, Unit(Span("unit", 0, 0, 0, 0)), Span("tapp", 0, 0, 0, 0))
    TFn(_params, _ret) -> Typ(1, Span("fn", 0, 0, 0, 0))
    TRecord(_fields) -> Typ(0, Span("rcd", 0, 0, 0, 0))
    TTuple(_elems) -> Typ(0, Span("tuple", 0, 0, 0, 0))
    THole -> Hole(0, Span("hole", 0, 0, 0, 0))
  }
}

// ============================================================================
// TYPE ANNOTATION BUILDING (Phase 1)
// ============================================================================

/// Convert Tao TypeAst to Core type term for type annotations.
/// Returns the Core type and updated context.
fn build_core_type_from_ast(t: TypeAst, dc: DesugarContext, span: Span) -> #(CoreTerm, DesugarContext) {
  case t {
    TVar(name) -> {
      // Check if this is a known builtin type or a type variable
      case name {
        "I32" -> #(CoreBuiltinType("I32T", span), dc)
        "I64" -> #(CoreBuiltinType("I64T", span), dc)
        "F32" -> #(CoreBuiltinType("F32T", span), dc)
        "F64" -> #(CoreBuiltinType("F64T", span), dc)
        "Bool" -> #(CoreCtr("Bool", CoreUnit(span), span), dc)
        "Option" -> #(CoreCtr("Option", CoreUnit(span), span), dc)
        "Result" -> #(CoreCtr("Result", CoreUnit(span), span), dc)
        "String" -> #(CoreBuiltinType("String", span), dc)
        _ -> {
          // Check if it's a type defined in the current context
          case lookup_type_in_ctrs(dc.ctrs, name) {
            True -> #(CoreCtr(name, CoreUnit(span), span), dc)
            False -> #(CoreHole(0, span), dc)  // Unknown type, use hole
          }
        }
      }
    }
    TApp(type_name, args) -> {
      // Type application: Option(Bool), List(I32), etc.
      let base = case lookup_type_in_ctrs(dc.ctrs, type_name) {
        True -> CoreCtr(type_name, CoreUnit(span), span)
        False -> CoreHole(0, span)
      }
      let #(core_args, dc1) = build_core_type_args(args, dc, span)
      #(build_type_applications(base, core_args, span), dc1)
    }
    TFn(params, ret) -> {
      // Function type: (I32, Bool) -> Bool
      // For now, use a simple Pi type representation
      let #(core_params, dc1) = build_core_type_args(params, dc, span)
      let #(core_ret, dc2) = build_core_type_from_ast(ret, dc1, span)
      let fn_type = build_fn_type(core_params, core_ret, span)
      #(fn_type, dc2)
    }
    TRecord(_fields) -> {
      // Record type - use hole for now
      #(CoreHole(0, span), dc)
    }
    TTuple(_elems) -> {
      // Tuple type - use hole for now
      #(CoreHole(0, span), dc)
    }
    THole -> {
      // Type hole - let inference fill it in
      #(CoreHole(0, span), dc)
    }
  }
}

/// Build type applications: Base(Arg1, Arg2, ...)
fn build_type_applications(base: CoreTerm, args: List(CoreTerm), span: Span) -> CoreTerm {
  case args {
    [] -> base
    [arg] -> CoreApp(base, arg, span)
    [arg, ..rest] -> {
      let app = CoreApp(base, arg, span)
      build_type_applications(app, rest, span)
    }
  }
}

/// Build list of type arguments.
fn build_core_type_args(args: List(TypeAst), dc: DesugarContext, span: Span) -> #(List(CoreTerm), DesugarContext) {
  let #(reversed_terms, final_dc) = list.fold(args, #([], dc), fn(acc, arg) {
    let #(terms, dc_acc) = acc
    let #(core_term, dc_new) = build_core_type_from_ast(arg, dc_acc, span)
    #([core_term, ..terms], dc_new)
  })
  #(list.reverse(reversed_terms), final_dc)
}

/// Build function type from parameter types and return type.
/// For a function (a: A, b: B) -> C, builds: Pi(_, A, Pi(_, B, C))
fn build_fn_type(param_types: List(CoreTerm), ret_type: CoreTerm, span: Span) -> CoreTerm {
  // Build nested Pi types: Pi(_, param1, Pi(_, param2, ... ret_type))
  // Using fold with reverse to simulate foldr
  let reversed = list.reverse(param_types)
  list.fold(reversed, ret_type, fn(acc, param_ty) {
    CorePi([], "_", param_ty, acc, span)
  })
}

/// Check if a type name exists in the constructor environment.
fn lookup_type_in_ctrs(ctrs: CtrEnv, type_name: String) -> Bool {
  case list.find(ctrs, fn(ctr) { ctr.0 == type_name }) {
    Ok(_) -> True
    Error(_) -> False
  }
}

/// Desugar a Tao module to a Core term.
pub fn desugar_module(
  module: Module,
  ctx: GlobalContext,
) -> #(Term, DesugarContext) {
  let dc = DesugarContext(
    global: ctx,
    current_module: module.path,
    local_scope: [],
    loop_stack: [],
    ctrs: [],
  )

  let dc_with_types = process_type_definitions(module.body, dc)

  // Check if the last statement is an expression (for expression-style modules)
  let last_is_expr = is_last_stmt_expr(module.body)

  case last_is_expr {
    True -> {
      // Expression-style module: separate the last expression from the bindings
      // First, desugar all statements EXCEPT the last one
      let all_but_last = drop_last(module.body)
      let #(core_stmts, dc1) = desugar_stmts(all_but_last, dc_with_types)

      // Then, desugar the last expression with the accumulated scope
      let last_stmt = get_last_stmt(module.body)
      let #(core_result, _dc2) = case last_stmt {
        StmtExpr(value, _span) -> {
          desugar_expr_core(value, dc1)
        }
        StmtRun(value, run_span) -> {
          // Run statement: evaluate and return as module result
          desugar_expr_core(value, dc1)
        }
        StmtTest(test_name, body, test_span) -> {
          // Test statement: evaluate body but return Unit
          let #(core_body, dc_test) = desugar_expr_core(body, dc1)
          #(CoreDoBlock([core_body], CoreUnit(test_span), test_span), dc_test)
        }
        _ -> #(CoreRcd([], module.span), dc1)
      }

      let core_term = CoreDoBlock(core_stmts, core_result, module.span)
      let term = core_term_to_term(core_term)
      #(term, dc1)
    }
    False -> {
      // Declaration-style module: desugar all statements and return a record
      let #(core_stmts, dc1) = desugar_stmts(module.body, dc_with_types)
      let public_names = get_public_names(module.body)
      case public_names {
        [] -> {
          let core_term = CoreDoBlock(core_stmts, CoreRcd([], module.span), module.span)
          let term = core_term_to_term(core_term)
          #(term, dc1)
        }
        names -> {
          let return_fields = list.map(names, fn(name) {
            #(name, CoreVar(name, module.span))
          })
          let core_term = CoreDoBlock(core_stmts, CoreRcd(return_fields, module.span), module.span)
          let term = core_term_to_term(core_term)
          #(term, dc1)
        }
      }
    }
  }
}

fn drop_last(list: List(a)) -> List(a) {
  case list {
    [] -> []
    [_] -> []
    [x, ..rest] -> [x, ..drop_last(rest)]
  }
}

fn get_last_stmt(list: List(Stmt)) -> Stmt {
  case list {
    [] -> StmtExpr(ExprVar("__error__", Span("error", 0, 0, 0, 0)), Span("error", 0, 0, 0, 0))
    [x] -> x
    [_x, ..rest] -> get_last_stmt(rest)
  }
}

/// Check if the last statement in a list is an expression statement.
fn is_last_stmt_expr(stmts: List(Stmt)) -> Bool {
  case stmts {
    [] -> False
    [stmt] -> {
      case stmt {
        StmtExpr(_, _) -> True
        StmtRun(_, _) -> True  // Run statement also determines module output
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
    [stmt, ..rest] -> {
      case stmt {
        CoreLet(name, value, _let_span) -> {
          // let x = e in rest  =>  (λx. process_rest) e
          let body = build_sequential_loop(rest, result, span)
          let lam = CoreLam(name, body, span)
          CoreApp(lam, value, span)
        }
        _ -> {
          // Non-let statements are evaluated and discarded, continue with rest
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
      let #(core_stmts, dc1) = desugar_stmt(stmt, dc)
      desugar_stmts_loop(rest, list.append(core_stmts, acc), dc1)
    }
  }
}

/// Desugar a single statement to Core terms.
pub fn desugar_stmt(
  stmt: Stmt,
  dc: DesugarContext,
) -> #(List(CoreTerm), DesugarContext) {
  case stmt {
    StmtLet(name, mutable, type_ann, value, span) -> {
      let #(core_value, dc1) = desugar_expr_core(value, dc)
      // If there's a type annotation, wrap the value in a CoreAnn
      let core_let_value = case type_ann {
        Some(type_ast) -> {
          let #(core_type, _dc2) = desugar_type_ast(type_ast, dc1)
          CoreAnn(core_value, core_type, span)
        }
        None -> core_value
      }
      let core_let = CoreLet(name, core_let_value, span)
      let dc2 = add_local(dc1, name)
      #([core_let], dc2)
    }

    StmtFn(name, type_params, params, return_type, body, span) -> {
      // Function → let name = fix name -> λparam1. λparam2. ... body
      // For recursive functions, wrap the lambda in a fixpoint
      // Add name to scope BEFORE building lambda so recursive calls can find it
      let dc_with_name = add_local(dc, name)
      // Functions with no params need a dummy param for Unit to support f() calls
      let params_with_unit = case params {
        [] -> [Param("_unit", None, span)]
        _ -> params
      }
      // Build lambda with parameter type annotations
      let #(core_lam, dc1) = build_lambdas_with_annotations(type_params, params_with_unit, body, span, dc_with_name)

      // KEY FIX: Build the full function type from parameter and return type annotations.
      // This allows the type checker to CHECK the lambda against the expected function type,
      // which provides domain types for each parameter.
      let core_fix = case return_type {
        Some(ret_ty_ast) -> {
          // Build function type: param1_ty -> param2_ty -> ... -> return_ty
          let #(core_ret_ty, _dc2) = build_core_type_from_ast(ret_ty_ast, dc1, span)
          let function_type = build_function_type(params_with_unit, core_ret_ty, span, dc1)
          CoreFix(name, CoreAnn(core_lam, function_type, span), span)
        }
        None -> CoreFix(name, core_lam, span)
      }

      let core_let = CoreLet(name, core_fix, span)
      let dc3 = add_local(dc1, name)
      #([core_let], dc3)
    }

    StmtImport(import_item, span) -> {
      // Import → let aliases
      let core_terms = desugar_import(import_item, dc, span)
      // Add all bindings to the context
      let dc1 = add_import_bindings(dc, core_terms)
      #(core_terms, dc1)
    }

    StmtType(_name, _type_params, _constructors, _span) -> {
      // Type definitions are processed in process_type_definitions
      // They don't produce Core terms - just populate the constructor environment
      #([], dc)
    }

    StmtExpr(value, span) -> {
      let #(core_expr, dc1) = desugar_expr_core(value, dc)
      #([core_expr], dc1)
    }

    StmtFor(pattern, collection, body, span) -> {
      // for pattern in collection { body... }
      // Desugar to: iterate over collection, binding pattern for each iteration
      let #(core_term, dc1) = desugar_for(pattern, collection, body, span, dc)
      #([core_term], dc1)
    }

    StmtWhile(condition, body, span) -> {
      // while condition { body... }
      // Desugar to: recursive fixpoint that checks condition and executes body
      let #(core_term, dc1) = desugar_while(condition, body, span, dc)
      #([core_term], dc1)
    }

    StmtLoop(body, span) -> {
      // loop { body... }
      // Desugar to: infinite loop using fixpoint
      let #(core_term, dc1) = desugar_loop(body, span, dc)
      #([core_term], dc1)
    }

    StmtBreak(span) -> {
      // break - exit current loop
      // Desugar to: return unit (exits the fixpoint)
      // The loop context tracks the fixpoint name for proper handling
      case in_loop(dc) {
        True -> #([CoreRcd([], span)], dc)
        False -> #([CoreErr("break outside of loop", span)], dc)
      }
    }

    StmtContinue(span) -> {
      // continue - skip to next iteration
      // Desugar to: recursive call to the current loop's fixpoint
      case dc.loop_stack {
        [InLoop(fix_name, _break_target), ..] -> {
          // Make recursive call to the loop fixpoint
          #([CoreApp(CoreVar(fix_name, span), CoreRcd([], span), span)], dc)
        }
        [] -> {
          #([CoreErr("continue outside of loop", span)], dc)
        }
      }
    }

    StmtReturn(value, span) -> {
      // return [expr] - return from function
      // Desugar to: the return value (or unit if none)
      // Note: This returns from the enclosing function, not just the loop
      case value {
        Some(expr) -> {
          let #(core_expr, dc1) = desugar_expr_core(expr, dc)
          #([core_expr], dc1)
        }
        None -> #([CoreRcd([], span)], dc)
      }
    }

    StmtYield(value, span) -> {
      // yield expr - produce a value in a generator
      // Desugar to: the yielded expression
      // Note: Full generator support requires continuation-passing style
      // For now, just return the expression
      let #(core_expr, dc1) = desugar_expr_core(value, dc)
      #([core_expr], dc1)
    }

    StmtTest(test_name, body, test_span) -> {
      // Test statement: evaluate the body
      // The test name is for the test harness, not the compiler
      let #(core_body, dc1) = desugar_expr_core(body, dc)
      // Return Unit to indicate test completed
      #([CoreDoBlock([core_body], CoreUnit(test_span), test_span)], dc1)
    }

    StmtRun(value, span) -> {
      // Run statement: evaluate and return the value
      // This is handled specially in desugar_module for module output
      let #(core_value, dc1) = desugar_expr_core(value, dc)
      #([core_value], dc1)
    }

    // Fallback for unimplemented statements
    _ -> #([CoreErr("Statement not yet implemented", get_stmt_span(stmt))], dc)
  }
}

/// Get span from any statement.
fn get_stmt_span(stmt: Stmt) -> Span {
  case stmt {
    StmtLet(_, _, _, _, span) -> span
    StmtFn(_, _, _, _, _, span) -> span
    StmtImport(_, span) -> span
    StmtType(_, _, _, span) -> span
    StmtExpr(_, span) -> span
    StmtFor(_, _, _, span) -> span
    StmtWhile(_, _, span) -> span
    StmtLoop(_, span) -> span
    StmtBreak(span) -> span
    StmtContinue(span) -> span
    StmtReturn(_, span) -> span
    StmtYield(_, span) -> span
    StmtTest(_, _, span) -> span
    StmtRun(_, span) -> span
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
      // import prelude/bool → let True = True, let False = False (for prelude)
      // For other modules, create a module alias
      case path {
        "prelude/bool" -> {
          // Prelude constructors are available by name in the core language
          // No need to create bindings - they're looked up in s.ctrs during type checking
          []
        }
        "prelude/option" -> {
          // Prelude constructors are available by name in the core language
          // No need to create bindings - they're looked up in s.ctrs during type checking
          []
        }
        "prelude/result" -> {
          // Prelude constructors are available by name in the core language
          // No need to create bindings - they're looked up in s.ctrs during type checking
          []
        }
        "prelude/ordering" -> {
          // Prelude constructors are available by name in the core language
          // No need to create bindings - they're looked up in s.ctrs during type checking
          []
        }
        _ -> {
          // For non-prelude modules, create a module alias
          let alias = path_to_alias(path)
          let module_ref = create_module_record(path, dc, span)
          [CoreLet(alias, module_ref, span)]
        }
      }
    }

    ImportAlias(path, alias, _) -> {
      // import math/trig as trig → let trig = @math/trig
      let module_ref = create_module_record(path, dc, span)
      [CoreLet(alias, module_ref, span)]
    }

    ImportSelective(path, items, _) -> {
      // import prelude/bool {True, False, not}
      // Constructors (True, False) are in s.ctrs - no binding needed
      // Builtin functions (not) need a binding that refers to them by name
      case path {
        "prelude/bool" -> {
          // Filter out constructor names and create bindings for functions
          list.flat_map(items, fn(item) {
            case item {
              ImportName(name, alias) -> {
                case name {
                  "True" | "False" -> []  // Constructors - no binding needed
                  _ -> {
                    // Function/type - create a binding
                    let binding_name = case alias {
                      Some(a) -> a
                      None -> name
                    }
                    [CoreLet(binding_name, CoreVar(name, span), span)]
                  }
                }
              }
              _ -> []
            }
          })
        }
        "prelude/option" -> {
          // Some, None are constructors - no binding needed
          list.flat_map(items, fn(item) {
            case item {
              ImportName(name, alias) -> {
                case name {
                  "Some" | "None" -> []  // Constructors
                  _ -> {
                    let binding_name = case alias {
                      Some(a) -> a
                      None -> name
                    }
                    [CoreLet(binding_name, CoreVar(name, span), span)]
                  }
                }
              }
              _ -> []
            }
          })
        }
        "prelude/result" -> {
          // Ok, Err are constructors - no binding needed
          list.flat_map(items, fn(item) {
            case item {
              ImportName(name, alias) -> {
                case name {
                  "Ok" | "Err" -> []  // Constructors
                  _ -> {
                    let binding_name = case alias {
                      Some(a) -> a
                      None -> name
                    }
                    [CoreLet(binding_name, CoreVar(name, span), span)]
                  }
                }
              }
              _ -> []
            }
          })
        }
        "prelude/ordering" -> {
          // LT, EQ, GT are constructors - no binding needed
          list.flat_map(items, fn(item) {
            case item {
              ImportName(name, alias) -> {
                case name {
                  "LT" | "EQ" | "GT" -> []  // Constructors
                  _ -> {
                    let binding_name = case alias {
                      Some(a) -> a
                      None -> name
                    }
                    [CoreLet(binding_name, CoreVar(name, span), span)]
                  }
                }
              }
              _ -> []
            }
          })
        }
        _ -> {
          // For non-prelude modules, use CoreDot
          let module_ref = create_module_record(path, dc, span)
          list.flat_map(items, fn(item) {
            desugar_import_item(item, module_ref, path, span)
          })
        }
      }
    }

    ImportSelectiveAlias(path, alias, items, _) -> {
      // import math/trig as trig {sin, cos}
      // → let trig = @math/trig
      //   let sin = trig.sin
      //   let cos = trig.cos
      let module_ref = create_module_record(path, dc, span)
      let module_binding = CoreLet(alias, module_ref, span)
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
      let module_ref = create_module_record(path, dc, span)
      let module_binding = CoreLet(alias, module_ref, span)
      
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

/// Create a module Record term for a given path.
fn create_module_record(path: String, dc: DesugarContext, span: Span) -> CoreTerm {
  // For prelude modules, create a Record with the actual constructors
  // For other modules, create a Record with holes
  case path {
    "prelude/bool" -> {
      // Bool module has True and False constructors
      CoreRcd([
        #("Bool", CoreHole(0, span)),
        #("True", CoreCtr("True", CoreUnit(span), span)),
        #("False", CoreCtr("False", CoreUnit(span), span)),
        #("not", CoreHole(1, span)),
        #("and", CoreHole(2, span)),
        #("or", CoreHole(3, span)),
      ], span)
    }
    "prelude/option" -> {
      // Option module has Some and None constructors
      CoreRcd([
        #("Option", CoreHole(0, span)),
        #("Some", CoreCtr("Some", CoreHole(1, span), span)),
        #("None", CoreCtr("None", CoreUnit(span), span)),
      ], span)
    }
    "prelude/result" -> {
      // Result module has Ok and Err constructors
      CoreRcd([
        #("Result", CoreHole(0, span)),
        #("Ok", CoreCtr("Ok", CoreHole(1, span), span)),
        #("Err", CoreCtr("Err", CoreHole(2, span), span)),
      ], span)
    }
    "prelude/ordering" -> {
      // Ordering module has LT, EQ, GT constructors
      CoreRcd([
        #("Ordering", CoreHole(0, span)),
        #("LT", CoreCtr("LT", CoreUnit(span), span)),
        #("EQ", CoreCtr("EQ", CoreUnit(span), span)),
        #("GT", CoreCtr("GT", CoreUnit(span), span)),
      ], span)
    }
    _ -> {
      // For non-prelude modules, get the public names and create a Record with holes
      case get_module_public_names(dc.global, path) {
        Some(public_names) -> {
          let fields = create_module_fields(public_names, path, span, 0)
          CoreRcd(fields, span)
        }
        None -> {
          // Module not found - create empty Record
          CoreRcd([], span)
        }
      }
    }
  }
}

fn create_module_fields(
  names: List(String),
  path: String,
  span: Span,
  base_id: Int,
) -> List(#(String, CoreTerm)) {
  case names {
    [] -> []
    [name, ..rest] -> {
      // Create a unique hole ID based on the path and name
      let hole_id = hash_path_name(path, name, base_id)
      [#(name, CoreHole(hole_id, span)), ..create_module_fields(rest, path, span, base_id + 1)]
    }
  }
}

fn hash_path_name(path: String, name: String, seed: Int) -> Int {
  // Simple hash function to create unique hole IDs
  // In practice, this should be a proper hash function
  let path_hash = string.length(path) * 1000
  let name_hash = string.length(name) * 10
  path_hash + name_hash + seed
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
      // Import name from module - use CoreDot to access module field
      [CoreLet(name, CoreDot(module_ref, name, span), span)]
    }
    ImportName(name, Some(alias)) -> {
      [CoreLet(alias, CoreDot(module_ref, name, span), span)]
    }
    ImportType(name, None) -> {
      // Type import - bind the type from module
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
  // Desugar to: fixpoint that iterates over collection
  // fix for_loop -> match collection { | [] -> () | x::xs -> let pattern = x in body; for_loop() }

  // Desugar the collection expression
  let #(core_collection, dc1) = desugar_expr_core(collection, dc)

  // Enter loop context for break/continue handling
  let dc2 = enter_loop(dc1, "for_loop")

  // Desugar the body statements
  let #(core_body_stmts, dc3) = desugar_stmts(body, dc2)

  // Exit loop context
  let dc4 = exit_loop(dc3)

  // Bind the collection
  let collection_binding = CoreLet("_for_collection", core_collection, span)

  // Build the fixpoint body: match collection { | [] -> () | x::xs -> ... }
  // Empty list case: return unit (loop done)
  let nil_clause = Case(
    pattern: PPCtr("Nil", PUnit),
    body: core_term_to_term(CoreRcd([], span)),
    guard: None,
    span: span,
  )

  // Cons case: bind head to pattern, execute body, recurse
  // for x in xs { body } → match xs { | x::rest -> body; for_loop() | _ -> () }
  let loop_call = CoreApp(CoreVar("for_loop", span), CoreRcd([], span), span)
  
  case pattern {
    ast.PVar(name, _pattern_span) -> {
      // for x in collection { body } → match collection { | x::rest -> body; for_loop() | _ -> () }
      let body_with_rec = CoreDoBlock(core_body_stmts, loop_call, span)
      
      // Use PAs to bind the head to the pattern variable
      let cons_clause = Case(
        pattern: PPCtr("Cons", PAs(PAny, name)),
        body: core_term_to_term(body_with_rec),
        guard: None,
        span: span,
      )
      
      let match_core = CoreMatchCore(
        arg: CoreVar("_for_collection", span),
        motive: CoreRcd([], span),
        cases: [cons_clause, nil_clause],
        span: span,
      )
      
      let fix = CoreFix("for_loop", match_core, span)
      let result = CoreDoBlock([collection_binding], fix, span)
      #(result, dc4)
    }
    ast.PAny(_pattern_span) -> {
      // for _ in collection { body } → match collection { | _::rest -> body; for_loop() | _ -> () }
      let body_with_rec = CoreDoBlock(core_body_stmts, loop_call, span)
      
      let cons_clause = Case(
        pattern: PPCtr("Cons", PAs(PAny, "_for_head")),
        body: core_term_to_term(body_with_rec),
        guard: None,
        span: span,
      )
      
      let match_core = CoreMatchCore(
        arg: CoreVar("_for_collection", span),
        motive: CoreRcd([], span),
        cases: [cons_clause, nil_clause],
        span: span,
      )
      
      let fix = CoreFix("for_loop", match_core, span)
      let result = CoreDoBlock([collection_binding], fix, span)
      #(result, dc4)
    }
    // For complex patterns, use wildcard
    _ -> {
      let body_with_rec = CoreDoBlock(core_body_stmts, loop_call, span)
      
      let cons_clause = Case(
        pattern: PPCtr("Cons", PAs(PAny, "_for_head")),
        body: core_term_to_term(body_with_rec),
        guard: None,
        span: span,
      )
      
      let match_core = CoreMatchCore(
        arg: CoreVar("_for_collection", span),
        motive: CoreRcd([], span),
        cases: [cons_clause, nil_clause],
        span: span,
      )
      
      let fix = CoreFix("for_loop", match_core, span)
      let result = CoreDoBlock([collection_binding], fix, span)
      #(result, dc4)
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

  // Enter loop context for break/continue handling
  let dc2 = enter_loop(dc1, "while_loop")

  // Desugar the body statements
  let #(core_body_stmts, dc3) = desugar_stmts(body, dc2)

  // Exit loop context
  let dc4 = exit_loop(dc3)

  // Body block that ends with recursive call
  let loop_call = CoreApp(CoreVar("while_loop", span), CoreRcd([], span), span)
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

  let fix = CoreFix("while_loop", match_core, span)

  #(fix, dc4)
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

  // Enter loop context for break/continue handling
  let dc1 = enter_loop(dc, "loop")

  // Desugar the body statements
  let #(core_body_stmts, dc2) = desugar_stmts(body, dc1)

  // Exit loop context
  let dc3 = exit_loop(dc2)

  // Body block that ends with recursive call
  let loop_call = CoreApp(CoreVar("loop", span), CoreRcd([], span), span)
  let body_with_rec = CoreDoBlock(core_body_stmts, loop_call, span)

  // Wrap in fixpoint
  let fix = CoreFix("loop", body_with_rec, span)

  #(fix, dc3)
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
      // Empty calls f() become f(Unit), non-empty calls f(x) become f(x)
      let core_app = case core_args {
        [] -> CoreApp(core_fun, CoreRcd([], span), span)
        _ -> build_apps(core_fun, core_args, span)
      }
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
      let core_ctr = case core_args {
        [] -> CoreCtr(name, CoreUnit(span), span)
        [first] -> CoreCtr(name, first, span)
        _ -> {
          // Multiple arguments: use record with numeric fields
          let fields = build_tuple_fields(core_args, 0, [])
          CoreCtr(name, CoreRcd(fields, span), span)
        }
      }
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

    ast.Test(test_name, body, test_span) -> {
      // Test statement: evaluate the body
      // The test name is for the test harness, not the compiler
      // Tests evaluate their body but return Unit
      let #(core_body, dc1) = desugar_expr_core(body, dc)
      // Return Unit to indicate test completed
      #(CoreDoBlock([core_body], CoreUnit(test_span), test_span), dc1)
    }

    ast.Run(value, span) -> {
      // Run statement: evaluate and return the value as module result
      desugar_expr_core(value, dc)
    }

    // Placeholder for unimplemented expressions
    _ -> #(CoreErr("Expression not yet implemented", get_expr_span(expr)), dc)
  }
}

/// Desugar a type AST to a CoreTerm.
fn desugar_type_ast(
  type_ast: TypeAst,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  // Type ASTs are converted to Core terms
  // For now, just convert to a variable or application
  case type_ast {
    ast.TVar(name) -> {
      // Type variable - use a hole for now
      #(CoreHole(0, Span(name, 0, 0, 0, 0)), dc)
    }
    ast.TApp(name, args) -> {
      // Type application - build nested applications
      let #(core_args, dc1) = desugar_type_args(args, dc)
      let base = case name {
        "I32" -> CoreBuiltinType("I32T", Span(name, 0, 0, 0, 0))
        "I64" -> CoreBuiltinType("I64T", Span(name, 0, 0, 0, 0))
        "U32" -> CoreBuiltinType("U32T", Span(name, 0, 0, 0, 0))
        "U64" -> CoreBuiltinType("U64T", Span(name, 0, 0, 0, 0))
        "F32" -> CoreBuiltinType("F32T", Span(name, 0, 0, 0, 0))
        "F64" -> CoreBuiltinType("F64T", Span(name, 0, 0, 0, 0))
        "Bool" -> CoreVar("Bool", Span(name, 0, 0, 0, 0))
        "Option" -> CoreVar("Option", Span(name, 0, 0, 0, 0))
        "Result" -> CoreVar("Result", Span(name, 0, 0, 0, 0))
        _ -> CoreVar(name, Span(name, 0, 0, 0, 0))
      }
      let core_type = build_core_type_app(base, core_args, Span(name, 0, 0, 0, 0))
      #(core_type, dc1)
    }
    ast.TFn(_, _) -> {
      // Function type - use a hole for now
      #(CoreHole(0, Span("fn", 0, 0, 0, 0)), dc)
    }
    ast.TRecord(_) -> {
      // Record type - use a hole for now
      #(CoreHole(0, Span("record", 0, 0, 0, 0)), dc)
    }
    ast.TTuple(_) -> {
      // Tuple type - use a hole for now
      #(CoreHole(0, Span("tuple", 0, 0, 0, 0)), dc)
    }
    ast.THole -> {
      // Hole - use a hole
      #(CoreHole(0, Span("_", 0, 0, 0, 0)), dc)
    }
  }
}

fn desugar_type_args(
  args: List(TypeAst),
  dc: DesugarContext,
) -> #(List(CoreTerm), DesugarContext) {
  list.fold(args, #([], dc), fn(acc, arg) {
    let #(core_args, dc1) = acc
    let #(core_arg, dc2) = desugar_type_ast(arg, dc1)
    #([core_arg, ..core_args], dc2)
  })
}

fn build_core_type_app(base: CoreTerm, args: List(CoreTerm), span: Span) -> CoreTerm {
  case args {
    [] -> base
    [arg, ..rest] -> {
      let inner = build_core_type_app(base, rest, span)
      CoreApp(inner, arg, span)
    }
  }
}

/// Desugar a type expression to a CoreTerm.
fn desugar_type_expr(
  type_expr: Expr,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  // Type expressions are simplified - just desugar as a regular expression
  // The type checker will handle the actual type semantics
  desugar_expr_core(type_expr, dc)
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
    LitInt(n) -> core.I32(n)
    LitFloat(f) -> core.F64(f)
    LitString(_s) -> core.I32(0)  // Strings not directly supported in core literals
  }
}

/// Convert a literal to Core term.
fn literal_to_core(literal: Literal, span: Span) -> CoreTerm {
  case literal {
    LitInt(n) -> CoreLit(int.to_string(n), span)
    LitFloat(f) -> CoreLit(float.to_string(f), span)
    LitString(s) -> CoreLit(s, span)
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

// ============================================================================
// TYPE ANNOTATION LAMBDAS (Phase 1)
// ============================================================================

/// Build nested lambdas with type annotations on parameters.
fn build_lambdas_with_annotations(
  type_params: List(String),
  value_params: List(Param),
  body: Expr,
  span: Span,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  // For now, ignore type params (they're erased at runtime)
  build_value_lambdas_with_annotations(value_params, body, span, dc)
}

fn build_value_lambdas_with_annotations(
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
      let #(inner_body, dc2) = build_value_lambdas_with_annotations(rest, body, span, dc1)

      // KEY FIX: Don't wrap the inner lambda with CoreAnn. Instead, just build
      // the lambda normally. Parameter type annotations will be used during
      // type checking via check(Lam) with expected VPi type.
      // The return type annotation (if any) should be on the outermost fixpoint.
      let core_lam = CoreLam(param.name, inner_body, span)
      #(core_lam, dc2)
    }
  }
}

/// Build the full function type from parameter and return type annotations.
/// Returns: param1_ty -> param2_ty -> ... -> return_ty
fn build_function_type(
  params: List(Param),
  return_ty: CoreTerm,
  span: Span,
  dc: DesugarContext,
) -> CoreTerm {
  case params {
    [] -> return_ty
    [param, ..rest] -> {
      // Build domain type from parameter annotation (or hole if no annotation)
      let domain_ty = case param.type_annotation {
        Some(ty_ast) -> {
          let #(core_ty, _dc) = build_core_type_from_ast(ty_ast, dc, span)
          core_ty
        }
        None -> CoreHole(-1, span)  // Placeholder hole, will be filled by type checker
      }
      // Build Pi type: domain -> codomain
      let codomain_ty = build_function_type(rest, return_ty, span, dc)
      CorePi([], param.name, domain_ty, codomain_ty, span)
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
    [] -> fun  // No args - return the function as-is
    [arg] -> CoreApp(fun, arg, span)  // Single arg - one application
    [arg, ..rest] -> {
      // Multiple args - build nested applications
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
  // For non-dependent matches, use a hole motive that will be unified with the result type.
  // The hole ID -999 is used as a placeholder - the type checker will unify it with the
  // actual result type inferred from the clause bodies.
  // Using a large negative ID to avoid conflicts with type checker's hole counter.
  let motive = CoreLam("_", CoreHole(-999, span), span)
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
      // Wildcard pattern (AST)
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
      // Or pattern: simplified to PAny (full support needs core changes)
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
      // End of list: Nil
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
    [first, ..rest_rest] -> {
      // More elements: Cons(h, t)
      let #(core_first, dc1) = tao_pattern_to_core_pattern(first, dc)
      let #(core_rest, dc2) = tao_list_rest_pattern_to_core(rest_rest, rest_name, dc1)
      #(PPCtr("Cons", core_first), dc2)
    }
  }
}

/// Build tuple fields for constructor with multiple arguments.
fn build_tuple_fields(
  args: List(CoreTerm),
  index: Int,
  acc: List(#(String, CoreTerm)),
) -> List(#(String, CoreTerm)) {
  case args {
    [] -> list.reverse(acc)
    [arg, ..rest] -> {
      let field_name = int.to_string(index)
      build_tuple_fields(rest, index + 1, [#(field_name, arg), ..acc])
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
  // Debug: print the term being converted
  // io.println("Converting: " <> debug_core_term(term) <> " with env: " <> inspect(env))
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
    CoreModuleRef(_, span) -> {
      // Module reference - should have been replaced by create_module_record
      // Fallback to a hole
      Hole(0, span)
    }
    CoreLam(param, body, span) -> {
      // Add parameter to environment for the body
      // Use a hole for the parameter type to enable type inference
      Lam(
        implicit: [],
        param: #(param, Hole(-1, span)),
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
      // Let bindings are handled by CoreDoBlock - this shouldn't be reached
      // Just convert the value and ignore the binding
      core_term_to_term_loop(value, env)
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
      // Try to parse as integer first
      case int.parse(value) {
        Ok(n) -> Lit(value: I32(n), span: span)
        Error(_) -> {
          // Not an integer - try float
          case float.parse(value) {
            Ok(f) -> Lit(value: F64(f), span: span)
            Error(_) -> {
              // String literal - core language doesn't support strings directly
              // For now, represent as unit to avoid type errors
              // A full implementation would represent strings as arrays of characters
              Unit(span)
            }
          }
        }
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
    CoreCtr(tag, arg, span) -> {
      // Convert CoreCtr to core/core.Ctr
      Ctr(tag, core_term_to_term_loop(arg, env), span)
    }
    CorePi(implicit, name, domain, codomain, span) -> {
      // Convert CorePi to core/core.Pi (dependent function type)
      Pi(
        implicit: implicit,
        name: name,
        in_term: core_term_to_term_loop(domain, env),
        out_term: core_term_to_term_loop(codomain, env),
        span: span,
      )
    }
    CoreAnn(term, typ, span) -> {
      // Convert CoreAnn to core/core.Ann (type annotation)
      Ann(
        core_term_to_term_loop(term, env),
        core_term_to_term_loop(typ, env),
        span,
      )
    }
    CoreUnit(span) -> {
      // Convert CoreUnit to core/core.Unit
      Unit(span)
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
    CoreCtr(_, _, span) -> span
    CorePi(_, _, _, _, span) -> span
    CoreAnn(_, _, span) -> span
    CoreUnit(span) -> span
    CoreErr(_, span) -> span
  }
}
