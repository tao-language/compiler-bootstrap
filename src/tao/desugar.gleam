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

import gleam/dict
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
  tao_type_to_core_ctrs,
  tao_constructor_to_ctr_def,
  build_type_app,
  constructor_field_to_type,
}
import tao/import_ast.{
  type Import, ImportModule, ImportAlias, ImportSelective,
  ImportSelectiveAlias, ImportWildcard,
  type ImportItem, ImportName, ImportType, ImportOperator,
}
import core/ast as core_ast
import tao/language_config as lang_config

// ============================================================================
// CORE TERM TYPES (simplified for desugaring)
// ============================================================================
/// Simplified Core term representation for desugaring.
/// Full Core terms are in src/core/core.gleam

/// A single match case (body and guard are CoreTerm, converted later in core_term_to_term_loop)
pub type CoreCase {
  CoreCase(pattern: core_ast.Pattern, body: CoreTerm, guard: Option(CoreTerm), span: Span)
}

pub type CoreTerm {
  /// Variable reference
  CoreVar(name: String, span: Span)

  /// Builtin function call (add, sub, mul, etc.)
  CoreCall(name: String, args: List(CoreTerm), span: Span)

  /// Module reference (@path)
  CoreModuleRef(path: String, span: Span)

  /// Lambda abstraction
  CoreLam(param: String, param_type: Option(CoreTerm), body: CoreTerm, span: Span)

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

  /// Type universe (core_ast.Typ(n) represents Type(n))
  CoreTyp(universe: Int, span: Span)

  /// Builtin type reference (e.g., "String", "Int")
  CoreBuiltinType(name: String, span: Span)

  /// Hole/metavariable for type inference
  CoreHole(id: Int, span: Span)

  /// Constructor reference (resolved via State.ctrs during type checking)
  CoreCtrRef(name: String, span: Span)

  /// Literal
  CoreLit(value: String, span: Span)

  /// Pattern match with cases (cases hold CoreTerm bodies to be converted later with correct env)
  CoreMatchCore(arg: CoreTerm, motive: CoreTerm, cases: List(CoreCase), span: Span)

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
    ctrs: core_ast.CtrEnv,
    /// Annotated function types (name -> type) for module-level bindings
    annotated_types: List(#(String, CoreTerm)),
    /// Language-specific configuration (constructors, operators, primitives)
    config: lang_config.LanguageConfig,
  )
}

/// Add a local variable to the scope.
fn add_local(dc: DesugarContext, name: String) -> DesugarContext {
  let DesugarContext(global, current_module, local_scope, loop_stack, ctrs, annotated_types, config) = dc
  DesugarContext(global, current_module, [name, ..local_scope], loop_stack, ctrs, annotated_types, config)
}

/// Create a CoreTerm with a hole (unknown type).
/// The desugarer always uses Hole(-1). During type-checking, `infer` instantiates
/// each negative hole into a fresh positive hole, ensuring uniqueness.
fn core_hole(dc: DesugarContext, span: Span) -> #(CoreTerm, DesugarContext) {
  #(CoreHole(-1, span), dc)
}

/// Enter a loop context.
fn enter_loop(dc: DesugarContext, fix_name: String) -> DesugarContext {
  let DesugarContext(global, current_module, local_scope, loop_stack, ctrs, annotated_types, config) = dc
  DesugarContext(global, current_module, local_scope, [InLoop(fix_name, BreakReturns), ..loop_stack], ctrs, annotated_types, config)
}

/// Exit the current loop context.
fn exit_loop(dc: DesugarContext) -> DesugarContext {
  let DesugarContext(global, current_module, local_scope, loop_stack, ctrs, annotated_types, config) = dc
  case loop_stack {
    [] -> dc  // Should not happen if well-formed
    [_loop, ..rest] -> DesugarContext(global, current_module, local_scope, rest, ctrs, annotated_types, config)
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
pub fn process_type_definitions(
  stmts: List(Stmt),
  dc: DesugarContext,
) -> DesugarContext {
  list.fold(stmts, dc, fn(acc_dc, stmt) {
    case stmt {
      StmtType(name, type_params, constructors, _span) -> {
        // Add the type itself as a constructor (types are constructors of universes)
        // The type constructor has no arguments and returns core_ast.Typ(0) (the universe)
        // arg_ty is Typ(0) because the argument (Unit) has type Typ(0), not VUnit
        let type_ctr = #(name, core_ast.CtrDef(params: type_params, arg_ty: core_ast.Typ(0, Span("type", 0, 0, 0, 0)), ret_ty: core_ast.Typ(0, Span("type", 0, 0, 0, 0))))
        let new_ctrs = tao_type_to_core_ctrs(name, type_params, constructors)
        let all_ctrs = [type_ctr, ..new_ctrs]
        DesugarContext(..acc_dc, ctrs: list.append(acc_dc.ctrs, all_ctrs), annotated_types: acc_dc.annotated_types)
      }
      _ -> acc_dc
    }
  })
}

// ============================================================================
// TYPE ANNOTATION BUILDING (Phase 1)
// ============================================================================

/// Convert Tao TypeAst to Core type term for type annotations.
/// Returns the Core type and updated context.
fn build_core_type_from_ast(t: TypeAst, dc: DesugarContext, span: Span) -> #(CoreTerm, DesugarContext) {
  case t {
    TVar(name) -> {
      // Check if it's a type defined in the current context (including prelude)
      case lookup_type_in_ctrs(dc.ctrs, name) {
        True -> #(CoreCtr(name, CoreUnit(span), span), dc)
        False -> core_hole(dc, span)  // Unknown type, use hole placeholder
      }
    }
    TApp(type_name, args) -> {
      // Type application: Option(Bool), List(I32), etc.
      let #(base, dc0) = case lookup_type_in_ctrs(dc.ctrs, type_name) {
        True -> #(CoreCtr(type_name, CoreUnit(span), span), dc)
        False -> core_hole(dc, span)
      }
      let #(core_args, dc1) = build_core_type_args(args, dc0, span)
      #(build_type_applications(base, core_args, span), dc1)
    }
    TFn(params, ret) -> {
      // Function type: (I32, Bool) -> Bool
      let #(core_params, dc1) = build_core_type_args(params, dc, span)
      let #(core_ret, dc2) = build_core_type_from_ast(ret, dc1, span)
      let fn_type = build_fn_type(core_params, core_ret, span)
      #(fn_type, dc2)
    }
    TRecord(_fields) -> {
      core_hole(dc, span)
    }
    TTuple(_elems) -> {
      core_hole(dc, span)
    }
    THole -> {
      core_hole(dc, span)
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

/// Desugar a call expression, handling both constructor calls and regular function calls.
fn desugar_call(
  call_fun: Expr,
  call_args: List(Expr),
  span: Span,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  // Check if this is a simple constructor call: Ctor(arg1, ..., argN)
  case call_fun, call_args {
    ast.Var(name, _), [arg, ..rest] -> {
      case list.key_find(dc.ctrs, name) {
        Ok(_) -> {
          // Constructor call - build CoreCtr with first arg, then apply rest
          let #(core_arg, dc1) = desugar_expr_core(arg, dc)
          let #(core_rest, dc2) = desugar_exprs(rest, dc1)
          let core_ctr = CoreCtr(name, core_arg, span)
          let core_app = case core_rest {
            [] -> core_ctr
            _ -> build_apps(core_ctr, core_rest, span)
          }
          #(core_app, dc2)
        }
        Error(_) -> {
          // Not a constructor - regular call
          desugar_regular_call(call_fun, call_args, span, dc)
        }
      }
    }
    _, _ -> {
      // Not a simple constructor call - regular call
      desugar_regular_call(call_fun, call_args, span, dc)
    }
  }
}

/// Desugar a regular function call (not a constructor).
fn desugar_regular_call(
  call_fun: Expr,
  call_args: List(Expr),
  span: Span,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  let #(core_fun, dc1) = desugar_expr_core(call_fun, dc)
  let #(core_args, dc2) = desugar_exprs(call_args, dc1)
  let core_app = case core_args {
    [] -> CoreApp(core_fun, CoreRcd([], span), span)
    _ -> build_apps(core_fun, core_args, span)
  }
  #(core_app, dc2)
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
/// For a function (a: A, b: B) -> C, builds: core_ast.Pi(_, A, core_ast.Pi(_, B, C))
fn build_fn_type(param_types: List(CoreTerm), ret_type: CoreTerm, span: Span) -> CoreTerm {
  // Build nested Pi types: core_ast.Pi(_, param1, core_ast.Pi(_, param2, ... ret_type))
  // Using fold with reverse to simulate foldr
  let reversed = list.reverse(param_types)
  list.fold(reversed, ret_type, fn(acc, param_ty) {
    CorePi([], "_", param_ty, acc, span)
  })
}

/// Check if a type name exists in the constructor environment.
fn lookup_type_in_ctrs(ctrs: core_ast.CtrEnv, type_name: String) -> Bool {
  case list.find(ctrs, fn(ctr) { ctr.0 == type_name }) {
    Ok(_) -> True
    Error(_) -> False
  }
}

/// Debug helper: check if a type name exists in the constructor environment and log.
fn lookup_type_in_ctrs_debug(ctrs: core_ast.CtrEnv, type_name: String) -> Bool {
  let result = lookup_type_in_ctrs(ctrs, type_name)
  // io.println("lookup_type_in_ctrs(" <> type_name <> ") -> " <> bool.to_string(result) <> " (ctrs: " <> int.to_string(list.length(ctrs)) <> ")")
  result
}

/// Collect annotated function types from module statements.
/// Returns a list of #(name, type_term) for functions with return type annotations.
fn collect_annotated_types(
  stmts: List(Stmt),
  dc: DesugarContext,
  span: Span,
) -> List(#(String, CoreTerm)) {
  collect_annotated_types_loop(stmts, dc, span, [])
}

fn collect_annotated_types_loop(
  stmts: List(Stmt),
  dc: DesugarContext,
  span: Span,
  acc: List(#(String, CoreTerm)),
) -> List(#(String, CoreTerm)) {
  case stmts {
    [] -> list.reverse(acc)
    [stmt, ..rest] -> {
      case stmt {
        StmtFn(name, _type_params, params, Some(return_type), _body, _fn_span) -> {
          // Build the function type from parameter types and return type
          let #(param_types, dc1) = build_param_types(params, dc, span)
          let #(core_ret, dc2) = build_core_type_from_ast(return_type, dc1, span)
          let fn_type = build_fn_type_from_types(param_types, core_ret, span)
          collect_annotated_types_loop(rest, dc2, span, [#(name, fn_type), ..acc])
        }
        _ -> collect_annotated_types_loop(rest, dc, span, acc)
      }
    }
  }
}

/// Build a list of parameter types from function parameters.
fn build_param_types(
  params: List(Param),
  dc: DesugarContext,
  span: Span,
) -> #(List(CoreTerm), DesugarContext) {
  build_param_types_loop(params, dc, span, [])
}

fn build_param_types_loop(
  params: List(Param),
  dc: DesugarContext,
  span: Span,
  acc: List(CoreTerm),
) -> #(List(CoreTerm), DesugarContext) {
  case params {
    [] -> #(list.reverse(acc), dc)
    [param, ..rest] -> {
      let #(core_type, dc1) = case param.type_annotation {
        Some(type_ast) -> build_core_type_from_ast(type_ast, dc, span)
        None -> core_hole(dc, span)  // Unannotated param - use hole placeholder
      }
      build_param_types_loop(rest, dc1, span, [core_type, ..acc])
    }
  }
}

/// Build a function type from a list of parameter types and a return type.
fn build_fn_type_from_types(
  param_types: List(CoreTerm),
  ret_type: CoreTerm,
  span: Span,
) -> CoreTerm {
  build_fn_type_from_types_loop(param_types, ret_type, span)
}

fn build_fn_type_from_types_loop(
  param_types: List(CoreTerm),
  ret_type: CoreTerm,
  span: Span,
) -> CoreTerm {
  case param_types {
    [] -> ret_type
    [param_type, ..rest] -> {
      let inner = build_fn_type_from_types_loop(rest, ret_type, span)
      CorePi([], "_", param_type, inner, span)
    }
  }
}

/// Desugar a Tao module to a Core term.
pub fn desugar_module(
  module: Module,
  ctx: GlobalContext,
) -> #(core_ast.Term, DesugarContext) {
  desugar_module_with_ctrs(module, ctx, [])
}

/// Desugar a Tao module to a Core term with initial constructor environment.
pub fn desugar_module_with_ctrs(
  module: Module,
  ctx: GlobalContext,
  initial_ctrs: core_ast.CtrEnv,
) -> #(core_ast.Term, DesugarContext) {
  // Use the initial constructor environment (from prelude or parent modules)
  let dc = DesugarContext(
    global: ctx,
    current_module: module.path,
    local_scope: [],
    loop_stack: [],
    ctrs: initial_ctrs,
    annotated_types: [],
    config: lang_config.default_config(),
  )

  // Process type definitions FIRST to populate constructor environment
  let dc_with_types = process_type_definitions(module.body, dc)

  // Collect annotated function types AFTER processing type definitions
  // so that type names like Bool are resolved correctly
  let annotated_types = collect_annotated_types(module.body, dc_with_types, module.span)
  let dc_with_annotated_types = DesugarContext(..dc_with_types, annotated_types: annotated_types)

  // Create implicit prelude imports ONLY if the module doesn't define its own types.
  // Modules that define their own types (like `type Bool = True | False`) don't need
  // prelude types - the local types shadow them. Adding prelude imports in this case
  // creates empty records that interfere with type-checking.
  let has_type_defs = has_type_definitions(module.body)
  let prelude_imports = case has_type_defs {
    True -> []  // Skip implicit prelude imports for self-contained modules
    False -> create_implicit_prelude_imports(dc.global, module.span)
  }

  // KEY FIX: Merge prelude constructor environment into dc.ctrs when the module
  // doesn't define its own types. This makes prelude constructors (True, False, etc.)
  // available for type checking. Without this, dc.ctrs is empty for modules that
  // rely on implicit prelude imports, causing "Constructor not found" errors.
  let dc_with_prelude_ctrs = case has_type_defs {
    True -> dc_with_annotated_types  // Local types shadow prelude, no merge needed
    False -> merge_prelude_ctr_env(dc_with_annotated_types)
  }

  // Check if the last statement is an expression (for expression-style modules)
  let last_is_expr = is_last_stmt_expr(module.body)

  case last_is_expr {
    True -> {
      // Expression-style module: separate the last expression from the bindings
      // First, desugar all statements EXCEPT the last one
      let all_but_last = drop_last(module.body)
      let #(core_stmts, dc1) = desugar_stmts(all_but_last, dc_with_prelude_ctrs)
      // Prepend prelude import statements
      let core_stmts_with_prelude = list.append(prelude_imports, core_stmts)

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

      let core_term = CoreDoBlock(core_stmts_with_prelude, core_result, module.span)
      let term = core_term_to_term_with_annotations(core_term, dc1.annotated_types)
      #(term, dc1)
    }
    False -> {
      // Declaration-style module: desugar all statements and return a record
      let #(core_stmts, dc1) = desugar_stmts(module.body, dc_with_prelude_ctrs)
      // Prepend prelude import statements
      let core_stmts_with_prelude = list.append(prelude_imports, core_stmts)
      let public_names = get_public_names(module.body)
      case public_names {
        [] -> {
          let core_term = CoreDoBlock(core_stmts_with_prelude, CoreRcd([], module.span), module.span)
          let term = core_term_to_term_with_annotations(core_term, dc1.annotated_types)
          #(term, dc1)
        }
        names -> {
          let return_fields = list.map(names, fn(name) {
            #(name, CoreVar(name, module.span))
          })
          let core_term = CoreDoBlock(core_stmts_with_prelude, CoreRcd(return_fields, module.span), module.span)
          let term = core_term_to_term_with_annotations(core_term, dc1.annotated_types)
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

/// Check if a module body contains type definitions.
fn has_type_definitions(stmts: List(Stmt)) -> Bool {
  case stmts {
    [] -> False
    [StmtType(_, _, _, _), ..] -> True
    [_, ..rest] -> has_type_definitions(rest)
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
  annotated_types: List(#(String, CoreTerm)),
) -> CoreTerm {
  build_sequential_loop(stmts, result, span, annotated_types)
}

fn build_sequential_loop(
  stmts: List(CoreTerm),
  result: CoreTerm,
  span: Span,
  annotated_types: List(#(String, CoreTerm)),
) -> CoreTerm {
  case stmts {
    [] -> result
    [stmt, ..rest] -> {
      case stmt {
        CoreLet(name, value, _let_span) -> {
          // let x = e in rest  =>  (λx. process_rest) e
          let body = build_sequential_loop(rest, result, span, annotated_types)
          // Look up the annotated type for this binding
          let param_type = case list.key_find(annotated_types, name) {
            Ok(ty) -> Some(ty)
            Error(Nil) -> None
          }
          let lam = CoreLam(name, param_type, body, span)
          CoreApp(lam, value, span)
        }
        _ -> {
          // Non-let statements are evaluated and discarded, continue with rest
          build_sequential_loop(rest, result, span, annotated_types)
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
      // First, merge the imported module's constructor environment
      let dc1 = merge_imported_ctr_env(dc, import_item)
      // Then create the import bindings
      let core_terms = desugar_import(import_item, dc1, span)
      // Add all bindings to the context
      let dc2 = add_import_bindings(dc1, core_terms)
      #(core_terms, dc2)
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

/// Merge the imported module's constructor environment into dc.ctrs.
/// This makes the imported module's types and constructors available for type-checking.
fn merge_imported_ctr_env(dc: DesugarContext, import_item: Import) -> DesugarContext {
  let module_path = case import_item {
    ImportModule(path, _) -> path
    ImportAlias(path, _, _) -> path
    ImportSelective(path, _, _) -> path
    ImportSelectiveAlias(path, _, _, _) -> path
    ImportWildcard(path, _) -> path
  }

  // Look up the imported module's ctr_env
  case get_module(dc.global, module_path) {
    Some(module_ref) -> {
      // Merge the imported module's constructors with existing ones
      DesugarContext(
        global: dc.global,
        current_module: dc.current_module,
        local_scope: dc.local_scope,
        loop_stack: dc.loop_stack,
        ctrs: list.append(dc.ctrs, module_ref.ctr_env),
        annotated_types: dc.annotated_types,
        config: dc.config,
      )
    }
    None -> dc  // Module not found - continue without merging
  }
}

/// Get a module reference from the global context.
fn get_module(global: GlobalContext, path: String) -> Option(ModuleRef) {
  case dict.get(global.modules, path) {
    Ok(mr) -> Some(mr)
    Error(_) -> None
  }
}

/// Create implicit prelude import terms for all registered prelude modules.
/// This adds wildcard imports (`import path as *`) for each prelude module.
fn create_implicit_prelude_imports(
  global: GlobalContext,
  span: Span,
) -> List(CoreTerm) {
  // Get all prelude module paths from the global context
  let prelude_paths = get_prelude_module_paths(global)
  // Create wildcard imports for each prelude module
  list.flat_map(prelude_paths, fn(path) {
    create_wildcard_import(path, span)
  })
}

/// Get all registered prelude module paths from the global context.
fn get_prelude_module_paths(global: GlobalContext) -> List(String) {
  // Prelude modules are those starting with "prelude/"
  case global.modules |> dict.to_list() {
    [] -> []
    [pair, ..rest] -> {
      let #(path, _) = pair
      case string.starts_with(path, "prelude/") {
        True -> [path, ..get_prelude_module_paths_loop(rest)]
        False -> get_prelude_module_paths_loop(rest)
      }
    }
  }
}

fn get_prelude_module_paths_loop(
  modules: List(#(String, ModuleRef)),
) -> List(String) {
  case modules {
    [] -> []
    [pair, ..rest] -> {
      let #(path, _) = pair
      case string.starts_with(path, "prelude/") {
        True -> [path, ..get_prelude_module_paths_loop(rest)]
        False -> get_prelude_module_paths_loop(rest)
      }
    }
  }
}

/// Merge constructor environments from all prelude modules into dc.ctrs.
/// This makes prelude constructors (True, False, Some, None, Ok, Err, etc.)
/// available for type checking in modules that don't define their own types.
fn merge_prelude_ctr_env(dc: DesugarContext) -> DesugarContext {
  let prelude_paths = get_prelude_module_paths(dc.global)
  list.fold(prelude_paths, dc, fn(acc, path) {
    case dict.get(acc.global.modules, path) {
      Ok(module_ref) ->
        DesugarContext(
          global: acc.global,
          current_module: acc.current_module,
          local_scope: acc.local_scope,
          loop_stack: acc.loop_stack,
          ctrs: list.append(acc.ctrs, module_ref.ctr_env),
          annotated_types: acc.annotated_types,
          config: acc.config,
        )
      Error(Nil) -> acc
    }
  })
}

/// Create a wildcard import for a module: `import path as *`
fn create_wildcard_import(path: String, span: Span) -> List(CoreTerm) {
  let alias = path_to_alias(path)
  let module_ref = CoreRcd([], span)  // Placeholder - will be filled by import resolution
  let module_binding = CoreLet(alias, module_ref, span)
  [module_binding]
}

/// Desugar an import statement to let bindings.
pub fn desugar_import(
  import_item: Import,
  dc: DesugarContext,
  span: Span,
) -> List(CoreTerm) {
  case import_item {
    ImportModule(path, _) -> {
      // import path → create a module alias
      let alias = path_to_alias(path)
      let module_ref = create_module_record(path, dc, span)
      [CoreLet(alias, module_ref, span)]
    }

    ImportAlias(path, alias, _) -> {
      // import path as alias → let alias = @path
      let module_ref = create_module_record(path, dc, span)
      [CoreLet(alias, module_ref, span)]
    }

    ImportSelective(path, items, _) -> {
      // import path {name1, name2, ...}
      // For functions, extract the actual function body from the module source
      // so evaluation works correctly (not just the type).
      let fn_bodies = get_module_function_bodies(path, dc, span)
      list.flat_map(items, fn(item) {
        desugar_import_item_with_bodies(item, path, span, dc, fn_bodies)
      })
    }

    ImportSelectiveAlias(path, alias, items, _) -> {
      // import path as alias {name1, name2, ...}
      // → let alias = @path
      //   let name1 = alias.name1
      //   let name2 = alias.name2
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
      // import path as * → let alias = @path + all exports
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
/// Uses actual function types from the module's source when available,
/// otherwise falls back to holes.
fn create_module_record(path: String, dc: DesugarContext, span: Span) -> CoreTerm {
  case get_module(dc.global, path) {
    Some(module_ref) -> {
      case module_ref.source {
        Some(module) -> {
          let body = module.body
          // Get ALL public names including types and constructors
          let all_names = get_all_public_names(body)
          let fn_types = extract_function_types(body, span, dc)
          let fields = create_fields_from_names(all_names, fn_types, span, dc.ctrs, 0)
          CoreRcd(fields, span)
        }
        None -> create_module_with_holes(path, dc, span)
      }
    }
    None -> create_module_with_holes(path, dc, span)
  }
}

/// Get all public names from a module body, including types and constructors.
fn get_all_public_names(stmts: List(Stmt)) -> List(String) {
  get_all_names_loop(stmts, [])
}

fn get_all_names_loop(stmts: List(Stmt), acc: List(String)) -> List(String) {
  case stmts {
    [] -> list.reverse(acc)
    [stmt, ..rest] -> {
      case stmt {
        StmtType(name, _, constructors, _) -> {
          // Include type name and all constructor names
          // Types/constructors are in module record so imports can reference them
          let type_names = case string.starts_with(name, "_") {
            True -> []
            False -> [name]
          }
          let ctr_names = list.flat_map(constructors, fn(ctr) {
            case ctr {
              Constructor(ctr_name, _, _) -> {
                case string.starts_with(ctr_name, "_") {
                  True -> []
                  False -> [ctr_name]
                }
              }
            }
          })
          get_all_names_loop(rest, list.append(list.append(acc, type_names), ctr_names))
        }
        StmtImport(_, _) -> get_all_names_loop(rest, acc)
        StmtExpr(_, _) -> get_all_names_loop(rest, acc)
        _ -> {
          case get_stmt_name(stmt) {
            Some(name) -> {
              case string.starts_with(name, "_") {
                True -> get_all_names_loop(rest, acc)
                False -> get_all_names_loop(rest, [name, ..acc])
              }
            }
            None -> get_all_names_loop(rest, acc)
          }
        }
      }
    }
  }
}

/// Fallback: create a module Record with holes for each public name.
fn create_module_with_holes(path: String, dc: DesugarContext, span: Span) -> CoreTerm {
  case get_module_public_names(dc.global, path) {
    Some(public_names) -> {
      let fields = create_module_fields(public_names, path, span, 0)
      CoreRcd(fields, span)
    }
    None -> CoreRcd([], span)
  }
}

/// Extract function type annotations from a module body.
fn extract_function_types(stmts: List(Stmt), span: Span, dc: DesugarContext) -> List(#(String, CoreTerm)) {
  extract_fn_types_loop(stmts, [], span, dc)
}

fn extract_fn_types_loop(stmts: List(Stmt), acc: List(#(String, CoreTerm)), span: Span, dc: DesugarContext) -> List(#(String, CoreTerm)) {
  case stmts {
    [] -> list.reverse(acc)
    [stmt, ..rest] -> {
      case stmt {
        StmtFn(name, _type_params, params, Some(return_type), _body, _fn_span) -> {
          let #(param_types, _dc1) = build_param_types(params, dc, span)
          let #(core_ret, _dc2) = build_core_type_from_ast(return_type, dc, span)
          let fn_type = build_fn_type_from_types(param_types, core_ret, span)
          extract_fn_types_loop(rest, [#(name, fn_type), ..acc], span, dc)
        }
        _ -> extract_fn_types_loop(rest, acc, span, dc)
      }
    }
  }
}

/// Create record fields from public names, using actual types where available.
/// Functions get their full Pi type, types/constructors get CoreCtrRef references
/// that the type checker resolves through the constructor environment.
fn create_fields_from_names(names: List(String), fn_types: List(#(String, CoreTerm)), span: Span, ctrs: core_ast.CtrEnv, base_id: Int) -> List(#(String, CoreTerm)) {
  case names {
    [] -> []
    [name, ..rest] -> {
      let field_value = case list.find(fn_types, fn(t) { t.0 == name }) {
        Ok(#(_n, typ)) -> typ  // Function - use extracted type
        Error(Nil) -> {
          // Type or constructor - create a constructor reference
          case lookup_type_in_ctrs(ctrs, name) {
            True -> CoreCtrRef(name, span)  // Constructor name
            False -> CoreHole(hash_path_name("", name, base_id), span)  // Unknown
          }
        }
      }
      [#(name, field_value), ..create_fields_from_names(rest, fn_types, span, ctrs, base_id + 1)]
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

/// Desugar a single import item, using actual function bodies where available.
fn desugar_import_item_with_bodies(
  item: ImportItem,
  path: String,
  span: Span,
  dc: DesugarContext,
  fn_bodies: List(#(String, CoreTerm)),
) -> List(CoreTerm) {
  case item {
    ImportName(name, None) -> {
      // Check if we have the actual function body
      case list.key_find(fn_bodies, name) {
        Ok(body) -> [CoreLet(name, body, span)]  // Use actual function body
        Error(Nil) -> {
          // No function body - use Dot into module record (for types/constructors)
          let module_ref = create_module_record(path, dc, span)
          [CoreLet(name, CoreDot(module_ref, name, span), span)]
        }
      }
    }
    ImportName(name, Some(alias)) -> {
      case list.key_find(fn_bodies, name) {
        Ok(body) -> [CoreLet(alias, body, span)]
        Error(Nil) -> {
          let module_ref = create_module_record(path, dc, span)
          [CoreLet(alias, CoreDot(module_ref, name, span), span)]
        }
      }
    }
    ImportType(name, None) -> {
      let module_ref = create_module_record(path, dc, span)
      [CoreLet(name, CoreDot(module_ref, name, span), span)]
    }
    ImportType(name, Some(alias)) -> {
      let module_ref = create_module_record(path, dc, span)
      [CoreLet(alias, CoreDot(module_ref, name, span), span)]
    }
    ImportOperator(name, None) -> {
      let var_name = string.replace(name, "+", "add")
      case list.key_find(fn_bodies, name) {
        Ok(body) -> [CoreLet(var_name, body, span)]
        Error(Nil) -> {
          let module_ref = create_module_record(path, dc, span)
          [CoreLet(var_name, CoreDot(module_ref, name, span), span)]
        }
      }
    }
    ImportOperator(name, Some(alias)) -> {
      case list.key_find(fn_bodies, name) {
        Ok(body) -> [CoreLet(alias, body, span)]
        Error(Nil) -> {
          let module_ref = create_module_record(path, dc, span)
          [CoreLet(alias, CoreDot(module_ref, name, span), span)]
        }
      }
    }
  }
}

/// Get function bodies from a module by path.
/// Process type definitions FIRST to populate constructor environment,
/// then extract function bodies with proper constructor resolution.
fn get_module_function_bodies(path: String, dc: DesugarContext, span: Span) -> List(#(String, CoreTerm)) {
  case get_module(dc.global, path) {
    Some(module_ref) -> {
      case module_ref.source {
        Some(module) -> {
          // Process type definitions to populate ctrs before extracting functions
          let dc_with_ctrs = process_imported_module_types(module.body, dc)
          extract_function_bodies(module.body, span, dc_with_ctrs)
        }
        None -> []
      }
    }
    None -> []
  }
}

/// Process type definitions from a module body to populate constructor environment.
fn process_imported_module_types(stmts: List(Stmt), dc: DesugarContext) -> DesugarContext {
  list.fold(stmts, dc, fn(acc, stmt) {
    case stmt {
      StmtType(name, type_params, constructors, _) -> {
        let type_ctr = #(name, core_ast.CtrDef(
          params: type_params,
          arg_ty: core_ast.Typ(0, Span("unit", 0, 0, 0, 0)),
          ret_ty: core_ast.Typ(0, Span("type", 0, 0, 0, 0)),
        ))
        let new_ctrs = tao_type_to_core_ctrs(name, type_params, constructors)
        let all_ctrs = [type_ctr, ..new_ctrs]
        DesugarContext(..acc, ctrs: list.append(acc.ctrs, all_ctrs))
      }
      _ -> acc
    }
  })
}

/// Extract function bodies from a module body.
fn extract_function_bodies(stmts: List(Stmt), span: Span, dc: DesugarContext) -> List(#(String, CoreTerm)) {
  extract_fn_bodies_loop(stmts, [], span, dc)
}

fn extract_fn_bodies_loop(stmts: List(Stmt), acc: List(#(String, CoreTerm)), span: Span, dc: DesugarContext) -> List(#(String, CoreTerm)) {
  case stmts {
    [] -> list.reverse(acc)
    [stmt, ..rest] -> {
      case stmt {
        StmtFn(name, type_params, params, _return_type, body, _fn_span) -> {
          // Build the function as a CoreTerm (lambda/fix)
          // Use build_lambdas_with_scope which properly handles variable scoping
          let #(core_lam, _dc1) = build_lambdas_with_scope(type_params, params, body, span, dc)
          // Wrap in Fix for recursion - the fix name must match for recursive calls to work
          let core_fix = CoreFix(name, core_lam, span)
          extract_fn_bodies_loop(rest, [#(name, core_fix), ..acc], span, dc)
        }
        _ -> extract_fn_bodies_loop(rest, acc, span, dc)
      }
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

  // Build the fixpoint body: match collection { | <list_nil> -> () | x::<list_cons> -> ... }
  // Empty list case: return unit (loop done)
  let nil_clause = CoreCase(
    pattern: core_ast.PCtr(dc.config.list_nil, core_ast.PUnit(span), span),
    body: CoreRcd([], span),
    guard: None,
    span: span,
  )

  // Cons case: bind head to pattern, execute body, recurse
  // for x in xs { body } → match xs { | x::rest -> body; for_loop() | _ -> () }
  let loop_call = CoreApp(CoreVar("for_loop", span), CoreRcd([], span), span)
  let list_cons = dc.config.list_cons
  
  case pattern {
    ast.PVar(name, pattern_span) -> {
      // for x in collection { body } → match collection { | x::rest -> body; for_loop() | _ -> () }
      let body_with_rec = CoreDoBlock(core_body_stmts, loop_call, span)
      
      // Use PAs to bind the head to the pattern variable
      let cons_clause = CoreCase(
        pattern: core_ast.PCtr(list_cons, core_ast.PAs(core_ast.PAny(pattern_span), name, pattern_span), pattern_span),
        body: body_with_rec,
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
    ast.PAny(pattern_span) -> {
      // for _ in collection { body } → match collection { | _::rest -> body; for_loop() | _ -> () }
      let body_with_rec = CoreDoBlock(core_body_stmts, loop_call, span)
      
      let cons_clause = CoreCase(
        pattern: core_ast.PCtr(list_cons, core_ast.PAs(core_ast.PAny(pattern_span), "_for_head", pattern_span), pattern_span),
        body: body_with_rec,
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
      
      let cons_clause = CoreCase(
        pattern: core_ast.PCtr(list_cons, core_ast.PAs(core_ast.PAny(span), "_for_head", span), span),
        body: body_with_rec,
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

  // Build match on condition: match condition { | <truth_ctor> -> body; loop () | _ -> () }
  // True clause: execute body and recurse (uses language config for truth constructor)
  let truth_ctor = dc.config.truth_constructor
  let true_clause = CoreCase(
    pattern: core_ast.PCtr(truth_ctor, core_ast.PUnit(span), span),
    body: body_with_rec,
    guard: None,
    span: span,
  )

  // Default clause: return unit (exit loop)
  let default_clause = CoreCase(
    pattern: core_ast.PAny(span),
    body: CoreRcd([], span),
    guard: None,
    span: span,
  )

  // Match expression as CoreTerm
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
) -> #(core_ast.Term, DesugarContext) {
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
      // KEY FIX: Check if this is a known constructor (not shadowed by a local variable).
      // The Tao parser doesn't distinguish between variables and constructors — both
      // are parsed as Var(name). We need to resolve this during desugaring.
      let is_local = list.any(dc.local_scope, fn(n) { n == name })
      case is_local {
        False -> {
          // Not a local variable — check if it's a known constructor
          case list.key_find(dc.ctrs, name) {
            Ok(_) -> #(CoreCtr(name, CoreUnit(span), span), dc)
            Error(_) -> #(CoreVar(name, span), dc)
          }
        }
        True -> #(CoreVar(name, span), dc)
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
      // KEY FIX: If this is a constructor call, build CoreCtr directly
      desugar_call(call_fun, call_args, span, dc)
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
    _ -> #(CoreErr("Expression not yet implemented: see debug", get_expr_span(expr)), dc)
  }
}

/// Desugar a type AST to a CoreTerm.
fn desugar_type_ast(
  type_ast: TypeAst,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  // Type ASTs are converted to Core terms
  case type_ast {
    ast.TVar(name) -> {
      // Check if it's a builtin type name (looked up from primitive types registry)
      case lang_config.lookup_primitive_type(dc.config.primitive_types, name) {
        Some(_) -> #(CoreBuiltinType(name, Span(name, 0, 0, 0, 0)), dc)
        None -> {
          // Type variable - check if it's a known type
          case lookup_type_in_ctrs(dc.ctrs, name) {
            True -> #(CoreCtr(name, CoreUnit(Span(name, 0, 0, 0, 0)), Span(name, 0, 0, 0, 0)), dc)
            False -> #(CoreHole(-1, Span(name, 0, 0, 0, 0)), dc)
          }
        }
      }
    }
    ast.TApp(name, args) -> {
      // Type application - build nested applications
      let #(core_args, dc1) = desugar_type_args(args, dc)
      let base = case lookup_type_in_ctrs(dc.ctrs, name) {
        True -> CoreCtr(name, CoreUnit(Span(name, 0, 0, 0, 0)), Span(name, 0, 0, 0, 0))
        False -> CoreVar(name, Span(name, 0, 0, 0, 0))
      }
      let core_type = build_core_type_app(base, core_args, Span(name, 0, 0, 0, 0))
      #(core_type, dc1)
    }
    ast.TFn(_, _) -> {
      #(CoreHole(-1, Span("fn", 0, 0, 0, 0)), dc)
    }
    ast.TRecord(_) -> {
      #(CoreHole(-1, Span("record", 0, 0, 0, 0)), dc)
    }
    ast.TTuple(_) -> {
      #(CoreHole(-1, Span("tuple", 0, 0, 0, 0)), dc)
    }
    ast.THole -> {
      #(CoreHole(-1, Span("_", 0, 0, 0, 0)), dc)
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
fn tao_literal_to_core_literal(literal: Literal) -> core_ast.Literal {
  case literal {
    LitInt(n) -> core_ast.IntLit(n)
    LitFloat(f) -> core_ast.FloatLit(f)
    LitString(_s) -> core_ast.IntLit(0)  // Strings not directly supported in core literals
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
      CoreLam(param.name, None, inner, span)
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
      let core_lam = CoreLam(param.name, None, inner_body, span)
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

      // Build parameter type from annotation (or hole if no annotation)
      let param_type = case param.type_annotation {
        Some(ty_ast) -> {
          let #(core_ty, _dc) = build_core_type_from_ast(ty_ast, dc, span)
          Some(core_ty)
        }
        None -> None
      }
      let core_lam = CoreLam(param.name, param_type, inner_body, span)
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
      // Build domain type from parameter annotation (or unique hole if no annotation)
      // KEY FIX: Use dc (current context) for each param, and pass dc1 to recursive call
      // to ensure hole counter is properly threaded through
      let #(domain_ty, dc1) = case param.type_annotation {
        Some(ty_ast) -> build_core_type_from_ast(ty_ast, dc, span)
        None -> core_hole(dc, span)  // Placeholder hole with unique ID
      }
      // Build Pi type: domain -> codomain
      let codomain_ty = build_function_type(rest, return_ty, span, dc1)
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

/// Token string representation of a binary operator (for operator map lookup).
fn binop_token(op: BinOperator) -> String {
  case op {
    OpAdd -> "+"
    OpSub -> "-"
    OpMul -> "*"
    OpDiv -> "/"
    OpMod -> "%"
    OpEq -> "=="
    OpNeq -> "/="
    OpLt -> "<"
    OpGt -> ">"
    OpLte -> "<="
    OpGte -> ">="
    OpAnd -> "and"
    OpOr -> "or"
    OpConcat -> "++"
    OpPipe -> "|>"
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
  // Convert operator token to function name using the language config's operator map
  let op_name = case lang_config.binary_op_name(dc.config, binop_token(op)) {
    Some(name) -> name
    None -> binop_to_name(op)  // Fallback for unknown operators
  }

  // Desugar operands
  let #(core_left, dc1) = desugar_expr_core(left, dc)
  let #(core_right, dc2) = desugar_expr_core(right, dc1)

  // Operator dispatch based on language config:
  // - FFI operators (add, sub, mul, div, eq, neq, lt, gt, lte, gte) use CoreCall
  // - Non-FFI operators (and, or, not, concat, pipe) call user-defined functions via App
  case lang_config.is_ffi_binary_op(dc.config, op_name) {
    True -> {
      // FFI builtin: use CoreCall
      let core_call = CoreCall(op_name, [core_left, core_right], span)
      // Wrap comparison operators in CoreAnn with the bool type from config
      let result = case op_name {
        "eq" | "neq" | "lt" | "lte" | "gt" | "gte" -> {
          CoreAnn(core_call, CoreCtr(dc.config.bool_type, CoreUnit(span), span), span)
        }
        _ -> core_call
      }
      #(result, dc2)
    }
    False -> {
      // User-defined function: use App(Var(name), arg) pattern
      // Build call: op_name(left, right) as App(App(Var(op_name), left), right)
      let app1 = CoreApp(CoreVar(op_name, span), core_left, span)
      #(CoreApp(app1, core_right, span), dc2)
    }
  }
}

/// Convert binary operator to function name (legacy fallback for operators not in the map).
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

/// Token string representation of a unary operator (for operator map lookup).
fn unaryop_token(op: UnaryOperator) -> String {
  case op {
    OpNegate -> "-"
    OpNot -> "not"
  }
}

/// Desugar unary operator to function call.
fn desugar_unaryop(
  op: UnaryOperator,
  expr: Expr,
  span: Span,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  // Convert operator token to function name using the language config's operator map
  let op_name = case lang_config.unary_op_name(dc.config, unaryop_token(op)) {
    Some(name) -> name
    None -> unaryop_to_name(op)  // Fallback for unknown operators
  }
  let #(core_expr, dc1) = desugar_expr_core(expr, dc)

  // Operator dispatch based on language config:
  // - FFI operators (negate) use CoreCall
  // - Non-FFI operators (not) call user-defined functions via App
  case lang_config.is_ffi_unary_op(dc.config, op_name) {
    True -> {
      // FFI builtin: use CoreCall
      #(CoreCall(op_name, [core_expr], span), dc1)
    }
    False -> {
      // User-defined function: use App(Var(name), arg) pattern
      #(CoreApp(CoreVar(op_name, span), core_expr, span), dc1)
    }
  }
}

/// Convert unary operator to function name (legacy fallback for operators not in the map).
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
  // The motive uses Hole(-1) as a placeholder. During type-checking, `infer`
  // instantiates each negative hole into a fresh positive hole, ensuring uniqueness.
  let #(motive_hole, dc3) = core_hole(dc2, span)
  let motive = CoreLam("_", None, motive_hole, span)
  let core_match = CoreMatchCore(core_scrutinee, motive, core_cases, span)

  #(core_match, dc3)
}

/// Desugar match clauses to Core Cases.
fn desugar_match_clauses_to_cases(
  clauses: List(MatchClause),
  span: Span,
  dc: DesugarContext,
) -> #(List(CoreCase), DesugarContext) {
  desugar_cases_loop(clauses, [], span, dc)
}

fn desugar_cases_loop(
  clauses: List(MatchClause),
  acc: List(CoreCase),
  span: Span,
  dc: DesugarContext,
) -> #(List(CoreCase), DesugarContext) {
  case clauses {
    [] -> #(list.reverse(acc), dc)
    [clause, ..rest] -> {
      let #(core_case, dc1) = desugar_single_case(clause, span, dc)
      desugar_cases_loop(rest, [core_case, ..acc], span, dc1)
    }
  }
}

/// Desugar a single match clause to a Core Case.
/// Returns CoreCase with body/guard as CoreTerm (not converted to ast.Term yet),
/// so they can be converted later with the correct environment.
fn desugar_single_case(
  clause: MatchClause,
  span: Span,
  dc: DesugarContext,
) -> #(CoreCase, DesugarContext) {
  let pattern = clause.pattern
  let guard = clause.guard
  let body = clause.body

  // Desugar the body to CoreTerm (keep as CoreTerm for later conversion)
  let #(core_body, dc1) = desugar_expr_core(body, dc)

  // Convert Tao pattern to Core pattern
  let #(core_pattern, dc2) = tao_pattern_to_core_pattern(pattern, dc1)

  // Desugar optional guard to CoreTerm (keep as CoreTerm for later conversion)
  let core_guard = case guard {
    Some(guard_expr) -> {
      let #(core_guard_term, _dc3) = desugar_expr_core(guard_expr, dc2)
      Some(core_guard_term)
    }
    None -> None
  }

  // Return CoreCase with body/guard as CoreTerm (NOT converted to ast.Term yet)
  let core_case = CoreCase(core_pattern, core_body, core_guard, span)
  #(core_case, dc2)
}

/// Convert a Tao pattern to a Core pattern.
fn tao_pattern_to_core_pattern(
  pattern: Pattern,
  dc: DesugarContext,
) -> #(core_ast.Pattern, DesugarContext) {
  case pattern {
    ast.PVar(name, pattern_span) -> {
      // Variable pattern: bind to as-pattern
      let core_pattern = core_ast.PAs(core_ast.PAny(pattern_span), name, pattern_span)
      let dc1 = add_local(dc, name)
      #(core_pattern, dc1)
    }
    ast.PAny(pattern_span) -> {
      // Wildcard pattern (AST)
      #(core_ast.PAny(pattern_span), dc)
    }
    ast.PLit(literal, pattern_span) -> {
      // Literal pattern
      let core_lit = tao_literal_to_core_literal(literal)
      #(core_ast.PLit(core_lit, pattern_span), dc)
    }
    ast.PCtr(name, args, pattern_span) -> {
      // Constructor pattern
      tao_ctr_pattern_to_core(name, args, dc, pattern_span)
    }
    ast.PRecord(field_names, pattern_span) -> {
      // Record pattern: {x, y} → {x = x, y = y}
      let core_fields = list.map(field_names, fn(field_name) {
        #(field_name, core_ast.PAs(core_ast.PAny(pattern_span), field_name, pattern_span))
      })
      let dc1 = list.fold(field_names, dc, fn(acc, name) {
        add_local(acc, name)
      })
      #(core_ast.PRcd(core_fields, pattern_span), dc1)
    }
    ast.PTuple(items, pattern_span) -> {
      // Tuple pattern: (a, b) → record with numeric fields
      tao_tuple_pattern_to_core(items, dc, pattern_span)
    }
    ast.PList(items, rest_name, pattern_span) -> {
      // List pattern: [h, ..t] or [a, b, c]
      tao_list_pattern_to_core(items, rest_name, dc, pattern_span)
    }
    ast.POr(_patterns, pattern_span) -> {
      // Or pattern: simplified to core_ast.PAny (full support needs core changes)
      #(core_ast.PAny(pattern_span), dc)
    }
    ast.PAs(inner_pattern, alias, pattern_span) -> {
      // As pattern: x @ Some(_)
      let #(core_inner, dc1) = tao_pattern_to_core_pattern(inner_pattern, dc)
      let core_pattern = core_ast.PAs(core_inner, alias, pattern_span)
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
  span: Span,
) -> #(core_ast.Pattern, DesugarContext) {
  case args {
    [] -> {
      // Nullary constructor
      #(core_ast.PCtr(name, core_ast.PUnit(span), span), dc)
    }
    [first, ..rest] -> {
      // Build nested constructor pattern
      tao_ctr_pattern_to_core_loop(name, [first, ..rest], dc, span)
    }
  }
}

fn tao_ctr_pattern_to_core_loop(
  name: String,
  args: List(Pattern),
  dc: DesugarContext,
  span: Span,
) -> #(core_ast.Pattern, DesugarContext) {
  case args {
    [] -> {
      #(core_ast.PUnit(span), dc)
    }
    [first] -> {
      // Last argument
      let #(core_first, dc1) = tao_pattern_to_core_pattern(first, dc)
      #(core_ast.PCtr(name, core_first, span), dc1)
    }
    [first, ..rest] -> {
      // Build nested pattern
      let #(core_first, dc1) = tao_pattern_to_core_pattern(first, dc)
      let #(core_rest, dc2) = tao_ctr_pattern_to_core_loop(name, rest, dc1, span)
      #(core_ast.PCtr(name, core_first, span), dc2)
    }
  }
}

/// Convert tuple pattern to Core (tuple = record with numeric fields).
fn tao_tuple_pattern_to_core(
  items: List(Pattern),
  dc: DesugarContext,
  span: Span,
) -> #(core_ast.Pattern, DesugarContext) {
  tao_tuple_pattern_loop(items, 0, [], dc, span)
}

fn tao_tuple_pattern_loop(
  items: List(Pattern),
  index: Int,
  acc: List(#(String, core_ast.Pattern)),
  dc: DesugarContext,
  span: Span,
) -> #(core_ast.Pattern, DesugarContext) {
  case items {
    [] -> {
      #(core_ast.PRcd(list.reverse(acc), span), dc)
    }
    [item, ..rest] -> {
      let field_name = int.to_string(index)
      let #(core_item, dc1) = tao_pattern_to_core_pattern(item, dc)
      tao_tuple_pattern_loop(rest, index + 1, [#(field_name, core_item), ..acc], dc1, span)
    }
  }
}

/// Convert list pattern to Core.
fn tao_list_pattern_to_core(
  items: List(Pattern),
  rest_name: Option(String),
  dc: DesugarContext,
  span: Span,
) -> #(core_ast.Pattern, DesugarContext) {
  case items {
    [] -> {
      // Empty list: <list_nil>
      case rest_name {
        Some(name) -> {
          // [..rest] or [] with rest
          let core_pattern = core_ast.PCtr(dc.config.list_nil, core_ast.PUnit(span), span)
          let dc1 = add_local(dc, name)
          #(core_ast.PAs(core_pattern, name, span), dc1)
        }
        None -> {
          #(core_ast.PCtr(dc.config.list_nil, core_ast.PUnit(span), span), dc)
        }
      }
    }
    [first, ..rest] -> {
      // Non-empty list: <list_cons>(h, t)
      let #(core_first, dc1) = tao_pattern_to_core_pattern(first, dc)
      let #(core_rest, dc2) = tao_list_rest_pattern_to_core(rest, rest_name, dc1, span)
      #(core_ast.PCtr(dc.config.list_cons, core_first, span), dc2)
    }
  }
}

fn tao_list_rest_pattern_to_core(
  rest: List(Pattern),
  rest_name: Option(String),
  dc: DesugarContext,
  span: Span,
) -> #(core_ast.Pattern, DesugarContext) {
  case rest {
    [] -> {
      // End of list: <list_nil>
      case rest_name {
        Some(name) -> {
          let core_pattern = core_ast.PCtr(dc.config.list_nil, core_ast.PUnit(span), span)
          let dc1 = add_local(dc, name)
          #(core_ast.PAs(core_pattern, name, span), dc1)
        }
        None -> {
          #(core_ast.PCtr(dc.config.list_nil, core_ast.PUnit(span), span), dc)
        }
      }
    }
    [first, ..rest_rest] -> {
      // More elements: <list_cons>(h, t)
      let #(core_first, dc1) = tao_pattern_to_core_pattern(first, dc)
      let #(core_rest, dc2) = tao_list_rest_pattern_to_core(rest_rest, rest_name, dc1, span)
      #(core_ast.PCtr(dc.config.list_cons, core_first, span), dc2)
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
      // <list_nil>
      #(CoreVar(dc.config.list_nil, span), dc)
    }
    [expr, ..rest] -> {
      let #(core_expr, dc1) = desugar_expr_core(expr, dc)
      let #(core_rest, dc2) = desugar_list_loop(rest, span, dc1)
      // <list_cons>(expr, rest)
      let cons = CoreVar(dc.config.list_cons, span)
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
      CoreLam(param.name, None, inner, span)
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
pub fn core_term_to_term(term: CoreTerm) -> core_ast.Term {
  core_term_to_term_loop(term, [], [], lang_config.default_primitive_types())
}

/// Convert a CoreTerm to a core AST term with annotated types.
/// This is needed for module-level terms where function parameter types
/// come from the `annotated_types` collected during desugaring.
pub fn core_term_to_term_with_annotations(
  term: CoreTerm,
  annotated_types: List(#(String, CoreTerm)),
) -> core_ast.Term {
  core_term_to_term_loop(term, [], annotated_types, lang_config.default_primitive_types())
}

fn core_term_to_term_loop(
  term: CoreTerm,
  env: List(String),
  annotated_types: List(#(String, CoreTerm)),
  ptypes: lang_config.PrimitiveTypes,
) -> core_ast.Term {
  // Debug: print the term being converted
  // io.println("Converting: " <> debug_core_term(term) <> " with env: " <> inspect(env))
  case term {
    CoreVar(name, span) -> {
      // Check if name is a numeric De Bruijn index
      case int.parse(name) {
        Ok(index) -> {
          // Already a De Bruijn index - use directly
          core_ast.Var(index: index, span: span)
        }
        Error(_) -> {
          // Named variable - look up in environment
          case find_var_index(env, name, 0) {
            Some(index) -> core_ast.Var(index: index, span: span)
            None -> core_ast.Var(index: 0, span: span)  // Undefined variable
          }
        }
      }
    }
    CoreCtrRef(name, span) -> {
      // Constructor reference - resolved via State.ctrs during type checking
      // Create a Ctr with Unit argument (for nullary constructors)
      core_ast.Ctr(tag: name, arg: core_ast.Unit(span), span: span)
    }
    CoreCall(name, args, span) -> {
      // Convert CoreCall to core/core.Call with typed args
      // Each arg gets paired with a type hole for inference
      let typed_args = list.map(args, fn(a) {
        let converted = core_term_to_term_loop(a, env, annotated_types, ptypes)
        #(converted, core_ast.Hole(-1, span))
      })
      let ret_type = core_ast.Hole(-1, span)
      core_ast.Call(name: name, args: typed_args, ret: ret_type, span: span)
    }
    CoreModuleRef(_, span) -> {
      // Module reference - should have been replaced by create_module_record
      // Fallback to a hole
      core_ast.Hole(0, span)
    }
    CoreLam(param, None, body, span) -> {
      // Add parameter to environment for the body
      // Use a hole for the parameter type to enable type inference
      core_ast.Lam(
        implicit: [],
        param: #(param, core_ast.Hole(-1, span)),
        body: core_term_to_term_loop(body, [param, ..env], annotated_types, ptypes),
        span: span,
      )
    }
    CoreLam(param, Some(param_type), body, span) -> {
      // Add parameter to environment for the body
      // Use the annotated type for the parameter type
      core_ast.Lam(
        implicit: [],
        param: #(param, core_term_to_term_loop(param_type, env, annotated_types, ptypes)),
        body: core_term_to_term_loop(body, [param, ..env], annotated_types, ptypes),
        span: span,
      )
    }
    CoreApp(fun, arg, span) -> {
      // KEY FIX: Detect the sequential binding pattern from build_sequential_loop:
      // CoreApp(CoreLam(name, Some(param_type), body), CoreFix(fix_name, fix_body))
      // and emit ast.Let instead of ast.App(ast.Lam, ast.Fix).
      // This avoids the extra VPi wrapping and De Bruijn index mismatch
      // that caused type failures with 3+ functions.
      case fun, arg {
        CoreLam(name, Some(_param_type), body, _lam_span), CoreFix(fix_name, fix_body, _fix_span) -> {
          // Convert the Fix value - the Fix body needs fix_name and outer names in env.
          // NOTE: Do NOT add `name` separately - it causes duplicates when fix_name == name.
          // The Fix's own name binding ([fix_name, ..env]) is sufficient.
          let fix_term = core_ast.Fix(
            fix_name,
            core_term_to_term_loop(fix_body, [fix_name, ..env], annotated_types, ptypes),
            span,
          )
          // Convert the body with name in env
          let body_term = core_term_to_term_loop(body, [name, ..env], annotated_types, ptypes)
          // Emit Let: let name = fix_value in body_term
          core_ast.Let(name, fix_term, body_term, span)
        }
        _, _ -> {
          // Regular application
          let arg_env = case fun, arg {
            CoreLam(param_name, _, _, _), CoreFix(fix_name, _, _) ->
              case param_name == fix_name {
                True -> [param_name, ..env]
                False -> [param_name, fix_name, ..env]
              }
            _, _ -> env
          }
          core_ast.App(
            fun: core_term_to_term_loop(fun, env, annotated_types, ptypes),
            implicit: [],
            arg: core_term_to_term_loop(arg, arg_env, annotated_types, ptypes),
            span: span,
          )
        }
      }
    }
    CoreRcd(fields, span) -> {
      core_ast.Rcd(
        fields: list.map(fields, fn(pair) {
          #(pair.0, core_term_to_term_loop(pair.1, env, annotated_types, ptypes))
        }),
        span: span,
      )
    }
    CoreDot(record, field, span) -> {
      core_ast.Dot(
        arg: core_term_to_term_loop(record, env, annotated_types, ptypes),
        field: field,
        span: span,
      )
    }
    CoreLet(name, value, span) -> {
      // Let bindings are handled by CoreDoBlock - this shouldn't be reached
      // Just convert the value and ignore the binding
      core_term_to_term_loop(value, env, annotated_types, ptypes)
    }
    CoreDoBlock(stmts, result, span) -> {
      let sequential_core = build_sequential_term(stmts, result, span, annotated_types)
      core_term_to_term_loop(sequential_core, env, annotated_types, ptypes)
    }
    CoreTyp(universe, span) -> {
      // Convert CoreTyp to core/core.Typ (type universe)
      core_ast.Typ(universe: universe, span: span)
    }
    CoreBuiltinType(name, span) -> {
      // Convert builtin type names to proper LiteralType terms using config
      case lang_config.lookup_primitive_type(ptypes, name) {
        Some(typ) -> core_ast.LitT(typ: typ, span: span)
        None -> core_ast.Hole(id: -1, span: span)  // Unknown type
      }
    }
    CoreHole(id, span) -> {
      // Convert CoreHole to core/core.Hole (metavariable)
      core_ast.Hole(id: id, span: span)
    }
    CoreLit(value, span) -> {
      // Try to parse as integer first — produce overloaded IntLit
      case int.parse(value) {
        Ok(n) -> core_ast.Lit(value: core_ast.IntLit(n), span: span)
        Error(_) -> {
          // Not an integer - try float — produce overloaded FloatLit
          case float.parse(value) {
            Ok(f) -> core_ast.Lit(value: core_ast.FloatLit(f), span: span)
            Error(_) -> {
              // String literal - core language doesn't support strings directly
              // For now, represent as unit to avoid type errors
              // A full implementation would represent strings as arrays of characters
              core_ast.Unit(span)
            }
          }
        }
      }
    }
    CoreMatchCore(arg, motive, cases, span) -> {
      // Convert CoreMatchCore to core/core.Match
      // KEY FIX: Convert each CoreCase body/guard with the current environment.
      // The body and guard are CoreTerm that may reference variables bound by
      // enclosing lambdas/lets/fixes. Using the current env ensures correct
      // De Bruijn indices.
      core_ast.Match(
        arg: core_term_to_term_loop(arg, env, annotated_types, ptypes),
        motive: core_term_to_term_loop(motive, env, annotated_types, ptypes),
        cases: list.map(cases, fn(core_case) {
          case core_case {
            CoreCase(pat, body, guard, cspan) -> {
              let body_term = core_term_to_term_loop(body, env, annotated_types, ptypes)
              let guard_term = case guard {
                Some(g) -> Some(core_term_to_term_loop(g, env, annotated_types, ptypes))
                None -> None
              }
              core_ast.Case(pat, body_term, guard_term, cspan)
            }
          }
        }),
        span: span,
      )
    }
    CoreFix(name, body, span) -> {
      // Convert CoreFix to core/core.Fix
      core_ast.Fix(name, core_term_to_term_loop(body, [name, ..env], annotated_types, ptypes), span)
    }
    CoreCtr(tag, arg, span) -> {
      // Convert CoreCtr to core/core.Ctr
      core_ast.Ctr(tag, core_term_to_term_loop(arg, env, annotated_types, ptypes), span)
    }
    CorePi(implicit, name, domain, codomain, span) -> {
      // Convert CorePi to core/core.Pi (dependent function type)
      core_ast.Pi(
        implicit: implicit,
        name: name,
        in_term: core_term_to_term_loop(domain, env, annotated_types, ptypes),
        out_term: core_term_to_term_loop(codomain, env, annotated_types, ptypes),
        span: span,
      )
    }
    CoreAnn(term, typ, span) -> {
      // Convert CoreAnn to core/core.Ann (type annotation)
      core_ast.Ann(
        core_term_to_term_loop(term, env, annotated_types, ptypes),
        core_term_to_term_loop(typ, env, annotated_types, ptypes),
        span,
      )
    }
    CoreUnit(span) -> {
      // Convert CoreUnit to core/core.Unit
      core_ast.Unit(span)
    }
    CoreErr(message, span) -> core_ast.Err(message: message, span: span)
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
    CoreLam(_, _, _, span) -> span
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
    CoreCtrRef(_, span) -> span
    CorePi(_, _, _, _, span) -> span
    CoreAnn(_, _, span) -> span
    CoreUnit(span) -> span
    CoreErr(_, span) -> span
  }
}
