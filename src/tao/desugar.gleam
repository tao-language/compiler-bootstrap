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

import gleam/dict.{type Dict}
import gleam/list
import gleam/int
import gleam/option.{type Option, Some, None}
import gleam/string
import syntax/grammar.{type Span, Span}
import tao/ast.{
  type Module, type Stmt, type Expr, type Param, type Pattern,
  StmtLet, StmtFn, StmtImport, StmtExpr,
  get_public_names, get_stmt_name,
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
    /// Local variable bindings (for scope tracking)
    local_scope: Dict(String, Bool),
  )
}

// ============================================================================
// PUBLIC API
// ============================================================================

/// Desugar a Tao module to a Core term.
pub fn desugar_module(
  module: Module,
  ctx: GlobalContext,
) -> #(CoreTerm, DesugarContext) {
  let dc = DesugarContext(
    global: ctx,
    current_module: module.path,
    local_scope: dict.new(),
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
  
  #(core_term, dc1)
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
      let #(core_value, dc1) = desugar_expr(value, dc)
      let core_let = CoreLet(name, core_value, span)
      let dc2 = add_local(dc1, name)
      #(core_let, dc2)
    }
    
    StmtFn(name, type_params, params, return_type, body, span) -> {
      // Function → let name = λparam1. λparam2. ... body
      let #(core_body, dc1) = desugar_expr(body, dc)
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
      let #(core_expr, dc1) = desugar_expr(value, dc)
      #(core_expr, dc1)
    }
    
    // TODO: Control flow statements
    _ -> #(CoreErr("Not yet implemented", get_stmt_span(stmt)), dc)
  }
}

/// Get span from any statement.
fn get_stmt_span(stmt: Stmt) -> Span {
  case stmt {
    StmtLet(_, _, _, _, span) -> span
    StmtFn(_, _, _, _, _, span) -> span
    StmtImport(_, span) -> span
    StmtExpr(_, span) -> span
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
// EXPRESSION DESUGARING
// ============================================================================

/// Desugar an expression to a Core term.
pub fn desugar_expr(
  expr: Expr,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  case expr {
    // TODO: Implement full expression desugaring
    // For now, return placeholders
    _ -> #(CoreErr("Expression desugaring not yet implemented", get_expr_span(expr)), dc)
  }
}

/// Get span from expression.
fn get_expr_span(expr: Expr) -> Span {
  // TODO: Implement proper span extraction
  Span("expr", 0, 0, 0, 0)
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

/// Add a local variable to the scope.
fn add_local(dc: DesugarContext, name: String) -> DesugarContext {
  DesugarContext(
    ..dc,
    local_scope: dict.insert(dc.local_scope, name, True),
  )
}

/// Check if a name is in local scope.
fn is_local(dc: DesugarContext, name: String) -> Bool {
  case dict.get(dc.local_scope, name) {
    Ok(_) -> True
    Error(_) -> False
  }
}

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
      Unit(span)
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
