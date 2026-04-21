// ============================================================================
// TAO GLOBAL CONTEXT
// ============================================================================
/// Global context for tracking all modules during compilation.
///
/// Each .tao file compiles to a Record containing all public names.
/// Modules are stored as @path records (e.g., @math/trig, @math).
///
/// For detailed documentation see:
/// - [Import System](../../docs/plans/tao/12-import-system.md)
/// - [Stmt System](../../docs/plans/tao/13-stmt-system.md)

import gleam/dict.{type Dict}
import gleam/list
import gleam/int
import gleam/option.{type Option, Some, None}
import gleam/result
import gleam/string
import syntax/grammar.{type ParseResult, type Span, Span}
import tao/prelude_data
import tao/ast.{type Module, Module as ModuleCtr, get_public_names, StmtType, type Stmt, StmtExpr, StmtImport, StmtFn, StmtLet, type Constructor, Constructor as Ctor, type ConstructorField, NamedField, UnnamedField, type TypeAst, TVar, TApp, THole, TFn, TRecord, TTuple, Param}
import tao/import_ast.{
  ImportModule, ImportAlias, ImportSelective, ImportSelectiveAlias,
  ImportWildcard, type Import,
}
import tao/syntax.{parse_module, type Expr, TypeDecl as ExprTypeDecl, type ConstructorDecl, ConstructorDecl as CtorDecl, expr_to_ast, get_expr_span, block_to_ast, Import as ExprImport, SimpleFn as ExprSimpleFn, Let as ExprLet}
import core/ast as core_ast
import simplifile

// ============================================================================
// GLOBAL CONTEXT
// ============================================================================

/// Global context tracking all modules.
pub type GlobalContext {
  GlobalContext(
    /// Map from module path to module reference
    modules: Dict(String, ModuleRef),
    /// Current module being compiled (for error messages)
    current_module: Option(String),
  )
}

/// Module reference - tracks a module's public names.
pub type ModuleRef {
  ModuleRef(
    /// Module path (e.g., "math/trig", "math")
    path: String,
    /// Public names exported by this module
    public_names: List(String),
    /// Constructor definitions from this module's type declarations
    ctr_env: core_ast.CtrEnv,
    /// Source module AST
    source: Option(Module),
  )
}

// ============================================================================
// PUBLIC API
// ============================================================================

/// Create a new empty global context.
pub fn new_context() -> GlobalContext {
  GlobalContext(
    modules: dict.new(),
    current_module: None,
  )
}

/// Set the current module being compiled.
pub fn set_current_module(ctx: GlobalContext, path: String) -> GlobalContext {
  GlobalContext(..ctx, current_module: Some(path))
}

/// Get the current module path.
pub fn get_current_module(ctx: GlobalContext) -> Option(String) {
  ctx.current_module
}

/// Register a module placeholder in the global context.
/// This creates a ModuleRef with empty ctr_env, allowing circular references.
pub fn register_module(
  ctx: GlobalContext,
  path: String,
  module: Module,
) -> GlobalContext {
  register_module_with_ctr_env(ctx, path, module, [])
}

/// Register a module with its constructor environment.
/// The ctr_env should contain type definitions extracted from the module.
pub fn register_module_with_ctr_env(
  ctx: GlobalContext,
  path: String,
  module: Module,
  ctr_env: core_ast.CtrEnv,
) -> GlobalContext {
  let public_names = get_public_names(module.body)
  let module_ref = ModuleRef(
    path: path,
    public_names: public_names,
    ctr_env: ctr_env,
    source: Some(module),
  )

  GlobalContext(
    ..ctx,
    modules: dict.insert(ctx.modules, path, module_ref),
  )
}

/// Get a module reference by path.
pub fn get_module(ctx: GlobalContext, path: String) -> Option(ModuleRef) {
  case dict.get(ctx.modules, path) {
    Ok(module_ref) -> Some(module_ref)
    Error(_) -> None
  }
}

/// Check if a module exists.
pub fn has_module(ctx: GlobalContext, path: String) -> Bool {
  case dict.get(ctx.modules, path) {
    Ok(_) -> True
    Error(_) -> False
  }
}

/// Get a module's public names.
pub fn get_module_public_names(
  ctx: GlobalContext,
  path: String,
) -> Option(List(String)) {
  case dict.get(ctx.modules, path) {
    Ok(module_ref) -> Some(module_ref.public_names)
    Error(_) -> None
  }
}

/// Check if a name is exported by a module.
pub fn is_exported(
  ctx: GlobalContext,
  module_path: String,
  name: String,
) -> Bool {
  case get_module_public_names(ctx, module_path) {
    Some(names) -> list.contains(names, name)
    None -> False
  }
}

// ============================================================================
// MODULE PATH UTILITIES
// ============================================================================

/// Convert a file path to a module path.
/// E.g., "src/math/trig.tao" → "math/trig"
pub fn path_to_module_path(file_path: String) -> String {
  file_path
  |> string.replace("src/", "")
  |> string.replace(".tao", "")
  |> string.replace("/", "/")
}

/// Get the directory path from a module path.
/// E.g., "math/trig" → "math"
pub fn module_directory(module_path: String) -> String {
  case string.split(module_path, "/") {
    [dir, ..] -> dir
    [] -> module_path
  }
}

/// Get the base name from a module path.
/// E.g., "math/trig" → "trig"
pub fn module_base_name(module_path: String) -> String {
  case string.split(module_path, "/") {
    parts -> {
      case list.last(parts) {
        Ok(name) -> name
        Error(_) -> module_path
      }
    }
  }
}

/// Check if a module is a prelude module.
pub fn is_prelude_module(module_path: String) -> Bool {
  string.starts_with(module_path, "prelude")
}

// ============================================================================
// IMPORT RESOLUTION
// ============================================================================

/// Resolve an import to a module path.
pub fn resolve_import(
  ctx: GlobalContext,
  import_item: Import,
  _current_module: String,
) -> Result(String, String) {
  let module_path = case import_item {
    ImportModule(path: path, ..) -> path
    ImportAlias(path: path, ..) -> path
    ImportSelective(path: path, ..) -> path
    ImportSelectiveAlias(path: path, ..) -> path
    ImportWildcard(path: path, ..) -> path
  }
  
  // Check if module exists
  case has_module(ctx, module_path) {
    True -> Ok(module_path)
    False -> Error("Module not found: " <> module_path)
  }
}

/// Get all modules in a directory (for directory imports).
pub fn get_directory_modules(
  ctx: GlobalContext,
  dir_path: String,
) -> List(String) {
  get_directory_modules_loop(ctx.modules, dir_path, [])
}

fn get_directory_modules_loop(
  modules: Dict(String, ModuleRef),
  dir_path: String,
  acc: List(String),
) -> List(String) {
  case dict.to_list(modules) {
    [] -> list.reverse(acc)
    [pair, ..rest] -> {
      let #(path, _) = pair
      case string.starts_with(path, dir_path) {
        True -> get_directory_modules_loop(
          dict.from_list(rest),
          dir_path,
          [path, ..acc],
        )
        False -> get_directory_modules_loop(
          dict.from_list(rest),
          dir_path,
          acc,
        )
      }
    }
  }
}

// ============================================================================
// CONSTRUCTOR ENVIRONMENT EXTRACTION
// ============================================================================

/// Extract constructor definitions from parsed module expressions.
/// This processes TypeDecl expressions directly from the parser output.
pub fn extract_ctr_env_from_exprs(exprs: List(Expr)) -> core_ast.CtrEnv {
  extract_ctr_env_from_exprs_loop(exprs, [])
}

fn extract_ctr_env_from_exprs_loop(
  exprs: List(Expr),
  acc: core_ast.CtrEnv,
) -> core_ast.CtrEnv {
  case exprs {
    [] -> acc
    [expr, ..rest] -> {
      case expr {
        ExprTypeDecl(name, _type_params, ctors, span) -> {
          // Add the type itself as a constructor
          let type_ctr = #(name, core_ast.CtrDef(
            params: [],
            arg_ty: core_ast.Typ(0, Span("unit", 0, 0, 0, 0)),
            ret_ty: core_ast.Typ(0, Span("type", 0, 0, 0, 0)),
          ))
          let new_ctrs = decl_type_to_core_ctrs(name, ctors, span)
          let all_ctrs = [type_ctr, ..new_ctrs]
          extract_ctr_env_from_exprs_loop(rest, list.append(acc, all_ctrs))
        }
        _ -> extract_ctr_env_from_exprs_loop(rest, acc)
      }
    }
  }
}

/// Convert a TypeDecl's constructors to Core CtrDefs.
fn decl_type_to_core_ctrs(
  type_name: String,
  ctors: List(ConstructorDecl),
  span: Span,
) -> core_ast.CtrEnv {
  list.map(ctors, fn(ctr) {
    let CtorDecl(name, _fields, _ctr_span) = ctr
    // Fields are stored as strings - for now create simple Unit args
    let arg_ty = core_ast.Typ(0, Span("unit", 0, 0, 0, 0))
    let ret_ty = core_ast.Ctr(type_name, core_ast.Unit(Span("unit", 0, 0, 0, 0)), span)
    let ctr_def = core_ast.CtrDef(params: [], arg_ty: arg_ty, ret_ty: ret_ty)
    #(name, ctr_def)
  })
}

/// Build type application: TypeName(param1, param2, ...)
pub fn build_type_app(type_name: String, type_params: List(String)) -> core_ast.Term {
  let span = Span("type_app", 0, 0, 0, 0)
  core_ast.Ctr(type_name, core_ast.Unit(span), span)
}

/// Extract constructor definitions from a module's type declarations.
/// This is used to populate ctr_env when registering modules.
pub fn extract_ctr_env_from_module(module: Module) -> core_ast.CtrEnv {
  extract_ctr_env_loop(module.body, [])
}

fn extract_ctr_env_loop(
  stmts: List(Stmt),
  acc: core_ast.CtrEnv,
) -> core_ast.CtrEnv {
  case stmts {
    [] -> acc
    [stmt, ..rest] -> {
      case stmt {
        StmtType(name, type_params, constructors, _span) -> {
          // Add the type itself as a constructor
          let type_ctr = #(name, core_ast.CtrDef(
            params: type_params,
            arg_ty: core_ast.Typ(0, Span("unit", 0, 0, 0, 0)),
            ret_ty: core_ast.Typ(0, Span("type", 0, 0, 0, 0)),
          ))
          let new_ctrs = tao_type_to_core_ctrs(name, type_params, constructors)
          let all_ctrs = [type_ctr, ..new_ctrs]
          extract_ctr_env_loop(rest, list.append(acc, all_ctrs))
        }
        _ -> extract_ctr_env_loop(rest, acc)
      }
    }
  }
}

/// Convert a Tao type definition to Core constructor definitions.
pub fn tao_type_to_core_ctrs(
  type_name: String,
  type_params: List(String),
  constructors: List(Constructor),
) -> core_ast.CtrEnv {
  list.map(constructors, fn(ctr) {
    let ctr_def = tao_constructor_to_ctr_def(type_name, type_params, ctr)
    #(ctr.name, ctr_def)
  })
}

/// Convert a Tao constructor to a Core CtrDef.
pub fn tao_constructor_to_ctr_def(
  type_name: String,
  type_params: List(String),
  constructor: Constructor,
) -> core_ast.CtrDef {
  let Ctor(_name, fields, _span) = constructor

  let arg_ty = case fields {
    [] -> core_ast.Typ(0, Span("unit", 0, 0, 0, 0))
    [field] -> constructor_field_to_type(field)
    fields -> {
      let field_types = list.index_map(fields, fn(field, index) {
        case field {
          UnnamedField(t) -> #("field_" <> int.to_string(index), type_ast_to_core(t))
          NamedField(name, t) -> #(name, type_ast_to_core(t))
        }
      })
      core_ast.Rcd(field_types, Span("rcd", 0, 0, 0, 0))
    }
  }

  let ret_ty = build_type_app(type_name, type_params)

  core_ast.CtrDef(params: type_params, arg_ty: arg_ty, ret_ty: ret_ty)
}

/// Convert a constructor field to a Core type.
pub fn constructor_field_to_type(field: ConstructorField) -> core_ast.Term {
  case field {
    UnnamedField(t) -> type_ast_to_core(t)
    NamedField(_name, t) -> type_ast_to_core(t)
  }
}

/// Convert a Tao TypeAst to a Core term. Exposed for desugar.gleam to
/// avoid duplication. Uses simplified Core terms — full type annotation
/// building should use `build_core_type_from_ast` instead.
pub fn type_ast_to_core(t: TypeAst) -> core_ast.Term {
  case t {
    TVar(name) -> core_ast.Ctr(name, core_ast.Unit(Span("unit", 0, 0, 0, 0)), Span("type", 0, 0, 0, 0))
    TApp(name, _args) -> core_ast.Ctr(name, core_ast.Unit(Span("unit", 0, 0, 0, 0)), Span("tapp", 0, 0, 0, 0))
    TFn(_, _) -> core_ast.Typ(1, Span("fn", 0, 0, 0, 0))
    TRecord(_) -> core_ast.Typ(0, Span("rcd", 0, 0, 0, 0))
    TTuple(_) -> core_ast.Typ(0, Span("tuple", 0, 0, 0, 0))
    THole -> core_ast.Hole(0, Span("hole", 0, 0, 0, 0))
  }
}

// ============================================================================
// ERROR HANDLING
// ============================================================================

/// Create an error placeholder module reference.
pub fn error_module_ref(path: String, _error: String) -> ModuleRef {
  ModuleRef(
    path: path,
    public_names: [],
    ctr_env: [],
    source: None,
  )
}

/// Register an error placeholder in the global context.
pub fn register_error_module(
  ctx: GlobalContext,
  path: String,
  error: String,
) -> GlobalContext {
  let error_ref = error_module_ref(path, error)
  GlobalContext(
    ..ctx,
    modules: dict.insert(ctx.modules, path, error_ref),
  )
}

/// Strip test lines from source code (lines starting with > are test annotations).
/// Test lines are not valid module syntax and must be removed before parsing.
fn strip_test_lines(source: String) -> String {
  source
  |> string.split("\n")
  |> list.filter(fn(line) {
    let trimmed = string.trim(line)
    !string.starts_with(trimmed, ">")
  })
  |> string.join("\n")
}

/// Convert expressions to statements.
fn exprs_to_stmts(exprs: List(Expr)) -> List(Stmt) {
  list.map(exprs, fn(expr) {
    case expr {
      ExprTypeDecl(name, type_params, constructors, span) -> {
        StmtType(name, type_params, list.map(constructors, fn(ctr) {
          case ctr {
            CtorDecl(ctr_name, _fields, ctr_span) ->
              Ctor(ctr_name, [], ctr_span)
          }
        }), span)
      }
      ExprImport(import_item, span) -> {
        StmtImport(import_item, span)
      }
      ExprSimpleFn(name, params, return_type, body, span) -> {
        let ast_params = list.map(params, fn(param) {
          let #(pname, ptype) = param
          let ast_type = case ptype {
            Some(type_name) -> Some(TVar(type_name))
            None -> None
          }
          Param(pname, ast_type, span)
        })
        let ast_body = block_to_ast(body)
        let ast_return_type = case return_type {
          Some(type_name) -> Some(TVar(type_name))
          None -> None
        }
        StmtFn(name, [], ast_params, ast_return_type, ast_body, span)
      }
      // Let binding at module level: let x = expr
      ExprLet(name, mutable, type_annotation, value, span) -> {
        let ast_type = case type_annotation {
          Some(type_name) -> Some(TVar(type_name))
          None -> None
        }
        let ast_value = expr_to_ast(value)
        StmtLet(name, mutable, ast_type, ast_value, span)
      }
      _ -> StmtExpr(expr_to_ast(expr), get_expr_span(expr))
    }
  })
}

// ============================================================================
// INITIALIZATION
// ============================================================================

/// Initialize global context with prelude modules by reading their source files.
/// This extracts type definitions from prelude source files and registers them,
/// avoiding any hardcoded prelude knowledge in the compiler.
pub fn with_prelude(ctx: GlobalContext) -> GlobalContext {
  // List of prelude module paths (relative to lib/)
  let prelude_paths = prelude_data.prelude_paths()

  // Register each prelude module by reading and parsing its source file
  register_prelude_modules_loop(ctx, prelude_paths)
}

fn register_prelude_modules_loop(
  ctx: GlobalContext,
  paths: List(String),
) -> GlobalContext {
  case paths {
    [] -> ctx
    [path, ..rest] -> {
      let file_path = "lib/" <> path <> ".tao"
      case simplifile.read(file_path) {
        Ok(source) -> {
          // Strip test lines before parsing (test lines starting with > are not valid module syntax)
          let code_only = strip_test_lines(source)
          let parse_result = parse_module(code_only, path <> ".tao")
          let body = exprs_to_stmts(parse_result.ast)
          let ctr_env = extract_ctr_env_from_exprs(parse_result.ast)
          // Store the full module body so imports can resolve function types
          let module = ModuleCtr(path, body, Span(path, 0, 0, 0, 0))
          let ctx1 = register_module_with_ctr_env(ctx, path, module, ctr_env)
          register_prelude_modules_loop(ctx1, rest)
        }
        Error(_) -> {
          // If file not found, register placeholder
          let ctx1 = register_module_placeholder(ctx, path)
          register_prelude_modules_loop(ctx1, rest)
        }
      }
    }
  }
}

/// Register a prelude module placeholder when source file is not available.
fn register_module_placeholder(ctx: GlobalContext, path: String) -> GlobalContext {
  let public_names = prelude_data.prelude_public_names(path)
  let module_ref = ModuleRef(
    path: path,
    public_names: public_names,
    ctr_env: [],
    source: None,
  )
  GlobalContext(
    ..ctx,
    modules: dict.insert(ctx.modules, path, module_ref),
  )
}
