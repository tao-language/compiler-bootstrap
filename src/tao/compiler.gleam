// ============================================================================
// TAO MULTI-FILE COMPILER
// ============================================================================
/// Multi-file compilation with import resolution.
///
/// Handles:
/// - Parsing multiple .tao files
/// - Resolving imports between files
/// - Building dependency graph
/// - Compiling modules in correct order
/// - Detecting circular imports

import tao/ast.{type Module, type Stmt, type Param, Module as ModuleCtr, StmtImport, StmtLet, StmtFn, StmtFor, StmtWhile, StmtLoop, StmtBreak, StmtContinue, StmtReturn, StmtYield, StmtExpr, StmtBind, StmtMut, StmtTest, StmtRun, StmtType, Param, TVar}
import tao/import_ast.{type Import as ImportType, type ImportContext, type ResolvedImport}
import tao/import_resolver.{resolve_imports}
import tao/global_context.{type GlobalContext, new_context, with_prelude, set_current_module, register_module}
import tao/syntax.{parse_module as tao_parse_module, type Expr as TaoExpr, Var, Int as TaoInt, Float as TaoFloat, BinOp, UnaryOp, OverloadedFn, OverloadedApp, Let, Block, SimpleFn, App, Lambda, Match, Str, Test, Run, If, For, While, Loop, Break, Continue, Import, Ctr, TypeDecl, expr_to_ast, block_to_ast, pattern_to_ast}
import tao/test_api.{strip_test_lines}
import syntax/grammar.{type Span, Span}
import gleam/dict.{type Dict}
import gleam/list
import gleam/option.{Some, None}
import simplifile

// ============================================================================
// TYPES
// ============================================================================

/// Result of compiling a module.
pub type CompileResult {
  CompileSuccess(
    path: String,
    module: Module,
    imports: List(ResolvedImport),
  )
  CompileError(
    path: String,
    errors: List(CompileErrorType),
  )
}

/// Error during compilation.
pub type CompileErrorType {
  ParseError(message: String, span: Span)
  ImportError(message: String, span: Span)
  CircularImport(cycle: List(String), span: Span)
  ModuleNotFound(path: String, span: Span)
}

/// Compilation state for multi-file compilation.
pub type CompileState {
  CompileState(
    /// Global context with all modules
    global: GlobalContext,
    /// Map from path to compiled module
    compiled_modules: Dict(String, Module),
    /// Map from path to import context
    import_contexts: Dict(String, ImportContext),
    /// Compilation errors
    errors: List(CompileErrorType),
    /// Files pending compilation
    pending: List(String),
    /// Files already compiled
    compiled: List(String),
  )
}

// ============================================================================
// PUBLIC API
// ============================================================================

/// Compile multiple Tao files with import resolution.
pub fn compile_files(
  file_paths: List(String),
  project_root: String,
) -> #(GlobalContext, List(CompileResult)) {
  let initial_state = CompileState(
    global: new_context() |> with_prelude(),
    compiled_modules: dict.new(),
    import_contexts: dict.new(),
    errors: [],
    pending: file_paths,
    compiled: [],
  )
  
  compile_loop(initial_state, project_root, [])
}

/// Compile a single file and return its module.
pub fn compile_single_file(
  path: String,
  contents: String,
  _project_root: String,
) -> #(GlobalContext, Module, List(CompileErrorType)) {
  // Register prelude modules as built-in placeholders
  let ctx = new_context() |> with_prelude()
  let ctx = ctx |> set_current_module(path)

  // Strip test lines before parsing (> expr ~> expected format)
  let code_only = strip_test_lines(contents)

  // Parse the file
  let parse_result = tao_parse_module(code_only, path)

  case parse_result.errors {
    [err, ..] -> {
      let error = ParseError(
        message: "Parse error: end of input got " <> err.got,
        span: err.span,
      )
      #(ctx, ModuleCtr(path, [], err.span), [error])
    }
    [] -> {
      // Convert expressions to statements
      let body = exprs_to_stmts(parse_result.ast)
      let module = ModuleCtr(path, body, get_module_span(body, path))

      // Register module in global context
      let ctx2 = register_module(ctx, path, module)

      #(ctx2, module, [])
    }
  }
}

// ============================================================================
// INTERNAL IMPLEMENTATION
// ============================================================================

fn compile_loop(
  state: CompileState,
  project_root: String,
  results: List(CompileResult),
) -> #(GlobalContext, List(CompileResult)) {
  case state.pending {
    [] -> #(state.global, list.reverse(results))
    [path, ..rest] -> {
      // Check if already compiled
      case list.contains(state.compiled, path) {
        True -> {
          // Already compiled, skip
          let new_state = CompileState(..state, pending: rest)
          compile_loop(new_state, project_root, results)
        }
        False -> {
          // Compile this file
          let #(result, new_state) = compile_single(path, state, project_root)
          compile_loop(new_state, project_root, [result, ..results])
        }
      }
    }
  }
}

fn compile_single(
  path: String,
  state: CompileState,
  project_root: String,
) -> #(CompileResult, CompileState) {
  // Read file contents
  case simplifile.read(path) {
    Error(_) -> {
      let error = ModuleNotFound(path, Span(path, 0, 0, 0, 0))
      let result = CompileError(path, [error])
      let new_state = CompileState(
        ..state,
        pending: list.filter(state.pending, fn(p) { p != path }),
        errors: [error, ..state.errors],
      )
      #(result, new_state)
    }
    Ok(contents) -> {
      // Parse the file
      let parse_result = tao_parse_module(contents, path)

      case parse_result.errors {
        [err, ..] -> {
          let error = ParseError(
            message: "Parse error: end of input got " <> err.got,
            span: err.span,
          )
          let result = CompileError(path, [error])
          let new_state = CompileState(
            ..state,
            pending: list.filter(state.pending, fn(p) { p != path }),
            compiled: [path, ..state.compiled],
            errors: [error, ..state.errors],
          )
          #(result, new_state)
        }
        [] -> {
          // Convert expressions to statements
          let body = exprs_to_stmts(parse_result.ast)
          let module_span = get_module_span(body, path)
          let module = ModuleCtr(path, body, module_span)
          
          // Resolve imports
          let imports = get_imports(body)
          let #(import_context, _resolution_results) = resolve_imports(
            imports,
            path,
            project_root,
          )
          
          // Register module in global context
          let ctx = register_module(state.global, path, module)
          
          // Add to compiled modules
          let new_state = CompileState(
            global: ctx,
            compiled_modules: dict.insert(state.compiled_modules, path, module),
            import_contexts: dict.insert(state.import_contexts, path, import_context),
            errors: state.errors,
            pending: list.filter(state.pending, fn(p) { p != path }),
            compiled: [path, ..state.compiled],
          )
          
          let result = CompileSuccess(path, module, import_context.imports)
          #(result, new_state)
        }
      }
    }
  }
}

/// Extract all imports from a module body.
fn get_imports(body: List(Stmt)) -> List(ImportType) {
  list.flat_map(body, fn(stmt) {
    case stmt {
      StmtImport(import_item, _) -> [import_item]
      _ -> []
    }
  })
}

/// Convert parsed expressions to statements.
fn exprs_to_stmts(exprs: List(TaoExpr)) -> List(Stmt) {
  list.flat_map(exprs, fn(expr) {
    case expr {
      Let(name, mutable, type_annotation, value, span) -> {
        // Convert let expression to StmtLet
        let ast_value = expr_to_ast(value)
        let ast_type = case type_annotation {
          Some(t) -> Some(TVar(t))
          None -> None
        }
        [StmtLet(name, mutable, ast_type, ast_value, span)]
      }
      SimpleFn(name, params, return_type, body, span) -> {
        // Convert function definition to StmtFn
        let ast_params = list.map(params, fn(param) {
          let #(pname, ptype) = param
          let ast_type = case ptype {
            Some(t) -> Some(TVar(t))
            None -> None
          }
          Param(pname, ast_type, span)
        })
        let ast_body = block_to_ast(body)
        let ast_return_type = case return_type {
          Some(t) -> Some(TVar(t))
          None -> None
        }
        [StmtFn(name, [], ast_params, ast_return_type, ast_body, span)]
      }
      If(_, _, _, _) -> {
        // If expressions become StmtExpr
        let ast_expr = expr_to_ast(expr)
        [StmtExpr(ast_expr, get_expr_span(expr))]
      }
      For(pattern, collection, body, span) -> {
        // For loops become StmtFor
        let ast_pattern = pattern_to_ast(pattern)
        let ast_collection = expr_to_ast(collection)
        let ast_body = exprs_to_stmts(body)
        [StmtFor(ast_pattern, ast_collection, ast_body, span)]
      }
      While(condition, body, span) -> {
        // While loops become StmtWhile
        let ast_condition = expr_to_ast(condition)
        let ast_body = exprs_to_stmts(body)
        [StmtWhile(ast_condition, ast_body, span)]
      }
      Loop(body, span) -> {
        // Loops become StmtLoop
        let ast_body = exprs_to_stmts(body)
        [StmtLoop(ast_body, span)]
      }
      Break(span) -> {
        [StmtBreak(span)]
      }
      Continue(span) -> {
        [StmtContinue(span)]
      }
      Import(import_item, span) -> {
        // Import expression becomes StmtImport
        [StmtImport(import_item, span)]
      }
      Test(name, body, span) -> {
        // Test expression becomes StmtTest
        let ast_body = expr_to_ast(body)
        [StmtTest(name, ast_body, span)]
      }
      Run(value, span) -> {
        // Run expression becomes StmtRun
        let ast_value = expr_to_ast(value)
        [StmtRun(ast_value, span)]
      }
      _ -> {
        // Other expressions become StmtExpr
        let ast_expr = expr_to_ast(expr)
        [StmtExpr(ast_expr, get_expr_span(expr))]
      }
    }
  })
}

/// Get span from expression.
fn get_expr_span(expr: TaoExpr) -> Span {
  case expr {
    Var(_, span) -> span
    TaoInt(_, span) -> span
    TaoFloat(_, span) -> span
    BinOp(_, _, _, span) -> span
    UnaryOp(_, _, span) -> span
    OverloadedFn(_, _, _, _, _, _, span) -> span
    OverloadedApp(_, _, span) -> span
    Let(_, _, _, _, span) -> span
    Block(_, span) -> span
    SimpleFn(_, _, _, _, span) -> span
    App(_, _, span) -> span
    Lambda(_, _, _, span) -> span
    Match(_, _, span) -> span
    If(_, _, _, span) -> span
    For(_, _, _, span) -> span
    While(_, _, span) -> span
    Loop(_, span) -> span
    Break(span) -> span
    Continue(span) -> span
    Str(_, span) -> span
    Test(_, _, span) -> span
    Run(_, span) -> span
    Import(_, span) -> span
    Ctr(_, _, span) -> span
    TypeDecl(_, _, _, span) -> span
  }
}

/// Get span for entire module.
fn get_module_span(body: List(Stmt), path: String) -> Span {
  case body {
    [] -> Span(path, 1, 1, 1, 1)
    [first, ..] -> {
      let first_span = get_stmt_span(first)
      Span(
        path,
        first_span.start_line,
        first_span.start_col,
        first_span.end_line,
        first_span.end_col,
      )
    }
  }
}

/// Get span from statement.
fn get_stmt_span(stmt: Stmt) -> Span {
  case stmt {
    StmtLet(_, _, _, _, span) -> span
    StmtFn(_, _, _, _, _, span) -> span
    StmtImport(_, span) -> span
    StmtType(_, _, _, span) -> span
    StmtFor(_, _, _, span) -> span
    StmtWhile(_, _, span) -> span
    StmtLoop(_, span) -> span
    StmtBreak(span) -> span
    StmtContinue(span) -> span
    StmtReturn(_, span) -> span
    StmtYield(_, span) -> span
    StmtExpr(_, span) -> span
    StmtBind(_, _, span) -> span
    StmtMut(_, _, span) -> span
    StmtTest(_, _, span) -> span
    StmtRun(_, span) -> span
  }
}
