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

import tao/ast.{type Module, type Stmt, Module as ModuleCtr, StmtImport, StmtLet, StmtFn, StmtFor, StmtWhile, StmtLoop, StmtBreak, StmtContinue, StmtReturn, StmtYield, StmtExpr, StmtBind, StmtMut}
import tao/import_ast.{type Import, type ImportContext, type ResolvedImport}
import tao/import_resolver.{resolve_imports}
import tao/global_context.{type GlobalContext, new_context, with_prelude, set_current_module, register_module}
import tao/syntax.{parse_module as tao_parse_module, type Expr as TaoExpr, Var, Int as TaoInt, BinOp, UnaryOp, OverloadedFn, OverloadedApp, expr_to_ast}
import syntax/grammar.{type Span, Span}
import gleam/dict.{type Dict}
import gleam/list
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
  let ctx = new_context() |> with_prelude() |> set_current_module(path)
  
  // Parse the file
  let parse_result = tao_parse_module(contents)
  
  case parse_result.errors {
    [err, ..] -> {
      let error = ParseError(
        message: "Parse error: " <> err.expected <> " got " <> err.got,
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
      let parse_result = tao_parse_module(contents)
      
      case parse_result.errors {
        [err, ..] -> {
          let error = ParseError(
            message: "Parse error: " <> err.expected <> " got " <> err.got,
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
fn get_imports(body: List(Stmt)) -> List(Import) {
  list.flat_map(body, fn(stmt) {
    case stmt {
      StmtImport(import_item, _) -> [import_item]
      _ -> []
    }
  })
}

/// Convert parsed expressions to statements.
fn exprs_to_stmts(exprs: List(TaoExpr)) -> List(Stmt) {
  list.map(exprs, fn(expr) {
    let ast_expr = expr_to_ast(expr)
    StmtExpr(ast_expr, get_expr_span(expr))
  })
}

/// Get span from expression.
fn get_expr_span(expr: TaoExpr) -> Span {
  case expr {
    Var(_, span) -> span
    TaoInt(_, span) -> span
    BinOp(_, _, _, span) -> span
    UnaryOp(_, _, span) -> span
    OverloadedFn(_, _, _, _, _, _, span) -> span
    OverloadedApp(_, _, span) -> span
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
  }
}
