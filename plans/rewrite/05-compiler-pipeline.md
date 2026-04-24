# Compiler Pipeline Design

## Pipeline Stages

```
┌─────────────────────────────────────────────────────────────────┐
│                        COMPILER PIPELINE                        │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  1. PARSE (Tao or Core)                                         │
│     String → Expr/Term + ParseErrors                           │
│                                                                 │
│  2. DESUGAR (Tao only)                                          │
│     Expr → Term + DesugarErrors                                │
│                                                                 │
│  3. TYPE CHECK                                                  │
│     Term → Type + TypeErrors                                   │
│                                                                 │
│  4. EVALUATE                                                    │
│     Term → Value + EvalErrors                                  │
│                                                                 │
│  5. QUOTE                                                       │
│     Value → Term                                               │
│                                                                 │
│  6. FORMAT                                                      │
│     Term → String                                              │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

## Pipeline Functions

### compiler.gleam — Multi-File Compilation

```gleam
/// Full compilation pipeline for a single Tao module
pub fn compile_tao(source: String, path: String, ctx: GlobalContext) -> CompileResult {
  // Phase 1: Parse
  let parse_result = tao_syntax.parse(source)
  let errors = parse_result.errors
  
  // Phase 2: Desugar
  let desugar_result = tao_desugar.desugar_module(parse_result.ast, ctx)
  let errors = list.append(errors, desugar_result.errors)
  
  // Phase 3: Type check
  let type_result = core_infer.check_module(desugar_result.term, ctx)
  let errors = list.append(errors, type_result.errors)
  
  // Phase 4: Evaluate
  let eval_result = core_eval.evaluate(desugar_result.term)
  let errors = list.append(errors, eval_result.errors)
  
  // Phase 5: Quote
  let quoted = core_quote.quote(eval_result.value)
  
  // Phase 6: Format
  let formatted = tao_syntax.format_expr(desugar_result.ast)
  
  CompileResult(
    term: quoted,
    value: eval_result.value,
    formatted: formatted,
    errors: errors,
  )
}

/// Full compilation pipeline for a single Core module
pub fn compile_core(source: String, path: String, ctx: GlobalContext) -> CompileResult {
  // Phase 1: Parse (Core grammar)
  let parse_result = core_syntax.parse(source)
  let errors = parse_result.errors
  
  // Phase 2: Type check (skip desugaring for Core)
  let type_result = core_infer.check_term(parse_result.ast, ctx)
  let errors = list.append(errors, type_result.errors)
  
  // Phase 3: Evaluate
  let eval_result = core_eval.evaluate(parse_result.ast)
  let errors = list.append(errors, eval_result.errors)
  
  // Phase 4: Quote
  let quoted = core_quote.quote(eval_result.value)
  
  // Phase 5: Format (Core grammar)
  let formatted = core_syntax.format_term(parse_result.ast)
  
  CompileResult(
    term: quoted,
    value: eval_result.value,
    formatted: formatted,
    errors: errors,
  )
}
```

### Compilation Result

```gleam
/// Result of a full compilation
pub type CompileResult {
  CompileResult(
    term: Option(Term),      // Quoted term (if no errors)
    value: Option(Value),    // Evaluated value (if no errors)
    formatted: String,       // Formatted output
    errors: List(Diagnostic), // ALL errors from all phases
  )
}
```

## Phase 1: Parse

```gleam
/// Parse Tao source → Tao AST + ParseErrors
pub fn parse(source: String) -> ParseResult(TaoExpr) {
  let grammar = tao_grammar()
  let tokens = tao_lexer.tokenize(source)
  
  // Try to parse at module level, collecting errors
  parse_module(grammar, tokens, source, "")
}

/// Parse Core source → Core Term + ParseErrors
pub fn parse(source: String) -> ParseResult(CoreTerm) {
  let grammar = core_grammar()
  let tokens = core_lexer.tokenize(source)
  
  parse_term(grammar, tokens, source, "")
}
```

**Error recovery:** The parser is designed to continue after errors:
- At the module level, try each statement independently
- At the expression level, try each alternative independently
- Create synthetic AST nodes for errors (with `ParseError` attached)
- Return all errors at once

### Module-Level Error Recovery

```gleam
/// Parse module with error recovery
fn parse_module(grammar: Grammar(a), tokens: List(Token), source: String, file: String) -> ParseResult(a) {
  let mut result: ParseResult(a) = ParseResult(ast: error_node, errors: [])
  
  for token in tokens {
    // Try to parse one statement
    case parse_statement(grammar, tokens) {
      Ok(#(stmt, new_tokens)) -> {
        result.ast = ast_cons(stmt, result.ast)
        result.errors = list.append(result.errors, [])  // No errors for this statement
      }
      Error(err) -> {
        result.errors = list.append(result.errors, err)
        // Skip to next token for recovery
        tokens = drop_tokens(tokens, 1)
      }
    }
  }
  
  result
}
```

## Phase 2: Desugar

```gleam
/// Desugar a Tao module to a Core term
pub fn desugar_module(module: TaoModule, ctx: GlobalContext) -> DesugarResult {
  let mut ctx = ctx
  
  // Process imports first (they affect the constructor environment)
  let imports = list.map(module.imports, fn(import) -> {
    desugar_import(import, ctx)
  })
  
  // Process declarations (types, functions, variables)
  let declarations = list.map(module.declarations, fn(stmt) -> {
    desugar_stmt(stmt, ctx)
  })
  
  // Return the module as a Core let-binding of public names
  DesugarResult(
    term: build_module_term(declarations),
    errors: collect_errors(imports, declarations),
    ctx: ctx,
  )
}

/// Desugar a single Tao statement to Core
pub fn desugar_stmt(stmt: TaoStmt, ctx: GlobalContext) -> CoreTerm {
  case stmt {
    StmtLet(name, mutable, type_ann, value) ->
      let core_value = desugar_expr(value, ctx)
      CoreLet(name, core_value, ctx)
    
    StmtFn(name, type_params, params, return_type, body) ->
      let core_body = desugar_expr(body, ctx)
      let core_param_types = list.map(params, fn(p) -> desugar_type(p.type_, ctx))
      CoreLet(name, CoreLam(params, core_body), ctx)
    
    StmtType(name, type_params, constructors) ->
      let ctr_defs = list.map(constructors, fn(c) -> build_ctr_def(c, ctx))
      CoreType(name, ctr_defs, ctx)
    
    StmtImport(import_item) ->
      CoreLet(name, CoreModuleRef(import_item.path, ctx), ctx)
    
    StmtBlock(stmts) ->
      let core_stmts = list.map(stmts, fn(s) -> desugar_stmt(s, ctx))
      CoreDoBlock(core_stmts, ctx)
  }
}
```

**Error handling in desugaring:**
- If a type annotation is invalid, emit `CoreErr` and continue
- If an import cannot be resolved, emit `CoreErr` and continue
- All errors are collected in `DesugarResult.errors`

## Phase 3: Type Check

```gleam
/// Type check a Core term
pub fn check_term(term: CoreTerm, ctx: GlobalContext) -> CheckResult {
  // Build constructor environment from type declarations
  let ctr_env = build_ctr_env(ctx.types)
  
  // Build FFI environment
  let ffi_env = tao_ffis(ctx.config)
  
  // Initialize state
  let initial_state = core_state.initial_state(
    ctrs: ctr_env,
    ffi: ffi_env,
    truth_ctor: ctx.config.truth_constructor,
    false_ctor: ctx.config.false_constructor,
  )
  
  // Infer: returns (resolved term, inferred type, updated state)
  let (resolved_term, inferred_type, inferred_state) = core_infer.infer(initial_state, term)
  
  // Check for unsolved holes
  let final_state = check_holes(inferred_state)
  
  CheckResult(
    term: resolved_term,    // Term with holes resolved
    type_: inferred_type,   // Inferred type
    errors: final_state.errors,
  )
}

/// Infer the type of a term (bidirectional inference)
/// Returns: (resolved term, inferred type, updated state)
pub fn infer(state: State, term: CoreTerm) -> #(CoreTerm, Value, State) {
  let (resolved_term, inferred_type, new_state) = {
    case term {
      CoreVar(index) -> infer_var(state, index)
      CoreLam(param, body) -> infer_lambda(state, param, body)
      CoreApp(fun, arg) -> infer_app(state, fun, arg)
      CorePi(domain, codomain) -> infer_pi(state, domain, codomain)
      CoreLit(literal) -> infer_literal(state, literal)
      CoreCtr(tag, arg) -> infer_constructor(state, tag, arg)
      CoreMatch(arg, motive, cases) -> infer_match(state, arg, motive, cases)
      CoreLet(name, value, body) -> infer_let(state, name, value, body)
      CoreFix(name, body) -> infer_fix(state, name, body)
      CoreCall(name, args, ret) -> infer_call(state, name, args, ret)
      CoreComptime(inner) -> infer_comptime(state, inner)
      CoreHole(id) -> infer_hole(state, id)
      CoreErr(msg) -> #(term, VErr, state)
    }
  }
  #(resolved_term, inferred_type, new_state)
}
```

## Phase 4: Evaluate

```gleam
/// Evaluate a Core term to a value
pub fn evaluate(term: CoreTerm) -> EvalResult {
  let initial_state = core_state.initial_state(
    ctrs: [],  // Constructor resolution already done during type checking
    ffi: tao_ffis(config),
    truth_ctor: "True",
    false_ctor: "False",
  )
  
  let value = core_eval.evaluate_with_ffi(initial_state.ffi, term)
  
  EvalResult(
    value: value,
    errors: [],  // Evaluation errors are rare (only step limit)
  )
}
```

## Phase 5: Quote

```gleam
/// Quote a value back to a term
pub fn quote(value: Value) -> CoreTerm {
  case value {
    VTyp(u) -> CoreTyp(u)
    VLit(lit) -> CoreLit(lit)
    VLitT(ty) -> CoreLitT(ty)
    VNeut(head, spine) -> quote_neut(head, spine)
    VRcd(fields) -> CoreRcd(list.map(fields, fn(f) -> #(f.0, quote(f.1))))
    VLam(implicit, name, env, body) -> CoreLam(name, body)  // body already has indices
    VPi(implicit, name, env, in_val, out_term) ->
      CorePi(quote(in_val), out_term)
    VCtrValue(tag, arg) -> CoreCtr(tag, quote(arg))
    VUnit -> CoreUnit
    VCall(name, args, ret) ->
      CoreCall(name, list.map(args, quote), quote(ret))
    VFix(name, env, body) -> CoreFix(name, quote(body))
    VErr -> CoreErr("Evaluation error")
  }
}
```

## Phase 6: Format

```gleam
/// Format a Core term to a string
pub fn format_term(term: CoreTerm) -> String {
  let doc = format_term_doc(term, 0)
  syntax_formatter.render(doc, 80)
}

/// Format a Tao expression to a string
pub fn format_expr(expr: TaoExpr) -> String {
  let doc = format_expr_doc(expr, 0)
  syntax_formatter.render(doc, 80)
}
```

## Integration Test Example

```gleam
/// End-to-end test: compile a Tao program and check the result
should("compile fibonacci and return correct value") {
  let source = """
    fn fib(n) {
      mut a = 0
      mut b = 1
      mut i = 0
      while i < n {
        let temp = a
        a = b
        b = temp + b
        i = i + 1
      }
      a
    }
  """
  
  let result = compile_tao(source, "test.tao")
  result.errors == []
  result.value == VLit(ILit(8))  // fib(6)
}

should("accumulate multiple parse errors") {
  let source = """
    fn foo(x
    let bar = 
    type Baz
  """
  
  let result = compile_tao(source, "test.tao")
  result.errors.length >= 3  // At least 3 parse errors
}

should("type check and evaluate a simple program") {
  let source = "let x = 42 + 1; x"
  
  let result = compile_core(source, "test.core.tao")
  result.errors == []
  result.value == VLit(ILit(43))
}
```
