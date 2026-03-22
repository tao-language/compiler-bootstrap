# Tao Desugaring Specification - Detailed

> **Goal**: Complete specification of Tao AST → Core Term desugaring
> **Status**: 📋 Designed, ⏳ Ready to implement
> **Date**: March 2025

---

## Overview

This document specifies the exact desugaring rules for converting Tao AST to Core Term. Each section includes:
1. Tao syntax example
2. Tao AST representation
3. Core Term output
4. Desugaring algorithm

---

## 1. Variables and Bindings

### 1.1 Immutable Let

**Tao**:
```tao
let x = 42
let y: Int = add(x, 3)
```

**Tao AST**:
```gleam
Let(LetDecl(
  name: "x",
  mutability: Immutable,
  type_annotation: None,
  value: Lit(Int(42), span),
  span: span
), span)
```

**Core Term**:
```gleam
Ann(
  Lit(Int(42)),
  Hole(0)  // Type to be inferred
)
```

**Desugaring**:
```gleam
fn desugar_let_decl(decl: ast.LetDecl) -> Term {
  let value_term = desugar_expr(decl.value)
  case decl.type_annotation {
    Some(type_) -> {
      let type_term = desugar_type(type_)
      mk_annotated(value_term, type_term, decl.span)
    }
    None -> value_term
  }
}
```

---

### 1.2 Mutable Let (SSA Renaming)

**Tao**:
```tao
let mut counter = 0
counter = counter + 1
counter = counter * 2
```

**Core Term** (SSA-style renaming):
```gleam
let counter_0 = Lit(Int(0))
let counter_1 = App(App(Var("add"), Var("counter_0")), Lit(Int(1)))
let counter_2 = App(App(Var("mul"), Var("counter_1")), Lit(Int(2)))
// Use counter_2 from here on
```

**Desugaring Algorithm**:
```gleam
type MutableState = Dict(String, Int)  // name -> current version

fn desugar_mutable_block(
  statements: List(BlockStatement),
  mut_state: MutableState,
) -> #(List(Term), MutableState) {
  case statements {
    [] -> #([], mut_state)
    [stmt, ..rest] -> {
      case stmt {
        StmtLet(LetDecl(name, Mutable, _, value, _)) -> {
          let version = dict.get(mut_state, name) |> option.unwrap(0)
          let new_name = name <> "_" <> int.to_string(version)
          let next_version = version + 1
          let new_state = dict.insert(mut_state, name, next_version)
          
          let value_term = desugar_expr(value)
          let let_term = mk_let(new_name, value_term)
          
          let #(rest_terms, final_state) = desugar_mutable_block(rest, new_state)
          #([let_term, ..rest_terms], final_state)
        }
        StmtAssign(name, value) -> {
          let version = dict.get(mut_state, name) |> option.unwrap(0)
          let new_name = name <> "_" <> int.to_string(version)
          let next_version = version + 1
          let new_state = dict.insert(mut_state, name, next_version)
          
          let value_term = desugar_expr(value)
          let let_term = mk_let(new_name, value_term)
          
          let #(rest_terms, final_state) = desugar_mutable_block(rest, new_state)
          #([let_term, ..rest_terms], final_state)
        }
        // ... other cases
      }
    }
  }
}
```

---

## 2. Functions

### 2.1 Basic Function

**Tao**:
```tao
fn add(a: Int, b: Int) -> Int {
  a + b
}
```

**Tao AST**:
```gleam
Fn(FnDecl(
  name: "add",
  type_params: [],
  params: [
    Param("a", Some(TPrim(Int)), span),
    Param("b", Some(TPrim(Int)), span)
  ],
  return_type: Some(TPrim(Int)),
  body: BinOp(Var("a"), OpAdd, Var("b"), span),
  attributes: [],
  span: span
))
```

**Core Term**:
```gleam
Ann(
  Lam("a",
    Lam("b",
      App(
        App(Var("add"), Var("a")),
        Var("b")
      )
    )
  ),
  Pi("a", LitT(I32T),
    Pi("b", LitT(I32T),
      LitT(I32T)
    )
  )
)
```

**Desugaring**:
```gleam
fn desugar_fn_decl(decl: ast.FnDecl) -> Term {
  let body_term = desugar_expr(decl.body)
  
  // Convert params to nested lambdas
  let lambda_term = list.foldr(decl.params, body_term, fn(param, acc) {
    let param_term = case param.type_annotation {
      Some(type_) -> {
        let type_term = desugar_type(type_)
        mk_annotated(mk_var(param.name, param.span), type_term, param.span)
      }
      None -> mk_var(param.name, param.span)
    }
    mk_lambda(param.name, acc, param.span)
  })
  
  // Add return type annotation
  case decl.return_type {
    Some(return_type) -> {
      let return_term = desugar_type(return_type)
      mk_annotated(lambda_term, return_term, decl.span)
    }
    None -> lambda_term
  }
}
```

---

## 3. Operators

### 3.1 Binary Operators

**Tao**:
```tao
a + b
x * y + z  // Precedence: (x * y) + z
```

**Core Term**:
```gleam
// a + b
App(App(Var("add"), Var("a")), Var("b"))

// x * y + z
App(
  App(Var("add"),
    App(App(Var("mul"), Var("x")), Var("y"))
  ),
  Var("z")
)
```

**Desugaring**:
```gleam
fn desugar_binop(
  left: ast.Expr,
  op: ast.BinOperator,
  right: ast.Expr,
  span: Span,
) -> Term {
  let left_term = desugar_expr(left)
  let right_term = desugar_expr(right)
  
  let op_name = case op {
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
    OpPipe -> "pipe"
    OpConcat -> "concat"
  }
  
  mk_app2(mk_var(op_name, span), left_term, right_term, span)
}
```

---

## 4. Sugar Expansion

### 4.1 Bind Operator (`<-`)

**Tao**:
```tao
let x <- result in x + 1
```

**Core Term**:
```gleam
App(
  App(Var("and_then"), result),
  Lam("x", App(App(Var("add"), Var("x")), Lit(Int(1))))
)
```

**Desugaring**:
```gleam
fn desugar_bind(
  name: String,
  bind_expr: ast.Expr,
  body: ast.Expr,
  span: Span,
) -> Term {
  let bind_term = desugar_expr(bind_expr)
  let body_term = desugar_expr(body)
  
  // let x <- e1 in e2  =>  and_then(e1, fn(x) { e2 })
  mk_app2(
    mk_var("and_then", span),
    bind_term,
    mk_lambda(name, body_term, span)
  )
}
```

---

### 4.2 Result Unwrap (`?`)

**Tao**:
```tao
result?
```

**Core Term**:
```gleam
Match(
  result,
  Hole(0),  // Motive (return type)
  [
    Case(
      PCtr("Ok", PAs(PAny, "x")),
      None,  // No guard
      Var("x")
    ),
    Case(
      PCtr("Err", PAs(PAny, "e")),
      None,
      Ctr("Err", Var("e"))
    )
  ]
)
```

**Desugaring**:
```gleam
fn desugar_result_unwrap(expr: ast.Expr, span: Span) -> Term {
  let expr_term = desugar_expr(expr)
  
  // e?  =>  match e { Ok(x) -> x, Err(e) -> Err(e) }
  mk_match(
    expr_term,
    mk_hole(span),
    [
      mk_case(
        mk_pctr("Ok", mk_pas(mk_pany(), "x", span), span),
        None,
        mk_var("x", span)
      ),
      mk_case(
        mk_pctr("Err", mk_pas(mk_pany(), "e", span), span),
        None,
        mk_ctr("Err", mk_var("e", span), span)
      )
    ],
    span
  )
}
```

---

### 4.3 Optional Chaining (`?.`)

**Tao**:
```tao
user?.address
```

**Core Term**:
```gleam
Match(
  user,
  Hole(0),
  [
    Case(
      PCtr("Some", PAs(PAny, "u")),
      None,
      Dot(Var("u"), "address")
    ),
    Case(
      PCtr("None", PAny),
      None,
      Ctr("None", Hole(0))
    )
  ]
)
```

**Desugaring**:
```gleam
fn desugar_optional_chain(
  expr: ast.Expr,
  field: String,
  span: Span,
) -> Term {
  let expr_term = desugar_expr(expr)
  
  // user?.address  =>  match user { Some(u) -> u.address, None -> None }
  mk_match(
    expr_term,
    mk_hole(span),
    [
      mk_case(
        mk_pctr("Some", mk_pas(mk_pany(), "u", span), span),
        None,
        mk_dot(mk_var("u", span), field, span)
      ),
      mk_case(
        mk_pctr("None", mk_pany(), span),
        None,
        mk_ctr("None", mk_hole(span), span)
      )
    ],
    span
  )
}
```

---

### 4.4 Imperative Blocks (`do { }`)

**Tao**:
```tao
do {
  mut sum = 0
  mut i = 0
  while i < 10 {
    sum = sum + i
    i = i + 1
  }
  sum
}
```

**Core Term** (tail-recursive loop):
```gleam
// Desugars to a tail-recursive function
let loop = Lam("sum", Lam("i",
  Match(
    App(App(Var("lt"), Var("i")), Lit(Int(10))),
    Hole(0),
    [
      Case(
        PCtr("True", PAny),
        None,
        App(
          App(Var("loop"),
            App(App(Var("add"), Var("sum")), Var("i"))
          ),
          App(App(Var("add"), Var("i")), Lit(Int(1)))
        )
      ),
      Case(
        PCtr("False", PAny),
        None,
        Var("sum")
      )
    ]
  )
))
App(App(loop, Lit(Int(0))), Lit(Int(0)))
```

**Desugaring Algorithm**:
```gleam
fn desugar_block(
  statements: List(BlockStatement),
  span: Span,
) -> Term {
  case statements {
    [] -> mk_ctr("Unit", span)
    [stmt] -> desugar_statement(stmt, span)
    [stmt, ..rest] -> {
      let stmt_term = desugar_statement(stmt, span)
      let rest_term = desugar_block(rest, span)
      // Sequence: stmt; rest
      mk_app2(mk_var("seq", span), stmt_term, rest_term, span)
    }
  }
}

fn desugar_statement(
  stmt: BlockStatement,
  span: Span,
) -> Term {
  case stmt {
    StmtLet(decl) -> desugar_let_decl(decl)
    StmtAssign(name, value) -> {
      // Assignment is just the value (SSA renaming handled elsewhere)
      desugar_expr(value)
    }
    StmtExpr(expr) -> desugar_expr(expr)
  }
}
```

---

## 5. Pattern Matching

### 5.1 Basic Match

**Tao**:
```tao
match maybe {
  | Some(x) -> x
  | None -> 0
}
```

**Core Term**:
```gleam
Match(
  maybe,
  Hole(0),  // Motive (return type)
  [
    Case(
      PCtr("Some", PAs(PAny, "x")),
      None,  // No guard
      Var("x")
    ),
    Case(
      PCtr("None", PAny),
      None,
      Lit(Int(0))
    )
  ]
)
```

**Desugaring**:
```gleam
fn desugar_match(
  scrutinee: ast.Expr,
  clauses: List(ast.MatchClause),
  span: Span,
) -> Term {
  let scrutinee_term = desugar_expr(scrutinee)
  let case_terms = list.map(clauses, desugar_clause)
  
  mk_match(
    scrutinee_term,
    mk_hole(span),  // Motive inferred
    case_terms,
    span
  )
}

fn desugar_clause(clause: ast.MatchClause) -> Case {
  let pattern = desugar_pattern(clause.pattern)
  let body_term = desugar_expr(clause.body)
  
  // Handle guard: if present, wrap body in if-then-else
  let final_body = case clause.guard {
    Some(guard) -> {
      let guard_term = desugar_expr(guard)
      mk_if(guard_term, body_term, mk_ctr("None", clause.span), clause.span)
    }
    None -> body_term
  }
  
  Case(pattern, final_body, clause.span)
}
```

---

### 5.2 Match with Guards

**Tao**:
```tao
match n {
  | x if x < 0 -> "negative"
  | x if x == 0 -> "zero"
  | x if x > 0 -> "positive"
}
```

**Core Term**:
```gleam
Match(
  n,
  Hole(0),
  [
    Case(
      PAs(PAny, "x"),
      Some(App(App(Var("lt"), Var("x")), Lit(Int(0)))),  // Guard
      Lit(String("negative"))
    ),
    Case(
      PAs(PAny, "x"),
      Some(App(App(Var("eq"), Var("x")), Lit(Int(0)))),  // Guard
      Lit(String("zero"))
    ),
    Case(
      PAs(PAny, "x"),
      Some(App(App(Var("gt"), Var("x")), Lit(Int(0)))),  // Guard
      Lit(String("positive"))
    )
  ]
)
```

---

## 6. Type Desugaring

### 6.1 Type Variables

**Tao**:
```tao
fn identity<a>(x: a) -> a { x }
```

**Core Term**:
```gleam
// Type params are erased at runtime, only used for type checking
Lam("x", Var("x"))
```

**Desugaring**:
```gleam
fn desugar_type(type_: ast.Type) -> Term {
  case type_ {
    TVar(name) -> mk_var(name, mk_span("unknown", 0, 0))
    TApp(name, args) -> {
      let arg_terms = list.map(args, desugar_type)
      list.foldl(arg_terms, mk_var(name, mk_span("unknown", 0, 0)), mk_app)
    }
    TFn(params, return_type) -> {
      let param_terms = list.map(params, desugar_type)
      let return_term = desugar_type(return_type)
      list.foldr(param_terms, return_term, fn(param, acc) {
        mk_pi("_", param, acc, mk_span("unknown", 0, 0))
      })
    }
    // ... other cases
  }
}
```

---

## 7. Error Handling

### 7.1 Desugaring Errors

```gleam
pub type DesugarError {
  DesugarError(message: String, span: Span)
}

pub type DesugarResult {
  DesugarResult(term: Term, errors: List(DesugarError))
}

fn desugar_expr(expr: ast.Expr) -> DesugarResult {
  case expr {
    // ... cases
  }
}

fn with_err(result: DesugarResult, err: DesugarError) -> DesugarResult {
  case result {
    DesugarResult(term, errors) ->
      DesugarResult(term, [err, ..errors])
  }
}
```

### 7.2 Error Recovery

```gleam
fn desugar_expr(expr: ast.Expr) -> DesugarResult {
  case expr {
    Var(name, span) ->
      DesugarResult(mk_var(name, span), [])
    
    BinOp(left, op, right, span) -> {
      let left_result = desugar_expr(left)
      let right_result = desugar_expr(right)
      
      let all_errors = list.append(left_result.errors, right_result.errors)
      
      case op {
        OpAdd -> {
          let term = mk_app2(mk_var("add", span), left_result.term, right_result.term, span)
          DesugarResult(term, all_errors)
        }
        // ... other operators
      }
    }
    
    // Always return a term, even on errors (for error recovery)
    Hole(span) ->
      DesugarResult(mk_hole(span), [DesugarError("Unknown expression", span)])
  }
}
```

---

## Related Documents

- **[01-overview.md](./01-overview.md)** - Tao language overview
- **[02-syntax.md](./02-syntax.md)** - Tao syntax specification
- **[06-implementation-plan.md](./06-implementation-plan.md)** - Implementation plan
- **[../../docs/core.md](../../docs/core.md)** - Core language semantics
