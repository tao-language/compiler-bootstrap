/// Core Abstract Syntax Tree
///
/// The core language is language-agnostic. It defines the fundamental
/// terms and values that make up the compiler's internal representation.
///
/// Terms use De Bruijn indices for variables. Values use De Bruijn
/// levels for runtime representation.
import gleam/float
import gleam/int
import gleam/list
import gleam/string
import gleam/option.{type Option, None, Some}
import syntax/span.{type Span, single}

// ============================================================================
// LITERALS
// ============================================================================

/// Literal values in the core language.
///
/// Simplified: single Int and Float types. Extended in Phase 5 to
/// support I32/I64/U32/U64/F32/F64 with literal type polymorphism.
pub type Literal {
  Int(value: Int)
  Float(value: Float)
}

/// Literal type annotations for type checking.
pub type LiteralType {
  IntT
  FloatT
  I8T
  I16T
  I32T
  I64T
  U8T
  U16T
  U32T
  U64T
  F16T
  F32T
  F64T
}

// ============================================================================
// TERMS (Syntax level - De Bruijn indices)
// ============================================================================

/// Core terms. The AST for type checking and evaluation.
///
/// Terms use De Bruijn indices: Var(0) refers to the innermost
/// enclosing binder, Var(1) to the one before that, etc.
pub type Term {
  Var(index: Int, span: Span)
  Hole(id: Int, span: Span)
  Lam(
    implicits: List(#(String, Term)),
    param: #(String, Term),
    body: Term,
    span: Span,
  )
  App(fun: Term, arg: Term, span: Span)
  Pi(
    implicits: List(#(String, Term)),
    domain: #(String, Term),
    codomain: Term,
    span: Span,
  )
  Lit(value: Literal, span: Span)
  Ctr(tag: String, arg: Term, span: Span)
  Match(arg: Term, cases: List(Case), span: Span)
  Ann(term: Term, type_: Term, span: Span)
  /// FFI builtin call: `%name(arg1: T1, arg2: T2, ...) -> ReturnType`
  /// `args` are (value, type) pairs for each argument.
  Call(
    name: String,
    args: List(#(Term, Term)),
    return_type: Term,
    span: Span,
  )
  Rcd(fields: List(#(String, Term)), span: Span)
  RcdT(fields: List(#(String, Term, Option(Term))), span: Span)
  Typ(universe: Int, span: Span)
  /// Literal type annotations: $Int, $Float, $I32, $F64, etc.
  LitT(t: LiteralType, span: Span)
  TypeDef(
    name: String,
    params: List(#(String, Term)),
    constructors: List(#(String, List(String), Term, Term, Span)),
    span: Span,
  )
  /// Fixpoint: recursive function via Y combinator
  /// $fix(name) => body - desugars to a recursive lambda
  Fix(name: String, body: Term, span: Span)
  Err(message: String, span: Span)
}

// ============================================================================
// NAMED TERMS (Syntax level - Named variables, before De Bruijn conversion)
// ============================================================================

/// Named terms - AST produced by the parser with named variables.
///
/// Variables use names instead of De Bruijn indices. A separate conversion
/// pass (term_to_debruijn) converts NamedTerm to Term, calculating
/// De Bruijn indices and desugaring syntax sugar like $let.
///
/// This separates parsing from index calculation, making both simpler.
pub type NamedTerm {
  NamedVar(name: String, span: Span)
  NamedHole(id: Int, span: Span)
  NamedLam(
    implicits: List(#(String, NamedTerm)),
    param: #(String, NamedTerm),
    body: NamedTerm,
    span: Span,
  )
  NamedApp(fun: NamedTerm, arg: NamedTerm, span: Span)
  NamedPi(
    implicits: List(#(String, NamedTerm)),
    domain: #(String, NamedTerm),
    codomain: NamedTerm,
    span: Span,
  )
  NamedLit(value: Literal, span: Span)
  NamedCtr(tag: String, arg: NamedTerm, span: Span)
  NamedMatch(arg: NamedTerm, cases: List(NamedCase), span: Span)
  NamedAnn(term: NamedTerm, type_: NamedTerm, span: Span)
  /// FFI builtin call: `%name(arg1: T1, arg2: T2, ...) -> ReturnType`
  /// `args` are (value, type) pairs for each argument.
  NamedCall(
    name: String,
    args: List(#(NamedTerm, NamedTerm)),
    return_type: NamedTerm,
    span: Span,
  )
  NamedRcd(fields: List(#(String, NamedTerm)), span: Span)
  NamedRcdT(fields: List(#(String, NamedTerm, Option(NamedTerm))), span: Span)
  NamedTyp(universe: Int, span: Span)
  NamedLitT(t: LiteralType, span: Span)
  NamedTypeDef(
    name: String,
    params: List(#(String, NamedTerm)),
    constructors: List(#(String, List(String), NamedTerm, NamedTerm, Span)),
    span: Span,
  )
  NamedErr(message: String, span: Span)
  /// Syntax sugar: `let name = value; body`
  /// Desugars to App(Lam([], (name, param_type), body), value)
  NamedLet(
    name: String,
    param_type: NamedTerm,
    value: NamedTerm,
    body: NamedTerm,
    span: Span,
  )
  /// Syntax sugar: `$fix name. body` — desugars to App(Lam(name, _, body), value)
  /// The body is a lambda that receives the recursive reference as its first parameter.
  NamedFix(
    name: String,
    body: NamedTerm,
    span: Span,
  )
}

/// Named case in a match expression.
pub type NamedCase {
  NamedCase(
    pattern: Pattern,  // Patterns already use named variables
    guard: Option(NamedTerm),
    body: NamedTerm,
    span: Span,
  )
}

/// A pattern in a match case.
pub type Pattern {
  PAny(span: Span)
  PVar(name: String, span: Span)
  PCtr(tag: String, pattern: Pattern, span: Span)
  PLit(value: Literal, span: Span)
  PAlias(name: String, pattern: Pattern, span: Span)
  PUnit(span: Span)
  PLitT(lit_type: LiteralType, span: Span)
  PTyp(universe: Int, span: Span)
  PRcd(fields: List(#(String, Pattern)), span: Span)
  PError(span: Span)
}

/// A case in a match expression.
pub type Case {
  Case(pattern: Pattern, guard: Option(Term), body: Term, span: Span)
}

// ============================================================================
// VALUES (Semantics level - De Bruijn levels)
// ============================================================================

/// Neutral term head - the start of a neutral spine.
pub type Head {
  HVar(level: Int)
  HHole(id: Int)
  /// HFix holds a VFix value directly (no name lookup needed)
  HFix(value: Value)
}

/// Elimination form applied to a neutral term.
pub type Elim {
  EApp(arg: Value)
  EMatch(env: Env, cases: List(Case))
}

/// Core values - normalized terms after evaluation.
///
/// Values use De Bruijn levels for variables (relative to their
/// binding site), and De Bruijn indices for bodies.
/// Alias for the evaluation environment.
pub type Env =
  List(Value)

pub type Value {
  VNeut(head: Head, spine: List(Elim))
  VLam(
    env: Env,
    implicits: List(#(String, Value)),
    param: #(String, Value),
    body: Term,
  )
  VPi(
    env: Env,
    implicits: List(#(String, Value)),
    domain: #(String, Value),
    codomain: Value,
  )
  VLit(value: Literal)
  VCtr(tag: String, arg: Value)
  VRcd(fields: List(#(String, Value)))
  VRcdT(fields: List(#(String, Value, Option(Value))))
  VTypeDef(name: String, params: List(#(String, Value)), constructors: List(#(String, List(String), Value, Value, Span)))
  VTyp(level: Int)
  /// Evaluated literal type: $Int, $Float, $I32, $F64, etc.
  VLitT(t: LiteralType)
  /// Deferred FFI call - FFI returned None (not concrete enough), carry forward
  /// for runtime evaluation.
  VCall(
    name: String,
    args: List(#(Value, Value)),
    return_type: Value,
  )
  /// Fixpoint value - when applied, unrolls the fix body with the VFix
  /// itself extended into the environment for recursive calls.
  VFix(
    name: String,
    env: Env,
    body: Term,
  )
  VErr
}

/// Look up a constructor by tag in a TypeDef.
pub fn find_constructor(
  constructors: List(#(String, List(String), Value, Value, Span)),
  tag: String,
) -> Option(#(String, List(String), Value, Value, Span)) {
  let match_tag = fn(c: #(String, List(String), Value, Value, Span)) {
    case c {
      #(t, _, _, _, _) -> t == tag
    }
  }
  case list.find(constructors, match_tag) {
    Ok(ctor) -> Some(ctor)
    Error(_) -> None
  }
}

/// Compute the type of a constructor from a TypeDef.
pub fn compute_constructor_type(
  constructors: List(#(String, List(String), Value, Value, Span)),
  type_args: List(Value),
  tag: String,
) -> Option(Value) {
  case find_constructor(constructors, tag) {
    None -> None
    Some(#(_, _, _, result, _)) -> Some(subst(type_args, result))
  }
}

/// Substitute HVar(level) references in a value with actual type arguments.
///
/// This is the core substitution for parametric types: given a TypeDef
/// like `Option(a)` and type arguments `[Int]`, this replaces HVar(0) in
/// the result template with `Int`.
pub fn subst(type_args: List(Value), v: Value) -> Value {
  case v {
    VNeut(HVar(level), spine) -> {
      case type_args |> list.drop(level) {
        [arg, ..] -> VNeut(HVar(0), [EApp(arg), ..spine])
        [] -> v
      }
    }
    VNeut(HHole(id), spine) -> VNeut(HHole(id), spine)
    VNeut(HFix(vfix), spine) -> VNeut(HFix(vfix), spine)
    VLam(_env, _implicits, _param, _body) -> v
    VPi(_env, _implicits, _domain, _codomain) -> v
    VLit(_value) -> v
    VCtr(tag, arg) -> VCtr(tag, subst(type_args, arg))
    VRcd(fields) ->
      VRcd(list.map(fields, fn(f) { #(f.0, subst(type_args, f.1)) }))
    VRcdT(fields) ->
      VRcdT(list.map(fields, fn(f) {
        let new_default = case f.2 {
          Some(d) -> Some(subst(type_args, d))
          None -> None
        }
        #(f.0, subst(type_args, f.1), new_default)
      }))
    VCall(name, args, return_type) ->
      VCall(
        name,
        list.map(args, fn(a) { #(subst(type_args, a.0), subst(type_args, a.1)) }),
        subst(type_args, return_type),
      )
    VFix(name, env, body) ->
      VFix(name, list.map(env, fn(v) { subst(type_args, v) }), body)
    VTypeDef(name: n, params: p, constructors: c) -> VTypeDef(name: n, params: p, constructors: c)
    VTyp(level) -> VTyp(level)
    VLitT(ltype) -> VLitT(ltype)
    VErr -> VErr
  }
}

/// Extract the type of a TypeDef (always `*` - universe 0).
///
/// A TypeDef has type * (universe 0), represented as a nested Pi type:
/// Pi(_, _, _, Pi(_, _, _, VTypeDef(name: "", params: [], constructors: constructors)))
pub fn type_of_type_def(
  constructors: List(#(String, List(String), Value, Value, Span)),
) -> Value {
  VPi(
    [],
    [],
    #("_", VLit(Int(0))),
    VPi(
      [],
      [],
      #("_", VLit(Int(1))),
      VTypeDef(name: "", params: [], constructors: constructors),
    ),
  )
}

/// Create a TypeDef from simple constructor tags (no result types).
/// Uses HVar(0) placeholders for all result types.
/// Bindings are empty (no constructor-bound variables).
pub fn make_type_def(name: String, constructor_tags: List(String)) -> Term {
  let self_type = Var(0, single("", 0, 0))
  let result_type = Var(0, single("", 0, 0))
  TypeDef(
    name: name,
    params: [],
    constructors: list.map(constructor_tags, fn(tag) {
      #(tag, [], self_type, result_type, single("", 0, 0))
    }),
    span: single("", 0, 0),
  )
}

// ============================================================================
// HELPERS
// ============================================================================

/// Create a neutral value with no spine.
pub fn make_neut(head: Head) -> Value {
  VNeut(head, [])
}

/// Create a neutral value from a hole ID.
pub fn make_hole_neut(id: Int) -> Value {
  VNeut(HHole(id), [])
}

/// Create a neutral value from a De Bruijn level.
pub fn make_var_neut(level: Int) -> Value {
  VNeut(HVar(level), [])
}

/// Create an error term (avoids conflict with Gleam's built-in Err).
pub fn error_term(message: String, span: Span) -> Term {
  Err(message, span)
}

/// Syntax sugar for let bindings: `let name = value; body`.
///
/// This is desugared to `App(Lam([], (name, param_type), body), value)` -
/// a beta-reduction application. The `param_type` is typically unit.
pub fn let_var(
  name: String,
  param_type: Term,
  value: Term,
  body: Term,
  span: Span,
) -> Term {
  App(Lam([], #(name, param_type), body, span), value, span)
}

// ============================================================================
// TERM SHIFTING (De Bruijn index manipulation)
// ============================================================================

/// Shift all De Bruijn indices in a term by `shift`.
///
/// Positive shift opens up scopes (e.g., when inserting a new binder).
/// Negative shift closes scopes (e.g., when leaving a binder).
///
/// Only shifts indices >= `from` - this allows selective shifting
/// (e.g., shifting only free indices, not bound ones).
pub fn shift_term(term: Term, shift: Int) -> Term {
  shift_term_from(term, shift, 0)
}

/// Shift all De Bruijn indices in a term by `shift`, starting from `from`.
///
/// Only shifts indices >= `from` - this allows selective shifting
/// (e.g., shifting only free indices, not bound ones).
pub fn shift_term_from(term: Term, shift: Int, from: Int) -> Term {
  case term {
    Var(i, span) ->
      case i >= from {
        True -> Var(i + shift, span)
        False -> Var(i, span)
      }
    Hole(id, span) -> Hole(id, span)
    Lam(implicits, #(name, param), func_body, span) ->
      Lam(
        list.map(implicits, fn(i) { #(i.0, shift_term_from(i.1, shift, from)) }),
        #(name, shift_term_from(param, shift, from)),
        shift_term_from(func_body, shift, from + list.length(implicits) + 1),
        span,
      )
    App(fun, arg, span) ->
      App(
        shift_term_from(fun, shift, from),
        shift_term_from(arg, shift, from),
        span,
      )
    Pi(implicits, #(name, domain), codomain, span) ->
      Pi(
        list.map(implicits, fn(i) { #(i.0, shift_term_from(i.1, shift, from)) }),
        #(name, shift_term_from(domain, shift, from)),
        shift_term_from(codomain, shift, from + list.length(implicits) + 1),
        span,
      )
    Lit(value, span) -> Lit(value, span)
    Ctr(tag, arg, span) -> Ctr(tag, shift_term_from(arg, shift, from), span)
    Match(arg, cases, span) ->
      Match(
        shift_term_from(arg, shift, from),
        list.map(cases, fn(c) {
          Case(
            c.pattern,
            shift_opt(c.guard, shift, from),
            shift_term_from(c.body, shift, from),
            c.span,
          )
        }),
        span,
      )
    Ann(term, type_, span) ->
      Ann(
        shift_term_from(term, shift, from),
        shift_term_from(type_, shift, from),
        span,
      )
    Call(name, args, return_type, span) ->
      Call(
        name,
        list.map(args, fn(ta) {
          #(
            shift_term_from(ta.0, shift, from),
            shift_term_from(ta.1, shift, from),
          )
        }),
        shift_term_from(return_type, shift, from),
        span,
      )
    Rcd(fields, span) ->
      Rcd(
        list.map(fields, fn(f) { #(f.0, shift_term_from(f.1, shift, from)) }),
        span,
      )
    RcdT(fields, span) ->
      RcdT(
        list.map(fields, fn(f) {
          let shifted_default = case f.2 {
            Some(t) -> Some(shift_term_from(t, shift, from))
            None -> None
          }
          #(f.0, shift_term_from(f.1, shift, from), shifted_default)
        }),
        span,
      )
    Typ(universe, span) -> Typ(universe, span)
    LitT(ltype, span) -> LitT(ltype, span)
    TypeDef(name: n, params: params, constructors: cons, span: s) -> {
      let shift_cons = fn(c) {
        case c {
          #(tag, bindings, self_ty, result, s) -> #(
            tag,
            bindings,
            shift_term_from(self_ty, shift, from),
            shift_term_from(result, shift, from),
            s,
          )
        }
      }
      TypeDef(name: n, params: params, constructors: list.map(cons, shift_cons), span: s)
    }
    Err(msg, span) -> Err(msg, span)
    Fix(name, body, span) -> Fix(name, shift_term_from(body, shift, from), span)
  }
}

/// Shift an optional term by `shift`, starting from `from`.
/// Find the index of a value in a list, returning Ok(index) or Error(Nil).
pub fn list_index_of(list: List(String), value: String) -> Option(Int) {
  list_index_of_acc(list, value, 0)
}

fn list_index_of_acc(list: List(String), value: String, acc: Int) -> Option(Int) {
  case list {
    [] -> None
    [first, ..rest] ->
      case first == value {
        True -> Some(acc)
        False -> list_index_of_acc(rest, value, acc + 1)
      }
  }
}

pub fn shift_opt(term: Option(Term), shift: Int, from: Int) -> Option(Term) {
  case term {
    Some(t) -> Some(shift_term_from(t, shift, from))
    None -> None
  }
}

// ============================================================================
// NAMED TERM → DE BRUIJN TERM CONVERSION
// ============================================================================

/// Convert a NamedTerm (with named variables) to a Term (with De Bruijn indices).
///
/// This pass:
/// 1. Walks the tree, maintaining a stack of bound variable names
/// 2. Converts NamedVar(name) → Var(index) by looking up the name on the stack
/// 3. Desugars NamedLet into App(Lam(...), value, body)
/// 4. Handles variable shadowing correctly
///
/// The environment is a stack of variable names, with the innermost
/// binder at the head. When we encounter a NamedVar(name), we find
/// it on the stack and assign the De Bruijn index.
pub fn term_to_debruijn(named: NamedTerm) -> Term {
  named_term_to_debruijn(named, [])
}

/// Collect variable names bound by a pattern.
/// These variables are added to the env when converting the match body.
fn collect_pattern_vars(pattern: Pattern) -> List(String) {
  case pattern {
    PAny(_) -> []
    PVar(name, _) -> [name]
    PCtr(_, inner, _) -> collect_pattern_vars(inner)
    PLit(_, _) -> []
    PAlias(name, inner, _) -> list.append([name], collect_pattern_vars(inner))
    PTyp(_, _) -> []
    PRcd(fields, _) -> {
      list.fold(fields, [], fn(acc, f) {
        list.append(acc, collect_pattern_vars(f.1))
      })
    }
    PUnit(_) -> []
    PLitT(_, _) -> []
    PError(_) -> []
  }
}


fn named_term_to_debruijn(nt: NamedTerm, env: List(String)) -> Term {
  case nt {
    NamedVar(name, span) -> {
      case list_index_of(env, name) {
        Some(idx) -> Var(idx, span)
        None -> Err("unbound variable: " <> name, span)
      }
    }
    NamedHole(id, span) -> Hole(id, span)
    NamedLit(value, span) -> Lit(value, span)
    NamedTyp(universe, span) -> Typ(universe, span)
    NamedLitT(ltype, span) -> LitT(ltype, span)

    NamedLam(implicits, #(name, param_type), body, span) -> {
      // Convert implicits and param_type in current env
      let implicits_debruijn = list.map(implicits, fn(i) {
        #(i.0, named_term_to_debruijn(i.1, env))
      })
      let param_type_debruijn = named_term_to_debruijn(param_type, env)
      // Push the lambda param onto the env for the body
      let body_debruijn = named_term_to_debruijn(body, [name, ..env])
      Lam(implicits_debruijn, #(name, param_type_debruijn), body_debruijn, span)
    }

    NamedPi(implicits, #(name, domain), codomain, span) -> {
      let implicits_debruijn = list.map(implicits, fn(i) {
        #(i.0, named_term_to_debruijn(i.1, env))
      })
      // Domain is converted with name in scope (for $pi(a) -> a style)
      let domain_env = [name, ..env]
      let domain_debruijn = named_term_to_debruijn(domain, domain_env)
      let codomain_debruijn = named_term_to_debruijn(codomain, domain_env)
      Pi(implicits_debruijn, #(name, domain_debruijn), codomain_debruijn, span)
    }

    NamedApp(fun, arg, span) -> {
      App(
        named_term_to_debruijn(fun, env),
        named_term_to_debruijn(arg, env),
        span
      )
    }

    NamedCtr(tag, arg, span) -> {
      Ctr(tag, named_term_to_debruijn(arg, env), span)
    }

    NamedRcd(fields, span) -> {
      Rcd(
        list.map(fields, fn(f) { #(f.0, named_term_to_debruijn(f.1, env)) }),
        span
      )
    }

    NamedRcdT(fields, span) -> {
      RcdT(
        list.map(fields, fn(f) {
          let default_debruijn = case f.2 {
            Some(d) -> Some(named_term_to_debruijn(d, env))
            None -> None
          }
          #(f.0, named_term_to_debruijn(f.1, env), default_debruijn)
        }),
        span
      )
    }

    NamedAnn(term, type_, span) -> {
      Ann(
        named_term_to_debruijn(term, env),
        named_term_to_debruijn(type_, env),
        span
      )
    }

    NamedCall(name, args, return_type, span) -> {
      Call(
        name,
        list.map(args, fn(ta) {
          #(named_term_to_debruijn(ta.0, env), named_term_to_debruijn(ta.1, env))
        }),
        named_term_to_debruijn(return_type, env),
        span,
      )
    }

    NamedMatch(arg, cases, span) -> {
      let arg_debruijn = named_term_to_debruijn(arg, env)
      let cases_debruijn = list.map(cases, fn(c) {
        // Extract pattern-bound variables and add them to the env
        let pattern_vars = collect_pattern_vars(c.pattern)
        let env_with_patterns = list.append(pattern_vars, env)
        let guard_debruijn = case c.guard {
          Some(g) -> Some(named_term_to_debruijn(g, env_with_patterns))
          None -> None
        }
        let body_debruijn = named_term_to_debruijn(c.body, env_with_patterns)
        Case(c.pattern, guard_debruijn, body_debruijn, c.span)
      })
      Match(arg_debruijn, cases_debruijn, span)
    }

    NamedTypeDef(name, params, constructors, span) -> {
      let params_debruijn = list.map(params, fn(p) {
        #(p.0, named_term_to_debruijn(p.1, env))
      })
      let shift_cons = fn(c) {
        let #(tag, bindings, self_ty, result, s) = c
        let self_ty_db = named_term_to_debruijn(self_ty, [name, ..env])
        let result_db = named_term_to_debruijn(result, env)
        #(tag, bindings, self_ty_db, result_db, s)
      }
      TypeDef(
        name: name,
        params: params_debruijn,
        constructors: list.map(constructors, shift_cons),
        span: span,
      )
    }

    NamedErr(message, span) -> Err(message, span)

    NamedLet(name, param_type, value, body, span) -> {
      // Desugar: let name = value; body → App(Lam([], (name, param_type), body), value)
      let param_type_debruijn = named_term_to_debruijn(param_type, env)
      let value_debruijn = named_term_to_debruijn(value, env)
      let body_debruijn = named_term_to_debruijn(body, [name, ..env])
      App(
        Lam([], #(name, param_type_debruijn), body_debruijn, span),
        value_debruijn,
        span
      )
    }

    NamedFix(name, body, span) -> {
      // Convert fixpoint: $fix name. body → Fix(name, body, span)
      // Add the fix variable to the environment so it resolves correctly
      let body_debruijn = named_term_to_debruijn(body, [name, ..env])
      Fix(name, body_debruijn, span)
    }
  }
}

/// Format a term for debugging / display.
///
/// This is NOT a formatter - it's a simple string representation for
/// debugging. The actual formatter lives in the syntax layer.
pub fn term_to_string(term: Term) -> String {
  case term {
    Var(i, _) -> "#" <> int.to_string(i)
    Hole(id, _) -> "?" <> int.to_string(id)
    Lam(implicits, #(name, param_type), func_body, _) -> {
      let implicit_str = case implicits {
        [] -> ""
        _ ->
          "<"
          <> list.fold(
            list.map(implicits, fn(i) { i.0 <> ": " <> term_to_string(i.1) }),
            "",
            fn(acc, s) {
              case acc {
                "" -> s
                _ -> acc <> ", " <> s
              }
            },
          )
          <> ">"
      }
      "$fn"
      <> implicit_str
      <> "("
      <> name
      <> ": "
      <> term_to_string(param_type)
      <> ") => "
      <> term_to_string(func_body)
    }
    App(fun, arg, _) ->
      "(" <> term_to_string(fun) <> " " <> term_to_string(arg) <> ")"
    Pi(implicits, #(name, domain), codomain, _) -> {
      let implicit_str = case implicits {
        [] -> ""
        _ ->
          "<"
          <> list.fold(
            list.map(implicits, fn(i) { i.0 <> ": " <> term_to_string(i.1) }),
            "",
            fn(acc, s) {
              case acc {
                "" -> s
                _ -> acc <> ", " <> s
              }
            },
          )
          <> ">"
      }
      "$pi"
      <> implicit_str
      <> "("
      <> name
      <> ": "
      <> term_to_string(domain)
      <> ") -> "
      <> term_to_string(codomain)
    }
    Lit(Int(value), _) -> int.to_string(value)
    Lit(Float(value), _) -> float.to_string(value)
    Ctr(tag, arg, _) -> "#" <> tag <> "(" <> term_to_string(arg) <> ")"
    Match(arg, cases, _) ->
      "$match ("
      <> term_to_string(arg)
      <> ") {"
      <> list.fold(cases, "", fn(acc, c) {
        acc <> "\n  | " <> case_to_string(c)
      })
      <> "\n}"
    Ann(term, type_, _) ->
      term_to_string(term) <> " : " <> term_to_string(type_)
    Call(name, args, return_type, _) ->
      "%"
      <> name
      <> "<"
      <> term_to_string(return_type)
      <> ">(" 
      <> list.fold(args, "", fn(acc, ta) {
        let arg_str = term_to_string(ta.0) <> ": " <> term_to_string(ta.1)
        case acc {
          "" -> arg_str
          _ -> acc <> ", " <> arg_str
        }
      })
      <> ")"
    Rcd(fields, _) ->
        "{"
        <> list.fold(fields, "", fn(acc, f) {
          case acc {
            "" -> f.0 <> ": " <> term_to_string(f.1)
            _ -> acc <> ", " <> f.0 <> ": " <> term_to_string(f.1)
          }
        })
        <> "}"
    RcdT(fields, _) ->
      "${"
      <> list.fold(fields, "", fn(acc, f) {
        let field_str = f.0 <> ": " <> term_to_string(f.1)
        let field_with_default = case f.2 {
          Some(default_) -> field_str <> " = " <> term_to_string(default_)
          None -> field_str
        }
        case acc {
          "" -> field_with_default
          _ -> acc <> ", " <> field_with_default
        }
      })
      <> "}"
    Typ(universe, _) -> "$Type<" <> int.to_string(universe) <> ">"
    LitT(ltype, _) -> literal_type_to_string(ltype)
    TypeDef(name: name, params: params, constructors: constructors, span: _span) -> {
      let params_str = case params {
        [] -> ""
        _ -> {
          let params_strs = list.map(params, fn(p) {
            p.0 <> ": " <> term_to_string(p.1)
          })
          "<" <> string.join(params_strs, ", ") <> "> "
        }
      }
      "$type "
      <> name
      <> params_str
      <> " { "
      <> list.fold(constructors, "", fn(acc, c) {
        let bindings_str = case c.1 {
          [] -> ""
          _ -> "@" <> list.fold(c.1, "", fn(a, b) {
            case a {
              "" -> b
              _ -> a <> " " <> b
            }
          }) <> ". "
        }
        case acc {
          "" ->
            "#"
            <> c.0
            <> "("
            <> bindings_str
            <> term_to_string(c.2)
            <> " -> "
            <> term_to_string(c.3)
            <> ")"
          _ ->
            acc
            <> ", #"
            <> c.0
            <> "("
            <> bindings_str
            <> term_to_string(c.2)
            <> " -> "
            <> term_to_string(c.3)
            <> ")"
        }
      })
      <> " }"
    }
    Err(msg, _) -> "\"" <> msg <> "\""
    Fix(name, body, _) ->
      "$fix " <> name <> ". " <> term_to_string(body)
  }
}

fn case_to_string(case_: Case) -> String {
  case case_.guard {
    Some(guard) ->
      pattern_to_string(case_.pattern)
      <> " ? "
      <> term_to_string(guard)
      <> " => "
      <> term_to_string(case_.body)
    None ->
      pattern_to_string(case_.pattern) <> " => " <> term_to_string(case_.body)
  }
}

pub fn pattern_to_string(pat: Pattern) -> String {
  case pat {
    PAny(_) -> "_"
    PVar(name, _) -> name
    PCtr(tag, inner, _) -> "#" <> tag <> "(" <> pattern_to_string(inner) <> ")"
    PLit(Int(value), _) -> int.to_string(value)
    PLit(Float(value), _) -> float.to_string(value)
    PAlias(name, inner, _) -> name <> "@" <> pattern_to_string(inner)
    PLitT(lit_type, _) -> "$" <> literal_type_to_string(lit_type)
    PTyp(universe, _) -> "$Type<" <> int.to_string(universe) <> ">"
    PRcd(fields, _) -> {
      "{"
      <> list.fold(fields, "", fn(acc, f) {
        case acc {
          "" -> f.0 <> ": " <> pattern_to_string(f.1)
          _ -> acc <> ", " <> f.0 <> ": " <> pattern_to_string(f.1)
        }
      })
      <> "}"
    }
    PUnit(_) -> "()"
    PError(_) -> "$error"
  }
}

/// Format a value for debugging / display.
pub fn value_to_string(value: Value) -> String {
  case value {
    VNeut(head, spine) ->
      case spine {
        [] -> neut_head_to_string(head)
        _ -> neut_to_string(head, spine)
      }
    VLam(_, implicits, #(name, _param_type), body) -> {
      let implicit_str = case implicits {
        [] -> ""
        _ ->
          "<"
          <> list.fold(list.map(implicits, fn(i) { i.0 }), "", fn(acc, s) {
            case acc {
              "" -> s
              _ -> acc <> ", " <> s
            }
          })
          <> ">"
      }
      "$fn" <> implicit_str <> "(" <> name <> ") => " <> term_to_string(body)
    }
    VPi(_, implicits, #(name, domain), codomain) -> {
      let implicit_str = case implicits {
        [] -> ""
        _ ->
          "<"
          <> list.fold(list.map(implicits, fn(i) { i.0 }), "", fn(acc, s) {
            case acc {
              "" -> s
              _ -> acc <> ", " <> s
            }
          })
          <> ">"
      }
      "$pi"
      <> implicit_str
      <> "("
      <> name
      <> ": "
      <> value_to_string(domain)
      <> ") -> "
      <> value_to_string(codomain)
    }
    VLit(Int(value)) -> int.to_string(value)
    VLit(Float(value)) -> float.to_string(value)
    VCtr(tag, arg) -> "#" <> tag <> "(" <> value_to_string(arg) <> ")"
    VRcd(fields) ->
      case fields {
        [] -> "()"
        _ ->
          "{"
          <> list.fold(fields, "", fn(acc, f) {
            case acc {
              "" -> f.0 <> ": " <> value_to_string(f.1)
              _ -> acc <> ", " <> f.0 <> ": " <> value_to_string(f.1)
            }
          })
          <> "}"
      }
    VRcdT(fields) ->
      "$"
      <> "{"
      <> list.fold(fields, "", fn(acc, f) {
        let field_str = f.0 <> ": " <> value_to_string(f.1)
        let with_default = case f.2 {
          Some(d) -> field_str <> " = " <> value_to_string(d)
          None -> field_str
        }
        case acc {
          "" -> with_default
          _ -> acc <> ", " <> with_default
        }
      })
      <> "}"
    VTypeDef(name: n, params: _, constructors: _c) -> {
      "<VTypeDef " <> n <> ">"
    }
    VTyp(level) -> "$Type<" <> int.to_string(level) <> ">"
    VLitT(ltype) -> literal_type_to_string(ltype)
    VCall(name, args, return_type) -> {
      let arg_strs = list.map(args, fn(a) {
        value_to_string(a.0) <> ": " <> value_to_string(a.1)
      })
      "VCall(" <> name <> "(" <> string.join(arg_strs, ", ") <> ") -> " <> value_to_string(return_type) <> ")"
    }
    VFix(name, _env, body) ->
      "VFix(" <> name <> " => " <> term_to_string(body) <> ")"
    VErr -> "\"error\""
  }
}

pub fn literal_type_to_string(type_: LiteralType) -> String {
  case type_ {
    IntT -> "$Int"
    FloatT -> "$Float"
    I8T -> "$I8"
    I16T -> "$I16"
    I32T -> "$I32"
    I64T -> "$I64"
    U8T -> "$U8"
    U16T -> "$U16"
    U32T -> "$U32"
    U64T -> "$U64"
    F16T -> "$F16"
    F32T -> "$F32"
    F64T -> "$F64"
  }
}


fn neut_head_to_string(head: Head) -> String {
  case head {
    HVar(level) -> "v" <> int.to_string(level)
    HHole(id) -> "?" <> int.to_string(id)
    HFix(vfix) -> case vfix {
      VFix(name, _, _) -> "$fix " <> name
      _ -> "$fix ?"
    }
  }
}

fn neut_to_string(head: Head, spine: List(Elim)) -> String {
  let head_str = neut_head_to_string(head)
  let spine_str =
    list.fold(spine, "", fn(acc, e) {
      let s = case e {
        EApp(arg) -> "(" <> value_to_string(arg) <> ")"
        EMatch(_env, cases) -> " {" <> list.fold(cases, "", fn(acc, c) {
          acc <> " | " <> pattern_to_string(c.pattern) <> " => " <> term_to_string(c.body)
        }) <> " }"
      }
      acc <> s
    })
  head_str <> spine_str
}
