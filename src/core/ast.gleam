// ============================================================================
// CORE AST - Abstract Syntax Tree
// ============================================================================
/// Terms represent the raw Abstract Syntax Tree (AST) as written by the
/// programmer. They use De Bruijn INDICES for variables.
import gleam/list
import gleam/option.{type Option}
import syntax/grammar.{type Span}

// ============================================================================
// LITERALS
// ============================================================================

pub type Literal {
  I32(value: Int)
  I64(value: Int)
  U32(value: Int)
  U64(value: Int)
  F32(value: Float)
  F64(value: Float)
  /// Overloaded integer literal — resolves to any integer or float type during type checking.
  IntLit(value: Int)
  /// Overloaded float literal — resolves to any float type during type checking.
  FloatLit(value: Float)
}

pub type LiteralType {
  I32T
  I64T
  U32T
  U64T
  F32T
  F64T
  /// Unresolved integer type — compatible with all integer and float LiteralTypes.
  ILitT
  /// Unresolved float type — compatible with all float LiteralTypes.
  FLitT
}

// ============================================================================
// TERMS
// ============================================================================

pub type Term {
  Typ(universe: Int, span: Span)
  Lit(value: Literal, span: Span)
  LitT(typ: LiteralType, span: Span)
  Var(index: Int, span: Span)
  Hole(id: Int, span: Span)
  Err(message: String, span: Span)
  Rcd(fields: List(#(String, Term)), span: Span)
  Ctr(tag: String, arg: Term, span: Span)
  Unit(span: Span)
  Dot(arg: Term, field: String, span: Span)
  Ann(term: Term, typ: Term, span: Span)
  Lam(implicit: List(String), param: #(String, Term), body: Term, span: Span)
  Pi(
    implicit: List(String),
    name: String,
    in_term: Term,
    out_term: Term,
    span: Span,
  )
  App(fun: Term, implicit: List(Term), arg: Term, span: Span)
  Match(arg: Term, motive: Term, cases: List(Case), span: Span)
  Call(name: String, args: List(Term), span: Span)
  Comptime(term: Term, span: Span)
  Fix(name: String, body: Term, span: Span)
  Let(name: String, value: Term, body: Term, span: Span)
}

pub fn get_span(term: Term) -> Span {
  case term {
    Typ(_, span) -> span
    Lit(_, span) -> span
    LitT(_, span) -> span
    Var(_, span) -> span
    Hole(_, span) -> span
    Err(_, span) -> span
    Rcd(_, span) -> span
    Ctr(_, _, span) -> span
    Unit(span) -> span
    Dot(_, _, span) -> span
    Ann(_, _, span) -> span
    Lam(_, _, _, span) -> span
    Pi(_, _, _, _, span) -> span
    App(_, _, _, span) -> span
    Match(_, _, _, span) -> span
    Call(_, _, span) -> span
    Comptime(_, span) -> span
    Fix(_, _, span) -> span
    Let(_, _, _, span) -> span
  }
}

// ============================================================================
// PATTERNS
// ============================================================================

pub type Pattern {
  PAny
  PAs(pattern: Pattern, name: String)
  PTyp(universe: Int)
  PLit(value: Literal)
  PLitT(value: LiteralType)
  PRcd(fields: List(#(String, Pattern)))
  PCtr(tag: String, arg: Pattern)
  PUnit
}

pub type Case {
  Case(pattern: Pattern, body: Term, guard: Option(Term), span: Span)
}

// ============================================================================
// NEUTRAL TERMS
// ============================================================================

pub type Head {
  HVar(level: Int)
  HHole(id: Int)
  HStepLimit
}

pub type Elim {
  EDot(name: String)
  EApp(arg: Value)
  EAppImplicit(value: Value)
  EMatch(env: Env, motive: Value, cases: List(Case))
}

// ============================================================================
// VALUES
// ============================================================================

pub type Value {
  VTyp(universe: Int)
  VLit(value: Literal)
  VLitT(typ: LiteralType)
  VNeut(head: Head, spine: List(Elim))
  VRcd(fields: List(#(String, Value)))
  VLam(implicit: List(String), name: String, env: Env, body: Term)
  VPi(
    implicit: List(String),
    name: String,
    env: Env,
    in_val: Value,
    out_term: Term,
  )
  VRecord(fields: List(#(String, Value)))
  VCall(name: String, args: List(Value))
  VFix(name: String, env: Env, body: Term)
  VCtrValue(CtrValue)
  VUnit
  VErr
}

pub type CtrValue {
  VCtr(tag: String, arg: Value)
}

// ============================================================================
// TYPE ALIASES
// ============================================================================

pub type Type = Value

pub type Env = List(Value)

pub type Context = List(#(String, #(Value, Type)))

pub type Subst = List(#(Int, Value))

/// Constructor definition for type checking and desugaring.
pub type CtrDef {
  CtrDef(params: List(String), arg_ty: Term, ret_ty: Term)
}

pub type CtrEnv = List(#(String, CtrDef))

pub type CtrIndex = List(#(String, String))

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

pub fn make_neut(head: Head) -> Value {
  VNeut(head, [])
}

pub fn make_hole_neut(id: Int) -> Value {
  VNeut(HHole(id), [])
}

pub fn make_var_neut(level: Int) -> Value {
  VNeut(HVar(level), [])
}

/// Create an error term (helper to avoid conflict with Gleam's built-in Err).
pub fn error_term(message: String, span: Span) -> Term {
  Err(message, span)
}

// ============================================================================
// TERM SHIFTING
// ============================================================================

pub fn shift_term(term: Term, shift: Int) -> Term {
  case term {
    Var(i, span) -> Var(i + shift, span)
    Lam(implicit, param, body, span) ->
      Lam(implicit, param, shift_term(body, shift), span)
    Pi(implicit, name, in_term, out_term, span) ->
      Pi(
        implicit,
        name,
        shift_term(in_term, shift),
        shift_term(out_term, shift),
        span,
      )
    App(fun, implicit, arg, span) ->
      App(shift_term(fun, shift), implicit, shift_term(arg, shift), span)
    Match(arg, motive, cases, span) ->
      Match(
        shift_term(arg, shift),
        shift_term(motive, shift),
        list.map(cases, fn(c) { shift_case(c, shift) }),
        span,
      )
    Hole(id, span) -> Hole(id, span)
    Typ(k, span) -> Typ(k, span)
    Lit(k, span) -> Lit(k, span)
    LitT(k, span) -> LitT(k, span)
    Rcd(fields, span) ->
      Rcd(list.map(fields, fn(kv) { #(kv.0, shift_term(kv.1, shift)) }), span)
    Ctr(tag, arg, span) -> Ctr(tag, shift_term(arg, shift), span)
    Unit(span) -> Unit(span)
    Dot(arg, name, span) -> Dot(shift_term(arg, shift), name, span)
    Ann(term, type_ann, span) ->
      Ann(shift_term(term, shift), shift_term(type_ann, shift), span)
    Call(name, args, span) ->
      Call(name, list.map(args, fn(a) { shift_term(a, shift) }), span)
    Comptime(term, span) -> Comptime(shift_term(term, shift), span)
    Fix(name, body, span) -> Fix(name, shift_term(body, shift), span)
    Let(name, value, body, span) -> Let(name, shift_term(value, shift), shift_term(body, shift), span)
    Err(msg, span) -> Err(msg, span)
  }
}

pub fn shift_case(case_val: Case, shift: Int) -> Case {
  case case_val {
    Case(pattern, body, guard, span) ->
      Case(
        pattern,
        shift_term(body, shift),
        option.map(guard, fn(g) { shift_term(g, shift) }),
        span,
      )
  }
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

/// Check if a value matches the given truth constructor tag.
/// This is language-agnostic — the truth constructor name is configured by
/// the language layer (e.g., "True" for Tao, "yes" for other languages).
pub fn is_true_value(value: Value, truth_ctor: String) -> Bool {
  case value {
    VCtrValue(VCtr(tag, _)) if tag == truth_ctor -> True
    _ -> False
  }
}
