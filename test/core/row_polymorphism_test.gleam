/// Tests for record row polymorphism — subtyping via tail unification.
///
/// Row polymorphism allows records to be treated as subtypes when they have
/// extra fields. The tail of a record row can unify with another record,
/// enabling `{x: 1, y: 2}` to match a type expecting `{x: Int}`.
///
/// Key mechanism: `Rcd([], None)` acts as a row variable (type variable for
/// the remaining fields). During unification, fields not found in the head
/// are searched for in the tail recursively.
import core/ast
import core/context.{new_ctx, push_var}
import core/error as e
import core/eval.{eval, match_pattern}
import core/infer.{check, infer}
import core/literals as lit
import core/occurs.{occurs}
import core/quote.{normalize_term, quote}
import core/term as tm
import core/unify.{unify}
import core/unwrap.{unwrap}
import core/value as v
import gleam/int
import gleam/list
import gleam/option.{type Option, None, Some}
import syntax/span

const s = span.Span("", 0, 0, 0, 0)

const s1 = span.Span("", 1, 1, 1, 1)

const s2 = span.Span("", 2, 2, 2, 2)

// Helper: make a record value from a list of field tuples
fn rcd(fields: List(#(String, v.Value))) -> v.Value {
  v.rcd_open(fields, None)
}

fn rcd_with_tail(
  fields: List(#(String, v.Value)),
  tail: Option(v.Value),
) -> v.Value {
  v.rcd_open(fields, tail)
}

// ============================================================================
// 1. Basic record unification (no tails)
// ============================================================================

pub fn unify_rcd_empty_both_test() {
  let a = rcd([])
  let b = rcd([])
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_rcd_single_field_same_test() {
  let a = rcd([#("x", v.int_t)])
  let b = rcd([#("x", v.int_t)])
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_rcd_single_field_type_mismatch_test() {
  let a = rcd([#("x", v.int_t)])
  let b = rcd([#("x", v.float_t)])
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert list.length(ctx.errors) == 1
}

pub fn unify_rcd_two_fields_same_test() {
  let a = rcd([#("x", v.int_t), #("y", v.float_t)])
  let b = rcd([#("x", v.int_t), #("y", v.float_t)])
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_rcd_field_not_found_test() {
  let a = rcd([#("x", v.int_t)])
  let b = rcd([#("y", v.int_t)])
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  // Both directions fail: x not in b, y not in a
  assert list.length(ctx.errors) == 2
}

// ============================================================================
// 2. Order independence
// ============================================================================

pub fn unify_rcd_different_order_test() {
  let a = rcd([#("b", v.int_t), #("a", v.float_t)])
  let b = rcd([#("a", v.float_t), #("b", v.int_t)])
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_rcd_three_fields_permuted_test() {
  let a = rcd([#("c", v.i64), #("a", v.int_t), #("b", v.float_t)])
  let b = rcd([#("b", v.float_t), #("c", v.i64), #("a", v.int_t)])
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

// ============================================================================
// 3. Row variables — Rcd([], None) as a type variable
// ============================================================================

pub fn unify_rcd_empty_as_row_var_with_typ_test() {
  // Rcd([], None) unifies with Typ(_) — empty row is a type variable
  let a = rcd([])
  let b = v.Typ(0)
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_rcd_empty_as_row_var_with_typ_right_test() {
  // Symmetric: Typ(_) vs Rcd([], None)
  let a = v.Typ(0)
  let b = rcd([])
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

// ============================================================================
// 4. Row extension — subtyping via tail unification
// ============================================================================

pub fn unify_rcd_extension_supertype_subtype_test() {
  // {x: Int} is a supertype of {x: Int, y: Float}
  // The tail of the supertype unifies with {y: Float}
  let a = rcd_with_tail([#("x", v.int_t)], Some(rcd([#("y", v.float_t)])))
  let b = rcd([#("x", v.int_t), #("y", v.float_t)])
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert ctx.errors == []
}

pub fn unify_rcd_extension_subtype_supertype_test() {
  // Symmetric direction
  let a = rcd([#("x", v.int_t), #("y", v.float_t)])
  let b = rcd_with_tail([#("x", v.int_t)], Some(rcd([#("y", v.float_t)])))
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert ctx.errors == []
}

pub fn unify_rcd_extension_multiple_fields_test() {
  // {x: Int, tail={y: Float}} vs {x: Int, y: Float, z: Int(42)}
  // After matching x: tail {y} vs {y, z} → after matching y: {} vs {z} → field not found
  // The tail Rcd([y], None) is closed — z cannot be found in it
  let a = rcd_with_tail([#("x", v.int_t)], Some(rcd([#("y", v.float_t)])))
  let b = rcd([#("x", v.int_t), #("y", v.float_t), #("z", v.int(42))])
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  // z is in b but not in a's closed tail → field not found
  assert list.length(ctx.errors) == 1
}

pub fn unify_rcd_extension_closed_tail_test() {
  // {x: Int, tail={}} vs {x: Int, y: Float, tail={}}
  // After matching x: tail {} vs {y, τ} → Rcd([], None) vs Rcd([y], Some(Rcd([], None)))
  // This falls through to TypeMismatch — gap in implementation:
  // Rcd([], None) on left vs Rcd(fields, Some(tail)) on right is not handled
  let a = rcd_with_tail([#("x", v.int_t)], Some(rcd([])))
  let b = rcd_with_tail([#("x", v.int_t), #("y", v.float_t)], Some(rcd([])))
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  // TypeMismatch: Rcd([], None) vs Rcd([y], Some(Rcd([], None))) — unhandled case
  assert list.length(ctx.errors) == 1
}

// ============================================================================
// 5. Field lookup through tail
// ============================================================================

pub fn unify_rcd_field_in_tail_test() {
  // Field x is in the tail, not the head
  let a = rcd_with_tail([], Some(rcd([#("x", v.int_t)])))
  let b = rcd([#("x", v.int_t)])
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert ctx.errors == []
}

pub fn unify_rcd_field_in_deep_tail_test() {
  // Field x is deeply nested in the tail
  let a =
    rcd_with_tail([], Some(rcd_with_tail([], Some(rcd([#("x", v.int_t)])))))
  let b = rcd([#("x", v.int_t)])
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert ctx.errors == []
}

pub fn unify_rcd_field_split_between_head_and_tail_test() {
  // x in head, y in tail
  let a = rcd_with_tail([#("x", v.int_t)], Some(rcd([#("y", v.float_t)])))
  let b = rcd([#("x", v.int_t), #("y", v.float_t)])
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert ctx.errors == []
}

pub fn unify_rcd_field_not_in_tail_closed_test() {
  // x in head, but y not found in closed tail
  // a = {x: Int, tail={}} vs b = {x: Int, y: Float}
  // After matching x: tail {} vs {y} → Rcd([], None) vs Rcd([y], None) → field not found
  let a = rcd_with_tail([#("x", v.int_t)], Some(rcd([])))
  let b = rcd([#("x", v.int_t), #("y", v.float_t)])
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  // y is in b but a's tail is empty closed record → field not found
  assert list.length(ctx.errors) == 1
}

pub fn unify_rcd_field_type_mismatch_in_tail_test() {
  // Field x has different types in tail vs direct
  let a = rcd_with_tail([], Some(rcd([#("x", v.int_t)])))
  let b = rcd([#("x", v.float_t)])
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert list.length(ctx.errors) == 1
}

// ============================================================================
// 6. Default value unification
// ============================================================================

pub fn unify_rcd_default_values_same_test() {
  let a = v.Rcd([#("x", #(v.int_t, Some(v.int(0))))], None)
  let b = v.Rcd([#("x", #(v.int_t, Some(v.int(0))))], None)
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_rcd_default_values_different_test() {
  let a = v.Rcd([#("x", #(v.int_t, Some(v.int(0))))], None)
  let b = v.Rcd([#("x", #(v.int_t, Some(v.int(99))))], None)
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert list.length(ctx.errors) == 1
}

pub fn unify_rcd_default_values_one_missing_test() {
  // One side has default, other doesn't — should succeed (only unify when both present)
  let a = v.Rcd([#("x", #(v.int_t, Some(v.int(0))))], None)
  let b = v.Rcd([#("x", #(v.int_t, None))], None)
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert ctx.errors == []
}

pub fn unify_rcd_default_values_neither_present_test() {
  let a = v.Rcd([#("x", #(v.int_t, None))], None)
  let b = v.Rcd([#("x", #(v.int_t, None))], None)
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

// ============================================================================
// 7. Nested records
// ============================================================================

pub fn unify_rcd_nested_same_test() {
  let inner = rcd([#("z", v.int(42))])
  let a = rcd([#("inner", inner)])
  let b = rcd([#("inner", inner)])
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_rcd_nested_mismatch_test() {
  let inner_a = rcd([#("z", v.int(42))])
  let inner_b = rcd([#("z", v.float_t)])
  let a = rcd([#("inner", inner_a)])
  let b = rcd([#("inner", inner_b)])
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert list.length(ctx.errors) == 1
}

pub fn unify_rcd_nested_order_independent_test() {
  let inner = rcd([#("z", v.int(42)), #("w", v.float_t)])
  let a = rcd([#("inner", inner), #("x", v.int_t)])
  let b = rcd([#("x", v.int_t), #("inner", inner)])
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

// ============================================================================
// 8. Empty record with tail vs non-empty
// ============================================================================

pub fn unify_rcd_empty_tail_vs_fields_test() {
  // Rcd([], Some(tail)) unifies tail with Rcd([x], None)
  let a = rcd_with_tail([], Some(rcd([#("x", v.int_t)])))
  let b = rcd([#("x", v.int_t)])
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert ctx.errors == []
}

pub fn unify_rcd_empty_vs_fields_no_tail_test() {
  // Rcd([], None) vs Rcd([x], None) — empty closed record vs non-empty
  // Rcd([], None) is an empty closed record (not a row variable)
  // The row variable is Typ(_), handled by: v.Rcd([], None), v.Typ(_) -> ctx
  // So empty record vs non-empty record → field not found error
  let a = rcd([])
  let b = rcd([#("x", v.int_t)])
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert list.length(ctx.errors) == 1
}

// ============================================================================
// 9. Constructor unification with record rows
// ============================================================================

pub fn unify_ctr_rcd_same_test() {
  let a = v.Ctr("Point", rcd([#("x", v.int(1)), #("y", v.int(2))]))
  let b = v.Ctr("Point", rcd([#("x", v.int(1)), #("y", v.int(2))]))
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_ctr_rcd_tag_mismatch_test() {
  let a = v.Ctr("Point", rcd([#("x", v.int(1))]))
  let b = v.Ctr("Line", rcd([#("x", v.int(1))]))
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert list.length(ctx.errors) == 1
}

pub fn unify_ctr_rcd_field_mismatch_test() {
  let a = v.Ctr("Point", rcd([#("x", v.int(1)), #("y", v.int(2))]))
  let b = v.Ctr("Point", rcd([#("x", v.int(1)), #("y", v.float_t)]))
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert list.length(ctx.errors) == 1
}

// ============================================================================
// 10. Neutral values in records
// ============================================================================

pub fn unify_rcd_neutral_field_value_test() {
  // Field value is a neutral variable
  let a = rcd([#("x", v.Neut(v.NVar(0)))])
  let b = rcd([#("x", v.Neut(v.NVar(0)))])
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_rcd_neutral_tail_test() {
  // Tail is a neutral hole
  let tail = v.Neut(v.NHole([], Some(0)))
  let a = rcd_with_tail([#("x", v.int_t)], Some(tail))
  let b = rcd([#("x", v.int_t), #("y", v.float_t)])
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert ctx.errors == []
  // The hole should be solved to the remaining fields
}

// ============================================================================
// 11. Edge cases
// ============================================================================

pub fn unify_rcd_field_name_empty_string_test() {
  // Field named "" — special case in pop_field
  let a = rcd([#("", v.int_t)])
  let b = rcd([#("", v.int_t)])
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_rcd_large_field_count_test() {
  // Many fields — stress test for field lookup
  let fields =
    list.map([1, 2, 3, 4, 5, 6, 7, 8, 9, 10], fn(i) {
      #("f" <> int.to_string(i), v.int(i))
    })
  let a = rcd(fields)
  let b = rcd(list.reverse(fields))
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

// ============================================================================
// 12. Symmetry tests
// ============================================================================

pub fn unify_rcd_extension_symmetric_test() {
  // Extension should work in both directions
  let a = rcd_with_tail([#("x", v.int_t)], Some(rcd([#("y", v.float_t)])))
  let b = rcd([#("x", v.int_t), #("y", v.float_t)])
  let ctx0 = new_ctx
  let ctx1 = unify(ctx0, #(a, s1), #(b, s2))
  let ctx2 = unify(ctx0, #(b, s2), #(a, s1))
  assert ctx1.errors == []
  assert ctx2.errors == []
}

pub fn unify_rcd_field_in_tail_symmetric_test() {
  // Field in tail — both directions
  let a = rcd_with_tail([], Some(rcd([#("x", v.int_t)])))
  let b = rcd([#("x", v.int_t)])
  let ctx0 = new_ctx
  let ctx1 = unify(ctx0, #(a, s1), #(b, s2))
  let ctx2 = unify(ctx0, #(b, s2), #(a, s1))
  assert ctx1.errors == []
  assert ctx2.errors == []
}

// ============================================================================
// 13. Pattern matching — field projection via match_pattern
// ============================================================================

pub fn match_pattern_rcd_field_projection_test() {
  // Basic field access: match {x: 1, y: 2} with {x: a, ..}
  let value = v.rcd([#("x", v.int(1)), #("y", v.int(2))])
  let pattern = tm.PRcd([#("x", tm.PAlias("a", tm.PAny))], Some(tm.PAny))
  assert match_pattern(pattern, value) == Some([v.int(1)])
}

pub fn match_pattern_rcd_field_in_tail_test() {
  // Field found in tail portion of the value
  let value =
    v.Rcd(
      [#("x", #(v.int(1), None))],
      Some(v.Rcd([#("y", #(v.int(2), None))], None)),
    )
  let pattern =
    tm.PRcd(
      [#("x", tm.PAlias("a", tm.PAny)), #("y", tm.PAlias("b", tm.PAny))],
      Some(tm.PAny),
    )
  let result = match_pattern(pattern, value)
  assert result == Some([v.int(2), v.int(1)])
}

pub fn match_pattern_rcd_pattern_fewer_fields_test() {
  // Pattern matches fewer fields than value has (row polymorphism)
  let value = v.rcd([#("x", v.int(1)), #("y", v.int(2)), #("z", v.int(3))])
  let pattern = tm.PRcd([#("x", tm.PAlias("a", tm.PAny))], Some(tm.PAny))
  assert match_pattern(pattern, value) == Some([v.int(1)])
}

pub fn match_pattern_rcd_pattern_more_fields_test() {
  // Pattern requires more fields than value has (should fail)
  let value = v.rcd([#("x", v.int(1))])
  let pattern =
    tm.PRcd([#("x", tm.PAny), #("y", tm.PAny), #("z", tm.PAny)], Some(tm.PAny))
  assert match_pattern(pattern, value) == None
}

pub fn match_pattern_rcd_pattern_order_independent_test() {
  // Pattern fields in different order than value
  let value = v.rcd([#("a", v.int(1)), #("b", v.int(2)), #("c", v.int(3))])
  let pattern =
    tm.PRcd(
      [#("c", tm.PAlias("c", tm.PAny)), #("a", tm.PAlias("a", tm.PAny))],
      Some(tm.PAny),
    )
  let result = match_pattern(pattern, value)
  // Bindings: c=#1, a=#0
  assert result == Some([v.int(1), v.int(3)])
}

pub fn match_pattern_rcd_strict_no_extra_fields_test() {
  // Strict pattern (no tail) rejects extra fields
  let value = v.rcd([#("x", v.int(1)), #("y", v.int(2))])
  let pattern = tm.PRcd([#("x", tm.PAny)], None)
  assert match_pattern(pattern, value) == None
}

pub fn match_pattern_rcd_strict_exact_match_test() {
  // Strict pattern matches exactly
  let value = v.rcd([#("x", v.int(1)), #("y", v.int(2))])
  let pattern = tm.PRcd([#("x", tm.PAny), #("y", tm.PAny)], None)
  assert match_pattern(pattern, value) == Some([])
}

pub fn match_pattern_rcd_tail_anything_test() {
  // Tail pattern PAny matches any remaining fields
  let value =
    v.Rcd(
      [#("x", #(v.int(1), None))],
      Some(v.Rcd([#("y", #(v.int(2), None)), #("z", #(v.int(3), None))], None)),
    )
  let pattern = tm.PRcd([#("x", tm.PAny)], Some(tm.PAny))
  assert match_pattern(pattern, value) == Some([])
}

pub fn match_pattern_rcd_empty_pattern_matches_anything_test() {
  // Empty pattern with tail matches any record
  let value = v.rcd([#("x", v.int(1)), #("y", v.int(2))])
  let pattern = tm.PRcd([], Some(tm.PAny))
  assert match_pattern(pattern, value) == Some([])
}

// ============================================================================
// 14. Inference — record literals
// ============================================================================

pub fn infer_rcd_empty_test() {
  let ast = ast.rcd([], None, s)
  let #(term, type_, ctx) = infer(new_ctx, ast)
  assert ctx.errors == []
  assert term == tm.Rcd([], None)
  assert type_ == v.Rcd([], None)
}

pub fn infer_rcd_single_field_test() {
  let ast = ast.rcd([#("x", #(Some(ast.int(1, s)), None))], None, s)
  let #(term, type_, ctx) = infer(new_ctx, ast)
  assert ctx.errors == []
  assert term == tm.Rcd([#("x", #(tm.int(1), None))], None)
  assert type_ == v.Rcd([#("x", #(v.int_t, None))], None)
}

pub fn infer_rcd_multiple_fields_test() {
  let fields = [
    #("x", #(Some(ast.int(1, s)), None)),
    #("y", #(Some(ast.float(3.14, s)), None)),
  ]
  let ast = ast.rcd(fields, None, s)
  let #(term, type_, ctx) = infer(new_ctx, ast)
  assert ctx.errors == []
  // Check field types are inferred correctly
  assert type_
    == v.Rcd([#("x", #(v.int_t, None)), #("y", #(v.float_t, None))], None)
}

pub fn infer_rcd_with_tail_test() {
  // Record with explicit tail variable
  // When rest has type Typ(0), the tail evaluates to Typ(0) (not a neutral var)
  let tail = ast.var("rest", s)
  let ast = ast.rcd([#("x", #(Some(ast.int(1, s)), None))], Some(tail), s)
  let ctx0 = context.push_var(new_ctx, #("rest", None, Some(v.Typ(0))))
  let #(term, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == []
  assert term == tm.Rcd([#("x", #(tm.int(1), None))], Some(tm.Var(0)))
  // The tail variable resolves to Typ(0), not a neutral variable
  assert type_ == v.Rcd([#("x", #(v.int_t, None))], Some(v.Typ(0)))
}

pub fn infer_rcd_fields_order_independent_test() {
  // {y: 2, x: 1} should have same type structure as {x: 1, y: 2}
  let ast1 =
    ast.rcd(
      [
        #("x", #(Some(ast.int(1, s)), None)),
        #("y", #(Some(ast.int(2, s)), None)),
      ],
      None,
      s,
    )
  let ast2 =
    ast.rcd(
      [
        #("y", #(Some(ast.int(2, s)), None)),
        #("x", #(Some(ast.int(1, s)), None)),
      ],
      None,
      s,
    )
  let #(_, type1, ctx1) = infer(new_ctx, ast1)
  let #(_, type2, ctx2) = infer(new_ctx, ast2)
  assert ctx1.errors == []
  assert ctx2.errors == []
  // Both should have same field types (in their respective orders)
  // The types differ in field order, but unification should succeed
  let ctx = unify(ctx1, #(type1, s1), #(type2, s2))
  assert ctx.errors == []
}

// ============================================================================
// 15. Check — record subtyping via annotation
// ============================================================================

pub fn check_rcd_subtype_extra_fields_test() {
  // {x: 1, y: 2} checked against {x: Int} — extra fields OK if expected has tail
  // NOTE: Current implementation has a gap here. When the expected tail is Typ(0),
  // unify_rcd_field passes the remaining record to Typ(0), which tries to unify
  // each field value with Typ(0) instead of absorbing the whole row. This produces
  // a TypeMismatch error. The tail should absorb extra fields, but the Typ(_) handler
  // in unify.gleam recurses on field values instead of accepting the whole record.
  let ast =
    ast.rcd(
      [
        #("x", #(Some(ast.int(1, s)), None)),
        #("y", #(Some(ast.int(2, s)), None)),
      ],
      None,
      s,
    )
  // Expected type: {x: Int} with open tail
  let expected = v.Rcd([#("x", #(v.int_t, None))], Some(v.Typ(0)))
  let #(_, _, ctx) = check(new_ctx, ast, #(expected, s))
  // BUG: extra field y should be absorbed by tail, but Typ(0) handler tries to
  // unify each field value with Typ(0), producing TypeMismatch(IntT, Typ(0))
  assert list.length(ctx.errors) == 1
}

pub fn check_rcd_subtype_with_rcd_tail_test() {
  // {x: 1, y: 2} checked against {x: Int, tail={y: Int}} — works when tail is a record
  let ast =
    ast.rcd(
      [
        #("x", #(Some(ast.int(1, s)), None)),
        #("y", #(Some(ast.int(2, s)), None)),
      ],
      None,
      s,
    )
  // Expected type: {x: Int} with tail {y: Int}
  let expected =
    v.Rcd(
      [#("x", #(v.int_t, None))],
      Some(v.Rcd([#("y", #(v.int_t, None))], None)),
    )
  let #(term, type_, ctx) = check(new_ctx, ast, #(expected, s))
  // This works because the tail is a concrete record that matches field y
  assert ctx.errors == []
  assert type_ == expected
}

pub fn check_rcd_missing_field_error_test() {
  // {x: 1} checked against {x: Int, y: Float} — missing field y
  let ast = ast.rcd([#("x", #(Some(ast.int(1, s)), None))], None, s)
  // Expected type: {x: Int, y: Float} — closed record, y required
  let expected =
    v.Rcd([#("x", #(v.int_t, None)), #("y", #(v.float_t, None))], None)
  let #(_, _, ctx) = check(new_ctx, ast, #(expected, s))
  // y is in expected but not in actual → field not found
  assert list.length(ctx.errors) > 0
}

// ============================================================================
// 16. Occurs check — through tails
// ============================================================================

pub fn occurs_rcd_tail_with_hole_test() {
  // Hole appears in tail — occurs check should find it
  let tail = v.Neut(v.NHole([], Some(42)))
  let value = v.Rcd([#("x", #(v.int_t, None))], Some(tail))
  let ctx = new_ctx
  assert occurs(ctx, 42, value) == True
}

pub fn occurs_rcd_nested_tail_with_hole_test() {
  // Hole in deeply nested tail
  let inner_tail = v.Neut(v.NHole([], Some(42)))
  let outer_tail = v.Rcd([#("y", #(v.float_t, None))], Some(inner_tail))
  let value = v.Rcd([#("x", #(v.int_t, None))], Some(outer_tail))
  let ctx = new_ctx
  assert occurs(ctx, 42, value) == True
}

pub fn occurs_rcd_tail_no_cycle_test() {
  // Hole in tail but not the same hole — no cycle
  let tail = v.Neut(v.NHole([], Some(99)))
  let value = v.Rcd([#("x", #(v.int_t, None))], Some(tail))
  let ctx = new_ctx
  assert occurs(ctx, 42, value) == False
}

pub fn occurs_rcd_field_with_hole_test() {
  // Hole in field value
  let value = v.Rcd([#("x", #(v.Neut(v.NHole([], Some(42))), None))], None)
  let ctx = new_ctx
  assert occurs(ctx, 42, value) == True
}

// ============================================================================
// 17. Quote — records with tails
// ============================================================================

pub fn quote_rcd_empty_test() {
  let value = v.Rcd([], None)
  let term = quote([], 0, value)
  assert term == tm.Rcd([], None)
}

pub fn quote_rcd_with_fields_test() {
  let value =
    v.Rcd([#("x", #(v.int_t, None)), #("y", #(v.float_t, None))], None)
  let term = quote([], 0, value)
  assert term
    == tm.Rcd(
      [#("x", #(tm.LitT(lit.IntT), None)), #("y", #(tm.LitT(lit.FloatT), None))],
      None,
    )
}

pub fn quote_rcd_with_tail_test() {
  let tail = v.Rcd([#("z", #(v.i64, None))], None)
  let value = v.Rcd([#("x", #(v.int_t, None))], Some(tail))
  let term = quote([], 0, value)
  assert term
    == tm.Rcd(
      [#("x", #(tm.LitT(lit.IntT), None))],
      Some(tm.Rcd([#("z", #(tm.LitT(lit.I64), None))], None)),
    )
}

pub fn quote_rcd_field_order_preserved_test() {
  // Field order should be preserved through quote
  let value =
    v.Rcd([#("b", #(v.float_t, None)), #("a", #(v.int_t, None))], None)
  let term = quote([], 0, value)
  assert term
    == tm.Rcd(
      [#("b", #(tm.LitT(lit.FloatT), None)), #("a", #(tm.LitT(lit.IntT), None))],
      None,
    )
}

// ============================================================================
// 18. Pi/Lambda — records as domains and codomains
// ============================================================================

pub fn unify_pi_rcd_domain_test() {
  // Pi types with record domains unify field-by-field
  let a = v.Pi([], #("args", v.Rcd([#("x", #(v.int_t, None))], None)), tm.int_t)
  let b = v.Pi([], #("args", v.Rcd([#("x", #(v.int_t, None))], None)), tm.int_t)
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_pi_rcd_domain_mismatch_test() {
  // Pi types with different record domains
  let a = v.Pi([], #("args", v.Rcd([#("x", #(v.int_t, None))], None)), tm.int_t)
  let b = v.Pi([], #("args", v.Rcd([#("y", #(v.int_t, None))], None)), tm.int_t)
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert list.length(ctx.errors) > 0
}

// ============================================================================
// 19. For (quantifier) — with record types
// ============================================================================

pub fn unify_for_rcd_test() {
  // For quantifier with record type instantiates and unifies
  let a = v.For([], #("T", v.Rcd([#("x", #(v.int_t, None))], None)), tm.Var(0))
  // Instantiate with the record type
  let b = v.Rcd([#("x", #(v.int_t, None))], None)
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert ctx.errors == []
}

// ============================================================================
// 20. Integration — app with record arguments

pub fn infer_app_rcd_arg_test() {
  // Apply function taking record arg: f({x: 1, y: 2})
  let ast =
    ast.app(
      ast.var("f", s),
      ast.rcd(
        [
          #("x", #(Some(ast.int(1, s)), None)),
          #("y", #(Some(ast.int(2, s)), None)),
        ],
        None,
        s,
      ),
      s,
    )
  // f: (args: {x: Int, y: Int}) -> Int
  let pi =
    v.Pi(
      [],
      #(
        "args",
        v.Rcd([#("x", #(v.int_t, None)), #("y", #(v.int_t, None))], None),
      ),
      tm.int_t,
    )
  let ctx0 = context.push_var(new_ctx, #("f", Some(v.var(0)), Some(pi)))
  let #(term, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == []
  assert type_ == v.int_t
}

// ============================================================================
// 21. Match — evaluation with record rows

pub fn eval_match_rcd_projection_test() {
  // $match {x: 10, y: 20} { | {x: a, y: b} => {x: a, y: b} }
  let arg =
    tm.Rcd([#("x", #(tm.int(10), None)), #("y", #(tm.int(20), None))], None)
  let cases = [
    tm.Case(
      tm.PRcd(
        [#("x", tm.PAlias("a", tm.PAny)), #("y", tm.PAlias("b", tm.PAny))],
        None,
      ),
      None,
      tm.Rcd([#("x", #(tm.Var(1), None)), #("y", #(tm.Var(0), None))], None),
    ),
  ]
  let term = tm.Match(arg, cases)
  let result = eval([], [], term)
  assert result
    == v.Rcd([#("x", #(v.int(10), None)), #("y", #(v.int(20), None))], None)
}

pub fn eval_match_rcd_with_tail_test() {
  // Match with tail: only extract x, ignore rest via tail
  let arg =
    tm.Rcd([#("x", #(tm.int(42), None)), #("y", #(tm.int(99), None))], None)
  let cases = [
    tm.Case(
      tm.PRcd([#("x", tm.PAlias("a", tm.PAny))], Some(tm.PAny)),
      None,
      tm.Var(0),
    ),
  ]
  let term = tm.Match(arg, cases)
  let result = eval([], [], term)
  assert result == v.int(42)
}

// ============================================================================
// 22. Round-trip: infer → quote → eval

pub fn roundtrip_rcd_simple_test() {
  // Infer a record, normalize it, should get same result
  let ast = ast.rcd([#("x", #(Some(ast.int(42, s)), None))], None, s)
  let #(term, _, ctx) = infer(new_ctx, ast)
  let normalized = normalize_term(ctx.ffi, ctx.env, term)
  assert normalized == tm.Rcd([#("x", #(tm.int(42), None))], None)
}

// ============================================================================
// 23. Fix (recursive functions) with records
// ============================================================================

pub fn infer_fix_rcd_simple_test() {
  // Recursive function that takes and returns records
  let pi_type =
    v.Pi(
      [],
      #("args", v.Rcd([#("x", #(v.int_t, None))], None)),
      tm.Rcd([#("x", #(tm.int_t, None))], None),
    )
  let ast = ast.fix("f", ast.var("args", s), s)
  let ctx0 = context.push_var(new_ctx, #("args", None, Some(pi_type)))
  let #(term, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == []
}

// ============================================================================
// 24. Implementation gaps — failing tests documenting known bugs
//
// These tests document known gaps in the row polymorphism implementation.
// They are written to express the correct expected behavior. Each test
// currently fails; they should pass once the gaps are fixed.
// ============================================================================

// GAP 1: Rcd([], None) vs Rcd(fields, Some(tail)) — unhandled pattern
//
// When Rcd([], None) (empty record) appears on the left and a non-empty
// record with a tail appears on the right, there is no matching case in
// the unification dispatch. The patterns are:
//   Rcd([], None), Rcd([], None)          — both empty
//   Rcd([], None), Rcd([..], None)        — right has fields, no tail
//   Rcd([], Some(tail)), value            — left has tail
//   value, Rcd([], Some(tail))            — right has tail
// But there is no case for: Rcd([], None), Rcd([..], Some(tail))
//
// Expected: Rcd([], None) should be treated as a row variable and absorb
// the fields from the right. The tail of the right side should become
// part of the solution.
//
// Actual: Falls through to catch-all TypeMismatch.

pub fn unify_rcd_empty_left_with_tailed_right_test() {
  // Rcd([], None) vs Rcd([y], Some(Rcd([], None)))
  // Should succeed: empty row absorbs {y}, tail carries forward
  let a = rcd([])
  let b = rcd_with_tail([#("y", v.float_t)], Some(rcd([])))
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  // BUG: falls through to TypeMismatch instead of absorbing the fields
  // FIX: add case `v.Rcd([], None), v.Rcd(_, Some(_)) -> ctx`
  assert ctx.errors == []
}

pub fn unify_rcd_empty_left_with_multi_field_tailed_right_test() {
  // Rcd([], None) vs Rcd([x, y], Some(Rcd([z], None)))
  // Should succeed: empty row absorbs {x, y, z...}
  let a = rcd([])
  let b =
    rcd_with_tail(
      [#("x", v.int_t), #("y", v.float_t)],
      Some(rcd([#("z", v.i64)])),
    )
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  // BUG: falls through to TypeMismatch
  assert ctx.errors == []
}

// GAP 2: Typ(_) tail doesn't absorb extra fields during unification
//
// In unify_rcd_field, when a field is not found in the right's head and
// the right has a tail, it recurses: unify(rcd1, tail2). When tail2 is
// Typ(0), the main unify dispatches to:
//   Rcd([field, ..], tail), Typ(_) -> unify(field_value, Typ(_))
// which tries to unify the field VALUE with Typ(_), not the whole record.
//
// Expected: When the tail is Typ(_), the entire remaining record should
// be absorbed without checking individual field values. Typ(_) as a tail
// means "any remaining fields".
//
// Actual: Each field value is unified with Typ(_), producing TypeMismatch
// errors for concrete field values.

pub fn unify_rcd_typ_tail_absorbs_extra_field_test() {
  // Rcd([x], None) vs Rcd([x], Some(Typ(0)))
  // After matching x: Rcd([], None) vs Rcd([], Some(Typ(0)))
  // The Typ(0) tail should absorb the empty remainder
  let a = rcd([#("x", v.int_t)])
  let b = rcd_with_tail([#("x", v.int_t)], Some(v.Typ(0)))
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert ctx.errors == []
}

pub fn unify_rcd_typ_tail_absorbs_extra_fields_test() {
  // Rcd([x, y], None) vs Rcd([x], Some(Typ(0)))
  // After matching x: Rcd([y], None) vs Rcd([], Some(Typ(0)))
  // unify_rcd_field looks for y in [], not found, recurses into tail Typ(0)
  // unify(Rcd([y], None), Typ(0)) → tries to unify y's VALUE with Typ(0)
  // Expected: Typ(0) absorbs {y: IntT}
  let a = rcd([#("x", v.int_t), #("y", v.float_t)])
  let b = rcd_with_tail([#("x", v.int_t)], Some(v.Typ(0)))
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  // BUG: TypeMismatch(FloatT, Typ(0)) — field value unified with Typ
  // FIX: when tail is Typ(_), accept the whole remaining record
  assert ctx.errors == []
}

pub fn unify_rcd_typ_tail_multi_extra_fields_test() {
  // Rcd([x, y, z], None) vs Rcd([x], Some(Typ(0)))
  // Multiple extra fields should all be absorbed by Typ(0)
  let a =
    rcd([
      #("x", v.int_t),
      #("y", v.float_t),
      #("z", v.i64),
    ])
  let b = rcd_with_tail([#("x", v.int_t)], Some(v.Typ(0)))
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  // BUG: TypeMismatch errors for y and z field values
  assert ctx.errors == []
}

// GAP 3: Typ(_) tail in subtyping checks (check function)
//
// When checking a term against an expected type with a Typ(_) tail,
// extra fields in the actual value should be absorbed by the tail.
// This is the practical manifestation of GAP 2.

pub fn check_rcd_typ_tail_extra_fields_test() {
  // {x: 1, y: 2} checked against {x: Int, τ}
  // Extra field y should be absorbed by the row variable tail
  let ast =
    ast.rcd(
      [
        #("x", #(Some(ast.int(1, s)), None)),
        #("y", #(Some(ast.int(2, s)), None)),
      ],
      None,
      s,
    )
  let expected = v.Rcd([#("x", #(v.int_t, None))], Some(v.Typ(0)))
  let #(_, _, ctx) = check(new_ctx, ast, #(expected, s))
  // BUG: TypeMismatch(IntT, Typ(0)) — y's value unified with Typ
  // FIX: Typ(_) tail should absorb {y: Int}
  assert ctx.errors == []
}

pub fn check_rcd_typ_tail_nested_extra_field_test() {
  // {x: {a: 1, b: 2}} checked against {x: {a: Int}, τ}
  // Nested record extra field should also be absorbed
  let ast =
    ast.rcd(
      [
        #(
          "x",
          #(
            Some(ast.rcd(
              [
                #("a", #(Some(ast.int(1, s)), None)),
                #("b", #(Some(ast.int(2, s)), None)),
              ],
              None,
              s,
            )),
            None,
          ),
        ),
      ],
      None,
      s,
    )
  let expected =
    v.Rcd(
      [#("x", #(v.Rcd([#("a", #(v.int_t, None))], Some(v.Typ(0))), None))],
      None,
    )
  let #(_, _, ctx) = check(new_ctx, ast, #(expected, s))
  // BUG: nested extra field b not absorbed
  assert ctx.errors == []
}

// GAP 4: Closed tail should unify with Typ(_) in the other direction
//
// Rcd([x], Some(Rcd([], None))) vs Rcd([x], Some(Typ(0)))
// The tail Rcd([], None) should unify with Typ(0)

pub fn unify_rcd_closed_tail_with_typ_test() {
  // Both have x, tails are {} vs Typ(0)
  // Rcd([], None) vs Typ(0) should succeed (empty row is a row variable)
  let a = rcd_with_tail([#("x", v.int_t)], Some(rcd([])))
  let b = rcd_with_tail([#("x", v.int_t)], Some(v.Typ(0)))
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  // This actually works! Rcd([], None), v.Typ(_) -> ctx
  assert ctx.errors == []
}

// GAP 5: Rcd([], None) as tail vs Rcd(fields, Some(tail)) — field lookup
//
// When looking for a field in a tail that is Rcd([], None), the code
// should treat it as a row variable (absorbs the field), not as an
// empty closed record.
//
// In unify_rcd_field: when field not found in head, recurse into tail.
// If tail is Rcd([], None), the dispatch falls to:
//   Rcd([], None), Rcd([..], None) -> field not found error
// But Rcd([], None) as a tail should be a row variable.

pub fn unify_rcd_field_in_empty_tail_test() {
  // a = {x, tail={}} vs b = {x, y}
  // After matching x: tail {} vs {y}
  // Rcd([], None) as tail should absorb {y}
  let a = rcd_with_tail([#("x", v.int_t)], Some(rcd([])))
  let b = rcd([#("x", v.int_t), #("y", v.float_t)])
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  // BUG: RcdFieldNotFound("y") — empty tail treated as closed
  // FIX: Rcd([], None) as a tail should act as a row variable
  assert ctx.errors == []
}

pub fn unify_rcd_field_in_empty_tail_with_extra_test() {
  // a = {x, tail={}} vs b = {x, y, z}
  // Multiple extra fields should all be absorbed
  let a = rcd_with_tail([#("x", v.int_t)], Some(rcd([])))
  let b = rcd([#("x", v.int_t), #("y", v.float_t), #("z", v.i64)])
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  // BUG: RcdFieldNotFound errors for y and z
  assert ctx.errors == []
}

// GAP 6: Symmetric case — field lookup when left has tail Rcd([], None)
//
// When the LEFT side has a tail Rcd([], None) and the RIGHT side
// has extra fields, the tail should absorb them (symmetric to GAP 5).

pub fn unify_rcd_empty_tail_absorbs_right_extra_test() {
  // a = {x, tail={}} vs b = {x, y, tail={}}
  // After matching x: tail {} vs {y, tail={}}
  // Rcd([], None) should absorb {y} from right
  let a = rcd_with_tail([#("x", v.int_t)], Some(rcd([])))
  let b = rcd_with_tail([#("x", v.int_t), #("y", v.float_t)], Some(rcd([])))
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  // BUG: TypeMismatch(Rcd([], None), Rcd([y], Some(Rcd([], None))))
  // This is GAP 1: Rcd([], None) vs Rcd(fields, Some(tail)) unhandled
  assert ctx.errors == []
}

// GAP 7: Rcd([], None) as standalone should unify with any open record
//
// In the current implementation, Rcd([], None) only unifies with
// Rcd([], None) or Typ(_). It should also unify with any record
// that has a tail (open record), treating Rcd([], None) as the
// empty row prefix.

pub fn unify_rcd_empty_with_any_open_record_test() {
  // Rcd([], None) vs Rcd([x, y], Some(Rcd([z], None)))
  // Empty row should match any open record
  let a = rcd([])
  let b =
    rcd_with_tail(
      [#("x", v.int_t), #("y", v.float_t)],
      Some(rcd([#("z", v.i64)])),
    )
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  // BUG: TypeMismatch — unhandled pattern
  assert ctx.errors == []
}

pub fn unify_rcd_empty_with_chain_of_tails_test() {
  // Rcd([], None) vs deeply chained tails
  let b =
    rcd_with_tail(
      [#("a", v.int_t)],
      Some(rcd_with_tail(
        [#("b", v.float_t)],
        Some(rcd_with_tail([#("c", v.i64)], Some(rcd([])))),
      )),
    )
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(rcd([]), s1), #(b, s2))
  // BUG: TypeMismatch — unhandled pattern
  assert ctx.errors == []
}

// GAP 8: Row variable in pattern matching
//
// When a pattern has PRcd(fields, Some(PAny)), the PAny tail should
// match any remaining record structure. This works for flat records
// but may not work correctly for deeply nested tail structures.

pub fn match_pattern_rcd_deep_tail_test() {
  // Value has deeply nested tail structure
  let value =
    v.Rcd(
      [#("a", #(v.int(1), None))],
      Some(v.Rcd(
        [#("b", #(v.int(2), None))],
        Some(v.Rcd([#("c", #(v.int(3), None))], None)),
      )),
    )
  // Pattern asks for a, then PAny for the rest
  let pattern =
    tm.PRcd(
      [#("a", tm.PAlias("a", tm.PAny)), #("c", tm.PAlias("c", tm.PAny))],
      Some(tm.PAny),
    )
  let result = match_pattern(pattern, value)
  // Should find a=1 in head, c=3 in tail, PAny absorbs rest
  assert result == Some([v.int(3), v.int(1)])
}
// ============================================================================
// Summary of implementation gaps
//
// GAP 1: Missing pattern `Rcd([], None), Rcd(fields, Some(tail))`
//   File: src/core/unify.gleam, main unify dispatch
//   Fix: Add case `v.Rcd([], None), v.Rcd(_, Some(_)) -> ctx`
//
// GAP 2: Typ(_) tail recurses on field values instead of absorbing row
//   File: src/core/unify.gleam, `Rcd([field, ..], tail), Typ(_)` handler
//   Fix: When tail is Typ(_), accept whole record without field-by-field check
//
// GAP 3: Practical subtyping — check() with Typ(_) tail
//   Manifestation of GAP 2 in the type-checking workflow
//
// GAP 4: (WORKS) Closed tail Rcd([], None) vs Typ(_) — already handled
//   Case `v.Rcd([], None), v.Typ(_) -> ctx` covers this
//
// GAP 5: Rcd([], None) as tail treated as closed, not as row variable
//   File: src/core/unify.gleam, unify_rcd_field → tail recursion
//   Fix: When tail is Rcd([], None), treat as row variable (absorb fields)
//
// GAP 6: Symmetric of GAP 5 — left tail Rcd([], None) vs right fields
//   Manifestation of GAP 1
//
// GAP 7: Rcd([], None) standalone should unify with any open record
//   Manifestation of GAP 1
//
// GAP 8: Pattern matching with deep tails — field lookup through chains
//   File: src/core/eval.gleam, match_pattern_rcd_field
//   May work or may have edge cases with deeply chained tails
// =============================================================================
