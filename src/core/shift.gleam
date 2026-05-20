import core/ast
import gleam/list

/// Shift a Value's DeBruijn levels by delta.
///
/// Used during lambda inference to maintain correct DeBruijn levels when
/// the environment changes (push_param shifts +1, pop_params shifts -delta).
///
/// Universes, literals, and neutral terms are handled. The following Value
/// variants are NOT yet implemented (will panic with todo):
///   - VCtr, VRcd, VRcdT: would need recursive field/arg shifting
///   - VLam, VPi: would need recursive env and codomain shifting
///   - VTypeDef: would need recursive constructor value shifting
///   - VErr: propagates as-is
///
/// Currently safe because inferred lambdas only capture VNeut/VLit/VLitT/VTyp
/// values in their env. If GADT constructors, records, or pi types appear as
/// captured env values, this will panic until the missing cases are implemented.
pub fn shift_value(value: ast.Value, delta: Int) -> ast.Value {
  case value {
    // Universes are constants — no DeBruijn levels to shift
    ast.VTyp(u) -> ast.VTyp(u)
    // Literals are constants — no DeBruijn levels to shift
    ast.VLit(k) -> ast.VLit(k)
    ast.VLitT(k) -> ast.VLitT(k)
    // Neutral terms have DeBruijn heads (HVar) that shift with delta
    ast.VNeut(head, spine) ->
      ast.VNeut(shift_head(head, delta), shift_spine(spine, delta))
    // --- UNIMPLEMENTED (panic on todo) ---
    ast.VCtr(tag, arg) -> todo
    ast.VRcd(fields) -> todo
    ast.VRcdT(fields) -> todo
    ast.VLam(env, implicits, param, body) -> todo
    ast.VPi(env, implicits, domain, codomain) -> todo
    ast.VTypeDef(params, constructors) -> todo
    ast.VErr -> ast.VErr
  }
}

fn shift_head(head: ast.Head, delta: Int) -> ast.Head {
  case head {
    // HVar: DeBruijn level shifts by delta
    ast.HVar(lvl) -> ast.HVar(lvl + delta)
    // HHole: hole IDs are stable identifiers, not DeBruijn levels
    ast.HHole(id) -> ast.HHole(id)
    // HCall: would need recursive arg shifting — unimplemented
    ast.HCall(name, args) -> todo
    // HFix: shift the captured env levels by delta
    ast.HFix(env, body) ->
      ast.HFix(list.map(env, fn(v) { shift_value(v, delta) }), body)
  }
}

fn shift_elim(elim: ast.Elim, delta: Int) -> ast.Elim {
  // EApp: arg value needs shifting
  // EMatch: env in elim needs shifting
  todo
}

fn shift_spine(spine: List(ast.Elim), delta: Int) -> List(ast.Elim) {
  case spine {
    [] -> []
    [elim, ..spine] -> [shift_elim(elim, delta), ..shift_spine(spine, delta)]
  }
}
