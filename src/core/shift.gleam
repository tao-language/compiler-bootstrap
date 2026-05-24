import core/ast
import gleam/list
import gleam/option

/// Shift a Value's DeBruijn levels by delta.
///
/// Used during lambda inference to maintain correct DeBruijn levels when
/// the environment changes (push_param shifts +1, pop_params shifts -delta).
///
/// Universes, literals, and neutral terms are handled. The following Value
/// variants are NOT yet implemented (will panic with todo):
///   - VCtr, VRcd, VRcdT: would need recursive field/arg shifting
///   - VLam, VPi: would need recursive implicits, domain, and codomain shifting
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
    // --- COMPOSITE VALUES ---
    ast.VCtr(tag, arg) -> ast.VCtr(tag, shift_value(arg, delta))
    ast.VRcd(fields) -> ast.VRcd(
      list.map(fields, fn(field) { #(field.0, shift_value(field.1, delta)) }),
    )
    ast.VRcdT(fields) -> ast.VRcdT(
      list.map(fields, fn(field) {
        #(field.0, shift_value(field.1, delta), option.map(field.2, shift_value(_, delta)))
      }),
    )
    ast.VLam(env, implicits, param, body) -> ast.VLam(
      list.map(env, shift_value(_, delta)),
      implicits,
      param,
      body,
    )
    ast.VPi(implicits, domain, codomain) -> ast.VPi(
      list.map(implicits, fn(v) { #(v.0, shift_value(v.1, delta)) }),
      #(domain.0, shift_value(domain.1, delta)),
      shift_value(codomain, delta),
    )
    ast.VTypeDef(params, constructors) -> ast.VTypeDef(
      list.map(params, fn(p) { #(p.0, shift_value(p.1, delta)) }),
      constructors,
    )
    ast.VErr -> ast.VErr
  }
}

fn shift_head(head: ast.Head, delta: Int) -> ast.Head {
  case head {
    ast.HVar(lvl) -> ast.HVar(lvl + delta)
    ast.HHole(id) -> ast.HHole(id)
    ast.HCall(name, args) -> todo
  }
}

fn shift_elim(elim: ast.Elim, delta: Int) -> ast.Elim {
  // EApp: arg value needs shifting
  // EFix
  // EMatch: env in elim needs shifting
  todo
}

fn shift_spine(spine: List(ast.Elim), delta: Int) -> List(ast.Elim) {
  case spine {
    [] -> []
    [elim, ..spine] -> [shift_elim(elim, delta), ..shift_spine(spine, delta)]
  }
}
