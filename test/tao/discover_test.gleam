import gleam/option.{None}
import syntax/span.{Span}
import tao/ast as tao
import tao/discover

const s = Span("discover_test", 0, 0, 0, 0)

fn let_(name) {
  tao.let_(tao.pvar(name, s), None, tao.int(42, s), s)
}
// pub fn definitions_test() {
//   assert definitions([]) == []
//   assert definitions([let_("x")]) == ["x"]
//   assert definitions([let_("A")]) == ["A"]
//   assert definitions([let_("_x")]) == ["_x"]
//   assert definitions([let_("_A")]) == ["_A"]
// }
