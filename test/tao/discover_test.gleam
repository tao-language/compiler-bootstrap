import gleam/option.{None}
import syntax/span.{Span}
import tao/ast as tao
import tao/discover.{definitions, definitions_public, tests}

const s = Span("discover_test", 0, 0, 0, 0)

fn def(name) {
  tao.let_(tao.pvar(name, s), None, tao.int(42, s), s)
}
// pub fn definitions_test() {
//   assert definitions([]) == []
//   assert definitions([def("x")]) == ["x"]
//   assert definitions([def("A")]) == ["A"]
//   assert definitions([def("_x")]) == ["_x"]
//   assert definitions([def("_A")]) == ["_A"]
// }
