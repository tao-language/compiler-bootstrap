import core/context.{new_ctx}
import core/term as tm
import core/value as v
import tao/compile

pub fn compile_module_empty_test() {
  let ctx0 = new_ctx
  let #(term, type_, ctx) = compile.module(ctx0, #("m", []))
  assert ctx.errors == []
  assert term == tm.Rcd([])
  assert type_ == v.RcdT([])
}
