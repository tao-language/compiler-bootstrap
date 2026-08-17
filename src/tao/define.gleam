import core/context.{type Context}
import gleam/list
import tao/declare.{type Declarations, type ModName}

pub fn declarations(
  ctx: Context,
  defs: List(#(ModName, Declarations)),
) -> Context {
  let exports = declare.get_exports(defs)
  todo
}
