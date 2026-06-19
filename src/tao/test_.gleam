import tao/ast.{type Module}
// pub fn package(
//   ctx: Context,
//   mods: List(Module),
// ) -> #(List(#(String, #(Term, Type))), Context) {
//   let #(pkg_mods, ctx) = define_modules(ctx, mods)
//   let #(typed_mods, ctx) = infer_modules(ctx, pkg_mods)
//   let typed_mods = resolve_modules(ctx, typed_mods)
//   #(typed_mods, ctx)
// }
