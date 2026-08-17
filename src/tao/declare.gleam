import core/context.{type Context}
import core/value.{type Value} as v
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/result
import syntax/span.{type Span}
import tao/ast.{type Module, type Stmt} as tao

pub type ModName =
  String

pub type Name =
  String

pub type Signature =
  #(Stmt, Option(tao.Type))

pub type Declarations =
  List(#(Name, Signature))

pub fn get_exports(
  defs: List(#(ModName, Declarations)),
) -> List(#(ModName, List(Name))) {
  list.map(defs, fn(def) {
    let #(mod_name, declarations) = def
    let names =
      list.map(declarations, fn(decl) {
        let #(name, _) = decl
        name
      })
    #(mod_name, names)
  })
}

pub fn package(mods: List(Module)) -> List(#(ModName, Declarations)) {
  case mods {
    [] -> []
    [mod, ..mods] -> [module(mods, mod), ..package(mods)]
  }
}

pub fn module(mods: List(Module), mod: Module) -> #(ModName, Declarations) {
  let #(mod_name, stmts) = mod
  #(mod_name, block(stmts))
}

pub fn block(stmts: List(Stmt)) -> Declarations {
  case stmts {
    [] -> []
    [stmt_, ..stmts] -> list.append(stmt(stmt_), block(stmts))
  }
}

pub fn stmt(stmt_: Stmt) -> Declarations {
  case stmt_.data {
    tao.Import(path, alias, names) -> []
    tao.ImportAll(path, alias) -> []
    tao.Extern(name, params, returns) -> {
      let typ = tao.fn_t(#([], None), params, returns, stmt_.span)
      [#("@" <> name, #(stmt_, Some(typ)))]
    }
    tao.LetVar(name, opt_type, _) -> [#(name, #(stmt_, opt_type))]
    tao.LetPat(pattern, types, value) -> todo
    tao.LetMut(name, opt_type, value) -> todo
    tao.Mut(name, value) -> todo
    tao.Test(name, expr, expect) -> [#(name, #(stmt_, None))]
    tao.FnDef(
      name,
      #(implicits, implicits_tail),
      #(params, params_tail),
      returns,
      body,
    ) -> todo
    tao.FnOverload(name, _) -> [#(name, #(stmt_, None))]
    tao.TypeDef(type_def) -> todo
    tao.For(iterator, range, body) -> todo
    tao.While(condition, body) -> todo
    tao.Return(expr) -> todo
    tao.Break -> todo
    tao.Continue -> todo
  }
}

pub fn overloads(
  defs: List(#(ModName, Declarations)),
) -> List(#(ModName, Declarations)) {
  list.map(defs, fn(def) {
    let #(mod_name, declarations) = def
    let declarations =
      list.map(declarations, fn(decl) {
        let #(name, sig) = decl
        #(name, overloads_signature(defs, mod_name, sig))
      })
    #(mod_name, declarations)
  })
}

fn overloads_signature(
  defs: List(#(ModName, Declarations)),
  mod_name: ModName,
  sig: Signature,
) -> Signature {
  let #(stmt_, _) = sig
  case stmt_.data {
    tao.FnOverload(_, choices) -> {
      let s = stmt_.span
      let implicits = [#(tao.pvar("__type", s), #(Some(tao.type_(s)), None))]
      let params = [
        #(tao.pvar("__args", s), #(Some(tao.var("__type", s)), None)),
      ]
      let cases = list.map(choices, overloads_choice_case(defs, mod_name, _))
      let typ =
        tao.FnT(
          #(implicits, None),
          #(params, None),
          tao.match(tao.var("__type", s), cases, s),
        )
      #(stmt_, Some(tao.Expr(typ, s)))
    }
    _ -> sig
  }
}

fn overloads_choice_case(
  defs: List(#(ModName, Declarations)),
  mod_name: ModName,
  choice: tao.OverloadChoice,
) -> tao.Case {
  let fun_type = case choice.fun_choice {
    tao.OverloadVar(name) ->
      overloads_choice_fun_type(defs, mod_name, name, choice.span)
    tao.OverloadCall(name) ->
      overloads_choice_fun_type(defs, mod_name, "@" <> name, choice.span)
    tao.OverloadModuleVar(mod_name, name) ->
      overloads_choice_fun_type(defs, mod_name, name, choice.span)
  }
  let ret_type = case fun_type.data {
    tao.FnT(_, _, ret_type) -> ret_type
    _ -> tao.err(choice.span)
  }
  tao.Case(tao.prcd_strict(choice.args, choice.span), choice.guard, ret_type)
}

fn overloads_choice_fun_type(
  defs: List(#(ModName, Declarations)),
  mod_name: ModName,
  name: Name,
  span: Span,
) -> tao.Type {
  list.key_find(defs, mod_name)
  |> result.unwrap([])
  |> list.key_find(name)
  |> result.map(fn(decl) {
    let #(_, opt_type) = decl
    opt_type
  })
  |> result.unwrap(None)
  |> option.unwrap(tao.err(span))
}
