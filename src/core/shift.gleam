import core/ast

pub fn shift_value(value: ast.Value, delta: Int) -> ast.Value {
  case value {
    ast.VTyp(u) -> ast.VTyp(u)
    ast.VLit(k) -> ast.VLit(k)
    ast.VLitT(k) -> ast.VLitT(k)
    ast.VNeut(head, spine) ->
      ast.VNeut(shift_head(head, delta), shift_spine(spine, delta))
    // VNeut(head: Head, spine: List(Elim))
    // VCtr(tag: String, arg: Value)
    // VRcd(fields: List(#(String, Value)))
    // VRcdT(fields: List(#(String, Value, Option(Value))))
    // VLam( env: Env, implicits: List(#(String, Value)), param: #(String, Value), body: Term, )
    // VPi( env: Env, implicits: List(#(String, Value)), domain: #(String, Value), codomain: Value, )
    // VTypeDef( params: List(#(String, Value)), constructors: List(#(String, #(List(String), Value, Term))), )
    // VErr
    _ -> {
      echo value
      todo
    }
  }
}

fn shift_head(head: ast.Head, delta: Int) -> ast.Head {
  case head {
    ast.HVar(lvl) -> ast.HVar(lvl + delta)
    _ -> {
      echo head
      todo
    }
  }
}

fn shift_elim(elim: ast.Elim, delta: Int) -> ast.Elim {
  echo elim
  todo
}

fn shift_spine(spine: List(ast.Elim), delta: Int) -> List(ast.Elim) {
  case spine {
    [] -> []
    [elim, ..spine] -> [shift_elim(elim, delta), ..shift_spine(spine, delta)]
  }
}
