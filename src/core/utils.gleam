pub fn list_at(list: List(a), index: Int) -> Result(a, Nil) {
  case list {
    [] -> Error(Nil)
    [head, ..] if index <= 0 -> Ok(head)
    [_, ..tail] -> list_at(tail, index - 1)
  }
}

pub fn list_lookup(list: List(#(k, v)), key: k) -> Result(v, Nil) {
  case list {
    [] -> Error(Nil)
    [#(k, v), ..] if k == key -> Ok(v)
    [_, ..tail] -> list_lookup(tail, key)
  }
}
