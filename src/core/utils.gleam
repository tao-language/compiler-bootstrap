import gleam/option.{type Option, None, Some}

pub fn list_at(list: List(a), index: Int) -> Option(a) {
  case list {
    [head, ..] if index <= 0 -> Some(head)
    [_, ..tail] -> list_at(tail, index - 1)
    [] -> None
  }
}
