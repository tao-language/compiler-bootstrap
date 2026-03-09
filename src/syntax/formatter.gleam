// ============================================================================
// FORMATTER - Document Algebra Pretty Printer
// ============================================================================
import gleam/list
import gleam/string

pub type Doc {
  Empty
  Text(String)
  Line
  HardLine
  Group(Doc)
  Nest(Int, Doc)
  Concat(List(Doc))
}

pub fn empty() -> Doc {
  Empty
}

pub fn text(s: String) -> Doc {
  case s == "" {
    True -> Empty
    False -> Text(s)
  }
}

pub fn line() -> Doc {
  Line
}

pub fn space() -> Doc {
  Text(" ")
}

pub fn hardline() -> Doc {
  HardLine
}

pub fn concat(docs: List(Doc)) -> Doc {
  case docs {
    [] -> Empty
    [d] -> d
    _ -> Concat(docs)
  }
}

pub fn append(d1: Doc, d2: Doc) -> Doc {
  concat([d1, d2])
}

pub fn nest(n: Int, doc: Doc) -> Doc {
  case n <= 0 {
    True -> doc
    False -> Nest(n, doc)
  }
}

pub fn group(doc: Doc) -> Doc {
  Group(doc)
}

pub fn join(sep: Doc, docs: List(Doc)) -> Doc {
  case docs {
    [] -> Empty
    [first] -> first
    [first, ..rest] -> {
      list.fold(over: rest, from: first, with: fn(acc, d) {
        concat([acc, sep, d])
      })
    }
  }
}

pub fn space_sep(docs: List(Doc)) -> Doc {
  join(text(" "), docs)
}

pub fn comma_sep(docs: List(Doc)) -> Doc {
  join(concat([text(","), line()]), docs)
}

pub fn parens(doc: Doc) -> Doc {
  concat([text("("), doc, text(")")])
}

pub fn braces(doc: Doc) -> Doc {
  concat([text("{"), doc, text("}")])
}

pub fn render(doc: Doc, width: Int) -> String {
  let formatted = format_to_string(doc, width, 0, True)
  string.trim(formatted)
}

pub fn render_default(doc: Doc) -> String {
  render(doc, 80)
}

fn format_to_string(doc: Doc, width: Int, indent: Int, flat: Bool) -> String {
  case doc {
    Empty -> ""
    Text(s) -> s
    Line -> {
      case flat {
        True -> " "
        False -> "\n" <> string.repeat(" ", indent)
      }
    }
    HardLine -> "\n" <> string.repeat(" ", indent)
    Group(inner) -> {
      let flat_str = format_to_string(inner, width, indent, True)
      case fits(flat_str, width) {
        True -> flat_str
        False -> format_to_string(inner, width, indent, False)
      }
    }
    Nest(n, inner) -> format_to_string(inner, width, indent + n, flat)
    Concat(docs) -> {
      string.concat(
        list.map(docs, fn(d) { format_to_string(d, width, indent, flat) }),
      )
    }
  }
}

fn fits(s: String, width: Int) -> Bool {
  case string.contains(s, "\n") {
    True -> False
    False -> {
      let lines = string.split(s, "\n")
      case lines {
        [first] -> string.length(first) <= width
        _ -> False
      }
    }
  }
}
