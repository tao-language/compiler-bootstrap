import syntax/span.{type Span}

pub type Error {
  UnexpectedToken(token: String, span: Span)
}
