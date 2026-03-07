// ============================================================================
// CORE LANGUAGE SYNTAX - Minimal Working Grammar
// ============================================================================

import grammar
import lexer
import parser

pub fn core_grammar() -> grammar.Grammar {
  grammar.new("Core")
  |> grammar.start("Expr")
  |> grammar.with_token("Ident")
  |> grammar.with_token("Number")
  |> grammar.with_token("String")
  |> grammar.with_token("LParen")
  |> grammar.with_token("RParen")
  |> grammar.with_token("LBrace")
  |> grammar.with_token("RBrace")
  |> grammar.with_token("Comma")
  |> grammar.with_token("Arrow")
  |> grammar.with_token("Pipe")
  |> grammar.with_token("Colon")
  |> grammar.with_keyword("fn")
  |> grammar.with_keyword("match")
  |> grammar.with_keyword("let")
  |> grammar.with_keyword("rec")
  |> grammar.with_keyword("do")
  |> grammar.with_keyword("handle")
  |> grammar.with_keyword("return")
  |> grammar.with_keyword("if")
  |> grammar.rule("Expr", grammar.choice([
    grammar.token("Ident"),
    grammar.token("Number"),
    grammar.token("String"),
    grammar.ref("FnExpr"),
    grammar.ref("MatchExpr"),
    grammar.ref("LetExpr"),
    grammar.ref("DoExpr"),
    grammar.ref("HandleExpr"),
    grammar.ref("RecordExpr"),
    grammar.ref("AppExpr"),
  ]))
  |> grammar.rule("AppExpr", grammar.seq([
    grammar.token("Ident"),
    grammar.token("LParen"),
    grammar.opt(grammar.sep(grammar.ref("Expr"), grammar.token("Comma"))),
    grammar.token("RParen"),
  ]))
  |> grammar.rule("FnExpr", grammar.seq([
    grammar.keyword("fn"),
    grammar.token("LParen"),
    grammar.opt(grammar.sep(grammar.token("Ident"), grammar.token("Comma"))),
    grammar.token("RParen"),
    grammar.token("Arrow"),
    grammar.ref("Expr"),
  ]))
  |> grammar.rule("MatchExpr", grammar.seq([
    grammar.keyword("match"),
    grammar.ref("Expr"),
    grammar.keyword("{"),
    grammar.many1(grammar.ref("MatchCase")),
    grammar.keyword("}"),
  ]))
  |> grammar.rule("MatchCase", grammar.seq([
    grammar.token("Pipe"),
    grammar.token("Ident"),
    grammar.token("Arrow"),
    grammar.ref("Expr"),
  ]))
  |> grammar.rule("LetExpr", grammar.seq([
    grammar.keyword("let"),
    grammar.token("Ident"),
    grammar.token("Arrow"),
    grammar.ref("Expr"),
  ]))
  |> grammar.rule("DoExpr", grammar.seq([
    grammar.keyword("do"),
    grammar.token("Ident"),
    grammar.token("LParen"),
    grammar.token("RParen"),
  ]))
  |> grammar.rule("HandleExpr", grammar.seq([
    grammar.keyword("handle"),
    grammar.ref("Expr"),
    grammar.keyword("{"),
    grammar.many1(grammar.ref("HandlerCase")),
    grammar.keyword("}"),
  ]))
  |> grammar.rule("HandlerCase", grammar.seq([
    grammar.token("Pipe"),
    grammar.keyword("return"),
    grammar.token("LParen"),
    grammar.token("Ident"),
    grammar.token("RParen"),
    grammar.token("Arrow"),
    grammar.ref("Expr"),
  ]))
  |> grammar.rule("RecordExpr", grammar.seq([
    grammar.token("LBrace"),
    grammar.opt(grammar.sep1(grammar.ref("Field"), grammar.token("Comma"))),
    grammar.token("RBrace"),
  ]))
  |> grammar.rule("Field", grammar.seq([
    grammar.token("Ident"),
    grammar.token("Colon"),
    grammar.ref("Expr"),
  ]))
}

pub fn parse(source: String) -> parser.ParseResult(parser.Tree) {
  let g = core_grammar()
  let parse_fn = grammar.to_parser(g)
  let tokens = lexer.tokenize(lexer.default_config(), "core", source)
  parse_fn(tokens)
}

pub fn format(ast: parser.Tree) -> String {
  let g = core_grammar()
  let format_fn = grammar.to_formatter(g)
  format_fn(ast)
}
