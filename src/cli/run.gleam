/// CLI Run Command — compile and evaluate Core programs
///
/// Usage:
///   gleam run <filename.core>           # Run a Core file
///   gleam run -c 'expression'           # Run an inline expression
///   gleam run --help                    # Show help
///   gleam run --debug <filename>        # Run with debug output
// import cli/debug_core
// import core/ast.{
//   type Head, type LiteralType, type Value, F16T, F32T, F64T, Float as AstFloat,
//   FloatT, HFix, HHole, HVar, I16, I32T, I64T, I8, Int, IntT, U16T, U32T, U64T,
//   U8T, VCall, VCtr, VErr, VFix, VLam, VLit, VLitT, VNeut, VPi, VRcd, VRcdT, VTyp,
//   VTypeDef, term_to_debruijn, term_to_string,
// }
// import core/eval.{evaluate}
// import core/infer.{infer}
// import core/quote.{quote}
// import core/state.{
//   type Error, CtorArgTypeMismatch, CtorNotFound, CtrUndefined, HoleUnsolved,
//   MatchMissing, MatchRedundant, NotAFunction, StepLimitExceeded, TypeMismatch,
//   VarUndefined, initial_state,
// }
// import core/syntax.{parse}
// import gleam/float
// import gleam/int
// import gleam/io
// import gleam/list
// import gleam/option.{None, Some}
// import gleam/string
// import simplifile
// import syntax/grammar.{type ParseError, ParseError as ParseErrorCtor}
// import syntax/span.{type Span}

// /// CLI command types.
// pub type Command {
//   Run(source: Source, verbose: Bool, debug: Bool)
//   Check(source: Source, verbose: Bool, debug: Bool)
//   DebugCore(expression: String, trace_parser: Bool, trace_infer: Bool)
//   Help
// }

// /// Where the source comes from.
// pub type Source {
//   File(path: String)
//   Inline(expression: String)
// }

// /// Parse debug flags from remaining arguments.
// fn parse_debug_flags(
//   args: List(String),
//   trace_parser: Bool,
//   trace_infer: Bool,
// ) -> Result(#(Bool, Bool), String) {
//   case args {
//     [] -> Ok(#(trace_parser, trace_infer))
//     ["--trace-parser", ..rest] -> parse_debug_flags(rest, True, trace_infer)
//     ["--trace-infer", ..rest] -> parse_debug_flags(rest, trace_parser, True)
//     [flag, ..] -> Error("Unknown debug flag: " <> flag)
//   }
// }

// /// Run a source (parse, infer, evaluate, print).
// pub fn run_source(source: Source) -> Nil {
//   let result = execute(source)
//   case result {
//     Ok(value) -> {
//       io.println(format_value(value))
//       cli_halt(0)
//     }
//     Error(errors) -> {
//       list.each(errors, fn(e) { io.println("Error: " <> e) })
//       cli_halt(1)
//     }
//   }
// }

// /// Check (type-check only) a source without evaluating.
// pub fn check_source(source: Source) -> Nil {
//   let result = execute(source)
//   case result {
//     Ok(value) -> {
//       let type_val = evaluate([], [], quote(value))
//       io.println("Result type: " <> format_type(type_val))
//       cli_halt(0)
//     }
//     Error(errors) -> {
//       list.each(errors, fn(e) { io.println("Error: " <> e) })
//       cli_halt(1)
//     }
//   }
// }

// /// Run the full pipeline: parse → infer → evaluate.
// pub fn execute(source: Source) -> Result(Value, List(String)) {
//   let contents = case source {
//     File(path) -> load_file(path)
//     Inline(expr) -> Ok(expr)
//   }

//   case contents {
//     Error(msg) -> Error([msg])
//     Ok(text) -> {
//       let #(named_term, parse_errors) = parse(text)
//       let term = term_to_debruijn(named_term)
//       let error_msgs = format_parse_errors(parse_errors)
//       let all_errors = case error_msgs {
//         [] -> []
//         errs -> {
//           list.each(errs, fn(e) { io.println("Parse error: " <> e) })
//           errs
//         }
//       }

//       let state = initial_state([])
//       let #(result_term, _, final_state) = infer(state, term)
//       let type_errors = list.map(final_state.errors, state.error_to_string)
//       let all_errors = list.append(all_errors, type_errors)

//       case all_errors {
//         [] -> Ok(evaluate([], [], result_term))
//         errs -> Error(errs)
//       }
//     }
//   }
// }

// /// Load file contents from disk.
// pub fn load_file(path: String) -> Result(String, String) {
//   case simplifile.read(path) {
//     Ok(contents) -> Ok(contents)
//     Error(err) ->
//       case err {
//         simplifile.Enoent -> Error("File not found: " <> path)
//         simplifile.Eacces -> Error("Permission denied: " <> path)
//         _ -> Error("Cannot read file: " <> path)
//       }
//   }
// }

// fn format_parse_errors(errors: List(ParseError)) -> List(String) {
//   errors
//   |> list.map(fn(e) {
//     case e {
//       ParseErrorCtor(
//         expected: exp,
//         got: got,
//         span: span,
//         context: ctx,
//         rule: rule,
//         surrounding: _surrounding,
//       ) -> format_single_error(exp, got, span, ctx, rule)
//     }
//   })
// }

// fn format_single_error(
//   exp: String,
//   got: String,
//   span: Span,
//   ctx: String,
//   rule: String,
// ) -> String {
//   let line_col =
//     int.to_string(span.start_line) <> ":" <> int.to_string(span.start_col)
//   let rule_info = case rule {
//     "" -> ""
//     r -> " (rule: " <> r <> ")"
//   }
//   let ctx_info = case ctx {
//     "" -> ""
//     c -> " in " <> c
//   }
//   "Parse error at "
//   <> line_col
//   <> ": expected "
//   <> exp
//   <> ", got "
//   <> got
//   <> ctx_info
//   <> rule_info
// }

// fn format_value(value: Value) -> String {
//   case value {
//     VLit(Int(v)) -> int.to_string(v)
//     VLit(AstFloat(v)) -> float.to_string(v)
//     VNeut(head, _) -> format_head(head)
//     VPi(_env, _implicits, domain, codomain) ->
//       "$pi("
//       <> domain.0
//       <> ": "
//       <> format_type(domain.1)
//       <> ") -> "
//       <> format_type(codomain)
//     VCtr(tag, arg) -> "#" <> tag <> "(" <> format_value(arg) <> ")"
//     VRcd(fields) ->
//       "{ "
//       <> string.join(
//         list.map(fields, fn(f) { f.0 <> ": " <> format_value(f.1) }),
//         with: ", ",
//       )
//       <> " }"
//     VRcdT(fields) ->
//       "${ "
//       <> string.join(
//         list.map(fields, fn(f) {
//           let field_str = f.0 <> ": " <> format_value(f.1)
//           case f.2 {
//             Some(d) -> field_str <> " = " <> format_value(d)
//             None -> field_str
//           }
//         }),
//         with: ", ",
//       )
//       <> " }"
//     VLam(_env, _implicits, param, _) -> "$fn(" <> param.0 <> ") => <lambda>"
//     VCall(name, args, return_type) ->
//       "%"
//       <> name
//       <> "("
//       <> string.join(
//         list.map(args, fn(a) { format_value(a.0) <> ": " <> format_value(a.1) }),
//         with: ", ",
//       )
//       <> ") -> "
//       <> format_value(return_type)
//     VFix(name, _env, body) ->
//       "VFix(" <> name <> " => " <> term_to_string(body) <> ")"
//     VTypeDef(name: n, params: _, constructors: _) -> "<VTypeDef " <> n <> ">"
//     VTyp(level) -> "$Type<" <> int.to_string(level) <> ">"
//     VLitT(t) -> format_litt(t)
//     VErr -> "<error>"
//   }
// }

// fn format_litt(type_: LiteralType) -> String {
//   case type_ {
//     IntT -> "$Int"
//     FloatT -> "$Float"
//     I8 -> "$I8"
//     I16 -> "$I16"
//     I32T -> "$I32"
//     I64T -> "$I64"
//     U8T -> "$U8"
//     U16T -> "$U16"
//     U32T -> "$U32"
//     U64T -> "$U64"
//     F16T -> "$F16"
//     F32T -> "$F32"
//     F64T -> "$F64"
//   }
// }

// fn format_head(head: Head) -> String {
//   case head {
//     HVar(level) -> "v" <> int.to_string(level)
//     HHole(id) -> "?" <> int.to_string(id)
//     HFix(vfix) ->
//       case vfix {
//         VFix(name, _, _) -> "$fix " <> name
//         _ -> "$fix ?"
//       }
//   }
// }

// fn format_type(type_val: Value) -> String {
//   case type_val {
//     VNeut(HVar(0), _) -> "$Type"
//     VNeut(HVar(1), _) -> "$Int"
//     VCtr(tag, arg) -> "#" <> tag <> "(" <> format_type(arg) <> ")"
//     VPi(_env, _implicits, domain, codomain) ->
//       "$pi("
//       <> domain.0
//       <> ": "
//       <> format_type(domain.1)
//       <> ") -> "
//       <> format_type(codomain)
//     VRcd(_) -> "{}"
//     VLam(_, _, _, _) -> "<lambda>"
//     VTypeDef(name: n, params: _, constructors: _) -> "<type " <> n <> ">"
//     VErr -> "<error type>"
//     _ -> "<type>"
//   }
// }

// /// External: halt the Erlang VM with the given exit code.
// @external(erlang, "erlang", "halt")
// pub fn cli_halt(code: Int) -> a
