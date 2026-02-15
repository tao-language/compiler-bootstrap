open Core

type type_error =
  | UnboundVariable of string * span
  | TypeMismatch of {
      expected: value;
      got: value;
      span: span;
      context_span: span option; (* Where the 'expected' type came from *)
    }
  | NotAFunction of {
      got_type: value;
      span: span;
    }

(* Color Coding: Red for error, Cyan for the snippet, Yellow for types *)
(* The "Did you mean?": If a variable is unbound, run a Levenshtein distance check against the current context to suggest the correct name *)
(* Exhaustiveness Visuals: For pattern matching errors, don't just say "Not exhaustive." Generate a sample case that isn't covered: "Case Option.None is not handled." *)
(* No Cascades: If a type check fails, return a "Hole" or "Error" type (often called a VError or TAny). This allows the compiler to keep checking the rest of the file without spitting out 500 follow-up errors caused by the first one *)
(* let report_error (err : type_error) (source_code : string) =
  match err with
  | TypeMismatch { expected; got; span; _ } ->
      let snippet = get_source_snippet source_code span in
      Printf.printf "Error on line %d:\n\n%s\n\n" span.start_line snippet;
      Printf.printf "Expected type: %s\n" (value_to_string expected);
      Printf.printf "   Actual type: %s\n" (value_to_string got) *)