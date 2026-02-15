open Core

type pattern =
  | PVar of string         (* Matches anything, binds it to a name *)
  | PWild                  (* Matches anything (the '_' underscore) *)
  | PLit of literal        (* Matches a specific literal like '5' or '"hello"' *)
  | PCon of int * pattern list (* Matches a constructor tag and its sub-patterns *)

type redundancy = Redundant of span
type missing = Missing of pattern list

type exhaustiveness_result = {
  unused: redundancy list;
  missing: missing option;
}

(* A simplified consistency check for Core *)
let rec is_consistent (equations : (value * value) list) : bool =
  match equations with
  | [] -> true
  | (v1, v2) :: rest ->
      match (v1, v2) with
      | VLit l1, VLit l2 -> if l1 = l2 then is_consistent rest else false
      | VCon (t1, a1), VCon (t2, a2) ->
          if t1 <> t2 then false
          else is_consistent (List.combine a1 a2 @ rest)
      | VNe (HVar i, []), VNe (HVar j, []) ->
          (* If two free variables are equated, they are consistent 
             but we might need to update a substitution table *)
          is_consistent rest
      | VNe (HVar _, []), _ | _, VNe (HVar _, []) -> true (* Variable can be anything *)
      | _ -> true (* Fallback for complex terms we can't solve *)

(* Simplified view of the Pattern Matrix logic *)
let rec check_match (ctx : context) (cases : (pattern * span) list) : exhaustiveness_result =
  let rec loop matrix remaining_cases diagnostics =
    match remaining_cases with
    | [] -> 
        (* Final step: Check if the 'wildcard' (default) case is useful. 
           If it is, something is missing! *)
        if is_useful matrix [PWild] then
          { diagnostics with missing = Some (Missing [construct_missing matrix]) }
        else 
          diagnostics
          
    | (pat, span) :: rest ->
        if not (is_useful matrix [pat]) then
          (* Report Redundancy *)
          loop matrix rest { diagnostics with unused = Redundant span :: diagnostics.unused }
        else
          (* Pattern is useful, add it to the matrix and continue *)
          loop (pat :: matrix) rest diagnostics
  in
  loop [] cases { unused = []; missing = None }

(* Conceptual OCaml logic for checking a branch *)
let check_branch lvl ctx pattern branch_body expected_type =
  let (refined_ctx, constraints) = unify_pattern_with_type pattern scrutinee_type in
  if is_consistent constraints then
    check (lvl + List.length refined_ctx) (refined_ctx @ ctx) branch_body expected_type
  else
    (* Mark branch as unreachable/impossible *)
    ()
