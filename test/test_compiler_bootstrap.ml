open Compiler_bootstrap.Core

let () = 
  try 
    (* Identity Function *)
    (* id : (A : Type) -> A -> A *)
    let id_type = Pi ("A", Univ 0, Pi ("x", Var 0, Var 1)) in
    let id_term = Lam ("A", Lam ("x", Var 0)) in
    check 0 [] id_term (eval [] id_type);
    print_endline "Type Check Passed!"
  with Failure msg -> 
    print_endline ("Error: " ^ msg)