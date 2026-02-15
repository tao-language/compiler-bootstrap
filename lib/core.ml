type literal =
  | I32 of int32
  | F64 of float

(* We use De Bruijn Indices for variables to avoid renaming hassles. 
   Var(0) is the most recently bound variable. *)
type term =
  | Var of int
  | Univ of int                  (* Universe level: Kind0, Kind1... *)
  | Lit of literal
  | Pi of string * term * term   (* (x : A) -> B *)
  | Lam of string * term         (* \x. body *)
  | App of term * term           (* f x *)
  | Ann of term * term           (* term : Type (Annotation) *)
  (*
  | Let of string * term * term * term (* let x: T = V in B *)
  | Con of int * term list             (* Constructor tag + args *)
  | Match of term * branch list        (* Pattern matching *)
  | Intrinsic of string * term list    (* Low-level ops *)
  | Loc of span * term
*)

and span = { 
  file: string; 
  start_line: int; 
  start_col: int; 
  end_line: int; 
  end_col: int 
}

(* "Values" are terms that have been evaluated as much as possible. 
   Closures capture the environment for lazy evaluation of function bodies. *)
type value =
  | VUniv of int
  | VLit of literal
  | VPi of string * value * (value -> value) (* Dependent function type *)
  | VLam of string * (value -> value)        (* Function closure *)
  | VNe of head * value list                 (* Neutral: blocked term (e.g. x, or x y) *)

and head = 
  | HVar of int (* De Bruijn Level (absolute index) to handle free vars safely *)

(* Environment for evaluation: maps De Bruijn indices to Values *)
type env = value list

type context = (string * value) list

(* Evaluate a term into a value *)
let rec eval (env : env) (t : term) : value =
  match t with
  | Var i -> List.nth env i
  | Univ k -> VUniv k
  | Pi (x, a, b) -> VPi (x, eval env a, fun v -> eval (v :: env) b)
  | Lam (x, t) -> VLam (x, fun v -> eval (v :: env) t)
  | App (f, a) ->
      let vf = eval env f in
      let va = eval env a in
      (match vf with
       | VLam (_, body) -> body va (* Beta Reduction *)
       | VNe (h, args) -> VNe (h, args @ [va]) (* Stick the arg on the neutral pile *)
       | _ -> failwith "Runtime Error: Applied non-function")
  | Ann (t, _) -> eval env t

(* Quote: Convert a Value back to a Term (Normal Form) 
   We need the current 'level' to convert De Bruijn Levels back to Indices *)
let rec quote (lvl : int) (v : value) : term =
  match v with
  | VUniv k -> Univ k
  | VPi (x, a, b) -> 
      let arg = VNe (HVar lvl, []) in
      Pi (x, quote lvl a, quote (lvl + 1) (b arg))
  | VLam (x, body) -> 
      let arg = VNe (HVar lvl, []) in
      Lam (x, quote (lvl + 1) (body arg))
  | VNe (HVar i, args) -> 
      (* Convert absolute Level 'i' back to relative Index *)
      List.fold_left (fun acc arg -> App (acc, quote lvl arg)) (Var (lvl - i - 1)) args

(* Conversion Check: Are two values equal? 
   We quote them to normal forms and check for syntactic equality. *)
let is_convertible (lvl : int) (v1 : value) (v2 : value) : bool =
  let t1 = quote lvl v1 in
  let t2 = quote lvl v2 in
  t1 = t2

let rec infer (lvl : int) (ctx : context) (t : term) : value =
  match t with
  | Var i -> 
      let (_, type_v) = List.nth ctx i in 
      type_v
  | Univ k -> VUniv (k + 1) (* Type n : Type (n+1) *)
  | Ann (e, t) -> 
      check lvl ctx t (VUniv 0); (* Ensure the annotation is a type *)
      let t_val = eval (List.map snd ctx) t in
      check lvl ctx e t_val;
      t_val
  | Pi (x, a, b) ->
      check lvl ctx a (VUniv 0);
      let a_val = eval (List.map snd ctx) a in
      (* Extend context with x:A to check B *)
      let _ = infer (lvl + 1) ((x, a_val) :: ctx) b in 
      VUniv 0 
  | App (f, a) ->
      (match infer lvl ctx f with
       | VPi (_, a_type, b_closure) ->
           check lvl ctx a a_type;
           b_closure (eval (List.map snd ctx) a) (* Dependent result type! *)
       | _ -> failwith "Error: Function application to non-function")
  | Lam _ -> failwith "Error: Cannot infer type of Lambda (needs annotation)"

and check (lvl : int) (ctx : context) (t : term) (want : value) : unit =
  match t, want with
  | Lam (x, body), VPi (_, a_type, b_closure) ->
      (* To check \x.body against (x:A)->B 
         we check body against B (with x:A in context) *)
      let x_val = VNe (HVar lvl, []) in
      check (lvl + 1) ((x, a_type) :: ctx) body (b_closure x_val)
  | _, _ ->
      (* Fallback: Infer type and check equality *)
      let got = infer lvl ctx t in
      if is_convertible lvl got want then ()
      else failwith "Type Mismatch"