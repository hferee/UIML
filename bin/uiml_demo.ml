open UIML.UIML_extraction
open UIML.Datatypes
open UIML.Formulas
open Js_of_ocaml
open Modal_expressions_parser
open Stringconversion

let rec string_of_formula ?(classical = false) = function
| Var v -> camlstring_of_coqstring v
| Bot -> "⊥"
| Implies(Bot, Bot) -> "⊤"
| Implies(Box(Implies(f, Bot)),Bot) when classical -> "⋄ " ^ bracket f
| Implies(Implies(f, Bot), Bot) when classical -> string_of_formula f
| Box f -> "□ " ^ bracket f
| And (f, g) -> bracket f ^ " ∧ " ^ bracket g
| Or (f, g) -> bracket f ^ " ∨ " ^ bracket g
| Implies (f, Bot) -> "¬ " ^ bracket f (* pretty print ¬ *)
| Implies (f, g) -> bracket f ^ " → " ^ bracket g
and bracket e = match e with
| Var _ | Bot | Implies(_, Bot) -> string_of_formula e
| e -> "(" ^ string_of_formula e ^ ")"
(* disable optims for now
| Implies (Bot, _) -> "⊤"                             (* ⊥ -> φ ≡ ⊤ *)
| Implies (Implies(Bot, _), f) -> string_of_formula f (* ⊤ -> φ ≡ φ *)
| Implies (f, Bot) -> "¬" ^ bracket f       (* φ -> ⊥ ≡ ¬ φ *)
| Implies (_, Implies(Bot, _)) -> "⊤"                 (* φ -> ⊤ ≡ ⊤ *)
| Implies (f, g) -> if f = g then "⊤" else            (* φ -> φ ≡ ⊤ *)
                    bracket f ^ " → " ^ bracket g
                    *)
(*
                    let var (n: int) = Var (nat_of_int n)
let rec test_formula (n: int) =
    if n = 0 then var 0 else
    Implies (test_formula(n-1), var(n))
(* let test_formula (n: int) =
  if n = 1 then Implies(Implies(var 1, var 0), var 0) else Bot *)
*)


(* let example1 = "x0 | (x1 & x2)" *)
(* let example2 = "x2 -> (x2 -> #)" *)

(* let _ = print_endline (string_of_formula (simplify true (gl_UI O (eval example1))))
let _ = print_endline (string_of_formula (simplify true (eval example2))) *)

(*
let _ = print_endline(string_of_formula (eval "□□□¬□#"))
*)

let catch_e f = try f() with 
  ParseError -> "Parse Error"
| e -> "Error: " ^ Printexc.to_string e

(* export functions to js *)

let v : variable = coqstring_of_camlstring "p"
let _ =
  Js.export "UIML"
    (object%js
       method islA s = catch_e (fun () -> string_of_formula (isl_A v (eval s)))
       method islE s = catch_e (fun () -> string_of_formula (isl_E v (eval s)))
       method k s = catch_e (fun () -> string_of_formula ~classical:true (k_UI v (eval s)))
       method gl s = catch_e (fun () -> string_of_formula ~classical:true (gl_UI v (eval s)))
       method parse s = catch_e (fun () -> string_of_formula (eval s))
     end);;

