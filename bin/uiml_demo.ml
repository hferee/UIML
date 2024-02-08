open UIML.UIML_extraction
open UIML.Datatypes
open UIML.Formulas
open Js_of_ocaml
open Modal_expressions_parser

let rec int_of_nat = function
| O -> 0
| S n -> 1 + int_of_nat n

let rec string_of_formula = function
| Var v -> "x" ^ string_of_int (int_of_nat v)
| Bot -> "⊥"
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

let _ = print_endline (string_of_formula (eval " (~x1 | □⊥ ) "))

(* export functions to js *)
let _ =
  Js.export "UIML"
    (object%js
       method islA s = string_of_formula (isl_A O (eval s))
       method islE s = string_of_formula (isl_E O (eval s))
       method k s = string_of_formula (k_UI O (eval s))
       method gl s = string_of_formula (gl_UI O (eval s))
       method parse s = string_of_formula (eval s)

     end)
