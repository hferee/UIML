open UIML.UIML_extraction
open UIML.Datatypes
open UIML.Formulas
open Js_of_ocaml

(* for random testing. *)

(* temporary, until we use strings *)
let rec int_of_nat = function
| O -> 0
| S n -> 1 + int_of_nat n

let rec nat_of_int (n: int) =
    if n <= 0 then O
    else S (nat_of_int (n-1))

let rec string_of_formula = function
| Var v -> "x" ^ string_of_int (int_of_nat v)
| Bot -> "⊥"
| Box f -> "□" ^ bracket f
| And (f, g) -> bracket f ^ " ∧ " ^ bracket g
| Or (f, g) -> bracket f ^ " ∨ " ^ bracket g
| Implies (f, g) -> bracket f ^ " → " ^ bracket g
and bracket e = match e with
| Var _ | Bot -> string_of_formula e
| e -> "(" ^ string_of_formula e ^ ")"
(* disable optims for now
| Implies (Bot, _) -> "⊤"                             (* ⊥ -> φ ≡ ⊤ *)
| Implies (Implies(Bot, _), f) -> string_of_formula f (* ⊤ -> φ ≡ φ *)
| Implies (f, Bot) -> "¬" ^ bracket f       (* φ -> ⊥ ≡ ¬ φ *)
| Implies (_, Implies(Bot, _)) -> "⊤"                 (* φ -> ⊤ ≡ ⊤ *)
| Implies (f, g) -> if f = g then "⊤" else            (* φ -> φ ≡ ⊤ *)
                    bracket f ^ " → " ^ bracket g
                    *)
let var (n: int) = Var (nat_of_int n)
let rec test_formula (n: int) =
    if n = 0 then var 0 else
    Implies (test_formula(n-1), var(n))
(* let test_formula (n: int) =
  if n = 1 then Implies(Implies(var 1, var 0), var 0) else Bot *)

(* export functions to js *)
let _ =
  Js.export "UIML"
    (object%js
       method islA n = string_of_formula (isl_A O (test_formula n))
       method islE n = string_of_formula (isl_E O (test_formula n))
       method k n = string_of_formula (gl_UI O (test_formula n))
       method gl n = string_of_formula (k_UI O (test_formula n))
     end)
