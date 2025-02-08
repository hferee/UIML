open UIML.Formulas
open Stringconversion
open UIML.Datatypes

let rec int_of_nat = function
| O -> 0
| S n -> 1 + int_of_nat n


let string_of_formula ?(classical = false) =
  let rec string_of_formula =
  function
| Var (_, v) -> camlstring_of_coqstring v
| Bot _ -> "⊥"
| Implies(_, Bot _, Bot _) -> "⊤"
(* diamond *)
| Implies(_, Box(Implies(_, f, Bot _)),Bot _) when classical -> "⋄ " ^ bracket f
(* double negation *)
| Implies(_, Implies(_, f, Bot _), Bot _) when classical -> string_of_formula f
| Box f -> "□ " ^ bracket f
| And (_, f, g) -> and_bracket f ^ " ∧ " ^ and_bracket g
| Or (_, f, g) -> or_bracket f ^ " ∨ " ^ or_bracket g
| Implies (_, f, Bot _) -> "¬ " ^ bracket f (* pretty print ¬ *)
| Implies (_, f, g) -> bracket f ^ " → " ^ bracket g
and bracket e = match e with
| Implies(_, Implies(_, f, Bot _), Bot _) when classical -> bracket f
| Implies(_, Box(Implies(_, f, Bot _)),Bot _) when classical -> "⋄ " ^ bracket f
| Var _ | Bot _| Implies(_, _, Bot _) | Box _ -> string_of_formula e
| e -> "(" ^ string_of_formula e ^ ")"
and or_bracket e = match e with
| Or (_, f, g) -> or_bracket f ^ " ∨ " ^ or_bracket g
| _ -> bracket e
and and_bracket e = match e with
| And (_, f, g) -> and_bracket f ^ " ∧ " ^ and_bracket g
| _ -> bracket e
  in string_of_formula
