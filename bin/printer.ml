open UIML.Formulas
open Stringconversion
open UIML.Datatypes

let rec int_of_nat = function
| O -> 0
| S n -> 1 + int_of_nat n


let string_of_formula ?(classical = false) =
  let rec string_of_formula =
  function
| Var v -> camlstring_of_coqstring v
| Bot -> "⊥"
| Implies(Bot, Bot) -> "⊤"
(* diamond *)
| Implies(Box(Implies(f, Bot)),Bot) when classical -> "⋄ " ^ bracket f
(* double negation *)
| Implies(Implies(f, Bot), Bot) when classical -> string_of_formula f
| Box f -> "□ " ^ bracket f
| And (f, g) -> and_bracket f ^ " ∧ " ^ and_bracket g
| Or (f, g) -> or_bracket f ^ " ∨ " ^ or_bracket g
| Implies (f, Bot) -> "¬ " ^ bracket f (* pretty print ¬ *)
| Implies (f, g) -> bracket f ^ " → " ^ bracket g
and bracket e = match e with
| Implies(Implies(f, Bot), Bot) when classical -> bracket f
| Implies(Box(Implies(f, Bot)),Bot) when classical -> "⋄ " ^ bracket f
| Var _ | Bot | Implies(_, Bot) | Box _ -> string_of_formula e
| e -> "(" ^ string_of_formula e ^ ")"
and or_bracket e = match e with
| Or (f, g) -> or_bracket f ^ " ∨ " ^ or_bracket g
| _ -> bracket e
and and_bracket e = match e with
| And (f, g) -> and_bracket f ^ " ∧ " ^ and_bracket g
| _ -> bracket e
  in string_of_formula
