open UIML.UIML_extraction
open UIML.Datatypes
open UIML.Formulas
open Js_of_ocaml
open Modal_expressions_parser
open Stringconversion

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
| And (f, g) -> bracket f ^ " ∧ " ^ bracket g
| Or (f, g) -> bracket f ^ " ∨ " ^ bracket g
| Implies (f, Bot) -> "¬ " ^ bracket f (* pretty print ¬ *)
| Implies (f, g) -> bracket f ^ " → " ^ bracket g
and bracket e = match e with
| Implies(Implies(f, Bot), Bot) when classical -> bracket f
| Implies(Box(Implies(f, Bot)),Bot) when classical -> "⋄ " ^ bracket f
| Var _ | Bot | Implies(_, Bot) | Box _ -> string_of_formula e
| e -> "(" ^ string_of_formula e ^ ")"
  in string_of_formula

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
       method k s = catch_e (fun () -> string_of_formula ~classical: true (k_UI v (eval s)))
       method gl s = catch_e (fun () -> string_of_formula ~classical: true (gl_UI v (eval s)))
       method parse s = catch_e (fun () -> string_of_formula (eval s))
     end);;

