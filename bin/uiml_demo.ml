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
| Failure s -> "Error: " ^ s
| e -> "Error: " ^ Printexc.to_string e

let fail_on_modality (f : form) : form =
  let rec aux = function
  | Box _ -> failwith "The provided formula contains modalities"
  | Or(x, y) | Implies(x, y) | And(x, y) -> aux x ; aux y
  | _ -> ()
  in (aux f; f)

(* export functions to js *)

let v : variable = coqstring_of_camlstring "p"
let _ =
  Js.export "UIML"
    (object%js
(* TODO: iE and iA are just an alias for isl_E and isl_A,
there should really at least be a function that checks that
iE and iA are given box-free formulas as input.*)
       method iA s =  catch_e (fun () -> s |> eval |> fail_on_modality |> isl_A v |> string_of_formula)
       method iE s =  catch_e (fun () -> s |> eval |> fail_on_modality |> isl_E v |> string_of_formula)
       method islA s = catch_e (fun () -> s |> eval |> isl_simplified_A v |> string_of_formula)
       method islE s = catch_e (fun () -> s |> eval |> isl_simplified_E v |> string_of_formula)
       method k s = catch_e (fun () -> s |> eval |> isl_E v |> string_of_formula ~classical: true)
       method gl s = catch_e (fun () -> s |> eval |> isl_E v |> string_of_formula ~classical: true)
       method parse s = catch_e (fun () -> s |> eval |> string_of_formula)
     end);;

