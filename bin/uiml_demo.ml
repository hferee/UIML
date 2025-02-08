open UIML.UIML_extraction
open UIML.Formulas
open Js_of_ocaml
open Modal_expressions_parser
open Stringconversion
open Printer

let catch_e f = try f() with
  ParseError -> "Parse Error"
| Failure s -> "Error: " ^ s
| e -> "Error: " ^ Printexc.to_string e


let fail_on_modality (f : form) : form =
  let rec aux = function
  | Box _ -> failwith "The provided formula contains modalities"
  | Or(_, x, y) | Implies(_, x, y) | And(_,x, y) -> aux x ; aux y
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
       method iA s =  catch_e (fun () -> s |> eval |> fail_on_modality |> isl_simplified_A v |> string_of_formula)
       method iE s =  catch_e (fun () -> s |> eval |> fail_on_modality |> isl_simplified_E v |> string_of_formula)
       method islA s = catch_e (fun () -> s |> eval |> isl_simplified_A v |> string_of_formula)
       method islE s = catch_e (fun () -> s |> eval |> isl_simplified_E v |> string_of_formula)
       method k s = catch_e (fun () -> s |> eval |> gl_UI v |> string_of_formula ~classical: true)
       method gl s = catch_e (fun () -> s |> eval |> k_UI v |> string_of_formula ~classical: true)
       method parse s = catch_e (fun () -> s |> eval |> string_of_formula)
     end);;

