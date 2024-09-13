open Exenum
open Printer
open UIML.Formulas
open Sys
open Char
open UIML.DecisionProcedure
open UIML.Datatypes
open Stringconversion
open Modal_expressions_parser



let nb_args = Array.length Sys.argv

let form = if nb_args = 2 then (Sys.argv.(1)) else "T"

let usage_string =
  "isl_dec φ: decides the provability of the modal formula φ in iSL.\n"

let print_decision = function
  | Coq_inl _ -> "Provable"
  | _ -> "Not provable"

let () =
  if nb_args = 2 then form |> eval |> coq_Provable_dec [] |>
     print_decision |> print_string |> print_newline
  else print_string usage_string
