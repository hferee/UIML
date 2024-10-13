open UIML.UIML_extraction
open Modal_expressions_parser
open Printer

let nb_args = Array.length Sys.argv
let usage_string = "isl_simp φ: Simplifies the formula φ in iSL.\n"

let () =
  if nb_args = 2 then
    Sys.argv.(1) |> eval |> isl_simp |> string_of_formula |> print_endline
  else print_string usage_string
