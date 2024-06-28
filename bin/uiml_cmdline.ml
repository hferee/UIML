open Exenum
open Printer
open UIML.Formulas
open Sys
open Char
open UIML.UIML_extraction
open Stringconversion



(* n first variables *)
let rec n_vars n = if n <= 1 then [['p']] else [Char.chr ((Char.code 'p') + n)] :: n_vars (n - 1)

let e_vars = from_list ~name:"variables" (n_vars 4)

(* Type term is recursive, hence we need a lazy enumeration first. *)
let rec l_e_formulas = lazy
    begin
      let r_formulas = pay l_e_formulas in
      union
	[ single Bot ;
    map e_vars (fun x -> Var x) ;
	  map (pair r_formulas r_formulas) (fun (t1, t2) -> And (t1, t2)) ;
    map (pair r_formulas r_formulas) (fun (t1, t2) -> Or (t1, t2)) ;
    map (pair r_formulas r_formulas) (fun (t1, t2) -> Implies (t1, t2)) ;
    map r_formulas (fun x -> Box x);
	]
    end


(* Enumeration for formulas. *)
let e_formulas = Lazy.force l_e_formulas

(* The code below prints _num_ formulas and their existential interpolant *)

let nb_args = Array.length Sys.argv

let start = if nb_args < 2 then 0 else int_of_string Sys.argv.(1)
let num = if nb_args < 3 then 1 else int_of_string Sys.argv.(2)

let usage_string =
"Usage: propquant s n shows n example formulas φ(0), ... φ(n-1),
        and computes E x0 φ(i) and A x0 φ(i) for each 0 ≤ i < n.
        The formulas are chosen from an enumeration of all formulas in variables p, q, r, s, t.
        The argument s determines where to start in this enumeration.

        For example, try: propquant.exe 0 10, propquant.exe 5893 100.\n"

let v : variable = coqstring_of_camlstring "p"

let show_test (f: form) : string =
    ("φ        : " ^ string_of_formula f ^ "\n" ^
                 "Weight: " ^ string_of_int (int_of_nat (weight f)) ^ "\n") ^
    let t_start = Sys.time() in
    let e_result = isl_E v f in
    let run_time = Sys.time() -. t_start in
    ("Time: " ^ string_of_float run_time ^ "s\n") ^
    ("Eₚ(φ): " ^
                  string_of_formula e_result ^ "\n" ^
                 "Weight: " ^ string_of_int (int_of_nat (weight e_result)) ^ "\n") ^
    let a_result = isl_A v f in
    ("Aₚ(φ): " ^
                 string_of_formula a_result ^ "\n" ^
                "Weight: " ^ string_of_int (int_of_nat (weight a_result)) ^ "\n-------------------\n")

let () = 
  if nb_args < 2 then (print_string usage_string)
  else
    show e_formulas show_test start num;
