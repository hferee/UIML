open UIML.UIML_extraction
open UIML.Formulas
open Modal_expressions_parser
open Printer

type 'a timed_result = { value : 'a; time : float }

type bench_info = {
  name : string;
  before : int timed_result;
  after : int timed_result;
}

let rec form_size = function
  | Var _ -> 1
  | Bot -> 1
  | Or (f1, f2) -> 1 + form_size f1 + form_size f2
  | And (f1, f2) -> 1 + form_size f1 + form_size f2
  | Implies (f1, f2) -> 1 + form_size f1 + form_size f2
  | Box f -> 1 + form_size f

let percentage_reduction before after = 100. -. (after /. before *. 100.)

let time f x =
  let t = Sys.time () in
  let fx = f x in
  { value = fx; time = Sys.time () -. t }

let print_value_results { name; before; after } =
  Printf.printf "| %s | %d | %d | %.2f | %.4f |\n" name before.value after.value
    (percentage_reduction
       (float_of_int before.value)
       (float_of_int after.value))
    before.time

let bench_one fs =
  let f = eval fs in
  let resA = time (isl_A [ 'p' ]) f in
  let simpA = time isl_simp resA.value in
  let resE = time (isl_E [ 'p' ]) f in
  let simpE = time isl_simp resE.value in
  [
    {
      name = "A " ^ fs;
      before = { value = form_size resA.value; time = resA.time };
      after = { value = form_size simpA.value; time = simpA.time };
    };
    {
      name = "E " ^ fs;
      before = { value = form_size resE.value; time = resE.time };
      after = { value = form_size simpE.value; time = simpE.time };
    };
  ]

let print_bench_value_info benches =
  Printf.printf
    "| Formula | Interpolant weight | Simplified interpolant weight | \
     Percentage reduction |Interpolant computation time (s)|\n\
     |--|--|--|--|--|\n";
  List.iter print_value_results benches;
  print_newline ();

  let sum_before =
    List.fold_left (fun acc x -> acc + x.before.value) 0 benches
  in
  let sum_after = List.fold_left (fun acc x -> acc + x.after.value) 0 benches in

  Printf.printf "Average percentage reduction: %.2f\n"
    (percentage_reduction (float_of_int sum_before) (float_of_int sum_after))

let bench l =
  let benches = List.map bench_one l |> List.flatten in
  print_bench_value_info benches;
  print_newline ()

let test_cases =
  [
    "(p ∧ q) -> ~p";
    "t ∨ q ∨ t";
    "~((F & p) -> ~p ∨ F)";
    "(q -> p) & (p -> ~r)";
    "(q -> (p -> r)) -> r";
    "((q -> p) -> r) -> r";
    "(a → (q ∧ r)) → s";
    "(a → (q ∧ r)) → ~p";
    "(a → (q ∧ r)) → ~p → k";
    "(q -> (p -> r)) -> ~t";
    "(q -> (p -> r)) -> ~t";
    "(q → (q ∧ (k -> p)) -> k)";
    "(q -> (p ∨  r)) -> ~(t ∨ p)";
    "((q -> (p ∨  r)) ∧ (t -> p)) -> t";
    "((~t -> (q  ∧ p)) ∧ (t -> p)) -> t";
    "(~p ∧ q) -> (p ∨ r -> t) -> o";
    "((s ∨ r) ∨ (⊥ ∨ r)) ∧ ((⊥ ∨ p) ∨ (t → s))";
    "((t ∧ r) ∨ (t ∧ s)) ∧ ((r ∧ p) ∧ (p → t))";
    "((t ∧ t) ∨ (t → s)) ∧ (~s ∧ (⊥ → r))";
    "(t ∨ r) → (t ∧ s)";
  ]

let _ = bench test_cases
