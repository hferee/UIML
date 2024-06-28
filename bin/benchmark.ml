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

let percentage_reduction before after = 100. -. (after /. before *. 100.)
let percentage_increase before after = (after /. before *. 100.) -. 100.

let time f x =
  let t = Sys.time () in
  let fx = f x in
  { value = fx; time = Sys.time () -. t }

let print_value_results { name; before; after } =
  Printf.printf "| %s | %d | %d | %.2f |\n" name before.value after.value
    (percentage_reduction
       (float_of_int before.value)
       (float_of_int after.value))

let print_time_results { name; before; after } =
  Printf.printf "| %s | %.4f | %.4f | %.2f |\n" name before.time after.time
    (percentage_increase before.time after.time)

let bench_one fs =
  let f = eval fs in
  [
    {
      name = "A " ^ fs;
      before = time (fun f -> int_of_nat (weight (isl_A [ 'p' ] f))) f;
      after = time (fun f -> int_of_nat (weight (isl_simplified_A [ 'p' ] f))) f;
    };
    {
      name = "E " ^ fs;
      before = time (fun f -> int_of_nat (weight (isl_E [ 'p' ] f))) f;
      after = time (fun f -> int_of_nat (weight (isl_simplified_E [ 'p' ] f))) f;
    };
  ]

let average f l =
  let total, len =
    List.fold_left (fun (total, len) e -> (f e +. total, len + 1)) (0., 0) l
  in
  total /. float_of_int len

let print_bench_value_info benches =
  Printf.printf
    "| Formula | Interpolant weight | Simplified interpolant weight | \
     Percentage reduction |\n\
     |--|--|--|--|\n";
  List.iter print_value_results benches;
  print_newline ();
  Printf.printf "Average percentage reduction: %.2f\n"
    (average
       (fun { before; after; _ } ->
         percentage_reduction
           (float_of_int before.value)
           (float_of_int after.value))
       benches)

let print_bench_time_info benches =
  Printf.printf
    "| Formula | Interpolant computation time (s) | Simplified interpolant \
     computation time (s) | Percentage increase |\n\
     |--|--|--|--|\n";
  List.iter print_time_results benches;
  print_newline ();
  Printf.printf "Average percentage increase: %.2f\n"
    (average
       (fun { before; after; _ } -> percentage_increase before.time after.time)
       benches);
  Printf.printf "Average absolute time increase (s): %.5f\n"
    (average (fun { before; after; _ } -> after.time -. before.time) benches)

let bench l =
  let benches = List.map bench_one l |> List.flatten in
  print_bench_value_info benches;
  print_newline ();
  print_bench_time_info benches

let test_cases =
  [
    "(p ∧ q) -> ~p";
    "t ∨ q ∨ t";
    "~((F & p) -> ~p | F)";
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
