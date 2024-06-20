open UIML.UIML_extraction
open UIML.Formulas
open Modal_expressions_parser

let rec weight = function
  | Bot -> 1
  | Var _ -> 1
  | And (f1, f2) -> 2 + weight f1 + weight f2
  | Or (f1, f2) -> 3 + weight f1 + weight f2
  | Implies (f1, f2) -> 1 + weight f1 + weight f2
  | Box f -> 1 + weight f

type bench_info = { name : string; before : int; after : int }

let percentage_reduction before after =
  100. -. (float_of_int after /. float_of_int before *. 100.)

let print_results { name; before; after } =
  Printf.printf "| %s | %d | %d | %.2f |\n" name before after
    (percentage_reduction before after)

let bench_one fs =
  let f = eval fs in
  [
    {
      name = "A " ^ fs;
      before = weight (isl_A [ 'p' ] f);
      after = weight (isl_simplified_A [ 'p' ] f);
    };
    {
      name = "E " ^ fs;
      before = weight (isl_E [ 'p' ] f);
      after = weight (isl_simplified_E [ 'p' ] f);
    };
  ]

let bench l =
  let benches = List.map bench_one l |> List.flatten in
  Printf.printf
    "| Formula | Before | After | Percentage reduction |\n|--|--|--|--|\n";
  List.iter print_results benches;
  print_newline ();
  let total, len =
    List.fold_left
      (fun (total, len) { before; after; _ } ->
        (percentage_reduction before after +. total, len + 1))
      (0., 0) benches
  in
  Printf.printf "Average percentage reduction: %.2f\n"
    (total /. float_of_int len)

let test_cases =
  [
    "(q -> p) & (p -> ~r)";
    "(q -> (p -> r)) -> r";
    "((q -> p) -> r) -> r";
    "(a → (q ∧ r)) → s";
    "(a → (q ∧ r)) → ~p";
    "(a → (q ∧ r)) → ~p → k";
    "(q → (q ∧ (k -> p)) -> k)";
  ]

let _ = bench test_cases
