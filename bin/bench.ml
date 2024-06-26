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

type 'a timed_result = { value : 'a; time : float }

type bench_info = {
  name : string;
  before : int timed_result;
  after : int timed_result;
}

let percentage_reduction before after = 100. -. (after /. before *. 100.)
let percentage_increase before after = (after /. before *. 100.) -. 100.

let time f x =
  let attempts = 20 in
  let total, value, _ =
    List.init attempts (fun _ -> ())
    (* Run the tests `attempts` times *)
    |> List.map (fun _ ->
           let t = Sys.time () in
           let fx = f x in
           { value = fx; time = Sys.time () -. t })
    (* Sort them by execution time *)
    |> List.sort (fun result1 result2 -> compare result1.time result2.time)
    (* Compute the average time removing the slowest and fastest times *)
    |> List.fold_left
         (fun (total, _, len) { value; time } ->
           if len >= 1 && len < attempts - 1 then (total +. time, value, len + 1)
           else (total, value, len + 1))
         (0., 0, 0)
  in
  { value; time = total /. float_of_int (attempts - 2) }

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
      before = time (fun f -> weight (isl_A [ 'p' ] f)) f;
      after = time (fun f -> weight (isl_simplified_A [ 'p' ] f)) f;
    };
    {
      name = "E " ^ fs;
      before = time (fun f -> weight (isl_E [ 'p' ] f)) f;
      after = time (fun f -> weight (isl_simplified_E [ 'p' ] f)) f;
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
    "t ∨ q ∨ t";
    "(q -> p) & (p -> ~r)";
    "(q -> (p -> r)) -> r";
    "((q -> p) -> r) -> r";
    "(a → (q ∧ r)) → s";
    "(a → (q ∧ r)) → ~p";
    "(a → (q ∧ r)) → ~p → k";
    "(q → (q ∧ (k -> p)) -> k)";
  ]

let _ = bench test_cases
