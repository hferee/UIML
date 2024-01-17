Require Import KS_cut_elim.

Require Import Extraction.
Extraction Language Haskell.

Unset Extraction Optimize.

(* Time Separate *) Extraction KS_cut_elimination.