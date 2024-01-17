Require Import GLS_cut_elim.

Require Import Extraction.
Extraction Language Haskell.

Unset Extraction Optimize.

(* Time Separate *) Extraction GLS_cut_elimination.