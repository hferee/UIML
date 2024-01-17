

(* Reflexive_Transitive_Closure stuff, using Type rather than Prop *)

Set Implicit Arguments.
Require Import List.
Import ListNotations.

Require Import gen genT.

(* compare 
  https://coq.inria.fr/stdlib/Coq.Relations.Relation_Definitions.html
  https://coq.inria.fr/stdlib/Coq.Relations.Relation_Operators.html
  https://coq.inria.fr/stdlib/Coq.Relations.Operators_Properties.html
  Require Import Coq.Relations.Relation_Definitions.
  Require Import Coq.Relations.Relation_Operators.
  Require Import Coq.Relations.Operators_Properties.  
  *)
(* this in genT.v in ../lnt/tense-logic-in-Coq 
Definition relationT (A : Type) := A -> A -> Type.
*)

Definition transitiveT W (R : relationT W) :=
  forall (x y z : W), R x y -> R y z -> R x z.
Check transitiveT.

(* see https://coq.inria.fr/stdlib/Coq.Relations.Relation_Operators.html *)
Section Reflexive_ClosureT.
  Variable A : Type.
  Variable R : relationT A.

Inductive clos_reflT (x: A) : A -> Type :=
  | rT_step (y:A) : R x y -> clos_reflT x y
  | rT_refl : clos_reflT x x.

End Reflexive_ClosureT.

Section Reflexive_Transitive_ClosureT.
  Variable A : Type.
  Variable R : relationT A.

Inductive clos_refl_transT (x:A) : A -> Type :=
  | rtT_step (y:A) : R x y -> clos_refl_transT x y
  | rtT_refl : clos_refl_transT x x
  | rtT_trans (y z:A) :
	clos_refl_transT x y -> clos_refl_transT y z -> clos_refl_transT x z.

(* Alternative definition by transitive extension on the left/right *)

Inductive clos_refl_transT_1n (x: A) : A -> Type :=
  | rt1nT_refl : clos_refl_transT_1n x x
  | rt1nT_trans (y z:A) :
       R x y -> clos_refl_transT_1n y z -> clos_refl_transT_1n x z.

Inductive clos_refl_transT_n1 (x: A) : A -> Type :=
  | rtn1T_refl : clos_refl_transT_n1 x x
  | rtn1T_trans (y z:A) :
      R y z -> clos_refl_transT_n1 x y -> clos_refl_transT_n1 x z.

End Reflexive_Transitive_ClosureT.

(* equivalences between above, need to reprove for ...T *)
Lemma clos_rt1n_rtT : forall A R (x y : A),
  clos_refl_transT_1n R x y -> clos_refl_transT R x y.
Proof. intros. induction X. apply rtT_refl.
eapply rtT_trans. apply rtT_step. eassumption. eassumption. Qed.

Lemma clos_rt_rt1nT : forall A R (x y : A),
  clos_refl_transT R x y -> clos_refl_transT_1n R x y.
Proof. intros. induction X. 
eapply rt1nT_trans. eassumption. apply rt1nT_refl.
apply rt1nT_refl. 
clear X1 X2.  induction IHX1. assumption.
apply IHIHX1 in IHX2. eapply rt1nT_trans ; eassumption. Qed.

Lemma clos_rtn1_rtT : forall A R (x y : A),
  clos_refl_transT_n1 R x y -> clos_refl_transT R x y.
Proof. intros. induction X.  apply rtT_refl.
eapply rtT_trans. eassumption. apply rtT_step. eassumption.  Qed.

Lemma clos_rt_rtn1T : forall A R (x y : A),
  clos_refl_transT R x y -> clos_refl_transT_n1 R x y.
Proof. intros. induction X. 
eapply rtn1T_trans. eassumption. apply rtn1T_refl.
apply rtn1T_refl. 
clear X1 X2.  induction IHX2. assumption.
eapply rtn1T_trans ; eassumption. Qed.

(*
Lemma clos_rt_rt1n_iffT : forall A R (x y : A),
  clos_refl_transT R x y <-> clos_refl_transT_1n R x y.

Lemma clos_rt_rtn1_iffT : forall A R (x y : A),
  clos_refl_transT R x y <-> clos_refl_transT_n1 R x y.
*)

