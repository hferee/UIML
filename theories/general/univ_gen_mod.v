Require Export List.
Export ListNotations.
Set Implicit Arguments.

From Coq Require Import ssreflect.

Require Import gen.
Require Import existsT.
Require Import genT.
Require Import gen_tacs.
Require Import gen_seq.
Require Import List_lemmasT.
Require Import FunctionalExtensionality.
Require Import Lia.

(* Effectively, univ_gen_mod allows to take a list and modify it by
    substituting elements (say x) in the initial list by other elements
    (say y) such that they are satisfying a specific relation (i.e. P x y).  *)

Inductive univ_gen_mod W (P : W -> W -> Type) : relationT (list W) :=
  | univ_gen_mod_nil : univ_gen_mod P [] []
  | univ_gen_mod_cons : forall x l lm, univ_gen_mod P l lm -> univ_gen_mod P (x :: l) (x :: lm)
  | univ_gen_mod_modif : forall x y l lm, P x y -> univ_gen_mod P l lm -> univ_gen_mod P (x :: l) (y :: lm)
  .

(* We can prove some general properties about univ_gen_mod. *)

(* univ_gen_mod is a reflexive relation. *)

Lemma univ_gen_mod_refl: forall A (l : list A) P, univ_gen_mod P l l.
Proof.
induction l.
- apply univ_gen_mod_nil.
- intro. apply univ_gen_mod_cons. apply IHl.
Qed.

(* The lemma univ_gen_mod_lem states that if a list x::Z is embedded in
   a list Y, then x must be appearing in Y, i.e. Y = Y1++x::Y2, and Y2 is
   is such that Z is embedded in Y2. Note that Y1 is here as it could well
   be that some elements were added via univ_gen_mod_modif before even
   treating x. *)

Lemma univ_gen_mod_lem: forall A (x : A) P Z Y,
  univ_gen_mod P (x :: Z) Y -> sigT (fun Y1 => sigT (fun y =>
  prod (P x y + (x = y)) (prod (Y = y :: Y1) (univ_gen_mod P Z Y1)))).
Proof.
intros A x P Z. induction Y.
intro. inversion X. intro. inversion X ; subst. exists Y. exists a. split ; auto.
exists Y. exists a ; repeat split ; auto.
Qed.

(* The next two lemmas deal with the interaction between univ_gen_mod
   and append. In essence, they say that if the embedded (resp. embedding)
   list is of the shape X1++X2, then the embedding list (resp. embedded)
   is of the shape W1++W2 where W1 embedds (resp. is embedded in) X1 and
   W2 embedds (resp. is embedded in) X1. *)

Lemma univ_gen_mod_splitL: forall A P (Z2 Z1 Y : list A),
  univ_gen_mod P (Z1 ++ Z2) Y -> sigT (fun Y1 => sigT (fun Y2 =>
    prod (Y = Y1 ++ Y2) (prod (univ_gen_mod P Z1 Y1) (univ_gen_mod P Z2 Y2)))).
Proof.
intros A P Z2. induction Z1 ; simpl.
- exists []. exists Y. simpl. split. trivial. split. apply univ_gen_mod_nil. trivial.
- intro. intro. apply univ_gen_mod_lem in X. destruct X. destruct s. repeat destruct p.
  destruct s ; subst.
  + apply IHZ1 in u. destruct u. destruct s. repeat destruct p0.
     exists (x0 :: x1). exists x2. repeat split ; auto. subst ; trivial.
     apply univ_gen_mod_modif ; auto.
  + apply IHZ1 in u. destruct u. destruct s. repeat destruct p ; subst.
     exists (x0 :: x1). exists x2. repeat split ; auto.
     apply univ_gen_mod_cons ; auto.
Qed.

Lemma univ_gen_mod_splitR: forall A P (Z2 Z1 Y : list A),
  univ_gen_mod P Y (Z1 ++ Z2) -> sigT (fun Y1 => sigT (fun Y2 =>
    prod (Y = Y1 ++ Y2) (prod (univ_gen_mod P Y1 Z1) (univ_gen_mod P Y2 Z2)))).
Proof.
intros V Z2. induction Z1 ; simpl.
- exists []. exists Y. simpl. split. trivial. split. apply univ_gen_mod_nil. trivial.
- intro. intro. inversion X ; subst. apply IHZ1 in X0. cD. subst.
  exists (a :: X0). exists X1. simpl. split. trivial.
  split. apply univ_gen_mod_cons.  assumption. assumption.
  apply IHZ1 in X1. cD. subst.
  exists (x :: X1). exists X2. split. trivial. split. apply univ_gen_mod_modif ; auto.
  assumption.
Qed.

(* univ_gen_mod_combine claims that if Y1 is embedded in Z1 and Y2 is embedded
   in Z2, then we can combine the embedded lists in the shape of Y1++Y2 and combine
   the embedding lists in Z1++Z2 to preserve the relation of embedding between the
   newly created lists.*)

Lemma univ_gen_mod_combine: forall A P (Z2 Z1 Y2 Y1 : list A),
    univ_gen_mod P Y1 Z1 -> univ_gen_mod P Y2 Z2 -> univ_gen_mod P (Y1 ++ Y2) (Z1 ++ Z2).
Proof.
intros A P Z2 Z1 Y2 Y1 gen1 gen2. induction gen1.
- repeat rewrite app_nil_l. assumption.
- simpl. apply univ_gen_mod_cons. assumption.
- simpl. apply univ_gen_mod_modif. assumption. assumption.
Qed.

(* The next lemma states that if a::Y is embedded in a::Z, then we know
   for sure that Y is embedded in Z. Note that this is not direct as the
   a in the embedding list could have been added via univ_gen_mod_modif.
   Effectively, this lemma allows one to remove the identical heads of two
   lists univ_gen_mod and preserve that relation. *)

Lemma univ_gen_mod_same_hd: forall A P (Y Z : list A) (a : A),
    univ_gen_mod P (a :: Y) (a :: Z) -> univ_gen_mod P Y Z.
Proof.
intros A P Y Z a gen. inversion gen ; auto.
Qed.

(* The lemma univ_gen_mod_elem_deep considers a list l1 embedded in a
   list l2 in which an element a appears deeply. Essentially, the lemma
   makes a case distinction about a: either it has been added by univ_gen_mod_modif
   (this is the first case of the sum) or it was added by univ_gen_mod_cons
   in which case it has to appear somewhere in l1. *)

Lemma univ_gen_mod_elem_deep {A : Type} : forall P (l1 l2 l3 l4: list A) a,
          univ_gen_mod P l1 l2 ->
          (l2 = l3 ++ a :: l4) ->
            sigT (fun l5 => sigT (fun l6 => sigT (fun b =>
              (prod (l1 = l5 ++ b :: l6) (prod (P b a + (a = b)) (prod (univ_gen_mod P l5 l3) (univ_gen_mod P l6 l4))))))).
Proof.
intros. subst. rewrite cons_single in X. apply univ_gen_mod_splitR in X.
destruct X. destruct s. repeat destruct p. subst.
apply univ_gen_mod_splitR in u0. destruct u0. destruct s. repeat destruct p.
subst. inversion u0 ; subst.
- inversion X ; subst. exists x. exists x2. exists a. repeat split ; auto.
- inversion X0. subst. exists x. exists x2. exists x0. repeat split ; auto.
Qed.

Lemma univ_gen_mod_In {A : Type} : forall (l0 l1 : list A) a P, univ_gen_mod P l0 l1 ->
                                        InT a l0 -> (InT a l1 + (existsT2 b, InT b l1 * P a b)).
Proof.
intros. induction X ; subst.
- inversion X0.
- inversion X0 ; subst. left ; apply InT_eq. apply IHX in X1. destruct X1.
  left ; apply InT_cons ; auto. destruct s ; destruct p. right ; exists x0 ; split ; auto.
  apply InT_cons ; auto.
- inversion X0 ; subst. right. exists y ; split ; auto. apply InT_eq. apply IHX in X1. destruct X1.
  left ; apply InT_cons ; auto. destruct s ; destruct p0. right ; exists x0 ; split ; auto.
  apply InT_cons ; auto.
Qed.

Lemma univ_gen_mod_smaller_length : forall {A: Type} (l1 l2 : list A) P,
                      univ_gen_mod P l1 l2 -> length l1 = length l2.
Proof.
intros. induction X.
- auto.
- simpl. lia.
- simpl. lia.
Qed.

Lemma InT_univ_gen_mod : forall {A : Type} (l1 l2 : list A) (P : A -> A -> Type) (a : A),
          (InT a l2) -> (univ_gen_mod P l1 l2) -> ((existsT2 b, InT b l1 * P b a) + (InT a l1)).
Proof.
intros. induction X0 ; subst ; simpl.
- inversion X.
- inversion X ; subst. right. apply InT_eq. apply IHX0 in X1. destruct X1. destruct s ; destruct p.
  left. exists x0. split ; auto. apply InT_cons. assumption. right ; apply InT_cons ; auto.
- inversion X ; subst. left. exists x ; split ; auto. apply InT_eq. apply IHX0 in X1. destruct X1.
  destruct s ; destruct p0. left ; exists x0 ; split ; auto. apply InT_cons ; auto. right ; apply InT_cons ; auto.
Qed.





