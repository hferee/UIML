Require Export List.
Export ListNotations.
Set Implicit Arguments.

From Coq Require Import ssreflect.

Require Import gen.
Require Import genT.
Require Import gen_tacs.
Require Import gen_seq.
Require Import List_lemmasT.
Require Import FunctionalExtensionality.
Require Import Lia.

(* The following definition is a generalization of the gen_ext property.
   As gen_ext, univ_gen_ext gives a precise definition of embedding between
   lists: l1 is embedded in l2 if all the elements in l1 appear in l2 in the
   same order as in l1. Some elements might be added in l2, under the condition
   that these elements satisfy a certain given property P.

   Effectively, univ_gen_ext allows to restrict the weakening of gen_ext_extra to
   elements of a type A satisfying some property P. *)

Inductive univ_gen_ext W (P : W -> Type) : relationT (list W) :=
  | univ_gen_ext_nil : univ_gen_ext P [] []
  | univ_gen_ext_cons : forall x l le, univ_gen_ext P l le -> univ_gen_ext P (x :: l) (x :: le)
  | univ_gen_ext_extra : forall x l le, P x -> univ_gen_ext P l le -> univ_gen_ext P l (x :: le)
  .

(* We can prove some general properties about univ_gen_ext. *)

(* univ_gen_ext is a reflexive relation. *)

Lemma univ_gen_ext_refl: forall A (l : list A) P, univ_gen_ext P l l.
Proof.
induction l.
- apply univ_gen_ext_nil.
- intro. apply univ_gen_ext_cons. apply IHl.
Qed.

(* It is also transitive. *)

Lemma univ_gen_ext_trans: forall A P (ys zs : list A),
  univ_gen_ext P ys zs -> 
  forall xs, univ_gen_ext P xs ys -> univ_gen_ext P xs zs.
Proof. intros until 1. induction X. tauto.
intros. inversion X0. subst. apply univ_gen_ext_cons. firstorder.
subst. apply univ_gen_ext_extra. firstorder. apply IHX. assumption.
intros. firstorder. firstorder. apply univ_gen_ext_extra. firstorder. apply IHX.
assumption.
Qed.

(* The empty list can be embedded in any other list xs as long as the
   elements of that list are all satisfying P. *)

Lemma all_P_univ_gen_ext_nil: forall A P (xs : list A),
              (forall x, InT x xs -> P x) -> (univ_gen_ext P [] xs).
Proof.
induction xs.
- intros. apply univ_gen_ext_nil.
- intros. apply univ_gen_ext_extra. apply X. apply InT_eq'. reflexivity.
  apply IHxs. intros. apply X. apply InT_cons. assumption.
Qed.

(* Reciprocally, if the empty list is embedded in another list then
   we know that all the elements of that list are satisfying P. *)

Lemma univ_gen_ext_nil_all_P: forall A P (xs : list A),
              (univ_gen_ext P [] xs) -> (forall x, InT x xs -> P x).
Proof.
induction xs.
- intros. inversion X0.
- intros. remember (a :: xs) as l0. remember [] as l1. destruct X.
  * inversion X0.
  * inversion Heql1.
  * inversion Heql0. subst. pose (IHxs X). inversion X0.
    + subst. assumption.
    + apply p0. assumption.
Qed.

(* The next lemmas state that if a list xs is embedded in a list
   ys, then xs is also embedded in the list ys appended (on the
   right or left of it) with a list zs of which all elements are
   satsfying the property P. *)

Lemma univ_gen_ext_appL: forall A P (xs ys zs : list A),
  univ_gen_ext P xs ys -> 
  (forall z, InT z zs -> P z) ->
  univ_gen_ext P xs (zs ++ ys).
Proof.
induction zs. tauto.
intros. simpl. apply univ_gen_ext_extra. apply X0. apply InT_eq.
apply IHzs. assumption. intros. apply X0. apply InT_cons. assumption.
Qed.

Lemma univ_gen_ext_appR: forall A P (xs ys zs : list A),
  univ_gen_ext P xs ys ->
  (forall z, InT z zs -> P z) ->
  univ_gen_ext P xs (ys ++ zs).
Proof.
intros. induction X.
- induction zs.
  * apply univ_gen_ext_nil.
  * apply univ_gen_ext_extra. apply X0. apply InT_eq. apply IHzs.
    intros. apply X0. apply InT_cons. assumption.
- simpl. apply univ_gen_ext_cons. assumption.
- simpl. apply univ_gen_ext_extra. assumption. assumption.
Qed.

(* The lemma univ_gen_ext_lem states that if a list x::Z is embedded in
   a list Y, then x must be appearing in Y, i.e. Y = Y1++x::Y2, and Y2 is
   is such that Z is embedded in Y2. Note that Y1 is here as it could well
   be that some elements were added via univ_gen_ext_extra before even
   treating x. *)

Lemma univ_gen_ext_lem: forall A (x : A) P Z Y,
  univ_gen_ext P (x :: Z) Y -> sigT (fun Y1 => sigT (fun Y2 =>
    prod (Y = Y1 ++ x :: Y2) (prod (univ_gen_ext P Z Y2)
      (forall y, InT y Y1 -> P y)))).
Proof.
intros A x P Z. induction Y.
intro. inversion X. intro. inversion X ; subst.
exists []. exists Y. simpl. split. tauto. split. tauto. intros.
inversion X1.
apply IHY in X1. cD. subst.
exists (a :: X1). exists X2. simpl. split.
auto. split. assumption. intros. remember (a :: X1) as l. destruct X3.
- subst. inversion Heql. assumption.
- apply X5. inversion Heql. subst. assumption.
Qed.

(* The next two lemmas deal with the interaction between univ_gen_ext
   and append. In essence, they say that if the embedded (resp. embedding)
   list is of the shape X1++X2, then the embedding list (resp. embedded)
   is of the shape W1++W2 where W1 embedds (resp. is embedded in) X1 and
   W2 embedds (resp. is embedded in) X1. *)

Lemma univ_gen_ext_splitL: forall A P (Z2 Z1 Y : list A),
  univ_gen_ext P (Z1 ++ Z2) Y -> sigT (fun Y1 => sigT (fun Y2 =>
    prod (Y = Y1 ++ Y2) (prod (univ_gen_ext P Z1 Y1) (univ_gen_ext P Z2 Y2)))).
Proof.
intros A P Z2. induction Z1 ; simpl.
- exists []. exists Y. simpl. split. trivial.
split. apply univ_gen_ext_nil. trivial.
- intro. intro. apply univ_gen_ext_lem in X. cD. subst.
apply IHZ1 in X2. cD. subst.
exists (X ++ a :: X2). exists X1.
split. rewrite app_comm_cons. rewrite app_assoc. trivial.
split. apply univ_gen_ext_appL. apply univ_gen_ext_cons. assumption.
2: assumption. assumption.
Qed.

Lemma univ_gen_ext_splitR: forall A P (Z2 Z1 Y : list A),
  univ_gen_ext P Y (Z1 ++ Z2) -> sigT (fun Y1 => sigT (fun Y2 =>
    prod (Y = Y1 ++ Y2) (prod (univ_gen_ext P Y1 Z1) (univ_gen_ext P Y2 Z2)))).
Proof.
intros V Z2. induction Z1 ; simpl.
- exists []. exists Y. simpl. split. trivial.
  split. apply univ_gen_ext_nil. trivial.
- intro. intro. inversion X ; subst.
apply IHZ1 in X0. cD. subst.
exists (a :: X0). exists X1. simpl. split. trivial.
split. apply univ_gen_ext_cons.  assumption. assumption.
apply IHZ1 in X1. cD. subst.
exists X1. exists X2. split. trivial. split. apply univ_gen_ext_extra.
assumption. assumption. assumption.
Qed.

(* univ_gen_ext_combine claims that if Y1 is embedded in Z1 and Y2 is embedded
   in Z2, then we can combine the embedded lists in the shape of Y1++Y2 and combine
   the embedding lists in Z1++Z2 to preserve the relation of embedding between the
   newly created lists.*)

Lemma univ_gen_ext_combine: forall A P (Z2 Z1 Y2 Y1 : list A),
    univ_gen_ext P Y1 Z1 -> univ_gen_ext P Y2 Z2 -> univ_gen_ext P (Y1 ++ Y2) (Z1 ++ Z2).
Proof.
intros A P Z2 Z1 Y2 Y1 gen1 gen2. induction gen1.
- repeat rewrite app_nil_l. assumption.
- simpl. apply univ_gen_ext_cons. assumption.
- simpl. apply univ_gen_ext_extra. assumption. assumption.
Qed.

(* The next lemma states that if a::Y is embedded in a::Z, then we know
   for sure that Y is embedded in Z. Note that this is not direct as the
   a in the embedding list could have been added via univ_gen_ext_extra.
   Effectively, this lemma allows one to remove the identical heads of two
   lists univ_gen_ext and preserve that relation. *)

Lemma univ_gen_ext_same_hd: forall A P (Y Z : list A) (a : A),
    univ_gen_ext P (a::Y) (a::Z) -> univ_gen_ext P Y Z.
Proof.
intros A P Y Z a gen. inversion gen.
- assumption.
- subst. assert (H: univ_gen_ext P Y (a :: Y)).
  apply univ_gen_ext_extra. assumption. apply univ_gen_ext_refl.
  apply univ_gen_ext_trans with (ys:=(a :: Y)). assumption. assumption.
Qed.

(* The lemma univ_gen_ext_elem_deep considers a list l1 embedded in a
   list l2 in which an element a appears deeply. Essentially, the lemma
   makes a case distinction about a: either it has been added by univ_gen_ext_extra
   (this is the first case of the sum) or it was added by univ_gen_ext_cons
   in which case it has to appear somewhere in l1. *)

Lemma univ_gen_ext_elem_deep {A : Type} : forall P (l1 l2 l3 l4: list A) a,
          univ_gen_ext P l1 l2 ->
          (l2 = l3 ++ a :: l4) ->
            ((univ_gen_ext P l1 (l3 ++ l4) * P a) +
            sigT (fun l5 => sigT (fun l6 =>
              (prod (l1 = l5 ++ a :: l6) (prod (univ_gen_ext P l5 l3) (univ_gen_ext P l6 l4)))))).
Proof.
intros. subst. rewrite cons_single in X. apply univ_gen_ext_splitR in X.
destruct X. destruct s. repeat destruct p. subst.
apply univ_gen_ext_splitR in u0. destruct u0. destruct s. repeat destruct p.
subst. inversion u0.
- right. exists x. exists (l ++ x2). split. auto.
  split. assumption. inversion X. subst. simpl. assumption.
- left. subst. inversion X0. subst. split. rewrite app_nil_l.
  apply univ_gen_ext_combine. assumption. assumption. assumption.
Qed.

(* The next lemma states that if a list l1 is embedded in another list,
   then one can add an element a however deep in the embedding list and
   keep the relation of embedding, as long as a satisfies P. *)

Lemma univ_gen_ext_add_elem_deep {A : Type} : forall P (l1 l2 l3: list A) a,
    univ_gen_ext P l1 (l2 ++ l3) ->
    P a -> univ_gen_ext P l1 (l2 ++ a :: l3).
Proof.
intros. apply univ_gen_ext_splitR in X. destruct X. destruct s.
repeat destruct p. subst. apply univ_gen_ext_combine.
assumption. apply univ_gen_ext_extra. assumption. assumption.
Qed.

(* This last lemma claims that if l0 is embedded in l1 with a property P,
   then l0 is also embedded in l1 with the property Q. Obviously, all elements
   which were added in l1 via univ_gen_ext_extra satisfied the property P, and
   as Q is weaker than P we get that these elements aso satisfy Q. Thus we preserve
   the embedding relation. *)

Lemma univ_gen_ext_Q_weaker_than_P {A : Type} : forall P Q (l0 l1 : list A),
          (forall a, P a -> Q a) ->
          (univ_gen_ext P l0 l1) ->
          (univ_gen_ext Q l0 l1).
Proof.
intros. induction X0.
- apply univ_gen_ext_nil.
- apply univ_gen_ext_cons. assumption.
- apply univ_gen_ext_extra. apply X. assumption. assumption.
Qed.

Lemma univ_gen_ext_In {A : Type} : forall (l0 l1 : list A) a P, univ_gen_ext P l0 l1 ->
                                        In a l0 -> In a l1.
Proof.
intros. induction X.
- subst. inversion H.
- subst. inversion H. subst. apply in_eq. subst. apply in_cons. apply IHX. assumption.
- apply in_cons. apply IHX. assumption.
Qed.

Lemma univ_gen_ext_smaller_length : forall {A: Type} (l1 l2 : list A) P,
                      univ_gen_ext P l1 l2 -> length l1 <= length l2.
Proof.
intros. induction X.
- auto.
- simpl. apply le_n_S. assumption.
- simpl. lia.
Qed.

Lemma univ_gen_ext_same_length_id : forall {A: Type} (l1 l2 : list A) P,
              (length l1 = length l2) -> univ_gen_ext P l1 l2 -> l1 = l2.
Proof.
intros A l1 l2 P H X. induction X.
- firstorder.
- simpl in H. inversion H. apply IHX in H1. subst. auto.
- simpl in H. exfalso. pose (univ_gen_ext_smaller_length X). lia.
Qed.

Lemma univ_gen_ext_not_In_delete : forall {A : Type} (l1 l2 : list A) P (a : A),
            ((In a l1) -> False) -> univ_gen_ext P l1 (a :: l2) -> univ_gen_ext P l1 l2.
Proof.
intros. remember (a :: l2) as l3. induction X.
- inversion Heql3.
- inversion Heql3. subst. exfalso. apply H. apply in_eq.
- inversion Heql3. subst. assumption.
Qed.

Lemma InT_univ_gen_ext : forall {A : Type} (l1 l2 : list A) (P : A -> Type) (a : A),
          (InT a l2) -> (univ_gen_ext P l1 l2) -> ((P a) + (InT a l1)).
Proof.
intros. induction X0.
- inversion X.
- inversion X. subst. right. apply InT_eq. apply IHX0 in X1. destruct X1. auto.
  right. apply InT_cons. assumption.
- inversion X. subst. auto. apply IHX0 in X1. assumption.
Qed.













(* univ_gen_ext simulates gen_ext: *)

Definition gen_ext {W : Type} := @univ_gen_ext W (fun x => True).

Lemma gen_ext_refl: forall W (l : list W), gen_ext l l.
Proof. induction l. apply univ_gen_ext_nil. apply univ_gen_ext_cons. exact IHl. Qed.

Lemma gen_ext_appL: forall W (xs ys zs : list W),
 gen_ext xs ys ->gen_ext xs (zs ++ ys).
Proof. induction zs. tauto. intros. apply univ_gen_ext_extra. tauto. tauto. Qed.

Lemma gen_ext_appR: forall W (xs ys zs : list W),
 gen_ext xs ys -> gen_ext xs (ys ++ zs).
Proof. intros. induction X.
induction zs. simpl. apply univ_gen_ext_nil. simpl.
apply univ_gen_ext_extra. apply I. assumption.
simpl. apply univ_gen_ext_cons. assumption.
simpl. apply univ_gen_ext_extra. assumption. assumption. Qed.

Lemma gen_ext_nil_any: forall W (xs : list W),gen_ext [] xs.
Proof. induction xs. apply univ_gen_ext_nil. apply univ_gen_ext_extra. tauto. tauto. Qed.

Lemma gen_ext_trans: forall W (ys zs : list W),
 gen_ext ys zs -> forall xs, gen_ext xs ys -> gen_ext xs zs.
Proof. intros until 1. induction X. tauto.
intros. inversion X0. subst. apply univ_gen_ext_cons. firstorder.
subst. apply univ_gen_ext_extra. firstorder. firstorder.
intros. apply univ_gen_ext_extra. firstorder. firstorder.  Qed.

Lemma gen_ext_app: forall W (ys zs : list W),
 gen_ext ys zs -> forall us vs, gen_ext us vs -> gen_ext (us ++ ys) (vs ++ zs).
Proof. intros. induction X0 ; simpl. exact X.
apply univ_gen_ext_cons. assumption.
apply univ_gen_ext_extra. assumption. assumption. Qed.

Definition gen_ext_sameL W xs ys zs ge :=
  @gen_ext_app W ys zs ge xs xs (@gen_ext_refl W xs).
Definition gen_ext_sameR W xs ys zs ge :=
  @gen_ext_app W xs xs (@gen_ext_refl W xs) ys zs ge.

Lemma gen_ext_lem: forall A (x : A) Z Y,
 gen_ext (x :: Z) Y -> sigT (fun Y1 => sigT (fun Y2 =>
    prod (Y = Y1 ++ x :: Y2) (gen_ext Z Y2))). 
Proof.  intros A x Z. induction Y.
intro. inversion X. intro. inversion X ; subst.
exists []. exists Y. simpl. tauto.
apply IHY in X0. cD. subst.
exists (a :: X0). exists X1. simpl. tauto. Qed.

Lemma gen_ext_splitL: forall A Z2 Z1 Y,
 gen_ext (Z1 ++ Z2 : list A) Y -> sigT (fun Y1 => sigT (fun Y2 =>
    prod (Y = Y1 ++ Y2) (prod (gen_ext Z1 Y1) (gen_ext Z2 Y2)))). 
Proof. intros A Z2. induction Z1 ; simpl.
exists []. exists Y. simpl. split. trivial. 
split. apply univ_gen_ext_nil. trivial.
intro. intro. apply gen_ext_lem in X. cD. subst.
apply IHZ1 in X2. cD. subst.
exists (X ++ a :: X2). exists X1.
split. rewrite app_comm_cons. rewrite app_assoc. trivial.
split. apply gen_ext_appL. apply univ_gen_ext_cons. assumption. assumption. Qed.

Lemma gen_ext_splitR: forall A Z2 Z1 Y,
 gen_ext Y (Z1 ++ Z2 : list A) -> sigT (fun Y1 => sigT (fun Y2 =>
    prod (Y = Y1 ++ Y2) (prod (gen_ext Y1 Z1) (gen_ext Y2 Z2)))). 
Proof. intros A Z2. induction Z1 ; simpl.
exists []. exists Y. simpl. split. trivial.
split. apply univ_gen_ext_nil. trivial.
intro. intro. inversion X ; subst.
apply IHZ1 in X0. cD. subst.
exists (a :: X0). exists X1. simpl. split. trivial.
split. apply univ_gen_ext_cons.  assumption. assumption.
apply IHZ1 in X0. cD. subst.
exists X0. exists X1. split. trivial.
split. apply univ_gen_ext_extra.  assumption. assumption. assumption. Qed.

Lemma gen_ext_combine: forall A (Z2 Z1 Y2 Y1 : list A),
   gen_ext Y1 Z1 ->gen_ext Y2 Z2 ->gen_ext (Y1 ++ Y2) (Z1 ++ Z2).
Proof.
intros A Z2 Z1 Y2 Y1 gen1 gen2. induction gen1.
- repeat rewrite app_nil_l. assumption.
- simpl. apply univ_gen_ext_cons. assumption.
- simpl. apply univ_gen_ext_extra. assumption. assumption.
Qed.

Lemma gen_ext_same_hd: forall A (Y Z : list A) a,
   gen_ext (a::Y) (a::Z) ->gen_ext Y Z.
Proof.
intros A Y Z a gen. inversion gen.
- assumption.
- subst. assert (H:gen_ext Y (a :: Y)).
  apply univ_gen_ext_extra. apply I. apply gen_ext_refl.
  apply gen_ext_trans with (ys:=(a :: Y)). assumption. assumption.
Qed.

Lemma gen_ext_single: forall A (l : list A), sing_empty l ->
  forall Y Z le,gen_ext (Z ++ l ++ Y) le -> sigT (fun Ze => sigT (fun Ye =>
    prod (prod (gen_ext Z Ze) (gen_ext Y Ye)) (le = Ze ++ l ++ Ye))).
Proof. intros A l es Y.  destruct es ; simpl ; intros.
apply gen_ext_splitL in X. cD. subst. firstorder.
apply gen_ext_splitL in X. cD.
apply gen_ext_lem in X3. cD. subst.
exists (X ++ X3). exists X4.
split. split.  apply gen_ext_appR. assumption. assumption.
rewrite app_assoc. trivial. Qed.

Lemma gen_ext_one': forall A (x : A) (xs l : list A),
  xs = [x] ->gen_ext xs l -> InT x l.
Proof. intros. induction X.
- discriminate H.
- injection H as . subst. apply InT_eq.
- apply InT_cons. apply (IHX H). Qed.

Definition gen_ext_one A x l := @gen_ext_one' A x [x] l eq_refl.
(* and note result InT_split *)

Lemma InT_gen_ext A x l: InT x l ->gen_ext [x : A] l.
Proof. intros. apply InT_split in X. cD. subst.
apply gen_ext_appL.  apply univ_gen_ext_cons.  apply gen_ext_nil_any. Qed.

Lemma gen_ext_InT A (x : A) l m:gen_ext l m -> InT x l -> InT x m.
Proof. intro ge. induction ge. tauto.
intro. inversion X ; subst. apply InT_eq.
apply InT_cons. exact (IHge X0).
intro. apply InT_cons. exact (IHge X). Qed.

Lemma gen_ext_diff' V X r :gen_ext X r -> forall (y : V) Y Z,
    r = (Y ++ y :: Z) -> InT y X +gen_ext X (Y ++ Z). 
Proof. intro ge. induction ge.
- intros. list_eq_ncT. contradiction.
- intros. acacD'T2 ; subst.
+ left. apply InT_eq.
+ erequire IHge.  erequire IHge.  erequire IHge.  require IHge.
  reflexivity.  destruct IHge.
 * left. apply InT_cons.  assumption.
 * right. simpl. apply univ_gen_ext_cons. assumption.
- intros. acacD'T2 ; subst.
+ right. simpl. assumption.
+ erequire IHge.  erequire IHge.  erequire IHge.  require IHge.
  reflexivity.  destruct IHge.
 * left.  assumption.
 * right. simpl. apply univ_gen_ext_extra. apply I. assumption.
Qed.

Definition gen_ext_diff V X y Y Z ge := @gen_ext_diff' V X _ ge y Y Z eq_refl.

Lemma gen_ext_delet_hd {A : Type} : forall (l1 l2 l3: list A) (a : A),
       gen_ext l1 l2 -> (l1 = a :: l3) ->gen_ext l3 l2.
Proof.
intros l1 l2 l3 a gen. generalize dependent l3. induction gen.
- intros l3 E. inversion E.
- intros l3 E. inversion E. destruct l3.
  * subst. apply gen_ext_nil_any.
  * inversion E. subst. apply univ_gen_ext_extra. apply I. assumption.
- intros l3 E. apply univ_gen_ext_extra. apply I. apply IHgen. assumption.
Qed.

Lemma gen_ext_elem_deep {A : Type} : forall (l1 l2 l3 l4: list A) (a : A),
         gen_ext l1 l2 ->
          (l2 = l3 ++ a :: l4) ->
            ((gen_ext l1 (l3 ++ l4)) +
            sigT (fun l5 => sigT (fun l6 =>
              (prod (l1 = l5 ++ a :: l6) (prod (gen_ext l5 l3) (gen_ext l6 l4)))))).
Proof.
intros l1 l2 l3 l4 a gen. generalize dependent a. generalize dependent l4.
generalize dependent l3. induction gen.
- intros l3 l4 a E. destruct l3. inversion E. inversion E.
- intros l3 l4 a E. destruct l3.
  * inversion E. simpl in E. destruct l4.
    + right. exists []. exists []. split. simpl. destruct l.
      reflexivity. exfalso. subst. inversion gen. split.
      apply univ_gen_ext_nil. apply univ_gen_ext_nil.
    + pose (IHgen [] l4 a0). simpl in s. pose (s H1). destruct s0.
      { right. exists []. exists l. split. reflexivity. split.
        apply univ_gen_ext_nil. apply univ_gen_ext_extra. apply I. assumption. }
      { repeat destruct s0. repeat destruct p. subst. right.
        exists []. exists (x0 ++ a0 :: x1). split. reflexivity.
        split. apply univ_gen_ext_nil. destruct x0. simpl. apply univ_gen_ext_cons. assumption.
        inversion g. }
  * inversion E. pose (IHgen l3 l4 a H1). destruct s.
    + left. apply univ_gen_ext_cons. assumption.
    + repeat destruct s. repeat destruct p. subst. right. exists (a0 :: x0).
      exists x1. split. reflexivity. split. apply univ_gen_ext_cons. assumption.
      assumption.
- intros l3 l4 a E. destruct l3.
  * simpl in E. inversion E. subst. left. simpl. assumption.
  * inversion E. pose (IHgen l3 l4 a H1). destruct s.
    + left. apply univ_gen_ext_extra. apply I. assumption.
    + repeat destruct s. repeat destruct p0. subst. right.
      exists x0. exists x1. split. reflexivity. split.
      apply univ_gen_ext_extra. apply I. assumption. assumption.
Qed.

Lemma gen_ext_add_elem_deep {A : Type} : forall (l1 l2 l3: list A) (a : A),
   gen_ext l1 (l2 ++ l3) ->gen_ext l1 (l2 ++ a :: l3).
Proof.
induction l1.
- intros. apply gen_ext_nil_any.
-  induction l2.
  * intros l3 a0 gen. simpl. simpl in gen. apply univ_gen_ext_extra. apply I. assumption.
  * intros l3 a1 gen. remember ((a0 :: l2) ++ l3) as l4. remember (a :: l1) as l5. destruct gen.
    + apply gen_ext_nil_any.
    + inversion Heql4. simpl. subst. apply univ_gen_ext_cons.
      inversion Heql5. apply IHl1. rewrite <- H1. assumption.
    + inversion Heql4. subst. simpl. apply univ_gen_ext_extra. apply I.
      apply IHl2. assumption.
Qed.

Ltac solve_gen_ext :=
  repeat (apply gen_ext_appR ||
      apply gen_ext_nil_any || apply gen_ext_refl ||
      apply gen_ext_sameL || apply gen_ext_appL ||
      apply univ_gen_ext_cons || apply univ_gen_ext_extra).

Ltac solve_univ_gen_ext :=
  repeat (apply univ_gen_ext_appR || apply univ_gen_ext_refl ||
      apply univ_gen_ext_appL || apply univ_gen_ext_cons ||
      apply univ_gen_ext_extra).


(* univ_gen_ext simulates rest_gen_ext. The latter allows to restrict
   the elements you can add to the embedding list to elements of a specific
   list l. *)

Definition rest_gen_ext {W : Type} l := univ_gen_ext (fun x => (@InT W x l)).
