Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Wellfounded.

Require Import GLS_calcs.
Require Import DLW_wf_lex.

Set Implicit Arguments.

Lemma NoDup_incl_lengthT : forall (l l' : list MPropF), NoDup l -> incl l l' ->
          {length l < length l'} + {length l = length l'}.
Proof. intros. apply Compare_dec.le_lt_eq_dec, NoDup_incl_length; assumption. Qed.


(* First, let us define a the second part of our measure. This number is simply
   the number of implication symbols in a sequent.

   To define it, we need to define the number of implications in a formula. *)

Fixpoint n_imp_subformF (A : MPropF) : nat :=
match A with
 | # P => 0
 | ⊥ => 0
 | Imp B C => 1 + (n_imp_subformF B) + (n_imp_subformF C)
 | Box B => (n_imp_subformF B)
end.

(* With this definition in hand, we can then straightforwardly define the number
   of implications in a list of formulae. *)

Fixpoint n_imp_subformLF (l : list MPropF) : nat :=
match l with
  | [] => 0
  | h :: t => (n_imp_subformF h) + (n_imp_subformLF t)
end.

(* The the definition we were initially looking for can be reached: *)

Definition n_imp_subformS (s : Seq) : nat :=
    (n_imp_subformLF (fst s)) + (n_imp_subformLF (snd s)).

(* It is clear that n_imp_subformS counts the occurrences of implications in a
   sequent s. As a consequence, if that number is 0 we know for sure that the
   rules for implication on the left or right cannot be applied upwards on s.
   This is the meaning of the lemma n_imp_subformS_is_0. 

   But first we need a preliminary lemma which claims that if an implication is
   in a list, then n_imp_subformLF of that list is higher than one.*)

Lemma In_n_imp_subformLF_is_non_0 (l : list MPropF) :
    forall A B, (In (Imp A B) l) -> (le 1 (n_imp_subformLF l)).
Proof.
intros A B Hin. induction l.
- inversion Hin.
- inversion Hin.
  * subst. simpl. rewrite <- Nat.succ_le_mono. apply le_0_n.
  * pose (IHl H). simpl. destruct l0.
    + rewrite Nat.add_1_r. rewrite <- Nat.succ_le_mono. apply le_0_n.
    + rewrite <- plus_n_Sm. rewrite <- Nat.succ_le_mono. apply le_0_n.
Qed.

Theorem n_imp_subformS_is_0 (s : Seq) :
    (n_imp_subformS s) = 0 -> (existsT2 ps, (ImpRRule ps s) + (ImpLRule ps s)) -> False.
Proof.
intros is0 RA. destruct RA. destruct s0.
- inversion i. subst. unfold n_imp_subformS in is0. simpl in is0.
  assert (n_imp_subformLF (Δ0 ++ A --> B :: Δ1) = 0). lia.
  assert (In (A --> B) (Δ0 ++ A --> B :: Δ1)). apply in_or_app. right. apply in_eq.
  pose (In_n_imp_subformLF_is_non_0 (Δ0 ++ A --> B :: Δ1) A B H0). lia.
- inversion i. subst.
  assert (In (A --> B) (Γ0 ++ A --> B :: Γ1)). apply in_or_app. right. apply in_eq.
  pose (In_n_imp_subformLF_is_non_0 (Γ0 ++ A --> B :: Γ1) A B H). unfold n_imp_subformS in is0.
  simpl in is0. assert (n_imp_subformLF (Δ0 ++ Δ1) = 0). lia. lia.
Qed.

Lemma n_imp_subformLF_dist_app : forall l1 l2, n_imp_subformLF (l1 ++ l2) =
                                               plus (n_imp_subformLF l1) (n_imp_subformLF l2).
Proof.
induction l1.
- intros. auto.
- intros. simpl. rewrite IHl1. lia.
Qed.



(* Second, we intend to define the notion of usable boxed formulae in a sequent. We also
   prove that if this measure is 0 then no GLR rule can be applied to this sequent.

   In the next definitions our aim is to define the list of all boxed subformulae (not
   occurrences) of all the formulae in a sequent. *)

Fixpoint subform_boxesF (A : MPropF) : list MPropF :=
match A with
 | # P => nil
 | ⊥ => nil
 | Imp B C => (subform_boxesF B) ++ (remove_list (subform_boxesF B) (subform_boxesF C))
 | Box B => (Box B) :: (subform_boxesF B)
end.

Fixpoint subform_boxesLF (l : list MPropF) : list MPropF :=
match l with
  | nil => nil
  | h :: t => (subform_boxesF h) ++ (remove_list (subform_boxesF h) (subform_boxesLF t))
end.

Definition subform_boxesS (s : Seq) : list MPropF :=
  (subform_boxesLF (fst s)) ++ (remove_list (subform_boxesLF (fst s)) (subform_boxesLF (snd s))).

Lemma In_subform_boxesF_box : forall (A B : MPropF), In A (subform_boxesF B) -> is_boxedT A.
Proof.
unfold is_boxedT. intros A B. generalize dependent A. induction B ; intros.
- simpl in H. destruct H.
- simpl in H. destruct H.
- simpl in H. apply in_app_or in H. destruct H.
  * apply IHB1 in H. assumption.
  * assert (In A (subform_boxesF B2)). apply In_remove_list_In_list in H. assumption.
    apply IHB2 in H0. assumption.
- simpl in H. destruct H. exists B. auto. apply IHB in H. assumption.
Qed.

Lemma In_subform_boxesLF_box : forall (A : MPropF) l, In A (subform_boxesLF l) -> is_boxedT A.
Proof.
unfold is_boxedT. intros A l. generalize dependent A. induction l ; intros.
- simpl in H. destruct H.
- simpl in H. apply in_app_or in H. destruct H. apply In_subform_boxesF_box in H. assumption.
  apply In_remove_list_In_list in H. apply IHl. assumption.
Qed.

(* Then next lemmas help us reach our goal. *)

Fixpoint length_form (a: MPropF) : nat :=
match a with
  | # n => 1
  | ⊥ => 1
  | Imp a0 a1 => S (length_form a0 + length_form a1)
  | Box a0 => S (length_form a0)
end.

Lemma S_le_False : forall (n : nat), S n <= n -> False.
Proof.
induction n.
- intro. inversion H.
- intro. apply Nat.succ_le_mono in H. apply IHn. assumption.
Qed.

Lemma in_subform_boxesF_smaller_length_form : forall (A B : MPropF), In A (subform_boxesF B) ->
                (length_form A <= length_form B).
Proof.
intros A B. generalize dependent A. induction B; intros .
- simpl. inversion H.
- simpl. inversion H.
- simpl. simpl in H. apply in_app_or in H. destruct H.
  * apply IHB1 in H. lia.
  * assert (In A (subform_boxesF B2)). apply In_remove_list_In_list in H. assumption.
    apply IHB2 in H0. lia.
- simpl in H. destruct H. subst. auto. apply IHB in H. simpl. apply le_S. assumption.
Qed.

Lemma contradic_subform_boxesF: forall A l, (l = (subform_boxesF A)) -> (In (Box A) l)  -> False.
Proof.
intros. subst. pose (in_subform_boxesF_smaller_length_form (Box A) A H0).
inversion l.
- apply eq_S_F in H1. assumption.
- simpl in l. apply S_le_False in l. assumption.
Qed.

Lemma NoDup_subform_boxesF : forall A, NoDup (subform_boxesF A).
Proof.
induction A.
- simpl. apply NoDup_nil.
- simpl. apply NoDup_nil.
- simpl. apply add_remove_list_preserve_NoDup. apply IHA1. apply IHA2.
- simpl. apply NoDup_cons. intro. apply contradic_subform_boxesF in H. assumption.
  reflexivity. apply IHA.
Qed.

Lemma subform_boxesLF_dist_app : forall l1 l2,
        (subform_boxesLF (l1 ++ l2)) =
        (subform_boxesLF l1) ++ (remove_list (subform_boxesLF l1) (subform_boxesLF l2)).
Proof.
induction l1.
- intros l2. simpl. reflexivity.
- intros l2. simpl. rewrite IHl1. repeat rewrite <- app_assoc.
  assert (E: remove_list (subform_boxesF a) (subform_boxesLF l1 ++
             remove_list (subform_boxesLF l1) (subform_boxesLF l2)) =
             remove_list (subform_boxesF a) (subform_boxesLF l1) ++
             remove_list (subform_boxesF a ++ remove_list (subform_boxesF a)
             (subform_boxesLF l1)) (subform_boxesLF l2)).
  { rewrite app_remove_list. rewrite redund_remove_list. rewrite <- remove_list_dist_app. reflexivity. }
  rewrite E. reflexivity.
Qed.

Lemma NoDup_subform_boxesLF : forall l, NoDup (subform_boxesLF l).
Proof.
induction l.
- intros. simpl. apply NoDup_nil.
- intros. simpl. apply add_remove_list_preserve_NoDup. apply NoDup_subform_boxesF.
  apply IHl.
Qed.

Lemma NoDup_subform_boxesS : forall s, NoDup (subform_boxesS s).
Proof.
intro s. unfold subform_boxesS. apply add_remove_list_preserve_NoDup ;
apply NoDup_subform_boxesLF.
Qed.

Lemma univ_gen_ext_incl_subform_boxes : forall l1 l2 P, (univ_gen_ext P l1 l2) ->
                                          incl (subform_boxesLF l1) (subform_boxesLF l2).
Proof.
intros. induction X.
- unfold incl. intros. auto.
- unfold incl. intros. simpl in H. simpl. apply in_app_or in H. destruct H.
  * apply in_or_app. left. assumption.
  * apply In_remove_list_In_list_not_In_remove_list in H. destruct H.
    apply in_or_app. right. apply not_removed_remove_list. apply IHX. assumption.
    assumption.
- unfold incl. intros. simpl. destruct (In_dec (subform_boxesF x) a).
  * apply in_or_app. left. assumption.
  * apply in_or_app. right. apply not_removed_remove_list. apply IHX. assumption.
    assumption.
Qed.

Lemma XBoxed_list_same_subform_boxes : forall l,
          incl (subform_boxesLF (XBoxed_list l)) (subform_boxesLF l) /\
          incl (subform_boxesLF l) (subform_boxesLF (XBoxed_list l)).
Proof.
induction l.
- split.
  * unfold incl. intros. simpl in H. inversion H.
  * unfold incl. intros. simpl in H. inversion H.
- split.
  * unfold incl. intros. simpl. simpl in H. apply in_app_or in H. destruct H.
    apply in_or_app. left. destruct a ; simpl in H ; try contradiction.
    simpl. assumption. simpl. right. assumption. apply In_remove_list_In_list in H.
    apply in_app_or in H. destruct H. apply in_or_app. left. assumption. apply in_or_app.
    right. apply In_remove_list_In_list_not_In_remove_list in H. destruct H. destruct IHl.
    apply H1 in H. apply not_removed_remove_list ; assumption.
  * destruct IHl. unfold incl. intros. simpl in H1. apply in_app_or in H1. destruct H1.
    destruct a ; simpl in H1 ; try contradiction. apply in_app_or in H1. destruct H1.
    simpl. apply in_or_app. left. apply in_or_app. left. assumption. apply
    In_remove_list_In_list_not_In_remove_list in H1. destruct H1. simpl. apply in_or_app.
    left. apply in_or_app. right. apply not_removed_remove_list ; assumption. destruct H1.
    subst. simpl. apply in_or_app. right. apply not_removed_remove_list. apply in_eq.
    intros. apply contradic_subform_boxesF in H1. assumption. auto. simpl. apply in_or_app.
    left. assumption. simpl. apply in_or_app. right. rewrite remove_list_dist_app.
    apply in_or_app. right. apply not_removed_remove_list. apply
    In_remove_list_In_list_not_In_remove_list in H1. destruct H1. apply H0 in H1.
    apply not_removed_remove_list ; assumption. intro. apply
    In_remove_list_In_list_not_In_remove_list in H1. destruct H1. destruct a ; simpl ; try assumption.
    simpl (unBox_formula (a1 --> a2)) in H2. firstorder. simpl (unBox_formula (Box a)) in H2.
    apply H3. simpl. right. assumption.
Qed.

Lemma In_incl_subform_boxes : forall l A, In A l ->
                  (forall B, In B (subform_boxesF A) -> In B (subform_boxesLF l)).
Proof.
induction l.
- intros. inversion H.
- intros. simpl. inversion H.
  * subst. apply in_or_app. left. assumption.
  * pose (IHl A H1). destruct (In_dec (subform_boxesF a) B).
    + apply in_or_app. left. assumption.
    + apply in_or_app. right. apply not_removed_remove_list. apply i. assumption.
      assumption.
Qed.








(* Now we can define the notion of usable boxed formulae: it is a one such that
   it does not appear as a top formula in the LHS of the sequent. To do so, we need to
   define the list of such formulae: *)

Lemma top_boxes_incl_list : forall l, incl (top_boxes l) l.
Proof.
induction l.
- simpl. unfold incl. intros. inversion H.
- unfold incl. intros. destruct a.
  * simpl in H. apply in_cons. apply IHl. assumption.
  * simpl in H. apply in_cons. apply IHl. assumption.
  * simpl in H. apply in_cons. apply IHl. assumption.
  * simpl in H. destruct H.
    + subst. apply in_eq.
    + apply in_cons. apply IHl. assumption.
Qed.

Lemma in_top_boxes : forall l A, (In A (top_boxes l)) -> (existsT2 B l1 l2, (A = Box B) * (l = l1 ++ A :: l2)).
Proof.
induction l.
- intros. simpl in H. inversion H.
- intros. destruct a as [n | | |].
  * simpl in H. apply IHl in H. destruct H. destruct s. destruct s. destruct p. subst.
    exists x. exists ([# n] ++ x0). exists x1. auto.
  * simpl in H. apply IHl in H. destruct H. destruct s. destruct s. destruct p. subst.
    exists x. exists ([⊥] ++ x0). exists x1. auto.
  * simpl in H. apply IHl in H. destruct H. destruct s. destruct s. destruct p. subst.
    exists x. exists ([a1 --> a2] ++ x0). exists x1. auto.
  * simpl (top_boxes (Box a :: l)) in H. destruct (eq_dec_form (Box a) A).
    + subst. exists a. exists []. exists l. auto.
    + subst. assert (H0 : In A (top_boxes l)). inversion H. exfalso. apply n. assumption.
      assumption. apply IHl in H0. destruct H0. destruct s. destruct s. destruct p.
      subst. exists x. exists ([Box a] ++ x0). exists x1. auto.
Qed.

Lemma box_preserv_top_boxes : forall l1 l2 l3 A, top_boxes l1 = l2 ++ Box A :: l3 ->
                                existsT2 l4 l5, l1 = l4 ++ Box A :: l5.
Proof.
induction l1.
- intros. simpl in H. destruct l2 ; inversion H.
- induction l2.
  * intros. rewrite app_nil_l in H. destruct a as [n | | |].
    + pose (IHl1 [] l3 A). simpl in s. apply s in H. destruct H. destruct s0. exists ([# n] ++ x).
      exists x0. subst. auto.
    + pose (IHl1 [] l3 A). simpl in s. apply s in H. destruct H. destruct s0. exists ([⊥] ++ x).
      exists x0. subst. auto.
    + pose (IHl1 [] l3 A). simpl in s. apply s in H. destruct H. destruct s0. exists ([a1 --> a2] ++ x).
      exists x0. subst. auto.
    + inversion H. exists []. exists l1. auto.
  * intros. destruct a as [n | | |].
    + simpl in H. pose (IHl1 (a0 :: l2) l3 A). simpl in s. apply s in H. destruct H. destruct s0. exists ([# n] ++ x).
      exists x0. subst. auto.
    + simpl in H. pose (IHl1 (a0 :: l2) l3 A). simpl in s. apply s in H. destruct H. destruct s0. exists ([⊥] ++ x).
      exists x0. subst. auto.
    + simpl in H. pose (IHl1 (a0 :: l2) l3 A). simpl in s. apply s in H. destruct H. destruct s0. exists ([a1 --> a2] ++ x).
      exists x0. subst. auto.
    + inversion H. apply IHl1 in H2. destruct H2. destruct s. subst. exists (Box a :: x). exists x0. auto.
Qed.

Lemma removed_box_exists : forall l1 l2 l3 A,
    (remove_list (top_boxes l1) (top_boxes (l2 ++ Box A :: l3))) = nil ->
    (existsT2 l4 l5, l1 = l4 ++ Box A :: l5).
Proof.
intros. pose (box_in_top_boxes l2 l3 A). repeat destruct s. rewrite e in H.
remember (top_boxes l1) as l. apply remove_list_in_nil in H. destruct H.
destruct s. subst. apply box_preserv_top_boxes in e0. assumption.
Qed.

Lemma is_box_in_top_boxes : forall l A, In A l -> is_boxedT A -> In A (top_boxes l).
Proof.
induction l.
- intros. inversion H.
- intros. inversion H.
  * subst. inversion X. subst. simpl. left. reflexivity.
  * pose (IHl A H0 X). destruct a ; simpl ; try assumption.
    right. assumption.
Qed.











(* Some more 'macro' lemmas dealing with subform_boxes and top_boxes. *)

Lemma RHS_top_box_is_subformLF : forall (s : Seq) (A : MPropF),
        (In A (top_boxes (snd s))) -> (In A (subform_boxesLF (snd s))).
Proof.
intros s A H. apply in_top_boxes in H. destruct H. repeat destruct s0. destruct p. subst. rewrite e0.
rewrite subform_boxesLF_dist_app. apply in_or_app. pose (In_dec (subform_boxesLF x0) (Box x)).
destruct s0.
- left. assumption.
- right. apply not_removed_remove_list.
  * simpl. left. reflexivity.
  * assumption.
Qed.

Lemma RHS_top_box_is_subform : forall s A, (In A (top_boxes (snd s))) -> (In A (subform_boxesS s)).
Proof.
intros s A H. unfold subform_boxesS. apply RHS_top_box_is_subformLF in H.
apply remove_list_is_in with (l2:=subform_boxesLF (fst s)) in H. assumption.
Qed.










(* Finally, we can define the list of usable boxed formulae. The length of that list is
   the first component of our measure. *)

Definition usable_boxes (s : Seq) : list MPropF :=
   remove_list (top_boxes (fst s)) (subform_boxesS s).

(* We can show that our notion of usable box effectively captures what it is intended to:
   an upper bound on how many GLR rules can be applied to a sequent. To check this, we can
   show that if the number of usable boxes is effectively 0 then no GLR is applicable. This
   is the content of the lemma length_usable_boxes_is_0. *)

Lemma no_RHS_box_no_GLR (s : Seq) :
    (top_boxes (snd s)) = nil -> (existsT2 ps, GLRRule ps s) -> False.
Proof.
intros isnil RA. destruct RA. inversion g. subst. simpl in isnil.
rewrite top_boxes_distr_app in isnil. apply app_eq_nil in isnil. destruct isnil.
simpl in H1. inversion H1.
Qed.

Lemma all_RHS_boxes_are_LHS_boxes_no_GLR (s : Seq) :
    (IdBRule [] s -> False) ->  (* This line makes sure that we do PS: no IdB can happen. *)
    (remove_list (top_boxes (fst s)) (top_boxes (snd s))) = nil ->
    (existsT2 ps, GLRRule ps s) -> False.
Proof.
intros noId isnil RA. destruct RA. inversion g. subst. simpl in isnil.
apply noId. apply removed_box_exists in isnil. destruct isnil. destruct s.
subst. apply IdBRule_I.
Qed.

Lemma no_usable_boxes_all_RHS_are_LHS (s : Seq) :
    length (usable_boxes s) = 0 -> (remove_list (top_boxes (fst s)) (top_boxes (snd s))) = nil.
Proof.
intro is0. remember (usable_boxes s) as l. destruct l.
- unfold usable_boxes in Heql. symmetry in Heql. rewrite remove_list_is_nil in Heql.
  rewrite remove_list_is_nil. intros. apply RHS_top_box_is_subform in H. apply Heql. assumption.
- inversion is0.
Qed.

Theorem length_usable_boxes_is_0 (s : Seq) :
    length (usable_boxes s) = 0 ->
    (IdBRule [] s -> False) ->
    (existsT2 ps, GLRRule ps s) -> False.
Proof.
intros H0 H1. pose (no_usable_boxes_all_RHS_are_LHS s H0).
pose (all_RHS_boxes_are_LHS_boxes_no_GLR H1 e). assumption.
Qed.

Lemma NoDup_usable_boxes : forall s, NoDup (usable_boxes s).
Proof.
intro s. unfold usable_boxes. destruct s. simpl. unfold subform_boxesS.
simpl. pose (NoDup_subform_boxesLF l0). pose (NoDup_subform_boxesLF l).
pose (add_remove_list_preserve_NoDup _ _ n0 n). apply remove_list_preserv_NoDup.
assumption.
Qed.



(* We can consequently define our measure on sequents: *)

Definition measure (s : Seq) : list nat :=
  [length (usable_boxes s) ; (n_imp_subformS s)].




(* Fourth, we show that the number of usable boxes decreases upwards in the application
   of a GLR rule. To do so we need to prove some lemmas beforehand. *)

Lemma GLR_applic_more_top_boxes : forall prem concl, GLRRule [prem] concl ->
                                                     (IdBRule [] concl -> False) ->
                                    incl (top_boxes (fst concl)) (top_boxes (fst prem)).
Proof.
intros prem concl RA noIdB. inversion RA. subst. simpl. rewrite top_boxes_distr_app.
simpl. unfold incl. intros. apply in_or_app. left. assert (In a Γ0). apply in_top_boxes in H.
destruct H. repeat destruct s. destruct p. subst. apply in_or_app. right. apply in_eq.
assert (InT a Γ0). apply in_splitT in H1. destruct H1. destruct s. rewrite e.
apply InT_or_app. right. apply InT_eq. pose (InT_univ_gen_ext H2 X). destruct s.
exfalso. apply f. apply in_top_boxes in H. destruct H. repeat destruct s.
destruct p. exists x. assumption. apply top_boxes_incl_list in H.
pose (list_preserv_XBoxed_list BΓ). pose (InT_In i). apply i0 in i1.
apply is_box_in_top_boxes. apply i0. apply InT_In. assumption.
apply H0. apply InT_In. assumption.
Qed.

Lemma GLR_applic_le_subform_boxes : forall prem concl, GLRRule [prem] concl ->
                                                        (IdBRule [] concl -> False) ->
                        (length (subform_boxesS prem) <= length (subform_boxesS concl) /\
                         forall B, (In B (subform_boxesS prem)) -> (In B (subform_boxesS concl))).
Proof.
intros prem concl RA noIdB. inversion RA. subst. split.
- apply NoDup_incl_length.
  * apply NoDup_subform_boxesS.
  * intro. intros. unfold subform_boxesS in H. unfold subform_boxesS. simpl. simpl in H.
    repeat rewrite length_app.  repeat rewrite length_app in H. repeat rewrite remove_list_of_nil.
    repeat rewrite remove_list_of_nil in H. rewrite app_nil_r in H. apply in_app_or in H.
    destruct H. rewrite subform_boxesLF_dist_app in H. apply in_app_or in H. destruct H.
    apply in_or_app. left. apply univ_gen_ext_incl_subform_boxes in X. apply X. pose (XBoxed_list_same_subform_boxes BΓ).
    destruct a0. apply H1. assumption. apply In_remove_list_In_list in H.
    apply remove_list_is_in. rewrite subform_boxesLF_dist_app. apply remove_list_is_in.
    simpl. simpl in H. destruct H. left. assumption. right. repeat rewrite remove_list_of_nil in H.
    apply in_app_or in H. destruct H. apply in_or_app. auto. simpl in H. destruct H.
    apply remove_list_is_in. apply In_remove_list_In_list in H. rewrite subform_boxesLF_dist_app.
    apply remove_list_is_in. simpl. right. apply in_or_app. auto.
- intro. intros. unfold subform_boxesS in H. unfold subform_boxesS. simpl. simpl in H.
  repeat rewrite length_app.  repeat rewrite length_app in H. repeat rewrite remove_list_of_nil.
  repeat rewrite remove_list_of_nil in H. rewrite app_nil_r in H. apply in_app_or in H.
  destruct H. rewrite subform_boxesLF_dist_app in H. apply in_app_or in H. destruct H.
  apply in_or_app. left. apply univ_gen_ext_incl_subform_boxes in X. apply X. pose (XBoxed_list_same_subform_boxes BΓ).
  destruct a. apply H1. assumption. apply In_remove_list_In_list in H.
  apply remove_list_is_in. rewrite subform_boxesLF_dist_app. apply remove_list_is_in.
  simpl. simpl in H. destruct H. left. assumption. right. repeat rewrite remove_list_of_nil in H.
  apply in_app_or in H. destruct H. apply in_or_app. auto. simpl in H. destruct H.
  apply remove_list_is_in. apply In_remove_list_In_list in H. rewrite subform_boxesLF_dist_app.
  apply remove_list_is_in. simpl. right. apply in_or_app. auto.
Qed.

Theorem GLR_applic_less_usable_boxes : forall prem concl, GLRRule [prem] concl ->
                                                          (IdBRule [] concl -> False) ->
                                         length (usable_boxes prem) < length (usable_boxes concl).
Proof.
intros prem concl RA noIdB. inversion RA. unfold usable_boxes. simpl.
apply remove_list_incr_decr.
- apply NoDup_subform_boxesS.
- apply NoDup_subform_boxesS.
- exists (Box A). repeat split. simpl. rewrite top_boxes_distr_app. apply in_or_app. right. simpl.
  left. reflexivity. unfold subform_boxesS. simpl.
  destruct (In_dec (subform_boxesLF Γ0) (Box A)). apply in_or_app. left. assumption.
  apply in_or_app. right. apply not_removed_remove_list. rewrite subform_boxesLF_dist_app.
  destruct (In_dec (subform_boxesLF Δ0) (Box A)). apply in_or_app. left. assumption.
  apply in_or_app. right. apply not_removed_remove_list. simpl. auto. assumption. assumption.
  intro. simpl in H2. apply noIdB. subst. pose (in_top_boxes Γ0 (Box A) H2). repeat destruct s.
  destruct p. subst. apply IdBRule_I.
- intro A0. pose (@GLR_applic_more_top_boxes prem concl). subst. pose (i RA). pose (i0 noIdB).
  apply i1.
- intro A0. subst. pose (GLR_applic_le_subform_boxes RA noIdB). destruct a. apply H1.
Qed.

Theorem ImpR_applic_less_Imp_same_usable_boxes : forall prem concl, ImpRRule [prem] concl ->
                   prod (sumbool (length (usable_boxes prem) < length(usable_boxes concl))
                    (length (usable_boxes prem) = length(usable_boxes concl)))
                   (n_imp_subformS (prem) < n_imp_subformS (concl)).
Proof.
intros prem concl RA. inversion RA. subst. split.
- pose (NoDup_usable_boxes (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)).
  pose (NoDup_usable_boxes (Γ0 ++ Γ1, Δ0 ++ A --> B :: Δ1)).
  apply NoDup_incl_lengthT. assumption. unfold incl. intros. unfold usable_boxes in H. simpl in H.
  unfold usable_boxes. simpl. apply In_remove_list_In_list_not_In_remove_list in H.
  destruct H. apply not_removed_remove_list. unfold subform_boxesS. unfold subform_boxesS in H.
  simpl. simpl in H. apply in_app_or in H. destruct H. rewrite subform_boxesLF_dist_app in H.
  apply in_app_or in H. destruct H. apply in_or_app. left. rewrite subform_boxesLF_dist_app.
  apply in_or_app. left. assumption. apply In_remove_list_In_list_not_In_remove_list in H.
  destruct H. simpl in H. apply in_app_or in H. destruct H. destruct (In_dec (subform_boxesLF (Γ0 ++ Γ1)) a).
  apply in_or_app. left. assumption. apply in_or_app. right. apply not_removed_remove_list.
  2: assumption. apply In_incl_subform_boxes with (A:=A --> B). apply in_or_app. right. apply in_eq.
  simpl. apply in_or_app. left.
  assumption. apply In_remove_list_In_list_not_In_remove_list in H. destruct H. apply in_or_app. left.
  rewrite subform_boxesLF_dist_app. apply in_or_app. right. apply not_removed_remove_list. assumption.
  assumption. apply In_remove_list_In_list_not_In_remove_list in H. destruct H. rewrite subform_boxesLF_dist_app in H.
  apply in_app_or in H. destruct H. apply in_or_app. right. apply not_removed_remove_list.
  rewrite subform_boxesLF_dist_app. apply in_or_app. left. assumption. intro.
  apply H1. rewrite subform_boxesLF_dist_app. apply in_or_app.
  rewrite subform_boxesLF_dist_app in H2. apply in_app_or in H2.
  destruct H2. auto. apply In_remove_list_In_list_not_In_remove_list in H2. destruct H2.
  right. apply not_removed_remove_list. simpl. apply in_or_app. right. apply not_removed_remove_list.
  assumption. intro. apply H1. rewrite subform_boxesLF_dist_app. apply in_or_app. right.
  apply not_removed_remove_list. simpl. apply in_or_app. left. assumption. assumption. assumption.
  apply in_or_app. right. apply not_removed_remove_list. apply In_remove_list_In_list_not_In_remove_list in H.
  destruct H. simpl in H. apply in_app_or in H. destruct H. apply In_incl_subform_boxes with (A:=A --> B).
  apply in_or_app. right. apply in_eq. simpl. apply in_or_app. right. apply not_removed_remove_list. assumption.
  intro. apply H1. rewrite subform_boxesLF_dist_app. apply in_or_app. right. apply not_removed_remove_list.
  simpl. apply in_or_app. left. assumption. intro. apply H1. rewrite subform_boxesLF_dist_app. apply in_or_app.
  auto. apply In_remove_list_In_list_not_In_remove_list in H. destruct H.
  rewrite subform_boxesLF_dist_app.
  apply in_or_app. right. apply not_removed_remove_list. simpl. apply in_or_app. right.
  apply not_removed_remove_list. assumption. intro. apply in_app_or in H4. destruct H4.
  apply H1. rewrite subform_boxesLF_dist_app. apply in_or_app. right. apply not_removed_remove_list.
  simpl. apply in_or_app. left. assumption. intro. apply H1. rewrite subform_boxesLF_dist_app.
  apply in_or_app. auto. apply H3. apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4.
  assumption. assumption. intro. apply H1. rewrite subform_boxesLF_dist_app.
  apply in_or_app. rewrite subform_boxesLF_dist_app in H2. apply in_app_or in H2.
  destruct H2. auto. apply In_remove_list_In_list_not_In_remove_list in H2.
  destruct H2. right. apply not_removed_remove_list. simpl. apply in_or_app. right.
  apply not_removed_remove_list. assumption. intro. apply H1. rewrite subform_boxesLF_dist_app.
  apply in_or_app. right. apply not_removed_remove_list. simpl. apply in_or_app. auto.
  assumption. assumption. intro. apply H0. rewrite top_boxes_distr_app. rewrite top_boxes_distr_app in H1.
  apply in_app_or in H1. destruct H1. apply in_or_app. auto. apply in_or_app. right.
  assert (A :: Γ1 = [A] ++ Γ1). auto. rewrite H2. rewrite top_boxes_distr_app. apply in_or_app. right.
  auto.
- unfold n_imp_subformS. simpl. repeat rewrite n_imp_subformLF_dist_app. simpl. lia.
Qed.

Theorem ImpL_applic_less_Imp_same_usable_boxes : forall prem1 prem2 concl, ImpLRule [prem1 ; prem2] concl ->
                   prod (prod (sumbool (length (usable_boxes prem1) < length(usable_boxes concl))
                    (length (usable_boxes prem1) = length(usable_boxes concl)))
                   (n_imp_subformS (prem1) < n_imp_subformS (concl)))
                   (prod (sumbool (length (usable_boxes prem2) < length(usable_boxes concl))
                    (length (usable_boxes prem2) = length(usable_boxes concl)))
                   (n_imp_subformS (prem2) < n_imp_subformS (concl))).
Proof.
intros prem1 prem2 concl RA. inversion RA. subst. split.
- split.
  * pose (NoDup_usable_boxes (Γ0 ++ Γ1, Δ0 ++ A :: Δ1)).
    pose (NoDup_usable_boxes (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)).
    apply NoDup_incl_lengthT. assumption. unfold incl. intros. unfold usable_boxes in H. simpl in H.
    unfold usable_boxes. simpl. apply In_remove_list_In_list_not_In_remove_list in H.
    destruct H. apply not_removed_remove_list. unfold subform_boxesS. unfold subform_boxesS in H.
    simpl. simpl in H. apply in_app_or in H. destruct H. rewrite subform_boxesLF_dist_app in H.
    apply in_app_or in H. destruct H. apply in_or_app. left. rewrite subform_boxesLF_dist_app.
    apply in_or_app. auto. apply in_or_app.
    apply In_remove_list_In_list_not_In_remove_list in H. destruct H. left.
    rewrite subform_boxesLF_dist_app. apply in_or_app. right.
    apply not_removed_remove_list. simpl. apply in_or_app.
    destruct (In_dec (subform_boxesF A ++ remove_list (subform_boxesF A) (subform_boxesF B)) a).
    auto. right. apply not_removed_remove_list.
    assumption. assumption. assumption. apply In_remove_list_In_list_not_In_remove_list in H.
    destruct H. rewrite subform_boxesLF_dist_app in H. apply in_app_or in H. destruct H. apply in_or_app.
    destruct (In_dec (subform_boxesLF (Γ0 ++ A --> B :: Γ1)) a). auto. right. apply not_removed_remove_list.
    2: assumption. rewrite subform_boxesLF_dist_app. apply in_or_app. auto.
    apply in_or_app. apply In_remove_list_In_list_not_In_remove_list in H. destruct H. simpl in H. apply in_app_or in H.
    destruct H. left. assert (In a (subform_boxesF (A --> B))). simpl. apply in_or_app. auto.
    apply In_incl_subform_boxes with (A:=A --> B). apply in_or_app. right. apply in_eq. assumption.
    apply In_remove_list_In_list_not_In_remove_list in H. destruct H.
    destruct (In_dec (subform_boxesLF (Γ0 ++ A --> B :: Γ1)) a). auto. right.
    apply not_removed_remove_list. rewrite subform_boxesLF_dist_app. apply in_or_app. right. apply not_removed_remove_list.
    assumption. assumption. assumption. intro. apply H0. rewrite top_boxes_distr_app in H1. rewrite top_boxes_distr_app.
    apply in_or_app. apply in_app_or in H1. destruct H1. auto. simpl in H1. auto.
  * unfold n_imp_subformS. simpl. repeat rewrite n_imp_subformLF_dist_app. simpl. lia.
- split.
  * pose (NoDup_usable_boxes (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)).
    pose (NoDup_usable_boxes (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)).
    apply NoDup_incl_lengthT. assumption. unfold incl. intros. unfold usable_boxes in H. simpl in H.
    unfold usable_boxes. simpl. apply In_remove_list_In_list_not_In_remove_list in H.
    destruct H. apply not_removed_remove_list. unfold subform_boxesS. unfold subform_boxesS in H.
    simpl. simpl in H. apply in_app_or in H. destruct H.
    apply in_or_app. left. rewrite subform_boxesLF_dist_app in H.
    apply in_app_or in H. destruct H. rewrite subform_boxesLF_dist_app. apply in_or_app. auto.
    apply In_remove_list_In_list_not_In_remove_list in H. destruct H. simpl in H. apply in_app_or in H.
    destruct H. simpl. rewrite subform_boxesLF_dist_app. apply in_or_app. right.
    apply not_removed_remove_list. simpl. apply in_or_app. destruct (In_dec (subform_boxesF A) a).
    left. apply in_or_app. auto. left.
    apply in_or_app. right. apply not_removed_remove_list. assumption. assumption. assumption.
    apply In_remove_list_In_list_not_In_remove_list in H. destruct H. rewrite subform_boxesLF_dist_app.
    apply in_or_app. right. apply not_removed_remove_list. simpl. destruct (In_dec (subform_boxesF A) a).
    apply in_or_app. left. apply in_or_app. auto. apply in_or_app. right.
    apply not_removed_remove_list. assumption. intro. apply in_app_or in H3. destruct H3.
    apply n1. auto. apply In_remove_list_In_list_not_In_remove_list in H3. destruct H3. auto.
    assumption. apply In_remove_list_In_list_not_In_remove_list in H. destruct H.
    destruct (In_dec (subform_boxesLF (Γ0 ++ A --> B :: Γ1)) a). apply in_or_app. auto.
    apply in_or_app. right. apply not_removed_remove_list. assumption. assumption.
    intro. apply H0. rewrite top_boxes_distr_app. rewrite top_boxes_distr_app in H1.
    apply in_app_or in H1. destruct H1. apply in_or_app. auto. simpl in H1.
    apply in_or_app. right. assert (B :: Γ1 = [B] ++ Γ1). reflexivity. rewrite H2.
    rewrite top_boxes_distr_app. apply in_or_app. auto.
  * unfold n_imp_subformS. simpl. repeat rewrite n_imp_subformLF_dist_app. simpl. lia.
Qed.

(* Now we show that the measure decreases upwards in the rule applications we considered. *)

Definition less_thanS (s0 s1 : Seq) : Prop := lex lt (measure s0) (measure s1).

Notation "s0 '<<' s1" := (less_thanS s0 s1) (at level 70).

Fact less_thanS_inv l m : l << m -> (lex lt (measure l) (measure m)).
Proof.
inversion 1; subst ; auto.
Qed.

Theorem less_thanS_wf : well_founded less_thanS.
Proof.
unfold less_thanS.
apply wf_inverse_image. apply lex_wf.
auto. apply Wf_nat.lt_wf.
Qed.

Fact lex_trans : forall l m n, (lex lt l m) -> (lex lt m n) -> (lex lt l n).
Proof.
intros l m n H. revert n. induction H.
- intros. inversion H0 ; subst. apply lex_skip ; auto. apply lex_cons ; auto. apply lex_length in H ; lia.
- intros. inversion H1 ; subst. apply lex_cons ; auto. apply lex_length in H5 ; lia.
  apply lex_cons ; lia.
Qed.

Fact less_thanS_trans l m n : l << m -> m << n -> l << n.
Proof.
unfold less_thanS. apply lex_trans.
Qed.

(* Corollary less_thanS_rect (P : (list MPropF * (MPropF)) -> Type)
(HP : forall s, (forall s1, (less_than lt (measure s1) (seq_list_occ_weight s)) -> P s1) -> P s) s : P s.
Proof.
  induction s as [ s IHs ] using (well_founded_induction_type less_thanS_wf).
  apply HP; intros; apply IHs. unfold less_thanS ; auto.
Qed. *)

Lemma decT_lt : forall m n, (m < n) + ((m < n) -> False).
Proof.
induction m.
- destruct n. right. intro. inversion H. left. lia.
- destruct n. right. intro. inversion H. pose (IHm n). destruct s. left. lia. right. intro. apply f. lia.
Qed.

Lemma decT_lex_lt : forall l0 l1, (lex lt l0 l1) + ((lex lt l0 l1) -> False).
Proof.
induction l0 ; intros.
- destruct l1. right ; intro. inversion H ; auto. right ; intro. inversion H ; auto.
- destruct l1. right ; intro. inversion H ; auto.
  destruct (IHl0 l1).
  + pose (lex_length l). destruct (decT_lt a n).
      * left. apply lex_cons ; auto.
      * destruct (Nat.eq_dec a n) ; subst.
        left. apply lex_skip ; auto.
        right. intro. inversion H ; subst ; auto.
  + destruct (decT_lt a n).
      * destruct (Nat.eq_dec (length l0) (length l1)). left. apply lex_cons ; auto.
        right. intro. inversion H ; auto.
      * right. intro. inversion H ; auto.
Qed.

Lemma decT_less_than_lt : forall l0 l1, (less_thanS l0 l1) + ((less_thanS l0 l1) -> False).
Proof.
intros. destruct l0, l1. unfold less_thanS.
apply decT_lex_lt.
Qed.

Theorem less_thanS_strong_inductionT:
forall P : Seq -> Type,
(forall s0 : Seq, (forall s1 : Seq, ((s1 << s0) -> P s1)) -> P s0) ->
forall s : Seq, P s.
Proof.
  induction s as [ s IHs ] using (well_founded_induction_type less_thanS_wf).
  apply X; intros; apply IHs. unfold less_thanS ; auto.
Qed.

Theorem GLR_applic_reduces_measure : forall prem concl,
                GLRRule [prem] concl ->
                (IdBRule [] concl -> False) ->
                prem << concl.
Proof.
intros. apply lex_cons ; auto.
apply GLR_applic_less_usable_boxes ; auto.
Qed.

Theorem ImpR_applic_reduces_ub_or_imp : forall prem concl,
                ImpRRule [prem] concl ->
                ((length (usable_boxes prem) < length (usable_boxes concl)) +
                ((length (usable_boxes prem) = length (usable_boxes concl)) *
                (n_imp_subformS prem < n_imp_subformS concl))).
Proof.
intros.
pose (ImpR_applic_less_Imp_same_usable_boxes H). destruct p ; auto.
destruct s ; auto.
Qed.

Theorem ImpR_applic_reduces_measure : forall prem concl,
                ImpRRule [prem] concl ->
                prem << concl.
Proof.
intros. destruct (ImpR_applic_less_Imp_same_usable_boxes H).
destruct s.
- apply lex_cons ; auto.
- unfold less_thanS ; unfold measure ; rewrite e ; apply lex_skip ; auto.
  apply lex_cons ; auto.
Qed.

Theorem ImpL_applic_reduces_ub_or_imp : forall prem1 prem2 concl,
                ImpLRule [prem1; prem2] concl ->
                ((length (usable_boxes prem1) < length (usable_boxes concl)) +
                ((length (usable_boxes prem1) = length (usable_boxes concl)) *
                (n_imp_subformS prem1 < n_imp_subformS concl))) *
                ((length (usable_boxes prem2) < length (usable_boxes concl)) +
                ((length (usable_boxes prem2) = length (usable_boxes concl)) *
                (n_imp_subformS prem2 < n_imp_subformS concl))).
Proof.
intros.
pose (ImpL_applic_less_Imp_same_usable_boxes H). destruct p ; auto. destruct p ; auto.
destruct p0 ; auto. destruct s ; auto. destruct s0 ; auto. destruct s0 ; auto.
Qed.

Theorem ImpL_applic_reduces_measure : forall prem1 prem2 concl,
                ImpLRule [prem1; prem2] concl ->
                (prem1 << concl) * (prem2 << concl).
Proof.
intros. destruct (ImpL_applic_less_Imp_same_usable_boxes H).
destruct p, p0. split.
- destruct s.
  + apply lex_cons ; auto.
  + unfold less_thanS ; unfold measure ; rewrite e ; apply lex_skip ; auto.
    apply lex_cons ; auto.
- destruct s0.
  + apply lex_cons ; auto.
  + unfold less_thanS ; unfold measure ; rewrite e ; apply lex_skip ; auto.
    apply lex_cons ; auto.
Qed.
