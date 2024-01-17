Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import KS_calc.

Lemma NoDup_incl_lengthT : forall (l l' : list MPropF), NoDup l -> incl l l' ->
          ((length l < length l') + (length l = length l')).
Proof.
induction l.
- intros. destruct l'.
  * right. auto.
  * left. simpl. lia.
- induction l' ; intros.
  * exfalso. assert (In a (a :: l)). apply in_eq. pose (H0 a H1). inversion i.
  * simpl. destruct (eq_dec_form a a0).
    + subst. assert (NoDup l). inversion H. assumption. assert (incl l l').
      unfold incl. intros. assert (In a (a0 :: l)). apply in_cons. assumption.
      apply H0 in H3. inversion H3. subst. exfalso. inversion H. apply H6. assumption. assumption.
      pose (IHl _ H1 H2). destruct s. left. lia. right. lia.
    + destruct (In_dec l a0).
      { destruct (In_dec l' a0).
        - assert (NoDup l). inversion H. assumption. assert (incl l l'). unfold incl.
          intros. assert (In a1 (a :: l)). apply in_cons. assumption. apply H0 in H3.
          inversion H3. subst. assumption. assumption. pose (IHl _ H1 H2). destruct s.
          left. lia. right. lia.
        - assert (NoDup l). inversion H. assumption. assert (incl l (a0 :: l')).
          unfold incl. intros. assert (In a1 (a :: l)). apply in_cons. assumption.
          apply H0 in H3. assumption. assert (In a l'). assert (In a (a :: l)).
          apply in_eq. apply H0 in H3. inversion H3. subst. exfalso. apply n. reflexivity.
          assumption. apply in_split in H3. destruct (Nat.eq_dec (length l) (length l')).
          * subst. right. auto.
          * left. destruct H3. destruct H3. subst.
            rewrite app_length. simpl. assert (incl l (a0 :: x ++ x0)). unfold incl.
            intros. assert (In a1 (a :: l)). apply in_cons. assumption. apply H0 in H4.
            inversion H4. subst. apply in_eq. apply in_app_or in H5. destruct H5.
            apply in_cons. apply in_or_app. auto. inversion H5. subst. exfalso. inversion H.
            apply H8. assumption. apply in_cons. apply in_or_app. auto.
            rewrite app_length in n0. simpl in n0.
            pose (IHl _ H1 H3). destruct s. 
            + simpl in l0. rewrite app_length in l0. lia.
            + exfalso. apply n0. simpl in e. rewrite app_length in e. lia.  }
      { assert (incl l l'). unfold incl. intros. assert (In a1 (a :: l)). apply in_cons. assumption.
        apply H0 in H2. inversion H2. subst. exfalso. apply f. assumption. assumption.
        assert (NoDup l). inversion H. assumption. pose (IHl _ H2 H1). destruct s.
        - left. lia.
        - right. lia. }
Qed.

(* Then the definition we were initially looking for can be reached: *)

Definition measure (s : Seq) : nat :=
    (size_LF (fst s)) + (size_LF (snd s)).

(* It is clear that measure counts the occurrences of implications in a
   sequent s. As a consequence, if that number is 0 we know for sure that the
   rules for implication on the left or right cannot be applied upwards on s.
   This is the meaning of the lemma measure_is_0. 

   But first we need a preliminary lemma which claims that if an implication is
   in a list, then size_LF of that list is higher than one.*)

Lemma In_Imp_size_LF_is_non_0 (l : list MPropF) :
    forall A B, (In (Imp A B) l) -> (le 1 (size_LF l)).
Proof.
intros A B Hin. induction l.
- inversion Hin.
- inversion Hin.
  * subst. simpl. rewrite <- Nat.succ_le_mono. apply le_0_n.
  * pose (IHl H). simpl. destruct l0.
    + rewrite Nat.add_1_r. rewrite <- Nat.succ_le_mono. apply le_0_n.
    + rewrite <- plus_n_Sm. rewrite <- Nat.succ_le_mono. apply le_0_n.
Qed.

Theorem term_meas_is_0 (s : Seq) :
    (measure s) = 0 -> (existsT2 ps, (ImpRRule ps s) + (ImpLRule ps s)) -> False.
Proof.
intros is0 RA. destruct RA. destruct s0.
- inversion i. subst. unfold measure in is0. simpl in is0.
  assert (size_LF (Δ0 ++ A --> B :: Δ1) = 0). lia.
  assert (In (A --> B) (Δ0 ++ A --> B :: Δ1)). apply in_or_app. right. apply in_eq.
  pose (In_Imp_size_LF_is_non_0 (Δ0 ++ A --> B :: Δ1) A B H0). lia.
- inversion i. subst.
  assert (In (A --> B) (Γ0 ++ A --> B :: Γ1)). apply in_or_app. right. apply in_eq.
  pose (In_Imp_size_LF_is_non_0 (Γ0 ++ A --> B :: Γ1) A B H). unfold measure in is0.
  simpl in is0. assert (size_LF (Δ0 ++ Δ1) = 0). lia. lia.
Qed.

Lemma size_LF_dist_app : forall l1 l2, size_LF (l1 ++ l2) =
                                               plus (size_LF l1) (size_LF l2).
Proof.
induction l1.
- intros. auto.
- intros. simpl. rewrite IHl1. lia.
Qed.

Lemma size_nobox_gen_ext : forall l1 l2, nobox_gen_ext l1 l2 ->
                                               (size_LF l1 <= size_LF l2).
Proof.
intros. induction X.
- simpl. lia.
- simpl. lia.
- simpl. lia.
Qed.

Lemma size_unboxed : forall l, (size_LF (unboxed_list l) <= size_LF l).
Proof.
induction l.
- simpl. lia.
- simpl. destruct a ; simpl ; lia.
Qed.

Lemma size_top_boxes : forall l, (size_LF (top_boxes l) <= size_LF l).
Proof.
induction l.
- simpl. lia.
- simpl. destruct a ; simpl ; lia.
Qed.

(* We prove some lemmas about these notions. *)

Lemma In_Box_size_LF_is_non_0 (l : list MPropF) :
    forall A, (In (Box A) l) -> (le 1 (size_LF l)).
Proof.
intros A Hin. induction l.
- inversion Hin.
- inversion Hin.
  * subst. simpl. rewrite <- Nat.succ_le_mono. apply le_0_n.
  * pose (IHl H). simpl. destruct l0.
    + rewrite Nat.add_1_r. rewrite <- Nat.succ_le_mono. apply le_0_n.
    + rewrite <- plus_n_Sm. rewrite <- Nat.succ_le_mono. apply le_0_n.
Qed.

Theorem measure_is_0 (s : Seq) :
    (measure s) = 0 -> (existsT2 ps, (KRRule ps s)) -> False.
Proof.
intros is0 RA. destruct RA. inversion k. subst. unfold measure in is0.
simpl in is0.
assert (size_LF (Δ0 ++ Box A :: Δ1) = 0). lia.
assert (In (Box A) (Δ0 ++ Box A :: Δ1)). apply in_or_app. right. apply in_eq.
pose (In_Box_size_LF_is_non_0 (Δ0 ++ Box A :: Δ1) A H1). lia.
Qed.






(* Third, we need to prove that if no KS rule is applicable to a sequent s,
   then its derivations have a height equal to 0. *)

Theorem no_KS_rule_applic : forall s, (forall ps, (KS_rules ps s) -> False) ->
                                 forall (D : KS_drv s), derrec_height D = 0.
Proof.
intros s noRA D. induction D.
- auto.
- exfalso. apply noRA with (ps:=ps). assumption.
Qed.