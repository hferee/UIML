Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import KS_calc.

Lemma NoDup_incl_lengthT : forall (l l' : list MPropF), NoDup l -> incl l l' ->
          {length l < length l'} + {length l = length l'}.
Proof. intros. apply Compare_dec.le_lt_eq_dec, NoDup_incl_length; assumption. Qed.

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