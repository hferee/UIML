  Require Import List.
  Export ListNotations.
  Require Import PeanoNat.
  Require Import Lia.

  Require Import general_export.

  Require Import GLS_export.

  Require Import UIGL_Def_measure.
  Require Import UIGL_Canopy.
  Require Import UIGL_irred_short.
  Require Import UIGL_braga.
  Require Import UIGL_Canopy_ImpR.

  Lemma repeat_more_than_one : forall n (A : MPropF), 0 < n -> In A (repeat A n).
  Proof.
  induction n ; simpl ; intros ; auto. inversion H.
  Qed.

  (* These two lemmas are crucial. *)

  Lemma mult_ImpL_R : forall s0 s1 A B,
          InT s1 (Canopy (replace (A --> B) B (fst s0), snd s0))->
          InT s1 (Canopy s0).
  Proof.
  intros s0 s1 A B. remember (count_occ eq_dec_form (fst s0) (A --> B)) as n. revert Heqn. generalize dependent B.
  generalize dependent A. generalize dependent s1. generalize dependent s0. induction n ; simpl ; intros.
  - symmetry in Heqn. rewrite <- count_occ_not_In in Heqn. rewrite notin_replace in H ; auto. destruct s0 ; auto.
  - assert (count_occ eq_dec_form (fst s0) (A --> B) > 0). lia. apply count_occ_In in H0. destruct s0. simpl in H0.
    simpl in H. simpl in Heqn. apply In_InT in H0. apply InT_split in H0. destruct H0. destruct s ; subst.
    repeat rewrite count_occ_app in Heqn. simpl in Heqn. repeat rewrite replace_app in H.
    simpl in H. destruct (eq_dec_form (A --> B) (A --> B)). 2: exfalso ; auto.
    assert (n = count_occ eq_dec_form (x ++ x0) (A --> B)). repeat rewrite count_occ_app ; lia.
    pose (IHn (x ++ B :: x0, l0) s1 A B). simpl in i.
    repeat rewrite count_occ_app in i. simpl in i. repeat rewrite replace_app in i.
    simpl in i. destruct (eq_dec_form B (A --> B)). exfalso. assert (length_form (A --> B) = length_form B). rewrite <- e0 ; auto.
    simpl in H1 ; lia. destruct (eq_dec_form (A --> B) B). exfalso ; auto. repeat rewrite count_occ_app in H0. pose (i H0 H).
    apply ImpRule_Canopy with (prems:=[(x ++ x0, A :: l0);(x ++ B :: x0, l0)]) (prem:=(x ++ B :: x0, l0)) ; auto.
     right. epose (ImpLRule_I _ _ _ _ []). simpl in i1 ; apply i1. apply InT_cons ; apply InT_eq.
  Qed.

  Lemma mult_ImpL_L : forall s0 s1 A B,
          InT s1 (Canopy (remove eq_dec_form (A --> B) (fst s0), repeat A (count_occ eq_dec_form (fst s0) (A --> B)) ++ (snd s0)))->
          InT s1 (Canopy s0).
  Proof.
  intros s0 s1 A B. remember (count_occ eq_dec_form (fst s0) (A --> B)) as n. revert Heqn. generalize dependent B.
  generalize dependent A. generalize dependent s1. generalize dependent s0. induction n ; simpl ; intros.
  - symmetry in Heqn. rewrite <- count_occ_not_In in Heqn. rewrite notin_remove in H ; auto. destruct s0 ; auto.
  - assert (count_occ eq_dec_form (fst s0) (A --> B) > 0). lia. apply count_occ_In in H0. destruct s0. simpl in H0.
    simpl in H. simpl in Heqn. apply In_InT in H0. apply InT_split in H0. destruct H0. destruct s ; subst.
    repeat rewrite count_occ_app in Heqn. simpl in Heqn. repeat rewrite remove_app in H.
    simpl in H. destruct (eq_dec_form (A --> B) (A --> B)). 2: exfalso ; auto.
    assert (n = count_occ eq_dec_form (x ++ x0) (A --> B)). repeat rewrite count_occ_app ; lia.
    pose (IHn (x ++ x0, A :: l0) s1 A B). simpl in i. repeat rewrite count_occ_app in i. repeat rewrite remove_app in i.
    repeat rewrite count_occ_app in H0. pose (i H0).
    assert (repeat A n ++ A :: l0 = A :: repeat A n ++ l0). assert (repeat A n ++ A :: l0 = (repeat A n ++ [A]) ++ l0).
    rewrite <- app_assoc. auto. rewrite H1. rewrite <- repeat_cons. simpl ; auto. rewrite H1 in i0. apply i0 in H.
    apply ImpRule_Canopy with (prems:=[(x ++ x0, A :: l0);(x ++ B :: x0, l0)]) (prem:=(x ++ x0, A :: l0)) ; auto.
    right. epose (ImpLRule_I _ _ _ _ []). simpl in i1 ; apply i1. apply InT_eq.
  Qed.
