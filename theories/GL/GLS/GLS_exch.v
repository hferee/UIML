Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import GLS_calcs.

Delimit Scope My_scope with M.
Open Scope My_scope.
Set Implicit Arguments.

(* First, as we want to mimick sequents based on multisets of formulae we need to
obtain exchange. *)

(* Definition of exchange with lists of formulae directly. It is more general and
makes the proofs easier to handle. *)

Inductive list_exch_L : relationT Seq :=
  | list_exch_LI Γ0 Γ1 Γ2 Γ3 Γ4 Δ : list_exch_L
      (Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4, Δ) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, Δ).

Inductive list_exch_R : relationT Seq :=
  | list_exch_RI Γ Δ0 Δ1 Δ2 Δ3 Δ4 : list_exch_R
        (Γ, Δ0 ++ Δ1 ++ Δ2 ++ Δ3 ++ Δ4) (Γ, Δ0 ++ Δ3 ++ Δ2 ++ Δ1 ++ Δ4).

(* Some lemmas about In and exchange. *)

Lemma InT_list_exch_R : forall l0 l1 l2,
            (@list_exch_R (l0,l1) (l0,l2)) ->
            (forall x, (InT x l1 -> InT x l2) * (InT x l2 -> InT x l1)).
Proof.
intros l0 l1 l2 exch. inversion exch.
intro x. split.
- intro. apply InT_app_or in H2. destruct H2. apply InT_or_app. left. assumption.
  apply InT_app_or in i. destruct i. apply InT_or_app. right. apply InT_or_app. right.
  apply InT_or_app. right. apply InT_or_app. left. assumption. apply InT_app_or in i.
  destruct i. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. left.
  assumption. apply InT_app_or in i. destruct i. apply InT_or_app. right. apply InT_or_app.
  left. assumption. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. right.
  assumption.
- intro. apply InT_app_or in H2. destruct H2. apply InT_or_app. left. assumption.
  apply InT_app_or in i. destruct i. apply InT_or_app. right. apply InT_or_app. right.
  apply InT_or_app. right. apply InT_or_app. left. assumption. apply InT_app_or in i.
  destruct i. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. left.
  assumption. apply InT_app_or in i. destruct i. apply InT_or_app. right. apply InT_or_app.
  left. assumption. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. right.
  assumption.
Qed.

Lemma InT_list_exch_L : forall l0 l1 l2,
            (@list_exch_L (l1,l0) (l2,l0)) ->
            (forall x, (InT x l1 -> InT x l2) * (InT x l2 -> InT x l1)).
Proof.
intros l0 l1 l2 exch. inversion exch.
intro x. split.
- intro. apply InT_app_or in H2. destruct H2. apply InT_or_app. left. assumption.
  apply InT_app_or in i. destruct i. apply InT_or_app. right. apply InT_or_app. right.
  apply InT_or_app. right. apply InT_or_app. left. assumption. apply InT_app_or in i.
  destruct i. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. left.
  assumption. apply InT_app_or in i. destruct i. apply InT_or_app. right. apply InT_or_app.
  left. assumption. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. right.
  assumption.
- intro. apply InT_app_or in H2. destruct H2. apply InT_or_app. left. assumption.
  apply InT_app_or in i. destruct i. apply InT_or_app. right. apply InT_or_app. right.
  apply InT_or_app. right. apply InT_or_app. left. assumption. apply InT_app_or in i.
  destruct i. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. left.
  assumption. apply InT_app_or in i. destruct i. apply InT_or_app. right. apply InT_or_app.
  left. assumption. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. right.
  assumption.
Qed.

(* Some useful lemmas about list exchange. *)

Lemma list_exch_R_id : forall s, (@list_exch_R s s).
Proof.
intros s. destruct s. pose (list_exch_RI l l0
[] [] [] []). simpl in l1. assert (H: l0 ++ [] = l0).
apply app_nil_r. rewrite H in l1. assumption.
Qed.


Lemma list_exch_L_id : forall s, (@list_exch_L s s).
Proof.
intros s. destruct s. pose (list_exch_LI l
[] [] [] [] l0). simpl in l1. assert (H: l ++ [] = l).
apply app_nil_r. rewrite H in l1. assumption.
Qed.

Lemma list_exch_R_same_L: forall s se,
    (@list_exch_R s se) ->
    (forall Γ Γe Δ Δe, (s = (Γ , Δ)) ->
    (se = (Γe , Δe)) ->
    (Γ = Γe)).
Proof.
intros s se exch. induction exch. intros Γ0 Γe Δ Δe E1 E2.
inversion E1. inversion E2. rewrite H0 in H2. assumption.
Qed.

Lemma list_exch_L_same_R : forall s se,
    (@list_exch_L s se) ->
    (forall Γ Γe Δ Δe, (s = (Γ , Δ)) ->
    (se = (Γe , Δe)) ->
    (Δ = Δe)).
Proof.
intros s se exch. induction exch. intros Γ Γe Δ0 Δe E1 E2.
inversion E1. inversion E2. rewrite H1 in H3. assumption.
Qed.

Lemma list_exch_R_permL : forall s se,
    (@list_exch_R s se) ->
      (forall Γ0 Γ1 Δ C, s = ((Γ0 ++ C :: Γ1), Δ) ->
      (existsT2 eΔ, se = ((Γ0 ++ C :: Γ1), eΔ))).
Proof.
intros s se exch. induction exch. intros Γ0 Γ1 Δ C E.
inversion E. exists (Δ0 ++ Δ3 ++ Δ2 ++ Δ1 ++ Δ4). reflexivity.
Qed.

Lemma list_exch_R_permR : forall s se,
    (@list_exch_R s se) ->
      (forall Γ Δ0 Δ1 C, s = (Γ, (Δ0 ++ C :: Δ1)) ->
      (existsT2 eΔ0 eΔ1, se = (Γ, (eΔ0 ++ C :: eΔ1)))).
Proof.
intros s se exch. induction exch. intros Γ0 Δ5 Δ6 C E.
inversion E. apply partition_1_element in H1. destruct H1.
+ destruct s. destruct s. rewrite e. exists x. exists (x0 ++ Δ3 ++ Δ2 ++ Δ1 ++ Δ4).
  simpl.
  assert (E1: (x ++ C :: x0) ++ Δ3 ++ Δ2 ++ Δ1 ++ Δ4 = x ++ C :: x0 ++ Δ3 ++ Δ2 ++ Δ1 ++ Δ4).
  { symmetry. apply app_assoc with (l:=x) (m:=C :: x0) (n:=Δ3 ++ Δ2 ++ Δ1 ++ Δ4). }
  rewrite E1. reflexivity.
+ destruct s.
  * destruct s. destruct s. exists (Δ0 ++ Δ3 ++ Δ2 ++ x). exists (x0 ++ Δ4).
    rewrite e. assert (E1: Δ0 ++ Δ3 ++ Δ2 ++ (x ++ C :: x0) ++ Δ4 =
    (Δ0 ++ Δ3 ++ Δ2 ++ x) ++ C :: x0 ++ Δ4).
    pose (app_assoc x (C :: x0) Δ4). rewrite <- e0. simpl.
    pose (app_assoc (Δ0 ++ Δ3 ++ Δ2) x (C :: x0 ++ Δ4)).
    pose (app_assoc (Δ0 ++ Δ3) Δ2 x).
    pose (app_assoc Δ0 Δ3 Δ2).
    rewrite <- e3 in e2. rewrite <- e2 in e1.
    pose (app_assoc Δ0 Δ3 (Δ2 ++ x)). rewrite <- e4 in e1. rewrite <- e1.
    pose (app_assoc (Δ0 ++ Δ3) Δ2 (x ++ C :: x0 ++ Δ4)).
    rewrite <- e3 in e5. rewrite <- e5.
    pose (app_assoc Δ0 Δ3 (Δ2 ++ x ++ C :: x0 ++ Δ4)). rewrite e6. reflexivity.
    rewrite E1. reflexivity.
  * destruct s.
    - destruct s. destruct s. exists (Δ0 ++ Δ3 ++ x). exists (x0 ++ Δ1 ++ Δ4).
      rewrite e. assert (E1: Δ0 ++ Δ3 ++ (x ++ C :: x0) ++ Δ1 ++ Δ4 =
      (Δ0 ++ Δ3 ++ x) ++ C :: x0 ++ Δ1 ++ Δ4).
      pose (app_assoc x (C :: x0) (Δ1 ++ Δ4)). rewrite <- e0. simpl.
      pose (app_assoc (Δ0 ++ Δ3) x (C :: x0 ++ Δ1 ++ Δ4)).
      pose (app_assoc Δ0 Δ3 x). rewrite <- e2 in e1. rewrite <- e1.
      pose (app_assoc Δ0 Δ3 (x ++ C :: x0 ++ Δ1 ++ Δ4)). rewrite <- e3.
      reflexivity. rewrite E1. reflexivity.
    - destruct s.
      { destruct s. destruct s. rewrite e. exists (Δ0 ++ x). exists (x0 ++ Δ2 ++ Δ1 ++ Δ4).
        assert (E1: Δ0 ++ (x ++ C :: x0) ++ Δ2 ++ Δ1 ++ Δ4 =
        (Δ0 ++ x) ++ C :: x0 ++ Δ2 ++ Δ1 ++ Δ4).
        pose (app_assoc x (C :: x0) (Δ2 ++ Δ1 ++ Δ4)). rewrite <- e0. simpl.
        pose (app_assoc Δ0 x (C :: x0 ++ Δ2 ++ Δ1 ++ Δ4)). rewrite e1.
        reflexivity. rewrite E1. reflexivity. }
      { destruct s. destruct s. rewrite e. exists (Δ0 ++ Δ3 ++ Δ2 ++ Δ1 ++ x).
        exists x0. assert (E1: Δ0 ++ Δ3 ++ Δ2 ++ Δ1 ++ x ++ C :: x0 =
        (Δ0 ++ Δ3 ++ Δ2 ++ Δ1 ++ x) ++ C :: x0).
        pose (app_assoc (Δ0 ++ Δ3 ++ Δ2 ++ Δ1) x (C :: x0)).
        pose (app_assoc (Δ0 ++ Δ3 ++ Δ2) Δ1 x).
        pose (app_assoc (Δ0 ++ Δ3) Δ2 Δ1).
        pose (app_assoc Δ0 Δ3 Δ2). rewrite <- e3 in e2. rewrite <- e2 in e1.
        pose (app_assoc Δ0 Δ3 (Δ2 ++ Δ1)). rewrite <- e4 in e1. rewrite <- e1 in e0.
        pose (app_assoc (Δ0 ++ Δ3) Δ2 (Δ1 ++ x)). rewrite <- e3 in e5.
        rewrite <- e5 in e0.
        pose (app_assoc Δ0 Δ3 (Δ2 ++ Δ1 ++ x)). rewrite <- e6 in e0.
        rewrite <- e0.
        pose (app_assoc (Δ0 ++ Δ3 ++ Δ2) Δ1 (x ++ C :: x0)).
        rewrite <- e2 in e7. rewrite <- e4 in e7. rewrite <- e7.
        pose (app_assoc (Δ0 ++ Δ3) Δ2 (Δ1 ++ x ++ C :: x0)).
        rewrite <- e3 in e8. rewrite <- e8.
        pose (app_assoc Δ0 Δ3 (Δ2 ++ Δ1 ++ x ++ C :: x0)).
        rewrite e9. reflexivity. rewrite E1. reflexivity. }
Qed.

Lemma list_exch_R_permLR : forall s se,
    (@list_exch_R s se) ->
      (forall Γ0 Γ1 Δ0 Δ1 C D, s = ((Γ0 ++ C :: Γ1), (Δ0 ++ D :: Δ1)) ->
      (existsT2 eΔ0 eΔ1, se = ((Γ0 ++ C :: Γ1), (eΔ0 ++ D :: eΔ1)))).
Proof.
intros s se exch. intros Γ0 Γ1 Δ0 Δ1 C D Eq.
pose (list_exch_R_permL exch). pose (s0 Γ0 Γ1 (Δ0 ++ D :: Δ1) C).
pose (s1 Eq). destruct s2.
pose (list_exch_R_permR exch). pose (s2 (Γ0 ++ C :: Γ1) Δ0 Δ1 D).
pose (s3 Eq). destruct s4. destruct s4. exists x0. exists x1. assumption.
Qed.

Lemma list_exch_L_permL : forall s se,
    (@list_exch_L s se) ->
      (forall Γ0 Γ1 Δ C, s = ((Γ0 ++ C :: Γ1), Δ) ->
      (existsT2 eΓ0 eΓ1, se = ((eΓ0 ++ C :: eΓ1), Δ))).
Proof.
intros s se exch. induction exch. intros Γ5 Γ6 Δ0 C E.
inversion E. apply partition_1_element in H0. destruct H0.
+ destruct s. destruct s. rewrite e. exists x. exists (x0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4).
  simpl.
  assert (E1: (x ++ C :: x0) ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4 = x ++ C :: x0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4).
  { symmetry. apply app_assoc with (l:=x) (m:=C :: x0) (n:=Γ3 ++ Γ2 ++ Γ1 ++ Γ4). }
  rewrite E1. reflexivity.
+ destruct s.
  * destruct s. destruct s. exists (Γ0 ++ Γ3 ++ Γ2 ++ x). exists (x0 ++ Γ4).
    rewrite e. assert (E1: Γ0 ++ Γ3 ++ Γ2 ++ (x ++ C :: x0) ++ Γ4 =
    (Γ0 ++ Γ3 ++ Γ2 ++ x) ++ C :: x0 ++ Γ4).
    pose (app_assoc x (C :: x0) Γ4). rewrite <- e0. simpl.
    pose (app_assoc (Γ0 ++ Γ3 ++ Γ2) x (C :: x0 ++ Γ4)).
    pose (app_assoc (Γ0 ++ Γ3) Γ2 x).
    pose (app_assoc Γ0 Γ3 Γ2).
    rewrite <- e3 in e2. rewrite <- e2 in e1.
    pose (app_assoc Γ0 Γ3 (Γ2 ++ x)). rewrite <- e4 in e1. rewrite <- e1.
    pose (app_assoc (Γ0 ++ Γ3) Γ2 (x ++ C :: x0 ++ Γ4)).
    rewrite <- e3 in e5. rewrite <- e5.
    pose (app_assoc Γ0 Γ3 (Γ2 ++ x ++ C :: x0 ++ Γ4)). rewrite e6. reflexivity.
    rewrite E1. reflexivity.
  * destruct s.
    - destruct s. destruct s. exists (Γ0 ++ Γ3 ++ x). exists (x0 ++ Γ1 ++ Γ4).
      rewrite e. assert (E1: Γ0 ++ Γ3 ++ (x ++ C :: x0) ++ Γ1 ++ Γ4 =
      (Γ0 ++ Γ3 ++ x) ++ C :: x0 ++ Γ1 ++ Γ4).
      pose (app_assoc x (C :: x0) (Γ1 ++ Γ4)). rewrite <- e0. simpl.
      pose (app_assoc (Γ0 ++ Γ3) x (C :: x0 ++ Γ1 ++ Γ4)).
      pose (app_assoc Γ0 Γ3 x). rewrite <- e2 in e1. rewrite <- e1.
      pose (app_assoc Γ0 Γ3 (x ++ C :: x0 ++ Γ1 ++ Γ4)). rewrite <- e3.
      reflexivity. rewrite E1. reflexivity.
    - destruct s.
      { destruct s. destruct s. rewrite e. exists (Γ0 ++ x). exists (x0 ++ Γ2 ++ Γ1 ++ Γ4).
        assert (E1: Γ0 ++ (x ++ C :: x0) ++ Γ2 ++ Γ1 ++ Γ4 =
        (Γ0 ++ x) ++ C :: x0 ++ Γ2 ++ Γ1 ++ Γ4).
        pose (app_assoc x (C :: x0) (Γ2 ++ Γ1 ++ Γ4)). rewrite <- e0. simpl.
        pose (app_assoc Γ0 x (C :: x0 ++ Γ2 ++ Γ1 ++ Γ4)). rewrite e1.
        reflexivity. rewrite E1. reflexivity. }
      { destruct s. destruct s. rewrite e. exists (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ x).
        exists x0. assert (E1: Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ x ++ C :: x0 =
        (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ x) ++ C :: x0).
        pose (app_assoc (Γ0 ++ Γ3 ++ Γ2 ++ Γ1) x (C :: x0)).
        pose (app_assoc (Γ0 ++ Γ3 ++ Γ2) Γ1 x).
        pose (app_assoc (Γ0 ++ Γ3) Γ2 Γ1).
        pose (app_assoc Γ0 Γ3 Γ2). rewrite <- e3 in e2. rewrite <- e2 in e1.
        pose (app_assoc Γ0 Γ3 (Γ2 ++ Γ1)). rewrite <- e4 in e1. rewrite <- e1 in e0.
        pose (app_assoc (Γ0 ++ Γ3) Γ2 (Γ1 ++ x)). rewrite <- e3 in e5.
        rewrite <- e5 in e0.
        pose (app_assoc Γ0 Γ3 (Γ2 ++ Γ1 ++ x)). rewrite <- e6 in e0.
        rewrite <- e0.
        pose (app_assoc (Γ0 ++ Γ3 ++ Γ2) Γ1 (x ++ C :: x0)).
        rewrite <- e2 in e7. rewrite <- e4 in e7. rewrite <- e7.
        pose (app_assoc (Γ0 ++ Γ3) Γ2 (Γ1 ++ x ++ C :: x0)).
        rewrite <- e3 in e8. rewrite <- e8.
        pose (app_assoc Γ0 Γ3 (Γ2 ++ Γ1 ++ x ++ C :: x0)).
        rewrite e9. reflexivity. rewrite E1. reflexivity. }
Qed.

Lemma list_exch_L_permR : forall s se,
    (@list_exch_L s se) ->
      (forall Γ Δ0 Δ1 C, s = (Γ, (Δ0 ++ C :: Δ1)) ->
      (existsT2 eΓ, se = (eΓ, (Δ0 ++ C :: Δ1)))).
Proof.
intros s se exch. induction exch. intros Γ Δ0 Δ1 C E.
inversion E. exists (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4). reflexivity.
Qed.

Lemma list_exch_L_permLR : forall s se,
    (@list_exch_L s se) ->
      (forall Γ0 Γ1 Δ0 Δ1 C D, s = ((Γ0 ++ C :: Γ1), (Δ0 ++ D :: Δ1)) ->
      (existsT2 eΓ0 eΓ1, se = ((eΓ0 ++ C :: eΓ1), (Δ0 ++ D :: Δ1)))).
Proof.
intros s se exch. intros Γ0 Γ1 Δ0 Δ1 C D Eq.
pose (list_exch_L_permR exch). pose (s0 (Γ0 ++ C :: Γ1) Δ0 Δ1 D).
pose (s1 Eq). destruct s2.
pose (list_exch_L_permL exch). pose (s2 Γ0 Γ1 (Δ0 ++ D :: Δ1) C).
pose (s3 Eq). destruct s4. destruct s4. exists x0. exists x1. assumption.
Qed.

(* Some lemmas about atomic generalized extensions of lists and exchange. *)

Lemma nobox_gen_ext_exch_R : forall Γ Γ' l0 l1 l2,
    (nobox_gen_ext l0 l1) -> (@list_exch_R (Γ,l1) (Γ,l2)) ->
    existsT2 l3, (nobox_gen_ext l3 l2) * (list_exch_R (Γ',l0) (Γ',l3)).
Proof.
intros Γ Γ' l0. induction l0.
+ intros l1 l2 gen. remember [] as l0. destruct gen.
  - intro exch. inversion exch. apply app_eq_nil in H1. destruct H1. apply app_eq_nil in H2. destruct H2.
    apply app_eq_nil in H3. destruct H3. apply app_eq_nil in H4. destruct H4.
    subst. simpl. exists []. split.
    * apply univ_gen_ext_nil.
    * apply list_exch_R_id.
  - intros exch. exists []. split.
    * inversion Heql0.
    * inversion Heql0.
  - intro exch. subst. exists []. split. apply all_P_univ_gen_ext_nil.
    intros. pose (InT_list_exch_R exch). pose (p x0). destruct p0. pose (univ_gen_ext_nil_all_P gen).
    pose (f0 x0). apply i0 in H. inversion H. subst. apply f. assumption. subst. apply f1 in H1.
    assumption. assumption.
    apply list_exch_R_id.
+ intros l1 l2 gen. induction gen.
  - intro exch. inversion exch. destruct Δ0.
    * rewrite app_nil_l in H. rewrite app_nil_l in H1. rewrite app_nil_l. destruct Δ1.
      { rewrite app_nil_l in H1. destruct Δ2.
        + rewrite app_nil_l in H1. destruct Δ3.
          - rewrite app_nil_l in H1. repeat rewrite app_nil_l in H. destruct Δ4.
            * simpl. exists []. split. apply univ_gen_ext_nil. apply list_exch_R_id.
            * inversion H1.
          - inversion H1.
        + inversion H1. }
      { inversion H1. }
    * inversion H1.
  - intro exch. inversion exch. destruct Δ0.
    * rewrite app_nil_l in H. rewrite app_nil_l in H1. rewrite app_nil_l. destruct Δ1.
      { rewrite app_nil_l in H1. destruct Δ2.
        + rewrite app_nil_l in H1. destruct Δ3.
          - rewrite app_nil_l in H1. repeat rewrite app_nil_l in H. destruct Δ4.
            * inversion H1.
            * inversion H1. simpl. subst. exists (x :: l).
              split. apply univ_gen_ext_cons. assumption. apply list_exch_R_id.
          - repeat rewrite app_nil_l in H. repeat rewrite app_nil_l. simpl. simpl in H. simpl in H1.
            inversion H1. subst. exists (x :: l). split. apply univ_gen_ext_cons. assumption. apply list_exch_R_id.
        + rewrite app_nil_l. rewrite app_nil_l in H. inversion H1. subst.
          pose (univ_gen_ext_splitR _ _ gen). repeat destruct s. repeat destruct p.
          pose (univ_gen_ext_splitR _ _ u0). repeat destruct s. repeat destruct p. subst.
          exists (x2 ++ x :: x0 ++ x3). split.
          - apply univ_gen_ext_cons with (x:=x) in u. pose (univ_gen_ext_combine u u2).
            pose (univ_gen_ext_combine u1 u3). assumption.
          - pose (list_exch_RI Γ' [] [] (x :: x0) x2 x3). repeat rewrite app_nil_l in l. assumption. }
      { inversion H1. subst. pose (univ_gen_ext_splitR _ _ gen). repeat destruct s. repeat destruct p.
        pose (univ_gen_ext_splitR _ _ u0). repeat destruct s. repeat destruct p. pose (univ_gen_ext_splitR _ _ u2).
        repeat destruct s. repeat destruct p. subst. exists (x4 ++ x2 ++ (x :: x0) ++ x5).
        split.
        - apply univ_gen_ext_cons with (x:=x) in u. pose (univ_gen_ext_combine u u4).
          pose (univ_gen_ext_combine u1 u5). pose (univ_gen_ext_combine u3 u6). assumption.
        - pose (list_exch_RI Γ' [] (x :: x0) x2 x4 x5). rewrite app_nil_l in l. assumption. }
    * inversion H1. subst. pose (univ_gen_ext_splitR _ _ gen).
      repeat destruct s. repeat destruct p. pose (univ_gen_ext_splitR _ _ u0).
      repeat destruct s. repeat destruct p. pose (univ_gen_ext_splitR _ _ u2).
      repeat destruct s. repeat destruct p. pose (univ_gen_ext_splitR _ _ u4).
      repeat destruct s. repeat destruct p. subst. exists (x :: x0 ++ x6 ++ x4 ++ x2 ++ x7).
      split.
      { apply univ_gen_ext_cons with (x:=x) in u. pose (univ_gen_ext_combine u1 u6).
        pose (univ_gen_ext_combine u3 u7). pose (univ_gen_ext_combine u5 u8).
        pose (univ_gen_ext_combine u u9). assumption. }
      { assert (E1: x :: x0 ++ x2 ++ x4 ++ x6 ++ x7 = (x :: x0) ++ x2 ++ x4 ++ x6 ++ x7).
        reflexivity. rewrite E1.
        assert (E2: x :: x0 ++ x6 ++ x4 ++ x2 ++ x7 = (x :: x0) ++ x6 ++ x4 ++ x2 ++ x7).
        reflexivity. rewrite E2. apply list_exch_RI. }
  - intro exch. inversion exch. destruct Δ0.
    * rewrite app_nil_l in H. rewrite app_nil_l in H1. rewrite app_nil_l. destruct Δ1.
      { rewrite app_nil_l in H1. destruct Δ2.
        + rewrite app_nil_l in H1. destruct Δ3.
          - rewrite app_nil_l in H1. repeat rewrite app_nil_l in H. destruct Δ4.
            * inversion H1.
            * inversion H1. simpl. subst. exists l.
              split. apply univ_gen_ext_extra. assumption. assumption. apply list_exch_R_id.
          - repeat rewrite app_nil_l in H. repeat rewrite app_nil_l. simpl. simpl in H. simpl in H1.
            inversion H1. subst. exists l. split. apply univ_gen_ext_extra. assumption. assumption. apply list_exch_R_id.
        + rewrite app_nil_l. rewrite app_nil_l in H. inversion H1. subst.
          pose (univ_gen_ext_splitR _ _ gen). repeat destruct s. repeat destruct p0.
          pose (univ_gen_ext_splitR _ _ u0). repeat destruct s. repeat destruct p0. subst.
          exists (x2 ++ x0 ++ x3). split.
          - apply univ_gen_ext_extra with (x:=x) in u. pose (univ_gen_ext_combine u u2).
            pose (univ_gen_ext_combine u1 u3). assumption. assumption.
          - pose (list_exch_RI Γ' [] [] x0 x2 x3). repeat rewrite app_nil_l in l. assumption. }
      { inversion H1. subst. pose (univ_gen_ext_splitR _ _ gen). repeat destruct s. repeat destruct p0.
        pose (univ_gen_ext_splitR _ _ u0). repeat destruct s. repeat destruct p0. pose (univ_gen_ext_splitR _ _ u2).
        repeat destruct s. repeat destruct p0. subst. exists (x4 ++ x2 ++ x0 ++ x5).
        split.
        - apply univ_gen_ext_extra with (x:=x) in u. pose (univ_gen_ext_combine u u4).
          pose (univ_gen_ext_combine u1 u5). pose (univ_gen_ext_combine u3 u6). assumption. assumption.
        - pose (list_exch_RI Γ' [] x0 x2 x4 x5). rewrite app_nil_l in l. assumption. }
    * inversion H1. subst. pose (univ_gen_ext_splitR _ _ gen).
      repeat destruct s. repeat destruct p0. pose (univ_gen_ext_splitR _ _ u0).
      repeat destruct s. repeat destruct p0. pose (univ_gen_ext_splitR _ _ u2).
      repeat destruct s. repeat destruct p0. pose (univ_gen_ext_splitR _ _ u4).
      repeat destruct s. repeat destruct p0. subst. exists (x0 ++ x6 ++ x4 ++ x2 ++ x7).
      split.
      { apply univ_gen_ext_extra with (x:=x) in u. pose (univ_gen_ext_combine u1 u6).
        pose (univ_gen_ext_combine u3 u7). pose (univ_gen_ext_combine u5 u8).
        pose (univ_gen_ext_combine u u9). assumption. assumption. }
      { apply list_exch_RI. }
Qed.

Lemma nobox_gen_ext_exch_L : forall Δ Δ' l0 l1 l2,
    (nobox_gen_ext l0 l1) -> (@list_exch_L (l1,Δ) (l2,Δ)) ->
    existsT2 l3, (nobox_gen_ext l3 l2) * (list_exch_L (l0,Δ') (l3,Δ')).
Proof.
intros Δ Δ' l0. induction l0.
+ intros l1 l2 gen. inversion gen.
  - intro exch. inversion exch. apply app_eq_nil in H1. destruct H1. apply app_eq_nil in H3. destruct H3.
    apply app_eq_nil in H4. destruct H4. apply app_eq_nil in H5. destruct H5.
    subst. simpl. exists []. split.
    * apply univ_gen_ext_nil.
    * apply list_exch_L_id.
  - intros exch. exists []. split.
    * subst. apply all_P_univ_gen_ext_nil. intros. pose (InT_list_exch_L exch).
      pose (p x0). destruct p0. apply i0 in H0. inversion H0. subst. apply H.
      assumption. subst. pose (univ_gen_ext_nil_all_P gen). apply f in H0.
      assumption. assumption.
    * apply list_exch_L_id.
+ intros l1 l2 gen. induction gen.
  - intro exch. inversion exch. destruct Γ0.
    * rewrite app_nil_l in H0. rewrite app_nil_l in H. rewrite app_nil_l. destruct Γ1.
      { rewrite app_nil_l in H0. destruct Γ2.
        + rewrite app_nil_l in H0. destruct Γ3.
          - rewrite app_nil_l in H0. repeat rewrite app_nil_l in H. destruct Γ4.
            * simpl. exists []. split. apply univ_gen_ext_nil. apply list_exch_L_id.
            * inversion H0.
          - inversion H0.
        + inversion H0. }
      { inversion H0. }
    * inversion H0.
  - intro exch. inversion exch. destruct Γ0.
    * rewrite app_nil_l in H. rewrite app_nil_l in H0. rewrite app_nil_l. destruct Γ1.
      { rewrite app_nil_l in H0. destruct Γ2.
        + rewrite app_nil_l in H0. destruct Γ3.
          - rewrite app_nil_l in H0. repeat rewrite app_nil_l in H. destruct Γ4.
            * inversion H0.
            * inversion H0. simpl. subst. exists (x :: l).
              split. apply univ_gen_ext_cons. assumption. apply list_exch_L_id.
          - repeat rewrite app_nil_l in H. repeat rewrite app_nil_l. simpl. simpl in H. simpl in H0.
            inversion H0. subst. exists (x :: l). split. apply univ_gen_ext_cons. assumption. apply list_exch_L_id.
        + rewrite app_nil_l. rewrite app_nil_l in H. inversion H0. subst.
          pose (univ_gen_ext_splitR _ _ gen). repeat destruct s. repeat destruct p.
          pose (univ_gen_ext_splitR _ _ u0). repeat destruct s. repeat destruct p. subst.
          exists (x2 ++ x :: x0 ++ x3). split.
          - apply univ_gen_ext_cons with (x:=x) in u. pose (univ_gen_ext_combine u u2).
            pose (univ_gen_ext_combine u1 u3). assumption.
          - pose (list_exch_LI [] [] (x :: x0) x2 x3 Δ'). repeat rewrite app_nil_l in l. assumption. }
      { inversion H0. subst. pose (univ_gen_ext_splitR _ _ gen). repeat destruct s. repeat destruct p.
        pose (univ_gen_ext_splitR _ _ u0). repeat destruct s. repeat destruct p. pose (univ_gen_ext_splitR _ _ u2).
        repeat destruct s. repeat destruct p. subst. exists (x4 ++ x2 ++ (x :: x0) ++ x5).
        split.
        - apply univ_gen_ext_cons with (x:=x) in u. pose (univ_gen_ext_combine u u4).
          pose (univ_gen_ext_combine u1 u5). pose (univ_gen_ext_combine u3 u6). assumption.
        - pose (list_exch_LI [] (x :: x0) x2 x4 x5 Δ'). rewrite app_nil_l in l. assumption. }
    * inversion H0. subst. pose (univ_gen_ext_splitR _ _ gen).
      repeat destruct s. repeat destruct p. pose (univ_gen_ext_splitR _ _ u0).
      repeat destruct s. repeat destruct p. pose (univ_gen_ext_splitR _ _ u2).
      repeat destruct s. repeat destruct p. pose (univ_gen_ext_splitR _ _ u4).
      repeat destruct s. repeat destruct p. subst. exists (x :: x0 ++ x6 ++ x4 ++ x2 ++ x7).
      split.
      { apply univ_gen_ext_cons with (x:=x) in u. pose (univ_gen_ext_combine u1 u6).
        pose (univ_gen_ext_combine u3 u7). pose (univ_gen_ext_combine u5 u8).
        pose (univ_gen_ext_combine u u9). assumption. }
      { assert (E1: x :: x0 ++ x2 ++ x4 ++ x6 ++ x7 = (x :: x0) ++ x2 ++ x4 ++ x6 ++ x7).
        reflexivity. rewrite E1.
        assert (E2: x :: x0 ++ x6 ++ x4 ++ x2 ++ x7 = (x :: x0) ++ x6 ++ x4 ++ x2 ++ x7).
        reflexivity. rewrite E2. apply list_exch_LI. }
  - intro exch. inversion exch. destruct Γ0.
    * rewrite app_nil_l in H. rewrite app_nil_l in H0. rewrite app_nil_l. destruct Γ1.
      { rewrite app_nil_l in H0. destruct Γ2.
        + rewrite app_nil_l in H0. destruct Γ3.
          - rewrite app_nil_l in H0. repeat rewrite app_nil_l in H. destruct Γ4.
            * inversion H0.
            * inversion H0. simpl. subst. exists l.
              split. apply univ_gen_ext_extra. assumption. assumption. apply list_exch_L_id.
          - repeat rewrite app_nil_l in H. repeat rewrite app_nil_l. simpl. simpl in H. simpl in H0.
            inversion H0. subst. exists l. split. apply univ_gen_ext_extra. assumption. assumption. apply list_exch_L_id.
        + rewrite app_nil_l. rewrite app_nil_l in H. inversion H0. subst.
          pose (univ_gen_ext_splitR _ _ gen). repeat destruct s. repeat destruct p0.
          pose (univ_gen_ext_splitR _ _ u0). repeat destruct s. repeat destruct p0. subst.
          exists (x2 ++ x0 ++ x3). split.
          - apply univ_gen_ext_extra with (x:=x) in u. pose (univ_gen_ext_combine u u2).
            pose (univ_gen_ext_combine u1 u3). assumption. assumption.
          - pose (list_exch_LI [] [] x0 x2 x3 Δ'). repeat rewrite app_nil_l in l. assumption. }
      { inversion H0. subst. pose (univ_gen_ext_splitR _ _ gen). repeat destruct s. repeat destruct p0.
        pose (univ_gen_ext_splitR _ _ u0). repeat destruct s. repeat destruct p0. pose (univ_gen_ext_splitR _ _ u2).
        repeat destruct s. repeat destruct p0. subst. exists (x4 ++ x2 ++ x0 ++ x5).
        split.
        - apply univ_gen_ext_extra with (x:=x) in u. pose (univ_gen_ext_combine u u4).
          pose (univ_gen_ext_combine u1 u5). pose (univ_gen_ext_combine u3 u6). assumption. assumption.
        - pose (list_exch_LI [] x0 x2 x4 x5 Δ'). rewrite app_nil_l in l. assumption. }
    * inversion H0. subst. pose (univ_gen_ext_splitR _ _ gen).
      repeat destruct s. repeat destruct p0. pose (univ_gen_ext_splitR _ _ u0).
      repeat destruct s. repeat destruct p0. pose (univ_gen_ext_splitR _ _ u2).
      repeat destruct s. repeat destruct p0. pose (univ_gen_ext_splitR _ _ u4).
      repeat destruct s. repeat destruct p0. subst. exists (x0 ++ x6 ++ x4 ++ x2 ++ x7).
      split.
      { apply univ_gen_ext_extra with (x:=x) in u. pose (univ_gen_ext_combine u1 u6).
        pose (univ_gen_ext_combine u3 u7). pose (univ_gen_ext_combine u5 u8).
        pose (univ_gen_ext_combine u u9). assumption. assumption. }
      { apply list_exch_LI. }
Qed.

(* Interactions between exchange and rules. *)

Lemma list_exch_L_IdP_notapplic : forall s se,
    (@list_exch_L s se) ->
    ((IdPRule [] s) -> False) ->
    ((IdPRule [] se) -> False).
Proof.
intros s se exch. induction exch. intros RA RAe. apply RA.
inversion RAe. symmetry in H. apply partition_1_element in H.
destruct H.
- destruct s. destruct s. rewrite e.
  assert (E: (x ++ # P :: x0) ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4 =
  x ++ # P :: x0 ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4).
  pose (app_assoc x (# P :: x0) (Γ1 ++ Γ2 ++ Γ3 ++ Γ4)). rewrite <- e0.
  auto. rewrite E. apply IdPRule_I.
- destruct s.
  + destruct s. destruct s. rewrite e.
    assert (E: Γ0 ++ Γ1 ++ Γ2 ++ (x ++ # P :: x0) ++ Γ4 =
    Γ0 ++ Γ1 ++ Γ2 ++ x ++ # P :: x0 ++ Γ4).
    pose (app_assoc x (# P :: x0) Γ4).
    simpl in e0. rewrite <- e0. reflexivity. rewrite E.
    assert (E1: Γ0 ++ Γ1 ++ Γ2 ++ x ++ # P :: x0 ++ Γ4 =
    (Γ0 ++ Γ1 ++ Γ2 ++ x) ++ # P :: x0 ++ Γ4).
    pose (app_assoc (Γ0 ++ Γ1 ++ Γ2) x (# P :: x0 ++ Γ4)).
    pose (app_assoc (Γ0 ++ Γ1) Γ2 x).
    pose (app_assoc Γ0 Γ1 Γ2). rewrite <- e2 in e1. rewrite <- e1 in e0.
    pose (app_assoc Γ0 Γ1 (Γ2 ++ x)). rewrite <- e3 in e0. rewrite <- e0.
    pose (app_assoc (Γ0 ++ Γ1) Γ2 (x ++ # P :: x0 ++ Γ4)). rewrite <- e2 in e4.
    rewrite <- e4.
    pose (app_assoc Γ0 Γ1 (Γ2 ++ x ++ # P :: x0 ++ Γ4)). rewrite e5. reflexivity.
    rewrite E1. apply IdPRule_I.
  + destruct s.
    * destruct s. destruct s. rewrite e.
      assert (E: Γ0 ++ Γ1 ++ (x ++ # P :: x0) ++ Γ3 ++ Γ4 =
      (Γ0 ++ Γ1 ++ x) ++ # P :: x0 ++ Γ3 ++ Γ4).
      pose (app_assoc x (# P :: x0) (Γ3 ++ Γ4)). rewrite <- e0. simpl.
      pose (app_assoc (Γ0 ++ Γ1) x (# P :: x0 ++ Γ3 ++ Γ4)).
      pose (app_assoc Γ0 Γ1 x). rewrite <- e2 in e1. rewrite <- e1.
      pose (app_assoc Γ0 Γ1 (x ++ # P :: x0 ++ Γ3 ++ Γ4)). rewrite <- e3.
      reflexivity. rewrite E. apply IdPRule_I.
    * destruct s.
      { destruct s. destruct s. rewrite e.
        assert (E: Γ0 ++ (x ++ # P :: x0) ++ Γ2 ++ Γ3 ++ Γ4 =
        (Γ0 ++ x) ++ # P :: x0 ++ Γ2 ++ Γ3 ++ Γ4).
        pose (app_assoc x (# P :: x0) (Γ2 ++ Γ3 ++ Γ4)).
        rewrite <- e0. simpl.
        pose (app_assoc Γ0 x (# P :: x0 ++ Γ2 ++ Γ3 ++ Γ4)).
        rewrite <- e1. reflexivity. rewrite E. apply IdPRule_I. }
      { destruct s. destruct s. rewrite e.
        assert (E: Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ x ++ # P :: x0 =
        (Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ x) ++ # P :: x0).
        pose (app_assoc (Γ0 ++ Γ1 ++ Γ2 ++ Γ3) x (# P :: x0)).
        pose (app_assoc (Γ0 ++ Γ1 ++ Γ2) Γ3 x).
        pose (app_assoc (Γ0 ++ Γ1) Γ2 Γ3).
        pose (app_assoc Γ0 Γ1 Γ2).
        rewrite <- e3 in e2. rewrite <- e2 in e1.
        pose (app_assoc Γ0 Γ1 (Γ2 ++ Γ3)).
        rewrite <- e4 in e1. rewrite <- e1 in e0.
        pose (app_assoc (Γ0 ++ Γ1) Γ2 (Γ3 ++ x)).
        rewrite <- e3 in e5. rewrite <- e5 in e0.
        pose (app_assoc Γ0 Γ1 (Γ2 ++ Γ3 ++ x)).
        rewrite <- e6 in e0. rewrite <- e0.
        pose (app_assoc (Γ0 ++ Γ1 ++ Γ2) Γ3 (x ++ # P :: x0)).
        pose (app_assoc (Γ0 ++ Γ1) Γ2 Γ3).
        rewrite <- e3 in e8. rewrite <- e8 in e7.
        pose (app_assoc Γ0 Γ1 (Γ2 ++ Γ3)). rewrite <- e9 in e7.
        rewrite <- e7.
        pose (app_assoc (Γ0 ++ Γ1) Γ2 (Γ3 ++ x ++ # P :: x0)).
        rewrite <- e3 in e10. rewrite <- e10.
        pose (app_assoc Γ0 Γ1 (Γ2 ++ Γ3 ++ x ++ # P :: x0)).
        rewrite <- e11. reflexivity.
        rewrite E. apply IdPRule_I. }
Qed.

Lemma list_exch_L_IdB_notapplic : forall s se,
    (@list_exch_L s se) ->
    ((IdBRule [] s) -> False) ->
    ((IdBRule [] se) -> False).
Proof.
intros s se exch. induction exch. intros RA RAe. apply RA.
inversion RAe. symmetry in H. apply partition_1_element in H.
destruct H.
- destruct s. destruct s. rewrite e.
  assert (E: (x ++ Box A :: x0) ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4 =
  x ++ Box A :: x0 ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4).
  pose (app_assoc x (Box A :: x0) (Γ1 ++ Γ2 ++ Γ3 ++ Γ4)). rewrite <- e0.
  auto. rewrite E. apply IdBRule_I.
- destruct s.
  + destruct s. destruct s. rewrite e.
    assert (E: Γ0 ++ Γ1 ++ Γ2 ++ (x ++ Box A :: x0) ++ Γ4 =
    Γ0 ++ Γ1 ++ Γ2 ++ x ++ Box A :: x0 ++ Γ4).
    pose (app_assoc x (Box A :: x0) Γ4).
    simpl in e0. rewrite <- e0. reflexivity. rewrite E.
    assert (E1: Γ0 ++ Γ1 ++ Γ2 ++ x ++ Box A :: x0 ++ Γ4 =
    (Γ0 ++ Γ1 ++ Γ2 ++ x) ++ Box A :: x0 ++ Γ4).
    pose (app_assoc (Γ0 ++ Γ1 ++ Γ2) x (Box A :: x0 ++ Γ4)).
    pose (app_assoc (Γ0 ++ Γ1) Γ2 x).
    pose (app_assoc Γ0 Γ1 Γ2). rewrite <- e2 in e1. rewrite <- e1 in e0.
    pose (app_assoc Γ0 Γ1 (Γ2 ++ x)). rewrite <- e3 in e0. rewrite <- e0.
    pose (app_assoc (Γ0 ++ Γ1) Γ2 (x ++ Box A :: x0 ++ Γ4)). rewrite <- e2 in e4.
    rewrite <- e4.
    pose (app_assoc Γ0 Γ1 (Γ2 ++ x ++ Box A :: x0 ++ Γ4)). rewrite e5. reflexivity.
    rewrite E1. apply IdBRule_I.
  + destruct s.
    * destruct s. destruct s. rewrite e.
      assert (E: Γ0 ++ Γ1 ++ (x ++ Box A :: x0) ++ Γ3 ++ Γ4 =
      (Γ0 ++ Γ1 ++ x) ++ Box A :: x0 ++ Γ3 ++ Γ4).
      pose (app_assoc x (Box A :: x0) (Γ3 ++ Γ4)). rewrite <- e0. simpl.
      pose (app_assoc (Γ0 ++ Γ1) x (Box A :: x0 ++ Γ3 ++ Γ4)).
      pose (app_assoc Γ0 Γ1 x). rewrite <- e2 in e1. rewrite <- e1.
      pose (app_assoc Γ0 Γ1 (x ++ Box A :: x0 ++ Γ3 ++ Γ4)). rewrite <- e3.
      reflexivity. rewrite E. apply IdBRule_I.
    * destruct s.
      { destruct s. destruct s. rewrite e.
        assert (E: Γ0 ++ (x ++ Box A :: x0) ++ Γ2 ++ Γ3 ++ Γ4 =
        (Γ0 ++ x) ++ Box A :: x0 ++ Γ2 ++ Γ3 ++ Γ4).
        pose (app_assoc x (Box A :: x0) (Γ2 ++ Γ3 ++ Γ4)).
        rewrite <- e0. simpl.
        pose (app_assoc Γ0 x (Box A :: x0 ++ Γ2 ++ Γ3 ++ Γ4)).
        rewrite <- e1. reflexivity. rewrite E. apply IdBRule_I. }
      { destruct s. destruct s. rewrite e.
        assert (E: Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ x ++ Box A :: x0 =
        (Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ x) ++ Box A :: x0).
        pose (app_assoc (Γ0 ++ Γ1 ++ Γ2 ++ Γ3) x (Box A :: x0)).
        pose (app_assoc (Γ0 ++ Γ1 ++ Γ2) Γ3 x).
        pose (app_assoc (Γ0 ++ Γ1) Γ2 Γ3).
        pose (app_assoc Γ0 Γ1 Γ2).
        rewrite <- e3 in e2. rewrite <- e2 in e1.
        pose (app_assoc Γ0 Γ1 (Γ2 ++ Γ3)).
        rewrite <- e4 in e1. rewrite <- e1 in e0.
        pose (app_assoc (Γ0 ++ Γ1) Γ2 (Γ3 ++ x)).
        rewrite <- e3 in e5. rewrite <- e5 in e0.
        pose (app_assoc Γ0 Γ1 (Γ2 ++ Γ3 ++ x)).
        rewrite <- e6 in e0. rewrite <- e0.
        pose (app_assoc (Γ0 ++ Γ1 ++ Γ2) Γ3 (x ++ Box A :: x0)).
        pose (app_assoc (Γ0 ++ Γ1) Γ2 Γ3).
        rewrite <- e3 in e8. rewrite <- e8 in e7.
        pose (app_assoc Γ0 Γ1 (Γ2 ++ Γ3)). rewrite <- e9 in e7.
        rewrite <- e7.
        pose (app_assoc (Γ0 ++ Γ1) Γ2 (Γ3 ++ x ++ Box A :: x0)).
        rewrite <- e3 in e10. rewrite <- e10.
        pose (app_assoc Γ0 Γ1 (Γ2 ++ Γ3 ++ x ++ Box A :: x0)).
        rewrite <- e11. reflexivity.
        rewrite E. apply IdBRule_I. }
Qed.

Lemma list_exch_L_BotL_notapplic : forall s se,
    (@list_exch_L s se) ->
    ((BotLRule [] s) -> False) ->
    ((BotLRule [] se) -> False).
Proof.
intros s se exch. induction exch. intros RA RAe. apply RA.
inversion RAe. symmetry in H. apply partition_1_element in H.
destruct H.
- destruct s. destruct s. rewrite e.
  assert (E: (x ++ ⊥ :: x0) ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4 =
  x ++ ⊥ :: x0 ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4).
  pose (app_assoc x (⊥ :: x0) (Γ1 ++ Γ2 ++ Γ3 ++ Γ4)). rewrite <- e0.
  auto. rewrite E. apply BotLRule_I.
- destruct s.
  + destruct s. destruct s. rewrite e.
    assert (E: Γ0 ++ Γ1 ++ Γ2 ++ (x ++ ⊥ :: x0) ++ Γ4 =
    Γ0 ++ Γ1 ++ Γ2 ++ x ++ ⊥ :: x0 ++ Γ4).
    pose (app_assoc x (⊥ :: x0) Γ4).
    simpl in e0. rewrite <- e0. reflexivity. rewrite E.
    assert (E1: Γ0 ++ Γ1 ++ Γ2 ++ x ++ ⊥ :: x0 ++ Γ4 =
    (Γ0 ++ Γ1 ++ Γ2 ++ x) ++ ⊥ :: x0 ++ Γ4).
    pose (app_assoc (Γ0 ++ Γ1 ++ Γ2) x (⊥ :: x0 ++ Γ4)).
    pose (app_assoc (Γ0 ++ Γ1) Γ2 x).
    pose (app_assoc Γ0 Γ1 Γ2). rewrite <- e2 in e1. rewrite <- e1 in e0.
    pose (app_assoc Γ0 Γ1 (Γ2 ++ x)). rewrite <- e3 in e0. rewrite <- e0.
    pose (app_assoc (Γ0 ++ Γ1) Γ2 (x ++ ⊥ :: x0 ++ Γ4)). rewrite <- e2 in e4.
    rewrite <- e4.
    pose (app_assoc Γ0 Γ1 (Γ2 ++ x ++ ⊥ :: x0 ++ Γ4)). rewrite e5. reflexivity.
    rewrite E1. apply BotLRule_I.
  + destruct s.
    * destruct s. destruct s. rewrite e.
      assert (E: Γ0 ++ Γ1 ++ (x ++ ⊥ :: x0) ++ Γ3 ++ Γ4 =
      (Γ0 ++ Γ1 ++ x) ++ ⊥ :: x0 ++ Γ3 ++ Γ4).
      pose (app_assoc x (⊥ :: x0) (Γ3 ++ Γ4)). rewrite <- e0. simpl.
      pose (app_assoc (Γ0 ++ Γ1) x (⊥ :: x0 ++ Γ3 ++ Γ4)).
      pose (app_assoc Γ0 Γ1 x). rewrite <- e2 in e1. rewrite <- e1.
      pose (app_assoc Γ0 Γ1 (x ++ ⊥ :: x0 ++ Γ3 ++ Γ4)). rewrite <- e3.
      reflexivity. rewrite E. apply BotLRule_I.
    * destruct s.
      { destruct s. destruct s. rewrite e.
        assert (E: Γ0 ++ (x ++ ⊥ :: x0) ++ Γ2 ++ Γ3 ++ Γ4 =
        (Γ0 ++ x) ++ ⊥ :: x0 ++ Γ2 ++ Γ3 ++ Γ4).
        pose (app_assoc x (⊥ :: x0) (Γ2 ++ Γ3 ++ Γ4)).
        rewrite <- e0. simpl.
        pose (app_assoc Γ0 x (⊥ :: x0 ++ Γ2 ++ Γ3 ++ Γ4)).
        rewrite <- e1. reflexivity. rewrite E. apply BotLRule_I. }
      { destruct s. destruct s. rewrite e.
        assert (E: Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ x ++ ⊥ :: x0 =
        (Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ x) ++ ⊥ :: x0).
        pose (app_assoc (Γ0 ++ Γ1 ++ Γ2 ++ Γ3) x (⊥ :: x0)).
        pose (app_assoc (Γ0 ++ Γ1 ++ Γ2) Γ3 x).
        pose (app_assoc (Γ0 ++ Γ1) Γ2 Γ3).
        pose (app_assoc Γ0 Γ1 Γ2).
        rewrite <- e3 in e2. rewrite <- e2 in e1.
        pose (app_assoc Γ0 Γ1 (Γ2 ++ Γ3)).
        rewrite <- e4 in e1. rewrite <- e1 in e0.
        pose (app_assoc (Γ0 ++ Γ1) Γ2 (Γ3 ++ x)).
        rewrite <- e3 in e5. rewrite <- e5 in e0.
        pose (app_assoc Γ0 Γ1 (Γ2 ++ Γ3 ++ x)).
        rewrite <- e6 in e0. rewrite <- e0.
        pose (app_assoc (Γ0 ++ Γ1 ++ Γ2) Γ3 (x ++ ⊥ :: x0)).
        pose (app_assoc (Γ0 ++ Γ1) Γ2 Γ3).
        rewrite <- e3 in e8. rewrite <- e8 in e7.
        pose (app_assoc Γ0 Γ1 (Γ2 ++ Γ3)). rewrite <- e9 in e7.
        rewrite <- e7.
        pose (app_assoc (Γ0 ++ Γ1) Γ2 (Γ3 ++ x ++ ⊥ :: x0)).
        rewrite <- e3 in e10. rewrite <- e10.
        pose (app_assoc Γ0 Γ1 (Γ2 ++ Γ3 ++ x ++ ⊥ :: x0)).
        rewrite <- e11. reflexivity.
        rewrite E. apply BotLRule_I. }
Qed.

Lemma list_exch_R_IdP_notapplic : forall s se,
    (@list_exch_R s se) ->
    ((IdPRule [] s) -> False) ->
    ((IdPRule [] se) -> False).
Proof.
intros s se exch. induction exch. intros RA RAe. apply RA.
inversion RAe. symmetry in H1. apply partition_1_element in H1.
destruct H1.
- destruct s. destruct s. rewrite e.
  assert (E: (x ++ # P :: x0) ++ Δ1 ++ Δ2 ++ Δ3 ++ Δ4 =
  x ++ # P :: x0 ++ Δ1 ++ Δ2 ++ Δ3 ++ Δ4).
  pose (app_assoc x (# P :: x0) (Δ1 ++ Δ2 ++ Δ3 ++ Δ4)). rewrite <- e0.
  auto. rewrite E. apply IdPRule_I.
- destruct s.
  + destruct s. destruct s. rewrite e.
    assert (E: Δ0 ++ Δ1 ++ Δ2 ++ (x ++ # P :: x0) ++ Δ4 =
    Δ0 ++ Δ1 ++ Δ2 ++ x ++ # P :: x0 ++ Δ4).
    pose (app_assoc x (# P :: x0) Δ4).
    simpl in e0. rewrite <- e0. reflexivity. rewrite E.
    assert (E1: Δ0 ++ Δ1 ++ Δ2 ++ x ++ # P :: x0 ++ Δ4 =
    (Δ0 ++ Δ1 ++ Δ2 ++ x) ++ # P :: x0 ++ Δ4).
    pose (app_assoc (Δ0 ++ Δ1 ++ Δ2) x (# P :: x0 ++ Δ4)).
    pose (app_assoc (Δ0 ++ Δ1) Δ2 x).
    pose (app_assoc Δ0 Δ1 Δ2). rewrite <- e2 in e1. rewrite <- e1 in e0.
    pose (app_assoc Δ0 Δ1 (Δ2 ++ x)). rewrite <- e3 in e0. rewrite <- e0.
    pose (app_assoc (Δ0 ++ Δ1) Δ2 (x ++ # P :: x0 ++ Δ4)). rewrite <- e2 in e4.
    rewrite <- e4.
    pose (app_assoc Δ0 Δ1 (Δ2 ++ x ++ # P :: x0 ++ Δ4)). rewrite e5. reflexivity.
    rewrite E1. apply IdPRule_I.
  + destruct s.
    * destruct s. destruct s. rewrite e.
      assert (E: Δ0 ++ Δ1 ++ (x ++ # P :: x0) ++ Δ3 ++ Δ4 =
      (Δ0 ++ Δ1 ++ x) ++ # P :: x0 ++ Δ3 ++ Δ4).
      pose (app_assoc x (# P :: x0) (Δ3 ++ Δ4)). rewrite <- e0. simpl.
      pose (app_assoc (Δ0 ++ Δ1) x (# P :: x0 ++ Δ3 ++ Δ4)).
      pose (app_assoc Δ0 Δ1 x). rewrite <- e2 in e1. rewrite <- e1.
      pose (app_assoc Δ0 Δ1 (x ++ # P :: x0 ++ Δ3 ++ Δ4)). rewrite <- e3.
      reflexivity. rewrite E. apply IdPRule_I.
    * destruct s.
      { destruct s. destruct s. rewrite e.
        assert (E: Δ0 ++ (x ++ # P :: x0) ++ Δ2 ++ Δ3 ++ Δ4 =
        (Δ0 ++ x) ++ # P :: x0 ++ Δ2 ++ Δ3 ++ Δ4).
        pose (app_assoc x (# P :: x0) (Δ2 ++ Δ3 ++ Δ4)).
        rewrite <- e0. simpl.
        pose (app_assoc Δ0 x (# P :: x0 ++ Δ2 ++ Δ3 ++ Δ4)).
        rewrite <- e1. reflexivity. rewrite E. apply IdPRule_I. }
      { destruct s. destruct s. rewrite e.
        assert (E: Δ0 ++ Δ1 ++ Δ2 ++ Δ3 ++ x ++ # P :: x0 =
        (Δ0 ++ Δ1 ++ Δ2 ++ Δ3 ++ x) ++ # P :: x0).
        pose (app_assoc (Δ0 ++ Δ1 ++ Δ2 ++ Δ3) x (# P :: x0)).
        pose (app_assoc (Δ0 ++ Δ1 ++ Δ2) Δ3 x).
        pose (app_assoc (Δ0 ++ Δ1) Δ2 Δ3).
        pose (app_assoc Δ0 Δ1 Δ2).
        rewrite <- e3 in e2. rewrite <- e2 in e1.
        pose (app_assoc Δ0 Δ1 (Δ2 ++ Δ3)).
        rewrite <- e4 in e1. rewrite <- e1 in e0.
        pose (app_assoc (Δ0 ++ Δ1) Δ2 (Δ3 ++ x)).
        rewrite <- e3 in e5. rewrite <- e5 in e0.
        pose (app_assoc Δ0 Δ1 (Δ2 ++ Δ3 ++ x)).
        rewrite <- e6 in e0. rewrite <- e0.
        pose (app_assoc (Δ0 ++ Δ1 ++ Δ2) Δ3 (x ++ # P :: x0)).
        pose (app_assoc (Δ0 ++ Δ1) Δ2 Δ3).
        rewrite <- e3 in e8. rewrite <- e8 in e7.
        pose (app_assoc Δ0 Δ1 (Δ2 ++ Δ3)). rewrite <- e9 in e7.
        rewrite <- e7.
        pose (app_assoc (Δ0 ++ Δ1) Δ2 (Δ3 ++ x ++ # P :: x0)).
        rewrite <- e3 in e10. rewrite <- e10.
        pose (app_assoc Δ0 Δ1 (Δ2 ++ Δ3 ++ x ++ # P :: x0)).
        rewrite <- e11. reflexivity.
        rewrite E. apply IdPRule_I. }
Qed.

Lemma list_exch_R_IdB_notapplic : forall s se,
    (@list_exch_R s se) ->
    ((IdBRule [] s) -> False) ->
    ((IdBRule [] se) -> False).
Proof.
intros s se exch. induction exch. intros RA RAe. apply RA.
inversion RAe. symmetry in H1. apply partition_1_element in H1.
destruct H1.
- destruct s. destruct s. rewrite e.
  assert (E: (x ++ Box A :: x0) ++ Δ1 ++ Δ2 ++ Δ3 ++ Δ4 =
  x ++ Box A :: x0 ++ Δ1 ++ Δ2 ++ Δ3 ++ Δ4).
  pose (app_assoc x (Box A :: x0) (Δ1 ++ Δ2 ++ Δ3 ++ Δ4)). rewrite <- e0.
  auto. rewrite E. apply IdBRule_I.
- destruct s.
  + destruct s. destruct s. rewrite e.
    assert (E: Δ0 ++ Δ1 ++ Δ2 ++ (x ++ Box A :: x0) ++ Δ4 =
    Δ0 ++ Δ1 ++ Δ2 ++ x ++ Box A :: x0 ++ Δ4).
    pose (app_assoc x (Box A :: x0) Δ4).
    simpl in e0. rewrite <- e0. reflexivity. rewrite E.
    assert (E1: Δ0 ++ Δ1 ++ Δ2 ++ x ++ Box A :: x0 ++ Δ4 =
    (Δ0 ++ Δ1 ++ Δ2 ++ x) ++ Box A :: x0 ++ Δ4).
    pose (app_assoc (Δ0 ++ Δ1 ++ Δ2) x (Box A :: x0 ++ Δ4)).
    pose (app_assoc (Δ0 ++ Δ1) Δ2 x).
    pose (app_assoc Δ0 Δ1 Δ2). rewrite <- e2 in e1. rewrite <- e1 in e0.
    pose (app_assoc Δ0 Δ1 (Δ2 ++ x)). rewrite <- e3 in e0. rewrite <- e0.
    pose (app_assoc (Δ0 ++ Δ1) Δ2 (x ++ Box A :: x0 ++ Δ4)). rewrite <- e2 in e4.
    rewrite <- e4.
    pose (app_assoc Δ0 Δ1 (Δ2 ++ x ++ Box A :: x0 ++ Δ4)). rewrite e5. reflexivity.
    rewrite E1. apply IdBRule_I.
  + destruct s.
    * destruct s. destruct s. rewrite e.
      assert (E: Δ0 ++ Δ1 ++ (x ++ Box A :: x0) ++ Δ3 ++ Δ4 =
      (Δ0 ++ Δ1 ++ x) ++ Box A :: x0 ++ Δ3 ++ Δ4).
      pose (app_assoc x (Box A :: x0) (Δ3 ++ Δ4)). rewrite <- e0. simpl.
      pose (app_assoc (Δ0 ++ Δ1) x (Box A :: x0 ++ Δ3 ++ Δ4)).
      pose (app_assoc Δ0 Δ1 x). rewrite <- e2 in e1. rewrite <- e1.
      pose (app_assoc Δ0 Δ1 (x ++ Box A :: x0 ++ Δ3 ++ Δ4)). rewrite <- e3.
      reflexivity. rewrite E. apply IdBRule_I.
    * destruct s.
      { destruct s. destruct s. rewrite e.
        assert (E: Δ0 ++ (x ++ Box A :: x0) ++ Δ2 ++ Δ3 ++ Δ4 =
        (Δ0 ++ x) ++ Box A :: x0 ++ Δ2 ++ Δ3 ++ Δ4).
        pose (app_assoc x (Box A :: x0) (Δ2 ++ Δ3 ++ Δ4)).
        rewrite <- e0. simpl.
        pose (app_assoc Δ0 x (Box A :: x0 ++ Δ2 ++ Δ3 ++ Δ4)).
        rewrite <- e1. reflexivity. rewrite E. apply IdBRule_I. }
      { destruct s. destruct s. rewrite e.
        assert (E: Δ0 ++ Δ1 ++ Δ2 ++ Δ3 ++ x ++ Box A :: x0 =
        (Δ0 ++ Δ1 ++ Δ2 ++ Δ3 ++ x) ++ Box A :: x0).
        pose (app_assoc (Δ0 ++ Δ1 ++ Δ2 ++ Δ3) x (Box A :: x0)).
        pose (app_assoc (Δ0 ++ Δ1 ++ Δ2) Δ3 x).
        pose (app_assoc (Δ0 ++ Δ1) Δ2 Δ3).
        pose (app_assoc Δ0 Δ1 Δ2).
        rewrite <- e3 in e2. rewrite <- e2 in e1.
        pose (app_assoc Δ0 Δ1 (Δ2 ++ Δ3)).
        rewrite <- e4 in e1. rewrite <- e1 in e0.
        pose (app_assoc (Δ0 ++ Δ1) Δ2 (Δ3 ++ x)).
        rewrite <- e3 in e5. rewrite <- e5 in e0.
        pose (app_assoc Δ0 Δ1 (Δ2 ++ Δ3 ++ x)).
        rewrite <- e6 in e0. rewrite <- e0.
        pose (app_assoc (Δ0 ++ Δ1 ++ Δ2) Δ3 (x ++ Box A :: x0)).
        pose (app_assoc (Δ0 ++ Δ1) Δ2 Δ3).
        rewrite <- e3 in e8. rewrite <- e8 in e7.
        pose (app_assoc Δ0 Δ1 (Δ2 ++ Δ3)). rewrite <- e9 in e7.
        rewrite <- e7.
        pose (app_assoc (Δ0 ++ Δ1) Δ2 (Δ3 ++ x ++ Box A :: x0)).
        rewrite <- e3 in e10. rewrite <- e10.
        pose (app_assoc Δ0 Δ1 (Δ2 ++ Δ3 ++ x ++ Box A :: x0)).
        rewrite <- e11. reflexivity.
        rewrite E. apply IdBRule_I. }
Qed.

Lemma list_exch_R_BotL_notapplic : forall s se,
    (@list_exch_R s se) ->
    ((BotLRule [] s) -> False) ->
    ((BotLRule [] se) -> False).
Proof.
intros s se exch RA RAe. apply RA.
inversion RAe. destruct s.
apply list_exch_R_same_L with (Γ:=l) (Γe:=Γ0 ++ ⊥ :: Γ1) (Δ:=l0) (Δe:=Δ) in exch.
subst. apply BotLRule_I. reflexivity. symmetry. assumption.
Qed.

(* The following lemmas make sure that if a rule is applied on a sequent s with
premises ps, then the same rule is applicable on a sequent se which is an exchanged
version of s, with some premises pse that are such that they are exchanged versions
of ps. *)

Lemma ImpR_app_list_exchL : forall s se ps,
  (@list_exch_L s se) ->
  (ImpRRule [ps] s) ->
  (existsT2 pse,
    (ImpRRule [pse] se) *
    (@list_exch_L ps pse)).
Proof.
intros s se ps exch. intro RA. inversion RA. inversion exch. subst.
inversion H. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
- exists (Γ2 ++ A :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6, Δ0 ++ B :: Δ1). split.
  apply ImpRRule_I. assert (Γ2 ++ A :: Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = (Γ2 ++ [A]) ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6).
  rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
  assert (Γ2 ++ A :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ [A]) ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6).
  rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
- apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
  + exists ((Γ2 ++ Γ5) ++ A :: Γ4 ++ Γ3 ++ Γ6, Δ0 ++ B :: Δ1). split.
    assert (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5) ++ Γ4 ++ Γ3 ++ Γ6). rewrite app_assoc.
    reflexivity. rewrite H0. clear H0. apply ImpRRule_I. repeat rewrite <- app_assoc.
    assert (Γ2 ++ Γ3 ++ A :: Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (A :: Γ4) ++ Γ5 ++ Γ6).
    reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ Γ5 ++ A :: Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ (A :: Γ4) ++ Γ3 ++ Γ6).
    reflexivity. rewrite H0. clear H0. apply list_exch_LI.
  + apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
    * exists ((Γ2 ++ Γ5 ++ Γ4) ++ A :: Γ3 ++ Γ6, Δ0 ++ B :: Δ1). split.
      assert (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5 ++ Γ4) ++ Γ3 ++ Γ6). repeat rewrite app_assoc.
      reflexivity. rewrite H0. clear H0. apply ImpRRule_I. repeat rewrite <- app_assoc.
      assert (Γ2 ++ Γ3 ++ Γ4 ++ A :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (Γ4 ++ [A]) ++ Γ5 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      assert (Γ2 ++ Γ5 ++ Γ4 ++ A :: Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ (Γ4 ++ [A]) ++ Γ3 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
    * apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
      { repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ A :: Γ6, Δ0 ++ B :: Δ1).
        split. repeat rewrite app_assoc. apply ImpRRule_I. apply list_exch_LI. }
      { repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x0 ++ A :: Γ1, Δ0 ++ B :: Δ1).
        split. repeat rewrite app_assoc. apply ImpRRule_I. apply list_exch_LI. }
      { repeat rewrite <- app_assoc. exists (Γ2 ++ (x ++ A :: x0) ++ Γ4 ++ Γ3 ++ Γ6, Δ0 ++ B :: Δ1).
        split. assert (Γ2 ++ (x ++ A :: x0) ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ x) ++ A :: x0 ++ Γ4 ++ Γ3 ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert (Γ2 ++ x ++ x0 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ x) ++ x0 ++ Γ4 ++ Γ3 ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        apply ImpRRule_I.
        assert (Γ2 ++ Γ3 ++ Γ4 ++ x ++ A :: x0 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (x ++ A :: x0) ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply list_exch_LI. }
    * repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ (x0 ++ A :: x) ++ Γ3 ++ Γ6, Δ0 ++ B :: Δ1).
      split. assert (Γ2 ++ Γ5 ++ (x0 ++ A :: x) ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5 ++ x0) ++ A :: x ++ Γ3 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      assert (Γ2 ++ Γ5 ++ x0 ++ x ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5 ++ x0) ++ x ++ Γ3 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      apply ImpRRule_I.
      assert (Γ2 ++ Γ3 ++ x0 ++ A :: x ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (x0 ++ A :: x) ++ Γ5 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply list_exch_LI.
  + repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ (x ++ A :: x0) ++ Γ6, Δ0 ++ B :: Δ1).
    split. assert (Γ2 ++ Γ5 ++ Γ4 ++ (x ++ A :: x0) ++ Γ6 = (Γ2 ++ Γ5 ++ Γ4 ++ x) ++ A :: x0 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ Γ5 ++ Γ4 ++ x ++ x0 ++ Γ6 = (Γ2 ++ Γ5 ++ Γ4 ++ x) ++ x0 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    apply ImpRRule_I.
    assert (Γ2 ++ x ++ A :: x0 ++ Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ (x ++ A :: x0) ++ Γ4 ++ Γ5 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply list_exch_LI.
- repeat rewrite <- app_assoc. exists (Γ0 ++ A :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6, Δ0 ++ B :: Δ1).
  split. apply ImpRRule_I.
  assert (Γ0 ++ A :: x ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = (Γ0 ++ A :: x) ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6).
  repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
  assert (Γ0 ++ A :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ0 ++ A :: x) ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6).
  repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
Qed.

Lemma ImpL_app_list_exchL : forall s se ps1 ps2,
  (@list_exch_L s se) ->
  (ImpLRule [ps1;ps2] s) ->
  (existsT2 pse1 pse2,
    (ImpLRule [pse1;pse2] se) *
    (@list_exch_L ps1 pse1) *
    (@list_exch_L ps2 pse2)).
Proof.
intros s se ps1 ps2 exch. intro RA. inversion RA. inversion exch. subst.
inversion H. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
- destruct Γ3 ; destruct Γ4 ; destruct Γ5 ; simpl ; simpl in e0 ; simpl in exch ; subst ; try inversion e0 ; subst.
  + exists (Γ2 ++ Γ1, Δ0 ++ A :: Δ1). exists (Γ2 ++ B :: Γ1, Δ0 ++ Δ1). split. split ; try assumption.
    apply list_exch_L_id. apply list_exch_L_id.
  + exists (Γ2 ++ Γ5 ++ Γ6, Δ0 ++ A :: Δ1). exists (Γ2 ++ B :: Γ5 ++ Γ6, Δ0 ++ Δ1). split. split ; try assumption.
    apply list_exch_L_id. apply list_exch_L_id.
  + exists (Γ2 ++ Γ4 ++ Γ6, Δ0 ++ A :: Δ1). exists (Γ2 ++ B :: Γ4 ++ Γ6, Δ0 ++ Δ1). split. split ; try assumption.
    apply list_exch_L_id. apply list_exch_L_id.
  + exists (Γ2 ++ (m0 :: Γ5) ++ Γ4 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ2 ++ (m0 :: Γ5) ++ B :: Γ4 ++ Γ6, Δ0 ++ Δ1). split. split.
    assert (Γ2 ++ (m0 :: Γ5) ++ B :: Γ4 ++ Γ6 = (Γ2 ++ m0 :: Γ5) ++ B :: Γ4 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ m0 :: Γ5 ++ A --> B :: Γ4 ++ Γ6 = (Γ2 ++ m0 :: Γ5) ++ A --> B :: Γ4 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ (m0 :: Γ5) ++ Γ4 ++ Γ6 = (Γ2 ++ m0 :: Γ5) ++ Γ4 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    apply ImpLRule_I.
    assert (Γ2 ++ Γ4 ++ m0 :: Γ5 ++ Γ6 = Γ2 ++ [] ++ Γ4 ++ (m0 :: Γ5) ++ Γ6).
    reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ (m0 :: Γ5) ++ Γ4 ++ Γ6 = Γ2 ++ (m0 :: Γ5) ++ Γ4 ++ [] ++ Γ6).
    reflexivity. rewrite H0. clear H0. apply list_exch_LI.
    assert (Γ2 ++ B :: Γ4 ++ m0 :: Γ5 ++ Γ6 = Γ2 ++ [] ++ (B :: Γ4) ++ (m0 :: Γ5) ++ Γ6).
    reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ (m0 :: Γ5) ++ B :: Γ4 ++ Γ6 = Γ2 ++ (m0 :: Γ5) ++ (B :: Γ4) ++ [] ++ Γ6).
    reflexivity. rewrite H0. clear H0. apply list_exch_LI.
  + exists (Γ2 ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1). exists (Γ2 ++ B :: Γ3 ++ Γ6, Δ0 ++ Δ1). split. split ; try assumption.
    apply list_exch_L_id. apply list_exch_L_id.
  + exists (Γ2 ++ (m0 :: Γ5) ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ2 ++ (m0 :: Γ5) ++ B :: Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
    assert (Γ2 ++ m0 :: Γ5 ++ A --> B :: Γ3 ++ Γ6 = (Γ2 ++ m0 :: Γ5) ++ A --> B :: Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ (m0 :: Γ5) ++ B :: Γ3 ++ Γ6 = (Γ2 ++ m0 :: Γ5) ++ B :: Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ (m0 :: Γ5) ++ Γ3 ++ Γ6 = (Γ2 ++ m0 :: Γ5) ++ Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    apply ImpLRule_I.
    assert (Γ2 ++ Γ3 ++ m0 :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ [] ++ (m0 :: Γ5) ++ Γ6).
    reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ (m0 :: Γ5) ++ Γ3 ++ Γ6 = Γ2 ++ (m0 :: Γ5) ++ [] ++ Γ3 ++ Γ6).
    reflexivity. rewrite H0. clear H0. apply list_exch_LI.
    assert (Γ2 ++ B :: Γ3 ++ m0 :: Γ5 ++ Γ6 = Γ2 ++ (B :: Γ3) ++ [] ++ (m0 :: Γ5) ++ Γ6).
    reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ (m0 :: Γ5) ++ B :: Γ3 ++ Γ6 = Γ2 ++ (m0 :: Γ5) ++ [] ++ (B :: Γ3) ++ Γ6).
    reflexivity. rewrite H0. clear H0. apply list_exch_LI.
  + exists (Γ2 ++ m0 :: Γ4 ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ2 ++ m0 :: Γ4 ++ B :: Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
    assert (Γ2 ++ m0 :: Γ4 ++ A --> B :: Γ3 ++ Γ6 = (Γ2 ++ m0 :: Γ4) ++ A --> B :: Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ m0 :: Γ4 ++ B :: Γ3 ++ Γ6 = (Γ2 ++ m0 :: Γ4) ++ B :: Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ m0 :: Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ m0 :: Γ4) ++ Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
    assert (Γ2 ++ Γ3 ++ m0 :: Γ4 ++ Γ6 = Γ2 ++ Γ3 ++ [] ++ (m0 :: Γ4) ++ Γ6).
    reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ m0 :: Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (m0 :: Γ4) ++ [] ++ Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
    assert (Γ2 ++ B :: Γ3 ++ m0 :: Γ4 ++ Γ6 = Γ2 ++ (B :: Γ3) ++ [] ++ (m0 :: Γ4) ++ Γ6).
    reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ m0 :: Γ4 ++ B :: Γ3 ++ Γ6 = Γ2 ++ (m0 :: Γ4) ++ [] ++ (B :: Γ3) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
  + exists (Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ B :: Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
    assert (Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ A --> B :: Γ3 ++ Γ6 = (Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4) ++ A --> B :: Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ B :: Γ3 ++ Γ6 = (Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4) ++ B :: Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4) ++ Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    apply ImpLRule_I.
    assert (Γ2 ++ Γ3 ++ m0 :: Γ4 ++ m1 :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (m0 :: Γ4) ++ (m1 :: Γ5) ++ Γ6).
    reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (m1 :: Γ5) ++ (m0 :: Γ4) ++ Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
    assert (Γ2 ++ B :: Γ3 ++ m0 :: Γ4 ++ m1 :: Γ5 ++ Γ6 = Γ2 ++ (B :: Γ3) ++ (m0 :: Γ4) ++ (m1 :: Γ5) ++ Γ6).
    reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ B :: Γ3 ++ Γ6 = Γ2 ++ (m1 :: Γ5) ++ (m0 :: Γ4) ++ (B :: Γ3) ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
- apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
  + destruct Γ4 ; destruct Γ5 ; simpl ; simpl in e0 ; simpl in exch ; subst ; try inversion e0 ; subst.
    * rewrite app_assoc. exists ((Γ2 ++ Γ3) ++ Γ1, Δ0 ++ A :: Δ1).
      exists ((Γ2 ++ Γ3) ++ B :: Γ1, Δ0 ++ Δ1). split. split ; try assumption. apply list_exch_L_id.
      apply list_exch_L_id.
    * exists (Γ2 ++ Γ5 ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
      exists (Γ2 ++ B :: Γ5 ++ Γ3 ++ Γ6, Δ0 ++ Δ1). split. split. apply ImpLRule_I.
      assert ((Γ2 ++ Γ3) ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ [] ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert (Γ2 ++ Γ5 ++ Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ [] ++ Γ3 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
      assert ((Γ2 ++ Γ3) ++ B :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ [] ++ (B :: Γ5) ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert (Γ2 ++ B :: Γ5 ++ Γ3 ++ Γ6 = Γ2 ++ (B :: Γ5) ++ [] ++ Γ3 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
    * exists (Γ2 ++ Γ4 ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
      exists (Γ2 ++ B :: Γ4 ++ Γ3 ++ Γ6, Δ0 ++ Δ1). split. split. apply ImpLRule_I.
      assert ((Γ2 ++ Γ3) ++ Γ4 ++ Γ6 = Γ2 ++ Γ3 ++ [] ++ Γ4 ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert (Γ2 ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ Γ4 ++ [] ++ Γ3 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
      assert ((Γ2 ++ Γ3) ++ B :: Γ4 ++ Γ6 = Γ2 ++ Γ3 ++ [] ++ (B :: Γ4) ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert (Γ2 ++ B :: Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (B :: Γ4) ++ [] ++ Γ3 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
    * exists ((Γ2 ++ m0 :: Γ5) ++ Γ4 ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
      exists ((Γ2 ++ m0 :: Γ5) ++ B :: Γ4 ++ Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
      assert (Γ2 ++ m0 :: Γ5 ++ A --> B :: Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ m0 :: Γ5) ++ A --> B :: Γ4 ++ Γ3 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpLRule_I.
      assert ((Γ2 ++ Γ3) ++ Γ4 ++ m0 :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (m0 :: Γ5) ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert ((Γ2 ++ m0 :: Γ5) ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (m0 :: Γ5) ++ Γ4 ++ Γ3 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
      assert ((Γ2 ++ Γ3) ++ B :: Γ4 ++ m0 :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (B :: Γ4) ++ (m0 :: Γ5) ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert ((Γ2 ++ m0 :: Γ5) ++ B :: Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (m0 :: Γ5) ++ (B :: Γ4) ++ Γ3 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
  + apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
    * destruct Γ5 ; simpl ; simpl in e0 ; simpl in exch ; subst ; try inversion e0 ; subst.
      { exists ((Γ2 ++ Γ4 ++ Γ3) ++ Γ1, Δ0 ++ A :: Δ1).
        exists ((Γ2 ++ Γ4 ++ Γ3) ++ B :: Γ1, Δ0 ++ Δ1). split. split.
        assert (Γ2 ++ Γ4 ++ Γ3 ++ A --> B :: Γ1 = (Γ2 ++ Γ4 ++ Γ3) ++ A --> B :: Γ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpLRule_I.
        assert ((Γ2 ++ Γ3 ++ Γ4) ++ Γ1 = Γ2 ++ Γ3 ++ [] ++ Γ4 ++ Γ1). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0.
        assert ((Γ2 ++ Γ4 ++ Γ3) ++ Γ1 = Γ2 ++ Γ4 ++ [] ++ Γ3 ++ Γ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
        assert ((Γ2 ++ Γ3 ++ Γ4) ++ B :: Γ1 = Γ2 ++ Γ3 ++ [] ++ Γ4 ++ B :: Γ1). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0.
        assert ((Γ2 ++ Γ4 ++ Γ3) ++ B :: Γ1 = Γ2 ++ Γ4 ++ [] ++ Γ3 ++ B :: Γ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI. }
      { exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
        exists (Γ2 ++ B :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6, Δ0 ++ Δ1). split. split. apply ImpLRule_I.
        repeat rewrite <- app_assoc. apply list_exch_LI.
        assert ((Γ2 ++ Γ3 ++ Γ4) ++ B :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (B :: Γ5) ++ Γ6). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0.
        assert (Γ2 ++ B :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (B :: Γ5) ++ Γ4 ++ Γ3 ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI. }
    * apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
      { exists ((Γ2 ++ Γ5 ++ Γ4 ++ Γ3) ++ Γ1, Δ0 ++ A :: Δ1).
        exists ((Γ2 ++ Γ5 ++ Γ4 ++ Γ3) ++ B :: Γ1, Δ0 ++ Δ1). split. split.
        assert (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ A --> B :: Γ1 = (Γ2 ++ Γ5 ++ Γ4 ++ Γ3) ++ A --> B :: Γ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpLRule_I.
        repeat rewrite <- app_assoc. apply list_exch_LI. repeat rewrite <- app_assoc. apply list_exch_LI. }
      { exists ((Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x0) ++ Γ1, Δ0 ++ A :: Δ1).
        exists ((Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x0) ++ B :: Γ1, Δ0 ++ Δ1). split. split.
        assert (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x0 ++ A --> B :: Γ1 = (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x0) ++ A --> B :: Γ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpLRule_I.
        repeat rewrite <- app_assoc. apply list_exch_LI. repeat rewrite <- app_assoc. apply list_exch_LI. }
      { destruct x0.
        - simpl in e0. subst. rewrite app_nil_r.
          exists ((Γ2 ++ x ++ Γ4 ++ Γ3) ++ Γ1, Δ0 ++ A :: Δ1).
          exists ((Γ2 ++ x ++ Γ4 ++ Γ3) ++ B :: Γ1, Δ0 ++ Δ1). split. split.
          assert (Γ2 ++ x ++ Γ4 ++ Γ3 ++ A --> B :: Γ1 = (Γ2 ++ x ++ Γ4 ++ Γ3) ++ A --> B :: Γ1).
          repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
          repeat rewrite <- app_assoc. apply list_exch_LI. repeat rewrite <- app_assoc. apply list_exch_LI.
        - inversion e0. subst.
          exists ((Γ2 ++ x) ++ x0 ++ Γ4 ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
          exists ((Γ2 ++ x) ++ B :: x0 ++ Γ4 ++ Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
          assert (Γ2 ++ (x ++ A --> B :: x0) ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ x) ++ A --> B :: x0 ++ Γ4 ++ Γ3 ++ Γ6).
          repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
          assert ((Γ2 ++ Γ3 ++ Γ4 ++ x) ++ x0 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (x ++ x0) ++ Γ6).
          repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
          assert ((Γ2 ++ x) ++ x0 ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (x ++ x0) ++ Γ4 ++ Γ3 ++ Γ6).
          repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
          apply list_exch_LI.
          assert ((Γ2 ++ Γ3 ++ Γ4 ++ x) ++ B :: x0 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (x ++ B :: x0) ++ Γ6).
          repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
          assert ((Γ2 ++ x) ++ B :: x0 ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (x ++ B :: x0) ++ Γ4 ++ Γ3 ++ Γ6).
          repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
          apply list_exch_LI. }
    * destruct x ; destruct Γ5 ; simpl ; simpl in e0 ; simpl in exch ; subst ; try inversion e0 ; subst.
      { rewrite app_nil_r. exists ((Γ2 ++ x0 ++ Γ3) ++ Γ1, Δ0 ++ A :: Δ1).
        exists ((Γ2 ++ x0 ++ Γ3) ++ B :: Γ1, Δ0 ++ Δ1). split. split.
        assert (Γ2 ++ x0 ++ Γ3 ++ A --> B :: Γ1 = (Γ2 ++ x0 ++ Γ3) ++ A --> B :: Γ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
        assert ((Γ2 ++ Γ3 ++ x0) ++ Γ1 = Γ2 ++ Γ3 ++ [] ++ x0 ++ Γ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert ((Γ2 ++ x0 ++ Γ3) ++ Γ1 = Γ2 ++ x0 ++ [] ++ Γ3 ++ Γ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
        assert ((Γ2 ++ Γ3 ++ x0) ++ B :: Γ1 = Γ2 ++ Γ3 ++ [] ++ x0 ++ B :: Γ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert ((Γ2 ++ x0 ++ Γ3) ++ B :: Γ1 = Γ2 ++ x0 ++ [] ++ Γ3 ++ B :: Γ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI. }
      { rewrite app_nil_r. exists (Γ2 ++ Γ5 ++ x0 ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
        exists (Γ2 ++ B :: Γ5 ++ x0 ++ Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
        apply ImpLRule_I. repeat rewrite <- app_assoc. apply list_exch_LI.
        assert ((Γ2 ++ Γ3 ++ x0) ++ B :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ x0 ++ (B :: Γ5) ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert (Γ2 ++ B :: Γ5 ++ x0 ++ Γ3 ++ Γ6 = Γ2 ++ (B :: Γ5) ++ x0 ++ Γ3 ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI. }
      { exists ((Γ2 ++ x0) ++ x ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
        exists ((Γ2 ++ x0) ++ B :: x ++ Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
        assert (Γ2 ++ (x0 ++ A --> B :: x) ++ Γ3 ++ Γ6 = (Γ2 ++ x0) ++ A --> B :: x ++ Γ3 ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
        assert ((Γ2 ++ Γ3 ++ x0) ++ x ++ Γ6 = Γ2 ++ Γ3 ++ [] ++ (x0 ++ x) ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert ((Γ2 ++ x0) ++ x ++ Γ3 ++ Γ6 = Γ2 ++ (x0 ++ x) ++ [] ++ Γ3 ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
        assert ((Γ2 ++ Γ3 ++ x0) ++ B :: x ++ Γ6 = Γ2 ++ Γ3 ++ [] ++ (x0 ++ B :: x) ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert ((Γ2 ++ x0) ++ B :: x ++ Γ3 ++ Γ6 = Γ2 ++ (x0 ++ B :: x) ++ [] ++ Γ3 ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI. }
      { exists ((Γ2 ++ m0 :: Γ5 ++ x0) ++ x ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
        exists ((Γ2 ++ m0 :: Γ5 ++ x0) ++ B :: x ++ Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
        assert (Γ2 ++ m0 :: Γ5 ++ (x0 ++ A --> B :: x) ++ Γ3 ++ Γ6 = (Γ2 ++ m0 :: Γ5 ++ x0) ++ A --> B :: x ++ Γ3 ++ Γ6).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
        assert ((Γ2 ++ Γ3 ++ x0) ++ x ++ m0 :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (x0 ++ x) ++ (m0 :: Γ5) ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert ((Γ2 ++ m0 :: Γ5 ++ x0) ++ x ++ Γ3 ++ Γ6 = Γ2 ++ (m0 :: Γ5) ++ (x0 ++ x) ++ Γ3 ++ Γ6).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        apply list_exch_LI.
        assert ((Γ2 ++ Γ3 ++ x0) ++ B :: x ++ m0 :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (x0 ++ B :: x) ++ (m0 :: Γ5) ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert ((Γ2 ++ m0 :: Γ5 ++ x0) ++ B :: x ++ Γ3 ++ Γ6 = Γ2 ++ (m0 :: Γ5) ++ (x0 ++ B :: x) ++ Γ3 ++ Γ6).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        apply list_exch_LI. }
  + destruct x0 ; destruct Γ4 ; destruct Γ5 ; simpl ; simpl in e0 ; simpl in exch ; subst ; try inversion e0 ; subst.
    * rewrite app_nil_r. rewrite app_assoc. exists ((Γ2 ++ x) ++ Γ1, Δ0 ++ A :: Δ1).
      exists ((Γ2 ++ x) ++ B :: Γ1, Δ0 ++ Δ1). split. split ; try assumption. apply list_exch_L_id. apply list_exch_L_id.
    * rewrite app_nil_r. exists (Γ2 ++ Γ5 ++ x ++ Γ6, Δ0 ++ A :: Δ1).
      exists (Γ2 ++ B :: Γ5 ++ x ++ Γ6, Δ0 ++ Δ1). split. split. apply ImpLRule_I.
      assert ((Γ2 ++ x) ++ Γ5 ++ Γ6 = Γ2 ++ x ++ [] ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert (Γ2 ++ Γ5 ++ x ++ Γ6 = Γ2 ++ Γ5 ++ [] ++ x ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
      assert ((Γ2 ++ x) ++ B :: Γ5 ++ Γ6 = Γ2 ++ x ++ [] ++ (B :: Γ5) ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert (Γ2 ++ B :: Γ5 ++ x ++ Γ6 = Γ2 ++ (B :: Γ5) ++ [] ++ x ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
    * rewrite app_nil_r. exists (Γ2 ++ Γ4 ++ x ++ Γ6, Δ0 ++ A :: Δ1).
      exists (Γ2 ++ B :: Γ4 ++ x ++ Γ6, Δ0 ++ Δ1). split. split. apply ImpLRule_I.
      assert ((Γ2 ++ x) ++ Γ4 ++ Γ6 = Γ2 ++ x ++ [] ++ Γ4 ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert (Γ2 ++ Γ4 ++ x ++ Γ6 = Γ2 ++ Γ4 ++ [] ++ x ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
      assert ((Γ2 ++ x) ++ B :: Γ4 ++ Γ6 = Γ2 ++ x ++ [] ++ (B :: Γ4) ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert (Γ2 ++ B :: Γ4 ++ x ++ Γ6 = Γ2 ++ (B :: Γ4) ++ [] ++ x ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
    * rewrite app_nil_r. exists ((Γ2 ++ m0 :: Γ5) ++ Γ4 ++ x ++ Γ6, Δ0 ++ A :: Δ1).
      exists ((Γ2 ++ m0 :: Γ5) ++ B :: Γ4 ++ x ++ Γ6, Δ0 ++ Δ1). split. split.
      assert (Γ2 ++ m0 :: Γ5 ++ A --> B :: Γ4 ++ x ++ Γ6 = (Γ2 ++ m0 :: Γ5) ++ A --> B :: Γ4 ++ x ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpLRule_I.
      assert ((Γ2 ++ x) ++ Γ4 ++ m0 :: Γ5 ++ Γ6 = Γ2 ++ x ++ Γ4 ++ (m0 :: Γ5) ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert ((Γ2 ++ m0 :: Γ5) ++ Γ4 ++ x ++ Γ6 = Γ2 ++ (m0 :: Γ5) ++ Γ4 ++ x ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
      assert ((Γ2 ++ x) ++ B :: Γ4 ++ m0 :: Γ5 ++ Γ6 = Γ2 ++ x ++ (B :: Γ4) ++ (m0 :: Γ5) ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert ((Γ2 ++ m0 :: Γ5) ++ B :: Γ4 ++ x ++ Γ6 = Γ2 ++ (m0 :: Γ5) ++ (B :: Γ4) ++ x ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
    * exists ((Γ2 ++ x) ++ x0 ++ Γ6, Δ0 ++ A :: Δ1).
      exists ((Γ2 ++ x) ++ B :: x0 ++ Γ6, Δ0 ++ Δ1). split. split.
      assert (Γ2 ++ (x ++ A --> B :: x0) ++ Γ6 = (Γ2 ++ x) ++ A --> B :: x0 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpLRule_I.
      apply list_exch_L_id. apply list_exch_L_id.
    * exists ((Γ2 ++ m0 :: Γ5 ++ x) ++ x0 ++ Γ6, Δ0 ++ A :: Δ1).
      exists ((Γ2 ++ m0 :: Γ5 ++ x) ++ B :: x0 ++ Γ6, Δ0 ++ Δ1). split. split.
      assert (Γ2 ++ m0 :: Γ5 ++ (x ++ A --> B :: x0) ++ Γ6 = (Γ2 ++ m0 :: Γ5 ++ x) ++ A --> B :: x0 ++ Γ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpLRule_I.
      assert ((Γ2 ++ x) ++ x0 ++ m0 :: Γ5 ++ Γ6 = Γ2 ++ [] ++ (x ++ x0) ++ (m0 :: Γ5) ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert ((Γ2 ++ m0 :: Γ5 ++ x) ++ x0 ++ Γ6 = Γ2 ++ (m0 :: Γ5) ++ (x ++ x0) ++ [] ++ Γ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
      rewrite H0. clear H0. apply list_exch_LI.
      assert ((Γ2 ++ x) ++ B :: x0 ++ m0 :: Γ5 ++ Γ6 = Γ2 ++ [] ++ (x ++ B :: x0) ++ (m0 :: Γ5) ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert ((Γ2 ++ m0 :: Γ5 ++ x) ++ B :: x0 ++ Γ6 = Γ2 ++ (m0 :: Γ5) ++ (x ++ B :: x0) ++ [] ++ Γ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
      rewrite H0. clear H0. apply list_exch_LI.
    * exists ((Γ2 ++ m0 :: Γ4 ++ x) ++ x0 ++ Γ6, Δ0 ++ A :: Δ1).
      exists ((Γ2 ++ m0 :: Γ4 ++ x) ++ B :: x0 ++ Γ6, Δ0 ++ Δ1). split. split.
      assert (Γ2 ++ m0 :: Γ4 ++ (x ++ A --> B :: x0) ++ Γ6 = (Γ2 ++ m0 :: Γ4 ++ x) ++ A --> B :: x0 ++ Γ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpLRule_I.
      assert ((Γ2 ++ x) ++ x0 ++ m0 :: Γ4 ++ Γ6 = Γ2 ++ [] ++ (x ++ x0) ++ (m0 :: Γ4) ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert ((Γ2 ++ m0 :: Γ4 ++ x) ++ x0 ++ Γ6 = Γ2 ++ (m0 :: Γ4) ++ (x ++ x0) ++ [] ++ Γ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
      rewrite H0. clear H0. apply list_exch_LI.
      assert ((Γ2 ++ x) ++ B :: x0 ++ m0 :: Γ4 ++ Γ6 = Γ2 ++ [] ++ (x ++ B :: x0) ++ (m0 :: Γ4) ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert ((Γ2 ++ m0 :: Γ4 ++ x) ++ B :: x0 ++ Γ6 = Γ2 ++ (m0 :: Γ4) ++ (x ++ B :: x0) ++ [] ++ Γ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
      rewrite H0. clear H0. apply list_exch_LI.
    * exists ((Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ x) ++ x0 ++ Γ6, Δ0 ++ A :: Δ1).
      exists ((Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ x) ++ B :: x0 ++ Γ6, Δ0 ++ Δ1). split. split.
      assert (Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ (x ++ A --> B :: x0) ++ Γ6 = (Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ x) ++ A --> B :: x0 ++ Γ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpLRule_I.
      assert ((Γ2 ++ x) ++ x0 ++ m0 :: Γ4 ++ m1 :: Γ5 ++ Γ6 = Γ2 ++ (x ++ x0) ++ (m0 :: Γ4) ++ (m1 :: Γ5) ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      assert ((Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ x) ++ x0 ++ Γ6 = Γ2 ++ (m1 :: Γ5) ++ (m0 :: Γ4) ++ (x ++ x0) ++ Γ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
      rewrite H0. clear H0. apply list_exch_LI.
      assert ((Γ2 ++ x) ++ B :: x0 ++ m0 :: Γ4 ++ m1 :: Γ5 ++ Γ6 = Γ2 ++ (x ++ B :: x0) ++ (m0 :: Γ4) ++ (m1 :: Γ5) ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      assert ((Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ x) ++ B :: x0 ++ Γ6 = Γ2 ++ (m1 :: Γ5) ++ (m0 :: Γ4) ++ (x ++ B :: x0) ++ Γ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
      rewrite H0. clear H0. apply list_exch_LI.
- destruct x ; destruct Γ3 ; destruct Γ4 ; destruct Γ5 ; simpl ; simpl in e0 ; simpl in exch ;
  subst ; try inversion e0 ; subst.
  * rewrite app_nil_r. exists (Γ0 ++ Γ1, Δ0 ++ A :: Δ1).
    exists (Γ0 ++ B :: Γ1, Δ0 ++ Δ1). split. split ; try assumption.
    apply list_exch_L_id. apply list_exch_L_id.
  * rewrite app_nil_r. exists (Γ0 ++ Γ5 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ0 ++ B :: Γ5 ++ Γ6, Δ0 ++ Δ1). split. split ; try assumption.
    apply list_exch_L_id. apply list_exch_L_id.
  * rewrite app_nil_r. exists (Γ0 ++ Γ4 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ0 ++ B :: Γ4 ++ Γ6, Δ0 ++ Δ1). split. split ; try assumption.
    apply list_exch_L_id. apply list_exch_L_id.
  * rewrite app_nil_r. exists ((Γ0 ++ m0 :: Γ5) ++ Γ4 ++ Γ6, Δ0 ++ A :: Δ1).
    exists ((Γ0 ++ m0 :: Γ5) ++ B :: Γ4 ++ Γ6, Δ0 ++ Δ1). split. split.
    assert (Γ0 ++ m0 :: Γ5 ++ A --> B :: Γ4 ++ Γ6 = (Γ0 ++ m0 :: Γ5) ++ A --> B :: Γ4 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpLRule_I.
    assert (Γ0 ++ Γ4 ++ m0 :: Γ5 ++ Γ6 = Γ0 ++ [] ++ Γ4 ++ (m0 :: Γ5) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert ((Γ0 ++ m0 :: Γ5) ++ Γ4 ++ Γ6 = Γ0 ++ (m0 :: Γ5) ++ Γ4 ++ [] ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
    assert (Γ0 ++ B :: Γ4 ++ m0 :: Γ5 ++ Γ6 = Γ0 ++ [] ++ (B :: Γ4) ++ (m0 :: Γ5) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert ((Γ0 ++ m0 :: Γ5) ++ B :: Γ4 ++ Γ6 = Γ0 ++ (m0 :: Γ5) ++ (B :: Γ4) ++ [] ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
  * rewrite app_nil_r. exists (Γ0 ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ0 ++ B :: Γ3 ++ Γ6, Δ0 ++ Δ1). split.  split ; try assumption.
    apply list_exch_L_id. apply list_exch_L_id.
  * rewrite app_nil_r. exists ((Γ0 ++ m0 :: Γ5) ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
    exists ((Γ0 ++ m0 :: Γ5) ++ B :: Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
    assert (Γ0 ++ m0 :: Γ5 ++ A --> B :: Γ3 ++ Γ6 = (Γ0 ++ m0 :: Γ5) ++ A --> B :: Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpLRule_I.
    assert (Γ0 ++ Γ3 ++ m0 :: Γ5 ++ Γ6 = Γ0 ++ [] ++ Γ3 ++ (m0 :: Γ5) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert ((Γ0 ++ m0 :: Γ5) ++ Γ3 ++ Γ6 = Γ0 ++ (m0 :: Γ5) ++ Γ3 ++ [] ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
    assert (Γ0 ++ B :: Γ3 ++ m0 :: Γ5 ++ Γ6 = Γ0 ++ [] ++ (B :: Γ3) ++ (m0 :: Γ5) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert ((Γ0 ++ m0 :: Γ5) ++ B :: Γ3 ++ Γ6 = Γ0 ++ (m0 :: Γ5) ++ (B :: Γ3) ++ [] ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
  * rewrite app_nil_r. exists ((Γ0 ++ m0 :: Γ4) ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
    exists ((Γ0 ++ m0 :: Γ4) ++ B :: Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
    assert (Γ0 ++ m0 :: Γ4 ++ A --> B :: Γ3 ++ Γ6 = (Γ0 ++ m0 :: Γ4) ++ A --> B :: Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpLRule_I.
    assert ((Γ0 ++ m0 :: Γ4) ++ Γ3 ++ Γ6 = Γ0 ++ (m0 :: Γ4) ++ Γ3 ++ [] ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ0 ++ Γ3 ++ m0 :: Γ4 ++ Γ6 = Γ0 ++ [] ++ Γ3 ++ (m0 :: Γ4) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
    assert ((Γ0 ++ m0 :: Γ4) ++ B :: Γ3 ++ Γ6 = Γ0 ++ (m0 :: Γ4) ++ (B :: Γ3) ++ [] ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ0 ++ B :: Γ3 ++ m0 :: Γ4 ++ Γ6 = Γ0 ++ [] ++ (B :: Γ3) ++ (m0 :: Γ4) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
  * rewrite app_nil_r. exists ((Γ0 ++ m1 :: Γ5 ++ m0 :: Γ4) ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
    exists ((Γ0 ++ m1 :: Γ5 ++ m0 :: Γ4) ++ B :: Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
    assert (Γ0 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ A --> B :: Γ3 ++ Γ6 = (Γ0 ++ m1 :: Γ5 ++ m0 :: Γ4) ++ A --> B :: Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpLRule_I.
    assert (Γ0 ++ Γ3 ++ m0 :: Γ4 ++ m1 :: Γ5 ++ Γ6 = Γ0 ++ Γ3 ++ (m0 :: Γ4) ++ (m1 :: Γ5) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert ((Γ0 ++ m1 :: Γ5 ++ m0 :: Γ4) ++ Γ3 ++ Γ6 = Γ0 ++ (m1 :: Γ5) ++ (m0 :: Γ4) ++ Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
    assert (Γ0 ++ B :: Γ3 ++ m0 :: Γ4 ++ m1 :: Γ5 ++ Γ6 = Γ0 ++ (B :: Γ3) ++ (m0 :: Γ4) ++ (m1 :: Γ5) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert ((Γ0 ++ m1 :: Γ5 ++ m0 :: Γ4) ++ B :: Γ3 ++ Γ6 = Γ0 ++ (m1 :: Γ5) ++ (m0 :: Γ4) ++ (B :: Γ3) ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
  * exists (Γ0 ++ x ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ0 ++ B :: x ++ Γ6, Δ0 ++ Δ1). split. split. repeat rewrite <- app_assoc. apply ImpLRule_I.
    apply list_exch_L_id. apply list_exch_L_id.
  * exists (Γ0 ++ x ++ m0 :: Γ5 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ0 ++ B :: x ++ m0 :: Γ5 ++ Γ6, Δ0 ++ Δ1). split. split. repeat rewrite <- app_assoc. apply ImpLRule_I.
    apply list_exch_L_id. apply list_exch_L_id.
  * exists (Γ0 ++ x ++ m0 :: Γ4 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ0 ++ B :: x ++ m0 :: Γ4 ++ Γ6, Δ0 ++ Δ1). split. split. repeat rewrite <- app_assoc. apply ImpLRule_I.
    apply list_exch_L_id. apply list_exch_L_id.
  * exists (Γ0 ++ x ++ m1 :: Γ5 ++ m0 :: Γ4 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ0 ++ B :: x ++ m1 :: Γ5 ++ m0 :: Γ4 ++ Γ6, Δ0 ++ Δ1). split. split.
    repeat rewrite <- app_assoc. apply ImpLRule_I.
    assert (Γ0 ++ x ++ m0 :: Γ4 ++ m1 :: Γ5 ++ Γ6 = (Γ0 ++ x) ++ (m0 :: Γ4) ++ [] ++ (m1 :: Γ5) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ0 ++ x ++ m1 :: Γ5 ++ m0 :: Γ4 ++ Γ6 = (Γ0 ++ x) ++ (m1 :: Γ5) ++ [] ++ (m0 :: Γ4) ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
    assert (Γ0 ++ B :: x ++ m0 :: Γ4 ++ m1 :: Γ5 ++ Γ6 = (Γ0 ++ B :: x) ++ (m0 :: Γ4) ++ [] ++ (m1 :: Γ5) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ0 ++ B :: x ++ m1 :: Γ5 ++ m0 :: Γ4 ++ Γ6 = (Γ0 ++ B :: x) ++ (m1 :: Γ5) ++ [] ++ (m0 :: Γ4) ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
  * exists (Γ0 ++ x ++ m0 :: Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ0 ++ B :: x ++ m0 :: Γ3 ++ Γ6, Δ0 ++ Δ1). split. split. repeat rewrite <- app_assoc. apply ImpLRule_I.
    apply list_exch_L_id. apply list_exch_L_id.
  * exists (Γ0 ++ x ++ m1 :: Γ5 ++ m0 :: Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ0 ++ B :: x ++ m1 :: Γ5 ++ m0 :: Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
    repeat rewrite <- app_assoc. apply ImpLRule_I.
    assert (Γ0 ++ x ++ m0 :: Γ3 ++ m1 :: Γ5 ++ Γ6 = (Γ0 ++ x) ++ (m0 :: Γ3) ++ [] ++ (m1 :: Γ5) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ0 ++ x ++ m1 :: Γ5 ++ m0 :: Γ3 ++ Γ6 = (Γ0 ++ x) ++ (m1 :: Γ5) ++ [] ++ (m0 :: Γ3) ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
    assert (Γ0 ++ B :: x ++ m0 :: Γ3 ++ m1 :: Γ5 ++ Γ6 = (Γ0 ++ B :: x) ++ (m0 :: Γ3) ++ [] ++ (m1 :: Γ5) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ0 ++ B :: x ++ m1 :: Γ5 ++ m0 :: Γ3 ++ Γ6 = (Γ0 ++ B :: x) ++ (m1 :: Γ5) ++ [] ++ (m0 :: Γ3) ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
  * exists (Γ0 ++ x ++ m1 :: Γ4 ++ m0 :: Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ0 ++ B :: x ++ m1 :: Γ4 ++ m0 :: Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
    repeat rewrite <- app_assoc. apply ImpLRule_I.
    assert (Γ0 ++ x ++ m0 :: Γ3 ++ m1 :: Γ4 ++ Γ6 = (Γ0 ++ x) ++ (m0 :: Γ3) ++ [] ++ (m1 :: Γ4) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ0 ++ x ++ m1 :: Γ4 ++ m0 :: Γ3 ++ Γ6 = (Γ0 ++ x) ++ (m1 :: Γ4) ++ [] ++ (m0 :: Γ3) ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
    assert (Γ0 ++ B :: x ++ m0 :: Γ3 ++ m1 :: Γ4 ++ Γ6 = (Γ0 ++ B :: x) ++ (m0 :: Γ3) ++ [] ++ (m1 :: Γ4) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ0 ++ B :: x ++ m1 :: Γ4 ++ m0 :: Γ3 ++ Γ6 = (Γ0 ++ B :: x) ++ (m1 :: Γ4) ++ [] ++ (m0 :: Γ3) ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
  * exists (Γ0 ++ x ++ m2 :: Γ5 ++ m1 :: Γ4 ++ m0 :: Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ0 ++ B :: x ++ m2 :: Γ5 ++ m1 :: Γ4 ++ m0 :: Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
    repeat rewrite <- app_assoc. apply ImpLRule_I.
    assert (Γ0 ++ x ++ m0 :: Γ3 ++ m1 :: Γ4 ++ m2 :: Γ5 ++ Γ6 = (Γ0 ++ x) ++ (m0 :: Γ3) ++ (m1 :: Γ4) ++ (m2 :: Γ5) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ0 ++ x ++ m2 :: Γ5 ++ m1 :: Γ4 ++ m0 :: Γ3 ++ Γ6 = (Γ0 ++ x) ++ (m2 :: Γ5) ++ (m1 :: Γ4) ++ (m0 :: Γ3) ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
    assert (Γ0 ++ B :: x ++ m0 :: Γ3 ++ m1 :: Γ4 ++ m2 :: Γ5 ++ Γ6 = (Γ0 ++ B :: x) ++ (m0 :: Γ3) ++ (m1 :: Γ4) ++ (m2 :: Γ5) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ0 ++ B :: x ++ m2 :: Γ5 ++ m1 :: Γ4 ++ m0 :: Γ3 ++ Γ6 = (Γ0 ++ B :: x) ++ (m2 :: Γ5) ++ (m1 :: Γ4) ++ (m0 :: Γ3) ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
Qed.

Lemma GLR_app_list_exchL : forall s se ps,
  (@list_exch_L s se) ->
  (GLRRule [ps] s) ->
  (existsT2 pse,
    (GLRRule [pse] se) *
    (@list_exch_L ps pse)).
Proof.
intros s se ps exch RA. inversion RA. inversion exch. rewrite <- H1 in H2.
inversion H2. subst.
pose (@nobox_gen_ext_exch_L (Δ0 ++ Box A :: Δ1) [A] BΓ (Γ1 ++ Γ2 ++ Γ3 ++ Γ4 ++ Γ5) (Γ1 ++ Γ4 ++ Γ3 ++ Γ2 ++ Γ5) X exch).
destruct s. destruct p. inversion l.
exists (XBoxed_list (Γ0 ++ Γ8 ++ Γ7 ++ Γ6 ++ Γ9) ++ [Box A], [A]). split.
- apply GLRRule_I.
  * unfold is_Boxed_list. intros. apply in_exch_list in H4. subst. apply H0 in H4.
    assumption.
  * subst. assumption.
- repeat rewrite XBox_app_distrib. repeat rewrite <- app_assoc. apply list_exch_LI.
Qed.

Lemma ImpR_app_list_exchR : forall s se ps,
  (@list_exch_R s se) ->
  (ImpRRule [ps] s) ->
  (existsT2 pse,
    (ImpRRule [pse] se) *
    (@list_exch_R ps pse)).
Proof.
intros s se ps exch. intro RA. inversion RA. inversion exch. subst.
inversion H. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
- destruct Δ3 ; destruct Δ4 ; destruct Δ5 ; simpl ; simpl in e0 ; simpl in exch ; subst ; try inversion e0 ; subst.
  + exists (Γ0 ++ A :: Γ1, Δ2 ++ B :: Δ1). split ; try assumption. apply list_exch_R_id.
  + exists (Γ0 ++ A :: Γ1, Δ2 ++ B :: Δ5 ++ Δ6). split ; try assumption. apply list_exch_R_id.
  + exists (Γ0 ++ A :: Γ1, Δ2 ++ B :: Δ4 ++ Δ6). split ; try assumption. apply list_exch_R_id.
  + exists (Γ0 ++ A :: Γ1, Δ2 ++ (m0 :: Δ5) ++ B :: Δ4 ++ Δ6). split.
    assert (Δ2 ++ (m0 :: Δ5) ++ B :: Δ4 ++ Δ6 = (Δ2 ++ m0 :: Δ5) ++ B :: Δ4 ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Δ2 ++ m0 :: Δ5 ++ A --> B :: Δ4 ++ Δ6 = (Δ2 ++ m0 :: Δ5) ++ A --> B :: Δ4 ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    apply ImpRRule_I. assert (Δ2 ++ B :: Δ4 ++ m0 :: Δ5 ++ Δ6 = Δ2 ++ [] ++ (B :: Δ4) ++ (m0 :: Δ5) ++ Δ6).
    reflexivity. rewrite H0. clear H0.
    assert (Δ2 ++ (m0 :: Δ5) ++ B :: Δ4 ++ Δ6 = Δ2 ++ (m0 :: Δ5) ++ (B :: Δ4) ++ [] ++ Δ6).
    reflexivity. rewrite H0. clear H0. apply list_exch_RI.
  + exists (Γ0 ++ A :: Γ1, Δ2 ++ B :: Δ3 ++ Δ6). split ; try assumption. apply list_exch_R_id.
  + exists (Γ0 ++ A :: Γ1, Δ2 ++ (m0 :: Δ5) ++ B :: Δ3 ++ Δ6). split.
    assert (Δ2 ++ m0 :: Δ5 ++ A --> B :: Δ3 ++ Δ6 = (Δ2 ++ m0 :: Δ5) ++ A --> B :: Δ3 ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Δ2 ++ (m0 :: Δ5) ++ B :: Δ3 ++ Δ6 = (Δ2 ++ m0 :: Δ5) ++ B :: Δ3 ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    apply ImpRRule_I. assert (Δ2 ++ B :: Δ3 ++ m0 :: Δ5 ++ Δ6 = Δ2 ++ (B :: Δ3) ++ [] ++ (m0 :: Δ5) ++ Δ6).
    reflexivity. rewrite H0. clear H0.
    assert (Δ2 ++ (m0 :: Δ5) ++ B :: Δ3 ++ Δ6 = Δ2 ++ (m0 :: Δ5) ++ [] ++ (B :: Δ3) ++ Δ6).
    reflexivity. rewrite H0. clear H0. apply list_exch_RI.
  + exists (Γ0 ++ A :: Γ1, (Δ2 ++ m0 :: Δ4) ++ B :: Δ3 ++ Δ6). split.
    assert (Δ2 ++ m0 :: Δ4 ++ A --> B :: Δ3 ++ Δ6 = (Δ2 ++ m0 :: Δ4) ++ A --> B :: Δ3 ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpRRule_I.
    assert (Δ2 ++ B :: Δ3 ++ m0 :: Δ4 ++ Δ6 = Δ2 ++ (B :: Δ3) ++ [] ++ (m0 :: Δ4) ++ Δ6).
    reflexivity. rewrite H0. clear H0.
    assert ((Δ2 ++ m0 :: Δ4) ++ B :: Δ3 ++ Δ6 = Δ2 ++ (m0 :: Δ4) ++ [] ++ (B :: Δ3) ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI.
  + exists (Γ0 ++ A :: Γ1, (Δ2 ++ m1 :: Δ5 ++ m0 :: Δ4) ++ B :: Δ3 ++ Δ6). split.
    assert (Δ2 ++ m1 :: Δ5 ++ m0 :: Δ4 ++ A --> B :: Δ3 ++ Δ6 = (Δ2 ++ m1 :: Δ5 ++ m0 :: Δ4) ++ A --> B :: Δ3 ++ Δ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpRRule_I.
    assert (Δ2 ++ B :: Δ3 ++ m0 :: Δ4 ++ m1 :: Δ5 ++ Δ6 = Δ2 ++ (B :: Δ3) ++ (m0 :: Δ4) ++ (m1 :: Δ5) ++ Δ6).
    reflexivity. rewrite H0. clear H0.
    assert ((Δ2 ++ m1 :: Δ5 ++ m0 :: Δ4) ++ B :: Δ3 ++ Δ6 = Δ2 ++ (m1 :: Δ5) ++ (m0 :: Δ4) ++ (B :: Δ3) ++ Δ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI.
- apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
  + destruct Δ4 ; destruct Δ5 ; simpl ; simpl in e0 ; simpl in exch ; subst ; try inversion e0 ; subst.
    * rewrite app_assoc. exists (Γ0 ++ A :: Γ1, (Δ2 ++ Δ3) ++ B :: Δ1). split ; try assumption. apply list_exch_R_id.
    * exists (Γ0 ++ A :: Γ1, Δ2 ++ B :: Δ5 ++ Δ3 ++ Δ6). split. apply ImpRRule_I.
      assert ((Δ2 ++ Δ3) ++ B :: Δ5 ++ Δ6 = Δ2 ++ Δ3 ++ [] ++ (B :: Δ5) ++ Δ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert (Δ2 ++ B :: Δ5 ++ Δ3 ++ Δ6 = Δ2 ++ (B :: Δ5) ++ [] ++ Δ3 ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI.
    * exists (Γ0 ++ A :: Γ1, Δ2 ++ B :: Δ4 ++ Δ3 ++ Δ6). split. apply ImpRRule_I.
      assert ((Δ2 ++ Δ3) ++ B :: Δ4 ++ Δ6 = Δ2 ++ Δ3 ++ [] ++ (B :: Δ4) ++ Δ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert (Δ2 ++ B :: Δ4 ++ Δ3 ++ Δ6 = Δ2 ++ (B :: Δ4) ++ [] ++ Δ3 ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI.
    * exists (Γ0 ++ A :: Γ1, (Δ2 ++ m0 :: Δ5) ++ B :: Δ4 ++ Δ3 ++ Δ6). split.
      assert (Δ2 ++ m0 :: Δ5 ++ A --> B :: Δ4 ++ Δ3 ++ Δ6 = (Δ2 ++ m0 :: Δ5) ++ A --> B :: Δ4 ++ Δ3 ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpRRule_I.
      assert ((Δ2 ++ Δ3) ++ B :: Δ4 ++ m0 :: Δ5 ++ Δ6 = Δ2 ++ Δ3 ++ (B :: Δ4) ++ (m0 :: Δ5) ++ Δ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert ((Δ2 ++ m0 :: Δ5) ++ B :: Δ4 ++ Δ3 ++ Δ6 = Δ2 ++ (m0 :: Δ5) ++ (B :: Δ4) ++ Δ3 ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI.
  + apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
    * destruct Δ5 ; simpl ; simpl in e0 ; simpl in exch ; subst ; try inversion e0 ; subst.
      { exists (Γ0 ++ A :: Γ1, (Δ2 ++ Δ4 ++ Δ3) ++ B :: Δ1). split.
        assert (Δ2 ++ Δ4 ++ Δ3 ++ A --> B :: Δ1 = (Δ2 ++ Δ4 ++ Δ3) ++ A --> B :: Δ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpRRule_I.
        assert ((Δ2 ++ Δ3 ++ Δ4) ++ B :: Δ1 = Δ2 ++ Δ3 ++ [] ++ Δ4 ++ B :: Δ1). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0.
        assert ((Δ2 ++ Δ4 ++ Δ3) ++ B :: Δ1 = Δ2 ++ Δ4 ++ [] ++ Δ3 ++ B :: Δ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI. }
      { exists (Γ0 ++ A :: Γ1, Δ2 ++ B :: Δ5 ++ Δ4 ++ Δ3 ++ Δ6). split. apply ImpRRule_I.
        assert ((Δ2 ++ Δ3 ++ Δ4) ++ B :: Δ5 ++ Δ6 = Δ2 ++ Δ3 ++ Δ4 ++ (B :: Δ5) ++ Δ6). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0.
        assert (Δ2 ++ B :: Δ5 ++ Δ4 ++ Δ3 ++ Δ6 = Δ2 ++ (B :: Δ5) ++ Δ4 ++ Δ3 ++ Δ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI. }
    * apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
      { exists (Γ0 ++ A :: Γ1, (Δ2 ++ Δ5 ++ Δ4 ++ Δ3) ++ B :: Δ1). split.
        assert (Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ A --> B :: Δ1 = (Δ2 ++ Δ5 ++ Δ4 ++ Δ3) ++ A --> B :: Δ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpRRule_I.
        repeat rewrite <- app_assoc. apply list_exch_RI. }
      { exists (Γ0 ++ A :: Γ1, (Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ x0) ++ B :: Δ1). split.
        assert (Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ x0 ++ A --> B :: Δ1 = (Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ x0) ++ A --> B :: Δ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpRRule_I.
        repeat rewrite <- app_assoc. apply list_exch_RI. }
      { destruct x0.
        - simpl in e0. subst. rewrite app_nil_r.
          exists (Γ0 ++ A :: Γ1, (Δ2 ++ x ++ Δ4 ++ Δ3) ++ B :: Δ1). split.
          assert (Δ2 ++ x ++ Δ4 ++ Δ3 ++ A --> B :: Δ1 = (Δ2 ++ x ++ Δ4 ++ Δ3) ++ A --> B :: Δ1).
          repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpRRule_I.
          repeat rewrite <- app_assoc. apply list_exch_RI.
        - inversion e0. subst.
          exists (Γ0 ++ A :: Γ1, (Δ2 ++ x) ++ B :: x0 ++ Δ4 ++ Δ3 ++ Δ6). split.
          assert (Δ2 ++ (x ++ A --> B :: x0) ++ Δ4 ++ Δ3 ++ Δ6 = (Δ2 ++ x) ++ A --> B :: x0 ++ Δ4 ++ Δ3 ++ Δ6).
          repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpRRule_I.
          assert ((Δ2 ++ Δ3 ++ Δ4 ++ x) ++ B :: x0 ++ Δ6 = Δ2 ++ Δ3 ++ Δ4 ++ (x ++ B :: x0) ++ Δ6).
          repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
          assert ((Δ2 ++ x) ++ B :: x0 ++ Δ4 ++ Δ3 ++ Δ6 = Δ2 ++ (x ++ B :: x0) ++ Δ4 ++ Δ3 ++ Δ6).
          repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
          apply list_exch_RI. }
    * destruct x ; destruct Δ5 ; simpl ; simpl in e0 ; simpl in exch ; subst ; try inversion e0 ; subst.
      { rewrite app_nil_r. exists (Γ0 ++ A :: Γ1, (Δ2 ++ x0 ++ Δ3) ++ B :: Δ1). split.
        assert (Δ2 ++ x0 ++ Δ3 ++ A --> B :: Δ1 = (Δ2 ++ x0 ++ Δ3) ++ A --> B :: Δ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpRRule_I.
        assert ((Δ2 ++ Δ3 ++ x0) ++ B :: Δ1 = Δ2 ++ Δ3 ++ [] ++ x0 ++ B :: Δ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert ((Δ2 ++ x0 ++ Δ3) ++ B :: Δ1 = Δ2 ++ x0 ++ [] ++ Δ3 ++ B :: Δ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI. }
      { rewrite app_nil_r. exists (Γ0 ++ A :: Γ1, Δ2 ++ B :: Δ5 ++ x0 ++ Δ3 ++ Δ6). split.
        apply ImpRRule_I.
        assert ((Δ2 ++ Δ3 ++ x0) ++ B :: Δ5 ++ Δ6 = Δ2 ++ Δ3 ++ x0 ++ (B :: Δ5) ++ Δ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert (Δ2 ++ B :: Δ5 ++ x0 ++ Δ3 ++ Δ6 = Δ2 ++ (B :: Δ5) ++ x0 ++ Δ3 ++ Δ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI. }
      { exists (Γ0 ++ A :: Γ1, (Δ2 ++ x0) ++ B :: x ++ Δ3 ++ Δ6). split.
        assert (Δ2 ++ (x0 ++ A --> B :: x) ++ Δ3 ++ Δ6 = (Δ2 ++ x0) ++ A --> B :: x ++ Δ3 ++ Δ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpRRule_I.
        assert ((Δ2 ++ Δ3 ++ x0) ++ B :: x ++ Δ6 = Δ2 ++ Δ3 ++ [] ++ (x0 ++ B :: x) ++ Δ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert ((Δ2 ++ x0) ++ B :: x ++ Δ3 ++ Δ6 = Δ2 ++ (x0 ++ B :: x) ++ [] ++ Δ3 ++ Δ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI. }
      { exists (Γ0 ++ A :: Γ1, (Δ2 ++ m0 :: Δ5 ++ x0) ++ B :: x ++ Δ3 ++ Δ6). split.
        assert (Δ2 ++ m0 :: Δ5 ++ (x0 ++ A --> B :: x) ++ Δ3 ++ Δ6 = (Δ2 ++ m0 :: Δ5 ++ x0) ++ A --> B :: x ++ Δ3 ++ Δ6).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0. apply ImpRRule_I.
        assert ((Δ2 ++ Δ3 ++ x0) ++ B :: x ++ m0 :: Δ5 ++ Δ6 = Δ2 ++ Δ3 ++ (x0 ++ B :: x) ++ (m0 :: Δ5) ++ Δ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert ((Δ2 ++ m0 :: Δ5 ++ x0) ++ B :: x ++ Δ3 ++ Δ6 = Δ2 ++ (m0 :: Δ5) ++ (x0 ++ B :: x) ++ Δ3 ++ Δ6).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        apply list_exch_RI. }
  + destruct x0 ; destruct Δ4 ; destruct Δ5 ; simpl ; simpl in e0 ; simpl in exch ; subst ; try inversion e0 ; subst.
    * rewrite app_nil_r. rewrite app_assoc. exists (Γ0 ++ A :: Γ1, (Δ2 ++ x) ++ B :: Δ1). split ; try assumption. apply list_exch_R_id.
    * rewrite app_nil_r. exists (Γ0 ++ A :: Γ1, Δ2 ++ B :: Δ5 ++ x ++ Δ6). split. apply ImpRRule_I.
      assert ((Δ2 ++ x) ++ B :: Δ5 ++ Δ6 = Δ2 ++ x ++ [] ++ (B :: Δ5) ++ Δ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert (Δ2 ++ B :: Δ5 ++ x ++ Δ6 = Δ2 ++ (B :: Δ5) ++ [] ++ x ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI.
    * rewrite app_nil_r. exists (Γ0 ++ A :: Γ1, Δ2 ++ B :: Δ4 ++ x ++ Δ6). split. apply ImpRRule_I.
      assert ((Δ2 ++ x) ++ B :: Δ4 ++ Δ6 = Δ2 ++ x ++ [] ++ (B :: Δ4) ++ Δ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert (Δ2 ++ B :: Δ4 ++ x ++ Δ6 = Δ2 ++ (B :: Δ4) ++ [] ++ x ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI.
    * rewrite app_nil_r. exists (Γ0 ++ A :: Γ1, (Δ2 ++ m0 :: Δ5) ++ B :: Δ4 ++ x ++ Δ6). split.
      assert (Δ2 ++ m0 :: Δ5 ++ A --> B :: Δ4 ++ x ++ Δ6 = (Δ2 ++ m0 :: Δ5) ++ A --> B :: Δ4 ++ x ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpRRule_I.
      assert ((Δ2 ++ x) ++ B :: Δ4 ++ m0 :: Δ5 ++ Δ6 = Δ2 ++ x ++ (B :: Δ4) ++ (m0 :: Δ5) ++ Δ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert ((Δ2 ++ m0 :: Δ5) ++ B :: Δ4 ++ x ++ Δ6 = Δ2 ++ (m0 :: Δ5) ++ (B :: Δ4) ++ x ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI.
    * exists (Γ0 ++ A :: Γ1, (Δ2 ++ x) ++ B :: x0 ++ Δ6). split.
      assert (Δ2 ++ (x ++ A --> B :: x0) ++ Δ6 = (Δ2 ++ x) ++ A --> B :: x0 ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpRRule_I.
      apply list_exch_R_id.
    * exists (Γ0 ++ A :: Γ1, (Δ2 ++ m0 :: Δ5 ++ x) ++ B :: x0 ++ Δ6). split.
      assert (Δ2 ++ m0 :: Δ5 ++ (x ++ A --> B :: x0) ++ Δ6 = (Δ2 ++ m0 :: Δ5 ++ x) ++ A --> B :: x0 ++ Δ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpRRule_I.
      assert ((Δ2 ++ x) ++ B :: x0 ++ m0 :: Δ5 ++ Δ6 = Δ2 ++ [] ++ (x ++ B :: x0) ++ (m0 :: Δ5) ++ Δ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert ((Δ2 ++ m0 :: Δ5 ++ x) ++ B :: x0 ++ Δ6 = Δ2 ++ (m0 :: Δ5) ++ (x ++ B :: x0) ++ [] ++ Δ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
      rewrite H0. clear H0. apply list_exch_RI.
    * exists (Γ0 ++ A :: Γ1, (Δ2 ++ m0 :: Δ4 ++ x) ++ B :: x0 ++ Δ6). split.
      assert (Δ2 ++ m0 :: Δ4 ++ (x ++ A --> B :: x0) ++ Δ6 = (Δ2 ++ m0 :: Δ4 ++ x) ++ A --> B :: x0 ++ Δ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpRRule_I.
      assert ((Δ2 ++ x) ++ B :: x0 ++ m0 :: Δ4 ++ Δ6 = Δ2 ++ [] ++ (x ++ B :: x0) ++ (m0 :: Δ4) ++ Δ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert ((Δ2 ++ m0 :: Δ4 ++ x) ++ B :: x0 ++ Δ6 = Δ2 ++ (m0 :: Δ4) ++ (x ++ B :: x0) ++ [] ++ Δ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
      rewrite H0. clear H0. apply list_exch_RI.
    * exists (Γ0 ++ A :: Γ1, (Δ2 ++ m1 :: Δ5 ++ m0 :: Δ4 ++ x) ++ B :: x0 ++ Δ6). split.
      assert (Δ2 ++ m1 :: Δ5 ++ m0 :: Δ4 ++ (x ++ A --> B :: x0) ++ Δ6 = (Δ2 ++ m1 :: Δ5 ++ m0 :: Δ4 ++ x) ++ A --> B :: x0 ++ Δ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpRRule_I.
      assert ((Δ2 ++ x) ++ B :: x0 ++ m0 :: Δ4 ++ m1 :: Δ5 ++ Δ6 = Δ2 ++ (x ++ B :: x0) ++ (m0 :: Δ4) ++ (m1 :: Δ5) ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      assert ((Δ2 ++ m1 :: Δ5 ++ m0 :: Δ4 ++ x) ++ B :: x0 ++ Δ6 = Δ2 ++ (m1 :: Δ5) ++ (m0 :: Δ4) ++ (x ++ B :: x0) ++ Δ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
      rewrite H0. clear H0. apply list_exch_RI.
- destruct x ; destruct Δ3 ; destruct Δ4 ; destruct Δ5 ; simpl ; simpl in e0 ; simpl in exch ;
  subst ; try inversion e0 ; subst.
  * rewrite app_nil_r. exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1). split ; try assumption.
    apply list_exch_R_id.
  * rewrite app_nil_r. exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ5 ++ Δ6). split ; try assumption.
    apply list_exch_R_id.
  * rewrite app_nil_r. exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ4 ++ Δ6). split ; try assumption.
    apply list_exch_R_id.
  * rewrite app_nil_r. exists (Γ0 ++ A :: Γ1, (Δ0 ++ m0 :: Δ5) ++ B :: Δ4 ++ Δ6). split.
    assert (Δ0 ++ m0 :: Δ5 ++ A --> B :: Δ4 ++ Δ6 = (Δ0 ++ m0 :: Δ5) ++ A --> B :: Δ4 ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpRRule_I.
    assert (Δ0 ++ B :: Δ4 ++ m0 :: Δ5 ++ Δ6 = Δ0 ++ [] ++ (B :: Δ4) ++ (m0 :: Δ5) ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert ((Δ0 ++ m0 :: Δ5) ++ B :: Δ4 ++ Δ6 = Δ0 ++ (m0 :: Δ5) ++ (B :: Δ4) ++ [] ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_RI.
  * rewrite app_nil_r. exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ3 ++ Δ6). split ; try assumption.
    apply list_exch_R_id.
  * rewrite app_nil_r. exists (Γ0 ++ A :: Γ1, (Δ0 ++ m0 :: Δ5) ++ B :: Δ3 ++ Δ6). split.
    assert (Δ0 ++ m0 :: Δ5 ++ A --> B :: Δ3 ++ Δ6 = (Δ0 ++ m0 :: Δ5) ++ A --> B :: Δ3 ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpRRule_I.
    assert (Δ0 ++ B :: Δ3 ++ m0 :: Δ5 ++ Δ6 = Δ0 ++ [] ++ (B :: Δ3) ++ (m0 :: Δ5) ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert ((Δ0 ++ m0 :: Δ5) ++ B :: Δ3 ++ Δ6 = Δ0 ++ (m0 :: Δ5) ++ (B :: Δ3) ++ [] ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_RI.
  * rewrite app_nil_r. exists (Γ0 ++ A :: Γ1, (Δ0 ++ m0 :: Δ4) ++ B :: Δ3 ++ Δ6). split.
    assert (Δ0 ++ m0 :: Δ4 ++ A --> B :: Δ3 ++ Δ6 = (Δ0 ++ m0 :: Δ4) ++ A --> B :: Δ3 ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpRRule_I.
    assert ((Δ0 ++ m0 :: Δ4) ++ B :: Δ3 ++ Δ6 = Δ0 ++ (m0 :: Δ4) ++ (B :: Δ3) ++ [] ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Δ0 ++ B :: Δ3 ++ m0 :: Δ4 ++ Δ6 = Δ0 ++ [] ++ (B :: Δ3) ++ (m0 :: Δ4) ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_RI.
  * rewrite app_nil_r. exists (Γ0 ++ A :: Γ1, (Δ0 ++ m1 :: Δ5 ++ m0 :: Δ4) ++ B :: Δ3 ++ Δ6). split.
    assert (Δ0 ++ m1 :: Δ5 ++ m0 :: Δ4 ++ A --> B :: Δ3 ++ Δ6 = (Δ0 ++ m1 :: Δ5 ++ m0 :: Δ4) ++ A --> B :: Δ3 ++ Δ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpRRule_I.
    assert (Δ0 ++ B :: Δ3 ++ m0 :: Δ4 ++ m1 :: Δ5 ++ Δ6 = Δ0 ++ (B :: Δ3) ++ (m0 :: Δ4) ++ (m1 :: Δ5) ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert ((Δ0 ++ m1 :: Δ5 ++ m0 :: Δ4) ++ B :: Δ3 ++ Δ6 = Δ0 ++ (m1 :: Δ5) ++ (m0 :: Δ4) ++ (B :: Δ3) ++ Δ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_RI.
  * exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: x ++ Δ6). split. repeat rewrite <- app_assoc. apply ImpRRule_I.
    apply list_exch_R_id.
  * exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: x ++ m0 :: Δ5 ++ Δ6). split. repeat rewrite <- app_assoc. apply ImpRRule_I.
    apply list_exch_R_id.
  * exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: x ++ m0 :: Δ4 ++ Δ6). split. repeat rewrite <- app_assoc. apply ImpRRule_I.
    apply list_exch_R_id.
  * exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: x ++ m1 :: Δ5 ++ m0 :: Δ4 ++ Δ6). split.
    repeat rewrite <- app_assoc. apply ImpRRule_I.
    assert (Δ0 ++ B :: x ++ m0 :: Δ4 ++ m1 :: Δ5 ++ Δ6 = (Δ0 ++ B :: x) ++ (m0 :: Δ4) ++ [] ++ (m1 :: Δ5) ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Δ0 ++ B :: x ++ m1 :: Δ5 ++ m0 :: Δ4 ++ Δ6 = (Δ0 ++ B :: x) ++ (m1 :: Δ5) ++ [] ++ (m0 :: Δ4) ++ Δ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_RI.
  * exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: x ++ m0 :: Δ3 ++ Δ6). split. repeat rewrite <- app_assoc. apply ImpRRule_I.
    apply list_exch_R_id.
  * exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: x ++ m1 :: Δ5 ++ m0 :: Δ3 ++ Δ6). split.
    repeat rewrite <- app_assoc. apply ImpRRule_I.
    assert (Δ0 ++ B :: x ++ m0 :: Δ3 ++ m1 :: Δ5 ++ Δ6 = (Δ0 ++ B :: x) ++ (m0 :: Δ3) ++ [] ++ (m1 :: Δ5) ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Δ0 ++ B :: x ++ m1 :: Δ5 ++ m0 :: Δ3 ++ Δ6 = (Δ0 ++ B :: x) ++ (m1 :: Δ5) ++ [] ++ (m0 :: Δ3) ++ Δ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_RI.
  * exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: x ++ m1 :: Δ4 ++ m0 :: Δ3 ++ Δ6). split.
    repeat rewrite <- app_assoc. apply ImpRRule_I.
    assert (Δ0 ++ B :: x ++ m0 :: Δ3 ++ m1 :: Δ4 ++ Δ6 = (Δ0 ++ B :: x) ++ (m0 :: Δ3) ++ [] ++ (m1 :: Δ4) ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Δ0 ++ B :: x ++ m1 :: Δ4 ++ m0 :: Δ3 ++ Δ6 = (Δ0 ++ B :: x) ++ (m1 :: Δ4) ++ [] ++ (m0 :: Δ3) ++ Δ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_RI.
  * exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: x ++ m2 :: Δ5 ++ m1 :: Δ4 ++ m0 :: Δ3 ++ Δ6). split.
    repeat rewrite <- app_assoc. apply ImpRRule_I.
    assert (Δ0 ++ B :: x ++ m0 :: Δ3 ++ m1 :: Δ4 ++ m2 :: Δ5 ++ Δ6 = (Δ0 ++ B :: x) ++ (m0 :: Δ3) ++ (m1 :: Δ4) ++ (m2 :: Δ5) ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Δ0 ++ B :: x ++ m2 :: Δ5 ++ m1 :: Δ4 ++ m0 :: Δ3 ++ Δ6 = (Δ0 ++ B :: x) ++ (m2 :: Δ5) ++ (m1 :: Δ4) ++ (m0 :: Δ3) ++ Δ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_RI.
Qed.

Lemma ImpL_app_list_exchR : forall s se ps1 ps2,
  (@list_exch_R s se) ->
  (ImpLRule [ps1;ps2] s) ->
  (existsT2 pse1 pse2,
    (ImpLRule [pse1;pse2] se) *
    (@list_exch_R ps1 pse1) *
    (@list_exch_R ps2 pse2)).
Proof.
intros s se ps1 ps2 exch. intro RA. inversion RA. inversion exch. subst.
inversion H. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
- exists (Γ0 ++ Γ1, Δ2 ++ A :: Δ5 ++ Δ4 ++ Δ3 ++ Δ6).
  exists (Γ0 ++ B :: Γ1, Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6). split. split. apply ImpLRule_I.
  assert (Δ2 ++ A :: Δ3 ++ Δ4 ++ Δ5 ++ Δ6 = (Δ2 ++ [A]) ++ Δ3 ++ Δ4 ++ Δ5 ++ Δ6).
  rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
  assert (Δ2 ++ A :: Δ5 ++ Δ4 ++ Δ3 ++ Δ6 = (Δ2 ++ [A]) ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6).
  rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI.
  apply list_exch_RI.
- apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
  + exists (Γ0 ++ Γ1, (Δ2 ++ Δ5) ++ A :: Δ4 ++ Δ3 ++ Δ6).
    exists (Γ0 ++ B :: Γ1, Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6).
    split. split.
    assert (Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6 = (Δ2 ++ Δ5) ++ Δ4 ++ Δ3 ++ Δ6). rewrite app_assoc.
    reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
    repeat rewrite <- app_assoc.
    assert (Δ2 ++ Δ3 ++ A :: Δ4 ++ Δ5 ++ Δ6 = Δ2 ++ Δ3 ++ (A :: Δ4) ++ Δ5 ++ Δ6).
    reflexivity. rewrite H0. clear H0.
    assert (Δ2 ++ Δ5 ++ A :: Δ4 ++ Δ3 ++ Δ6 = Δ2 ++ Δ5 ++ (A :: Δ4) ++ Δ3 ++ Δ6).
    reflexivity. rewrite H0. clear H0. apply list_exch_RI. apply list_exch_RI.
  + apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
    * exists (Γ0 ++ Γ1, (Δ2 ++ Δ5 ++ Δ4) ++ A :: Δ3 ++ Δ6).
      exists (Γ0 ++ B :: Γ1, Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6). split. split.
      assert (Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6 = (Δ2 ++ Δ5 ++ Δ4) ++ Δ3 ++ Δ6). repeat rewrite app_assoc.
      reflexivity. rewrite H0. clear H0. apply ImpLRule_I. repeat rewrite <- app_assoc.
      assert (Δ2 ++ Δ3 ++ Δ4 ++ A :: Δ5 ++ Δ6 = Δ2 ++ Δ3 ++ (Δ4 ++ [A]) ++ Δ5 ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      assert (Δ2 ++ Δ5 ++ Δ4 ++ A :: Δ3 ++ Δ6 = Δ2 ++ Δ5 ++ (Δ4 ++ [A]) ++ Δ3 ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI. apply list_exch_RI.
    * apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
      { repeat rewrite <- app_assoc. exists (Γ0 ++ Γ1, Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ A :: Δ6).
        exists (Γ0 ++ B :: Γ1, Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6).
        split. split. repeat rewrite app_assoc. apply ImpLRule_I. apply list_exch_RI.
        apply list_exch_RI. }
      { repeat rewrite <- app_assoc. exists (Γ0 ++ Γ1, Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ x0 ++ A :: Δ1).
        exists (Γ0 ++ B :: Γ1, Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ x0 ++ Δ1). split. split. repeat rewrite app_assoc.
        apply ImpLRule_I. apply list_exch_RI. apply list_exch_RI. }
      { repeat rewrite <- app_assoc. exists (Γ0 ++ Γ1, Δ2 ++ (x ++ A :: x0) ++ Δ4 ++ Δ3 ++ Δ6).
        exists (Γ0 ++ B :: Γ1, Δ2 ++ x ++ x0 ++ Δ4 ++ Δ3 ++ Δ6). split. split.
        assert (Δ2 ++ (x ++ A :: x0) ++ Δ4 ++ Δ3 ++ Δ6 = (Δ2 ++ x) ++ A :: x0 ++ Δ4 ++ Δ3 ++ Δ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert (Δ2 ++ x ++ x0 ++ Δ4 ++ Δ3 ++ Δ6 = (Δ2 ++ x) ++ x0 ++ Δ4 ++ Δ3 ++ Δ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        apply ImpLRule_I.
        assert (Δ2 ++ Δ3 ++ Δ4 ++ x ++ A :: x0 ++ Δ6 = Δ2 ++ Δ3 ++ Δ4 ++ (x ++ A :: x0) ++ Δ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply list_exch_RI.
        assert (Δ2 ++ Δ3 ++ Δ4 ++ x ++ x0 ++ Δ6 = Δ2 ++ Δ3 ++ Δ4 ++ (x ++ x0) ++ Δ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert (Δ2 ++ x ++ x0 ++ Δ4 ++ Δ3 ++ Δ6 = Δ2 ++ (x ++ x0) ++ Δ4 ++ Δ3 ++ Δ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply list_exch_RI. }
    * repeat rewrite <- app_assoc. exists (Γ0 ++ Γ1, Δ2 ++ Δ5 ++ (x0 ++ A :: x) ++ Δ3 ++ Δ6).
      exists (Γ0 ++ B :: Γ1, Δ2 ++ Δ5 ++ (x0 ++ x) ++ Δ3 ++ Δ6). split. split.
      assert (Δ2 ++ Δ5 ++ (x0 ++ A :: x) ++ Δ3 ++ Δ6 = (Δ2 ++ Δ5 ++ x0) ++ A :: x ++ Δ3 ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      assert (Δ2 ++ Δ5 ++ x0 ++ x ++ Δ3 ++ Δ6 = (Δ2 ++ Δ5 ++ x0) ++ x ++ Δ3 ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      assert (Δ2 ++ Δ5 ++ (x0 ++ x) ++ Δ3 ++ Δ6 = (Δ2 ++ Δ5 ++ x0) ++ x ++ Δ3 ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      apply ImpLRule_I.
      assert (Δ2 ++ Δ3 ++ x0 ++ A :: x ++ Δ5 ++ Δ6 = Δ2 ++ Δ3 ++ (x0 ++ A :: x) ++ Δ5 ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply list_exch_RI.
      assert (Δ2 ++ Δ3 ++ x0 ++ x ++ Δ5 ++ Δ6 = Δ2 ++ Δ3 ++ (x0 ++ x) ++ Δ5 ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply list_exch_RI.
  + repeat rewrite <- app_assoc. exists (Γ0 ++ Γ1, Δ2 ++ Δ5 ++ Δ4 ++ (x ++ A :: x0) ++ Δ6).
    exists (Γ0 ++ B :: Γ1, Δ2 ++ Δ5 ++ Δ4 ++ (x ++ x0) ++ Δ6). split. split.
    assert (Δ2 ++ Δ5 ++ Δ4 ++ (x ++ A :: x0) ++ Δ6 = (Δ2 ++ Δ5 ++ Δ4 ++ x) ++ A :: x0 ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Δ2 ++ Δ5 ++ Δ4 ++ x ++ x0 ++ Δ6 = (Δ2 ++ Δ5 ++ Δ4 ++ x) ++ x0 ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Δ2 ++ Δ5 ++ Δ4 ++ (x ++ x0) ++ Δ6 = (Δ2 ++ Δ5 ++ Δ4 ++ x) ++ x0 ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    apply ImpLRule_I.
    assert (Δ2 ++ x ++ A :: x0 ++ Δ4 ++ Δ5 ++ Δ6 = Δ2 ++ (x ++ A :: x0) ++ Δ4 ++ Δ5 ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply list_exch_RI.
    assert (Δ2 ++ x ++ x0 ++ Δ4 ++ Δ5 ++ Δ6 = Δ2 ++ (x ++ x0) ++ Δ4 ++ Δ5 ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply list_exch_RI.
- repeat rewrite <- app_assoc. exists (Γ0 ++ Γ1, Δ0 ++ A :: x ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6).
  exists (Γ0 ++ B :: Γ1, Δ0 ++ x ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6). split. split. apply ImpLRule_I.
  assert (Δ0 ++ A :: x ++ Δ3 ++ Δ4 ++ Δ5 ++ Δ6 = (Δ0 ++ A :: x) ++ Δ3 ++ Δ4 ++ Δ5 ++ Δ6).
  repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
  assert (Δ0 ++ A :: x ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6 = (Δ0 ++ A :: x) ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6).
  repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI.
  assert (Δ0 ++ x ++ Δ3 ++ Δ4 ++ Δ5 ++ Δ6 = (Δ0 ++ x) ++ Δ3 ++ Δ4 ++ Δ5 ++ Δ6).
  repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
  assert (Δ0 ++ x ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6 = (Δ0 ++ x) ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6).
  repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI.
Qed.

Lemma GLR_app_list_exchR : forall s se ps,
  (@list_exch_R s se) ->
  (GLRRule [ps] s) ->
  (existsT2 pse,
    (GLRRule [pse] se) *
    (@list_exch_R ps pse)).
Proof.
intros s se ps exch RA. inversion RA. inversion exch. rewrite <- H1 in H2.
inversion H2. exists (XBoxed_list BΓ ++ [Box A], [A]). split.
- pose (partition_1_element2 Δ2 Δ3 Δ4 Δ5 Δ6 Δ0 Δ1 (Box A) H6). destruct s0.
  + repeat destruct s0. repeat destruct p. subst. assert (E : (Δ0 ++ Box A :: x0) ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6 = Δ0 ++ Box A :: (x0 ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6)).
    repeat rewrite <- app_assoc. reflexivity. rewrite E. apply GLRRule_I.
    * assumption.
    * assumption.
  + destruct s0.
    * repeat destruct s0. repeat destruct p. subst. assert (E: Δ2 ++ Δ5 ++ Δ4 ++ (x ++ Box A :: x0) ++ Δ6 = (Δ2 ++ Δ5 ++ Δ4 ++ x) ++ Box A :: x0 ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite E. apply GLRRule_I.
      { assumption. }
      { assumption. }
    * destruct s0.
      { repeat destruct s0. repeat destruct p. subst. assert (E: Δ2 ++ Δ5 ++ (x ++ Box A :: x0) ++ Δ3 ++ Δ6 = (Δ2 ++ Δ5 ++ x) ++ Box A :: x0 ++ Δ3 ++ Δ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite E. apply GLRRule_I.
        - assumption.
        - assumption. }
      { destruct s0.
        - repeat destruct s0. repeat destruct p. subst. assert (E: Δ2 ++ (x ++ Box A :: x0) ++ Δ4 ++ Δ3 ++ Δ6 = (Δ2 ++ x) ++ Box A :: x0 ++ Δ4 ++ Δ3 ++ Δ6).
          repeat rewrite <- app_assoc. reflexivity. rewrite E. apply GLRRule_I.
          + assumption.
          + assumption.
        - repeat destruct s0. repeat destruct p. subst. assert (E: Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ x ++ Box A :: Δ1 = (Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ x) ++ Box A :: Δ1).
          repeat rewrite <- app_assoc. reflexivity. rewrite E. apply GLRRule_I.
          + assumption.
          + assumption. }
- apply list_exch_R_id.
Qed.

(* We can now prove the admissibility of list_exchange on the left. *)

Theorem GLS_adm_list_exch_L : forall s,
        (GLS_prv s) ->
        (forall se, (@list_exch_L s se) ->
        (GLS_prv se)).
Proof.
intros s D. apply derrec_all_rect with 
(Q:= fun x => forall (se : Seq),
list_exch_L x se ->
derrec GLS_rules  (fun _ : Seq => False)
  se)
in D.
- exact D.
- intros concl F. inversion F.
- intros ps concl rule. induction rule.
  (* IdP *)
  * intros ders IH se exch. inversion i. apply derI with (ps:=[]).
    apply IdP.
    + assert (Permstose: existsT2 eΓ0 eΓ1, se = (eΓ0 ++ # P :: eΓ1, Δ0 ++ # P :: Δ1)).
      { pose (list_exch_L_permLR exch). subst. destruct s0 with (Γ0:=Γ0) (Γ1:=Γ1) (Δ0:=Δ0) (Δ1:=Δ1)
      (C:=# P) (D:=# P). auto. exists x. assumption. }
      destruct Permstose. repeat destruct s0. subst. apply IdPRule_I.
    + apply dersrec_all in ders. apply dersrec_all. subst. assumption.
  (* BotL *)
  * intros ders IH se exch. apply derI with (ps:=ps).
    + apply BotL. inversion b. symmetry in H0.
      assert (Permstose: existsT2 eΓ0 eΓ1, se = ((eΓ0 ++ Bot :: eΓ1), Δ)).
      { apply list_exch_L_permL with (s:=c) (Γ0:=Γ0) (Γ1:=Γ1) (Δ:=Δ). assumption.
        assumption. }
      destruct Permstose. destruct s0. subst. apply BotLRule_I.
    + apply dersrec_all in ders. apply dersrec_all. assumption.
  (* ImpR *)
  * intros ders IH se exch. inversion i. subst. pose (ImpR_app_list_exchL exch i).
    destruct s0. destruct p. apply derI with (ps:=[x]).
    + apply ImpR. assumption.
    + apply dersrec_all. apply dersrec_all in ders. inversion i0.
      inversion i. apply ForallT_inv in IH. apply ForallT_cons.
      { apply IH. subst. assumption. }
      { apply ForallT_nil. }
  (* ImpL *)
  * intros ders IH se exch. inversion i. subst. pose (ImpL_app_list_exchL exch i).
    destruct s0. destruct s0. destruct p. destruct p. apply derI with (ps:=[x;x0]).
    + apply ImpL. assumption.
    + apply dersrec_all. apply dersrec_all in ders. inversion i0.
      inversion i. apply ForallT_cons_inv in IH. destruct IH.
      apply ForallT_inv in f. apply ForallT_cons.
      { apply d. subst. assumption. }
      { apply ForallT_cons. apply f. subst. assumption. apply ForallT_nil. }
  (* GLR *)
  * intros ders IH se exch. inversion g. subst. pose (GLR_app_list_exchL exch g).
    destruct s0. destruct p. apply derI with (ps:=[x]).
    + apply GLR. assumption.
    + apply dersrec_all. apply dersrec_all in ders. inversion g0.
      inversion g. apply ForallT_inv in IH. apply ForallT_cons.
      { apply IH. subst. assumption. }
      { apply ForallT_nil. }
Qed.

Theorem GLS_adm_list_exch_R : forall s,
        (GLS_prv s) ->
        (forall se, (@list_exch_R s se) ->
        (GLS_prv se)).
Proof.
intros s D. apply derrec_all_rect with
(Q:= fun x => forall (se : Seq),
list_exch_R x se ->
derrec GLS_rules  (fun _ : Seq => False)
  se)
in D.
- exact D.
- intros concl F. inversion F.
- intros ps concl rule. induction rule.
  (* IdP *)
  * intros ders IH se exch. inversion i. apply derI with (ps:=[]).
    apply IdP.
    + assert (Permstose: existsT2 eΔ0 eΔ1, se = (Γ0 ++ # P :: Γ1, eΔ0 ++ # P :: eΔ1)).
      { pose (list_exch_R_permLR exch). subst. destruct s0 with (Γ0:=Γ0) (Γ1:=Γ1) (Δ0:=Δ0) (Δ1:=Δ1)
      (C:=# P) (D:=# P). auto. exists x. assumption. }
      destruct Permstose. repeat destruct s0. subst. apply IdPRule_I.
    + apply dersrec_all in ders. apply dersrec_all. subst. assumption.
  (* BotL *)
  * intros ders IH se exch. apply derI with (ps:=ps).
    + apply BotL. inversion b. symmetry in H0.
      assert (Permstose: existsT2 eΔ, se = ((Γ0 ++ Bot :: Γ1), eΔ)).
      { apply list_exch_R_permL with (s:=c) (Γ0:=Γ0) (Γ1:=Γ1) (Δ:=Δ). assumption.
        assumption. }
      destruct Permstose. subst. apply BotLRule_I.
    + apply dersrec_all in ders. apply dersrec_all. assumption.
  (* ImpR *)
  * intros ders IH se exch. inversion i. subst. pose (ImpR_app_list_exchR exch i).
    destruct s0. destruct p. apply derI with (ps:=[x]).
    + apply ImpR. assumption.
    + apply dersrec_all. apply dersrec_all in ders. inversion i0.
      inversion i. apply ForallT_inv in IH. apply ForallT_cons.
      { apply IH. subst. assumption. }
      { apply ForallT_nil. }
  (* ImpL *)
  * intros ders IH se exch. inversion i. subst. pose (ImpL_app_list_exchR exch i).
    destruct s0. destruct s0. destruct p. destruct p. apply derI with (ps:=[x;x0]).
    + apply ImpL. assumption.
    + apply dersrec_all. apply dersrec_all in ders. inversion i0.
      inversion i. apply ForallT_cons_inv in IH. destruct IH.
      apply ForallT_inv in f. apply ForallT_cons.
      { apply d. subst. assumption. }
      { apply ForallT_cons. apply f. subst. assumption. apply ForallT_nil. }
  (* GLR *)
  * intros ders IH se exch. inversion g. subst. pose (GLR_app_list_exchR exch g).
    destruct s0. destruct p. apply derI with (ps:=[x]).
    + apply GLR. assumption.
    + apply dersrec_all. apply dersrec_all in ders. inversion g0.
      inversion g. apply ForallT_inv in IH. apply ForallT_cons.
      { apply IH. subst. assumption. }
      { apply ForallT_nil. }
Qed.

(* Now we can turn to the derivability of list_exchange. *)

Inductive Closure {X: Type} (F : X -> Type) (P : X -> X -> Type) : X -> Type :=
  | InitClo : forall x, F x -> Closure F P x
  | IndClo : forall x y,  Closure F P y -> (P y x) -> Closure F P x.

Inductive ExcClosure (hyps : Seq -> Type) : Seq -> Type :=
  | InitLExch : forall x, Closure hyps list_exch_L x -> ExcClosure hyps x
  | InitRExch : forall x, Closure hyps list_exch_R x -> ExcClosure hyps x
  | IndLExch : forall x y, ExcClosure hyps x -> list_exch_L x y -> ExcClosure hyps y
  | IndRExch : forall x y, ExcClosure hyps x -> list_exch_R x y -> ExcClosure hyps y.

Theorem GLS_der_list_exch_L : forall hyps s,
        (derrec GLS_rules hyps s) ->
        (forall se, (@list_exch_L s se) ->
        (derrec GLS_rules (ExcClosure hyps) se)).
Proof.
intros hyps s D. apply derrec_all_rect with
(Q:= fun x => forall (se : Seq),
list_exch_L x se ->
derrec GLS_rules  (ExcClosure hyps) se) in D.
- exact D.
- intros concl H1 se exch. apply dpI. apply InitLExch. apply IndClo with (y:=concl).
  apply InitClo. assumption. assumption.
- intros ps concl rule. induction rule.
  (* IdP *)
  * intros ders IH se exch. inversion i. apply derI with (ps:=[]).
    apply IdP.
    + assert (Permstose: existsT2 eΓ0 eΓ1, se = (eΓ0 ++ # P :: eΓ1, Δ0 ++ # P :: Δ1)).
      { pose (list_exch_L_permLR exch). subst. destruct s0 with (Γ0:=Γ0) (Γ1:=Γ1) (Δ0:=Δ0) (Δ1:=Δ1)
      (C:=# P) (D:=# P). auto. exists x. assumption. }
      destruct Permstose. repeat destruct s0. subst. apply IdPRule_I.
    + apply dersrec_all in ders. apply dersrec_nil.
  (* BotL *)
  * intros ders IH se exch. apply derI with (ps:=ps).
    + apply BotL. inversion b. symmetry in H0.
      assert (Permstose: existsT2 eΓ0 eΓ1, se = ((eΓ0 ++ Bot :: eΓ1), Δ)).
      { apply list_exch_L_permL with (s:=c) (Γ0:=Γ0) (Γ1:=Γ1) (Δ:=Δ). assumption.
        assumption. }
      destruct Permstose. repeat destruct s0. subst. apply BotLRule_I.
    + apply dersrec_all in ders. inversion b. apply dersrec_nil.
  (* ImpR *)
  * intros ders IH se exch. inversion i. subst. pose (ImpR_app_list_exchL exch i).
    destruct s0. destruct p. apply derI with (ps:=[x]).
    + apply ImpR. assumption.
    + apply dersrec_all. apply dersrec_all in ders. inversion i0.
      inversion i. apply ForallT_inv in IH. apply ForallT_cons.
      { apply IH. subst. assumption. }
      { apply ForallT_nil. }
  (* ImpL *)
  * intros ders IH se exch. inversion i. subst. pose (ImpL_app_list_exchL exch i).
    destruct s0. destruct s0. destruct p. destruct p. apply derI with (ps:=[x;x0]).
    + apply ImpL. assumption.
    + apply dersrec_all. apply dersrec_all in ders. inversion i0.
      inversion i. apply ForallT_cons_inv in IH. destruct IH.
      apply ForallT_inv in f. apply ForallT_cons.
      { apply d. subst. assumption. }
      { apply ForallT_cons. apply f. subst. assumption. apply ForallT_nil. }
  (* GLR *)
  * intros ders IH se exch. inversion g. subst. pose (GLR_app_list_exchL exch g).
    destruct s0. destruct p. apply derI with (ps:=[x]).
    + apply GLR. assumption.
    + apply dersrec_all. apply dersrec_all in ders. inversion g0.
      inversion g. apply ForallT_inv in IH. apply ForallT_cons.
      { apply IH. subst. assumption. }
      { apply ForallT_nil. }
Qed.

Theorem GLS_der_list_exch_R : forall hyps s,
        (derrec GLS_rules hyps s) ->
        (forall se, (@list_exch_R s se) ->
        (derrec GLS_rules (ExcClosure hyps) se)).
Proof.
intros hyps s D. apply derrec_all_rect with
(Q:= fun x => forall (se : Seq),
list_exch_R x se ->
derrec GLS_rules  (ExcClosure hyps) se) in D.
- exact D.
- intros concl H1 se exch. apply dpI. apply InitRExch. apply IndClo with (y:=concl).
  apply InitClo. assumption. assumption.
- intros ps concl rule. induction rule.
  (* IdP *)
  * intros ders IH se exch. inversion i. apply derI with (ps:=[]).
    apply IdP.
    + assert (Permstose: existsT2 eΔ0 eΔ1, se = (Γ0 ++ # P :: Γ1, eΔ0 ++ # P :: eΔ1)).
      { pose (list_exch_R_permLR exch). subst. destruct s0 with (Γ0:=Γ0) (Γ1:=Γ1) (Δ0:=Δ0) (Δ1:=Δ1)
      (C:=# P) (D:=# P). auto. exists x. assumption. }
      destruct Permstose. repeat destruct s0. subst. apply IdPRule_I.
    + apply dersrec_all in ders. apply dersrec_nil.
  (* BotL *)
  * intros ders IH se exch. apply derI with (ps:=ps).
    + apply BotL. inversion b. symmetry in H0.
      assert (Permstose: existsT2 eΔ, se = ((Γ0 ++ Bot :: Γ1), eΔ)).
      { apply list_exch_R_permL with (s:=c) (Γ0:=Γ0) (Γ1:=Γ1) (Δ:=Δ). assumption.
        assumption. }
      destruct Permstose. subst. apply BotLRule_I.
    + apply dersrec_all in ders. inversion b. apply dersrec_nil.
  (* ImpR *)
  * intros ders IH se exch. inversion i. subst. pose (ImpR_app_list_exchR exch i).
    destruct s0. destruct p. apply derI with (ps:=[x]).
    + apply ImpR. assumption.
    + apply dersrec_all. apply dersrec_all in ders. inversion i0.
      inversion i. apply ForallT_inv in IH. apply ForallT_cons.
      { apply IH. subst. assumption. }
      { apply ForallT_nil. }
  (* ImpL *)
  * intros ders IH se exch. inversion i. subst. pose (ImpL_app_list_exchR exch i).
    destruct s0. destruct s0. destruct p. destruct p. apply derI with (ps:=[x;x0]).
    + apply ImpL. assumption.
    + apply dersrec_all. apply dersrec_all in ders. inversion i0.
      inversion i. apply ForallT_cons_inv in IH. destruct IH.
      apply ForallT_inv in f. apply ForallT_cons.
      { apply d. subst. assumption. }
      { apply ForallT_cons. apply f. subst. assumption. apply ForallT_nil. }
  (* GLR *)
  * intros ders IH se exch. inversion g. subst. pose (GLR_app_list_exchR exch g).
    destruct s0. destruct p. apply derI with (ps:=[x]).
    + apply GLR. assumption.
    + apply dersrec_all. apply dersrec_all in ders. inversion g0.
      inversion g. apply ForallT_inv in IH. apply ForallT_cons.
      { apply IH. subst. assumption. }
      { apply ForallT_nil. }
Qed.

(* In fact, we can prove that exchange is height-preserving admissible. *)

Theorem GLS_hpadm_list_exch_R : forall (k : nat) s
                                  (D0: GLS_prv s),
        k = (derrec_height D0) ->
        (forall se, (list_exch_R s se) ->
        (existsT2 (D1 : GLS_prv se),
          derrec_height D1 <=k)).
Proof.
(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall (s : Seq)
  (D0 : derrec GLS_rules  (fun _ : Seq => False) s),
x = derrec_height D0 ->
(forall se,
(list_exch_R s se) ->
(existsT2
  D1 : derrec GLS_rules 
         (fun _ : Seq => False) se,
  derrec_height D1 <= x)))).
apply s. intros n IH. clear s.
(* Now we do the actual proof-theoretical work. *)
intros s0 D0. remember D0 as D0'. destruct D0.
(* D0 ip a leaf *)
- inversion f.
(* D0 is ends with an application of rule *)
- intros hei se exch. inversion exch.
  assert (DersNil: dersrec GLS_rules  (fun _ : Seq => False) []).
  apply dersrec_nil. inversion g.
  (* IdP *)
  * inversion H1. subst. inversion H5. subst. simpl.
    assert (In # P (Δ0 ++ Δ3 ++ Δ2 ++ Δ1 ++ Δ4)). assert (In # P (Δ0 ++ Δ1 ++ Δ2 ++ Δ3 ++ Δ4)).
    rewrite <- H2. apply in_or_app. right. apply in_eq. apply in_app_or in H. apply in_or_app.
    destruct H. auto. apply in_app_or in H. right. apply in_or_app. destruct H. right. apply in_or_app.
    right. apply in_or_app. auto. apply in_app_or in H. destruct H. right. apply in_or_app. auto.
    apply in_app_or in H. destruct H. auto. right. apply in_or_app. right. apply in_or_app. auto.
    apply in_splitT in H. destruct H. destruct s. rewrite e.
    assert (IdPRule [] (Γ0 ++ # P :: Γ1, x ++ # P :: x0)). apply IdPRule_I. apply IdP in H.
    pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (Γ0 ++ # P :: Γ1, x ++ # P :: x0) H DersNil). exists d0. simpl. rewrite dersrec_height_nil.
    lia. reflexivity.
  (* BotL *)
  * inversion H1. subst. inversion H5. subst. simpl.
    assert (BotLRule [] (Γ0 ++ ⊥ :: Γ1, Δ0 ++ Δ3 ++ Δ2 ++ Δ1 ++ Δ4)). apply BotLRule_I. apply BotL in H.
    pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (Γ0 ++ ⊥ :: Γ1, Δ0 ++ Δ3 ++ Δ2 ++ Δ1 ++ Δ4) H DersNil). exists d0. simpl. rewrite dersrec_height_nil.
    lia. reflexivity.
  (* ImpR *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (ImpR_app_list_exchR exch H1). destruct s. destruct p.
    apply ImpR in i. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec_height d J0). destruct s.
    assert (E: derrec_height x0 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x0 = derrec_height x0). auto.
    pose (IH (derrec_height x0) E (Γ0 ++ A :: Γ1, Δ5 ++ B :: Δ6) x0 E1 x l).
    destruct s. pose (dlCons x1 DersNil).
    pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
    (ps:=[x]) (Γ0 ++ Γ1, Δ0 ++ Δ3 ++ Δ2 ++ Δ1 ++ Δ4) i d0). exists d1. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* ImpL *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (ImpL_app_list_exchR exch H1). repeat destruct s. repeat destruct p.
    apply ImpL in i. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec2_height d J0). repeat destruct s.
    assert (E: derrec_height x1 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x1 = derrec_height x1). auto.
    pose (IH (derrec_height x1) E (Γ0 ++ Γ1, Δ5 ++ A :: Δ6) x1 E1 x l0).
    destruct s.
    assert (E2: derrec_height x2 < S (dersrec_height d)). lia.
    assert (E3: derrec_height x2 = derrec_height x2). auto.
    pose (IH (derrec_height x2) E2 (Γ0 ++ B :: Γ1, Δ5 ++ Δ6) x2 E3 x0 l).
    destruct s. pose (dlCons x4 DersNil). pose (dlCons x3 d0).
    pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
    (ps:=[x; x0]) (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ3 ++ Δ2 ++ Δ1 ++ Δ4) i d1). exists d2. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* GLR *)
  * inversion X. subst. inversion H5. subst. simpl. simpl in IH.
    pose (GLR_app_list_exchR exch X). destruct s. destruct p.
    apply GLR in g0. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec_height d J0). destruct s.
    assert (E: derrec_height x0 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x0 = derrec_height x0). auto.
    pose (IH (derrec_height x0) E (XBoxed_list BΓ ++ [Box A], [A]) x0 E1 x l).
    destruct s. pose (dlCons x1 DersNil).
    pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
    (ps:=[x]) (Γ, Δ0 ++ Δ3 ++ Δ2 ++ Δ1 ++ Δ4) g0 d0). exists d1. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
Qed.

Theorem GLS_hpadm_list_exch_L : forall (k : nat) s
                                  (D0: GLS_prv s),
        k = (derrec_height D0) ->
        (forall se, (list_exch_L s se) ->
        (existsT2 (D1 : GLS_prv se),
          derrec_height D1 <=k)).
Proof.
(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall (s : Seq)
  (D0 : derrec GLS_rules  (fun _ : Seq => False) s),
x = derrec_height D0 ->
(forall se,
(list_exch_L s se) ->
(existsT2
  D1 : derrec GLS_rules 
         (fun _ : Seq => False) se,
  derrec_height D1 <= x)))).
apply s. intros n IH. clear s.
(* Now we do the actual proof-theoretical work. *)
intros s0 D0. remember D0 as D0'. destruct D0.
(* D0 ip a leaf *)
- inversion f.
(* D0 is ends with an application of rule *)
- intros hei se exch. inversion exch.
  assert (DersNil: dersrec GLS_rules  (fun _ : Seq => False) []).
  apply dersrec_nil. inversion g.
  (* IdP *)
  * inversion H1. subst. inversion H5. subst. simpl.
    assert (In # P (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4)). assert (In # P (Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4)).
    rewrite <- H0. apply in_or_app. right. apply in_eq. apply in_app_or in H. apply in_or_app.
    destruct H. auto. apply in_app_or in H. right. apply in_or_app. destruct H. right. apply in_or_app.
    right. apply in_or_app. auto. apply in_app_or in H. destruct H. right. apply in_or_app. auto.
    apply in_app_or in H. destruct H. auto. right. apply in_or_app. right. apply in_or_app. auto.
    apply in_splitT in H. destruct H. destruct s. rewrite e.
    assert (IdPRule [] (x ++ # P :: x0, Δ0 ++ # P :: Δ1)). apply IdPRule_I. apply IdP in H.
    pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x ++ # P :: x0, Δ0 ++ # P :: Δ1) H DersNil). exists d0. simpl. rewrite dersrec_height_nil.
    lia. reflexivity.
  (* BotL *)
  * inversion H1. subst. inversion H5. subst. simpl.
    assert (In (⊥) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4)). assert (In (⊥) (Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4)).
    rewrite <- H0. apply in_or_app. right. apply in_eq. apply in_app_or in H. apply in_or_app.
    destruct H. auto. apply in_app_or in H. right. apply in_or_app. destruct H. right. apply in_or_app.
    right. apply in_or_app. auto. apply in_app_or in H. destruct H. right. apply in_or_app. auto.
    apply in_app_or in H. destruct H. auto. right. apply in_or_app. right. apply in_or_app. auto.
    apply in_splitT in H. destruct H. destruct s. rewrite e.
    assert (BotLRule [] (x ++ ⊥ :: x0, Δ)). apply BotLRule_I. apply BotL in H.
    pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x ++ ⊥ :: x0, Δ) H DersNil). exists d0. simpl. rewrite dersrec_height_nil.
    lia. reflexivity.
  (* ImpR *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (ImpR_app_list_exchL exch H1). destruct s. destruct p.
    apply ImpR in i. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec_height d J0). destruct s.
    assert (E: derrec_height x0 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x0 = derrec_height x0). auto.
    pose (IH (derrec_height x0) E (Γ5 ++ A :: Γ6, Δ0 ++ B :: Δ1) x0 E1 x l).
    destruct s. pose (dlCons x1 DersNil).
    pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
    (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, Δ0 ++ A --> B :: Δ1) i d0). exists d1. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* ImpL *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (ImpL_app_list_exchL exch H1). repeat destruct s. repeat destruct p.
    apply ImpL in i. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec2_height d J0). repeat destruct s.
    assert (E: derrec_height x1 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x1 = derrec_height x1). auto.
    pose (IH (derrec_height x1) E (Γ5 ++ Γ6, Δ0 ++ A :: Δ1) x1 E1 x l0).
    destruct s.
    assert (E2: derrec_height x2 < S (dersrec_height d)). lia.
    assert (E3: derrec_height x2 = derrec_height x2). auto.
    pose (IH (derrec_height x2) E2 (Γ5 ++ B :: Γ6, Δ0 ++ Δ1) x2 E3 x0 l).
    destruct s. pose (dlCons x4 DersNil). pose (dlCons x3 d0).
    pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
    (ps:=[x; x0]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, Δ0 ++ Δ1) i d1). exists d2. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* GLR *)
  * inversion X. subst. inversion H5. subst. simpl. simpl in IH.
    pose (GLR_app_list_exchL exch X). destruct s. destruct p.
    apply GLR in g0. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec_height d J0). destruct s.
    assert (E: derrec_height x0 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x0 = derrec_height x0). auto.
    pose (IH (derrec_height x0) E (XBoxed_list BΓ ++ [Box A], [A]) x0 E1 x l).
    destruct s. pose (dlCons x1 DersNil).
    pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
    (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, Δ0 ++ Box A :: Δ1) g0 d0). exists d1. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
Qed.

Theorem GLS_adm_list_exch_LR : forall s (D0: GLS_prv s),
        (forall se, ((list_exch_L s se) -> (GLS_prv se)) *
                        ((list_exch_R s se) -> (GLS_prv se))).
Proof.
intros. assert (J1: derrec_height D0 = derrec_height D0). auto. split ; intro.
- pose (@GLS_hpadm_list_exch_L (derrec_height D0) s D0 J1 se H). destruct s0 ; auto.
- pose (@GLS_hpadm_list_exch_R (derrec_height D0) s D0 J1 se H). destruct s0 ; auto.
Qed.


