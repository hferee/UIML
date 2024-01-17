Require Import List.
Export ListNotations.
Require Import Lia.
Require Import PeanoNat.

Require Import KS_calc.

(* First, as we want to mimic sequents based on multisets of formulae we need to
obtain exchange. *)

(* Definition of exchange with lists of formulae directly. It is more general and
makes the proofs about exchange easier to handle. *)

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
pose (list_exch_R_permL _ _ exch). pose (s0 Γ0 Γ1 (Δ0 ++ D :: Δ1) C).
pose (s1 Eq). destruct s2.
pose (list_exch_R_permR _ _ exch). pose (s2 (Γ0 ++ C :: Γ1) Δ0 Δ1 D).
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
pose (list_exch_L_permR _ _ exch). pose (s0 (Γ0 ++ C :: Γ1) Δ0 Δ1 D).
pose (s1 Eq). destruct s2.
pose (list_exch_L_permL _ _ exch). pose (s2 Γ0 Γ1 (Δ0 ++ D :: Δ1) C).
pose (s3 Eq). destruct s4. destruct s4. exists x0. exists x1. assumption.
Qed.

(* Some lemmas about nobox_gen_ext and exchange. *)

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
    intros. pose (InT_list_exch_R _ _ _ exch). pose (p x0). destruct p0. pose (univ_gen_ext_nil_all_P gen).
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
    * subst. apply all_P_univ_gen_ext_nil. intros. pose (InT_list_exch_L _ _ _ exch).
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