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

  (* Operation to remove and replace an element in a list. *)

  Fixpoint replace (A B : MPropF) (l : list MPropF) : list MPropF :=
    match l with
      | [] => []
      | C :: t => if (eq_dec_form A C) then B :: replace A B t else C :: (replace A B t)
    end.

  Lemma replace_app : forall l0 l1 A B, replace A B (l0 ++ l1) = replace A B l0 ++ replace A B l1.
  Proof.
  induction l0 ; simpl ; auto. intros. destruct (eq_dec_form A a).
  subst. simpl. rewrite IHl0 ; auto. simpl. rewrite IHl0 ; auto.
  Qed.

  Lemma in_not_touched_replace : forall (l : list MPropF) [A B C : MPropF], In C l -> C <> A ->
              In C (replace A B l).
  Proof.
  induction l ; simpl ; intros ; auto. destruct (eq_dec_form A a) ; subst.
  destruct H. exfalso ; auto. apply in_cons ; auto.
  destruct H ; subst. apply in_eq. apply in_cons ; auto.
  Qed.

  Lemma in_replace : forall l A B C, A <> B -> In C (replace A B l) -> (In C l \/ C = B) /\ A <> C.
  Proof.
  induction l ; simpl ; intros ; auto. destruct (eq_dec_form A a) ; subst.
  inversion H0 ; subst. split ; auto. pose (IHl _ _ _ H H1). destruct a0. split ; auto. destruct H2 ; auto.
  inversion H0 ; subst. split ; auto. pose (IHl _ _ _ H H1). destruct a0 ; split ; auto. destruct H2 ; auto.
  Qed.

  Lemma notin_replace : forall l (A B : MPropF), (In A l -> False) -> replace A B l = l.
  Proof.
  induction l ; simpl ; intros ; auto. destruct (eq_dec_form A a) ; subst. destruct H ; auto. rewrite IHl ; auto.
  Qed.

  Lemma univ_gen_ext_count_occ : forall l0 l1 A, univ_gen_ext (fun x : MPropF => x = A) l0 l1 ->
                count_occ eq_dec_form l0 A <= count_occ eq_dec_form l1 A.
  Proof.
  intros. induction X ; simpl ; try lia. all: destruct (eq_dec_form x A) ; try lia.
  Qed.

  Lemma univ_gen_ext_S_count_occ : forall l0 l1 A, (count_occ eq_dec_form l0 A < count_occ eq_dec_form l1 A) ->
                (univ_gen_ext (fun x : MPropF => x = A) l0 l1) ->
                existsT2 l2 l3 l4 l5, (l0 = l2 ++ l3) * (l1 = l4 ++ A :: l5) * (univ_gen_ext (fun x : MPropF => x = A) l2 l4) *
                                              (univ_gen_ext (fun x : MPropF => x = A) l3 l5).
  Proof.
  intros. revert H. induction X ; simpl ; intros ; auto ; try lia.
  - destruct (eq_dec_form x A) ; subst.
    * assert ((count_occ eq_dec_form l A) < (count_occ eq_dec_form le A)). lia. apply IHX in H0.
      destruct H0. destruct s. destruct s. destruct s. destruct p. destruct p. destruct p ; subst.
      exists (A :: x). exists x0. exists (A :: x1). exists x2. simpl. repeat split ; auto.
      apply univ_gen_ext_cons ; auto.
    * apply IHX in H. destruct H. destruct s. destruct s. destruct s. destruct p. destruct p. destruct p ; subst.
      exists (x :: x0). exists x1. exists (x :: x2). exists x3. simpl. repeat split ; auto.
      apply univ_gen_ext_cons ; auto.
  - destruct (eq_dec_form x A) ; subst.
    * exists []. exists l. exists []. exists le. simpl. repeat split ; auto. apply univ_gen_ext_nil.
    * apply IHX in H. destruct H. destruct s. destruct s. destruct s. destruct p. destruct p. destruct p ; subst.
      exists x. exists x0. exists (A :: x1). exists x2. simpl. repeat split ; auto.
      apply univ_gen_ext_extra ; auto.
  Qed.

  Lemma count_occ_n_imp_subformLF : forall l A B, count_occ eq_dec_form l (A --> B) * S (n_imp_subformF A) <= n_imp_subformLF l.
  Proof.
  induction l ; simpl ; intros ; auto. destruct (eq_dec_form a (A --> B)) ; subst ; auto.
  - pose (IHl A B). assert (n_imp_subformF A < n_imp_subformF (A --> B)). simpl. lia. lia.
  - pose (IHl A B). lia.
  Qed.

  Lemma count_le_n_imp : forall l A B, count_occ eq_dec_form l (A --> B) <= n_imp_subformLF l.
  Proof.
  intros. pose (count_occ_n_imp_subformLF l A B). lia.
  Qed.

  Lemma n_imp_subformLF_replace : forall l A B, n_imp_subformLF (replace (A --> B) B l) =
        (n_imp_subformLF l - ((count_occ eq_dec_form l (A --> B)) * S (n_imp_subformF A))).
  Proof.
  intros. remember (count_occ eq_dec_form l (A --> B)) as n. revert Heqn. generalize dependent B.
  generalize dependent A. generalize dependent l. induction n ; simpl ; intros.
  - rewrite notin_replace ; try lia. symmetry in Heqn. rewrite <- count_occ_not_In in Heqn ; auto.
  - assert (count_occ eq_dec_form l (A --> B) > 0). lia. apply count_occ_In in H. apply in_split in H. destruct H.
    destruct H ; subst. repeat rewrite n_imp_subformLF_dist_app. simpl. repeat rewrite count_occ_app in Heqn.
    repeat rewrite  replace_app. simpl. simpl in Heqn. destruct (eq_dec_form (A --> B) (A --> B)). 2: exfalso ; auto.
    assert (n = count_occ eq_dec_form (x ++ x0) (A --> B)). repeat rewrite count_occ_app ; lia.
    apply IHn in H.  repeat rewrite replace_app in H. simpl in H. repeat rewrite n_imp_subformLF_dist_app.
    simpl. repeat rewrite n_imp_subformLF_dist_app in H. simpl in H.
    assert ((n_imp_subformLF (replace (A --> B) B x) + (n_imp_subformF B + n_imp_subformLF (replace (A --> B) B x0)))%nat =
    (n_imp_subformF B + ((n_imp_subformLF (replace (A --> B) B x) + n_imp_subformLF (replace (A --> B) B x0))))%nat). lia.
    rewrite H0. clear H0. rewrite H. simpl. 
    assert ((n_imp_subformLF x + S (n_imp_subformF A + n_imp_subformF B + n_imp_subformLF x0) - S (n_imp_subformF A + n * S (n_imp_subformF A)))%nat =
    ((n_imp_subformLF x + n_imp_subformF A + n_imp_subformF B + n_imp_subformLF x0) - (n_imp_subformF A + n * S (n_imp_subformF A)))%nat).
    lia. rewrite H0. clear H0. rewrite Nat.sub_add_distr.
    assert ((n * S (n_imp_subformF A))%nat <= (n_imp_subformLF x + n_imp_subformLF x0)%nat).
    assert (n = (count_occ eq_dec_form x (A --> B) + (count_occ eq_dec_form x0 (A --> B)))%nat). lia.
    rewrite H0. pose (count_occ_n_imp_subformLF (x ++ x0) A B). rewrite n_imp_subformLF_dist_app in l.
    rewrite count_occ_app in l. lia. lia.
  Qed.

  Lemma univ_gen_ext_more_occ : forall l0 l1 A, univ_gen_ext (fun x : MPropF => x = A) l0 l1 ->
          (count_occ eq_dec_form l0 A) <= (count_occ eq_dec_form l1 A).
  Proof.
  intros. induction X ; simpl ; auto ; subst.
  - destruct (eq_dec_form x A) ; subst ; lia.
  - destruct (eq_dec_form A A) ; auto.
  Qed.

  Lemma univ_gen_ext_n_imp_subform : forall l0 l1 A, univ_gen_ext (fun x : MPropF => x = A) l0 l1->
                 (n_imp_subformLF l1 = (n_imp_subformLF l0 + (n_imp_subformF A * ((count_occ eq_dec_form l1 A) - (count_occ eq_dec_form l0 A))))%nat).
  Proof.
  intros. induction X ; simpl ; auto ; subst.
  - destruct (eq_dec_form x A) ; subst ; lia.
  - destruct (eq_dec_form A A). 2: exfalso ; auto. rewrite IHX. apply univ_gen_ext_more_occ in X.
    assert ((S (count_occ eq_dec_form le A) - count_occ eq_dec_form l A)%nat = S ((count_occ eq_dec_form le A) - count_occ eq_dec_form l A)).
    lia. rewrite H. lia.
  Qed.

  Lemma n_imp_subformS_ImpR_mult : forall x Γ0 Γ1 Δ0 Δ1 A B,
                              (univ_gen_ext (fun x : MPropF => x = A) (Γ0 ++ A :: Γ1) x) ->
          ((count_occ eq_dec_form (Δ0 ++ B :: Δ1) (A --> B) + count_occ eq_dec_form (Γ0 ++ A :: Γ1) A)%nat = count_occ eq_dec_form x A) ->
          (n_imp_subformS (x, replace (A --> B) B (Δ0 ++ B :: Δ1)) < n_imp_subformS (Γ0 ++ Γ1, Δ0 ++ A --> B :: Δ1)).
  Proof.
  intros. remember (count_occ eq_dec_form (Δ0 ++ B :: Δ1) (A --> B)) as n. revert H. revert Heqn. revert X.
  generalize dependent B. generalize dependent A. generalize dependent Δ1. generalize dependent Δ0. 
  generalize dependent Γ1. generalize dependent Γ0. generalize dependent x. induction n.
  - simpl. intros. symmetry in Heqn. rewrite <- count_occ_not_In in Heqn. rewrite notin_replace ; auto.
    repeat rewrite count_occ_app in H. simpl in H. destruct (eq_dec_form A A). 2: exfalso ; auto.
    unfold n_imp_subformS ; simpl. repeat rewrite n_imp_subformLF_dist_app ; simpl.
    assert (n_imp_subformLF x = (n_imp_subformLF Γ0 + n_imp_subformLF Γ1 + n_imp_subformF A)%nat).
    pose (univ_gen_ext_n_imp_subform _ _ _ X). rewrite e0. repeat rewrite count_occ_app. simpl.
    destruct (eq_dec_form A A). 2: exfalso ; auto. repeat rewrite n_imp_subformLF_dist_app ; simpl. lia.
    lia.
  - intros. repeat rewrite replace_app. simpl. repeat rewrite count_occ_app in H. simpl in H. destruct (eq_dec_form A A). 2: exfalso ; auto.
    destruct (eq_dec_form (A --> B) B). exfalso. assert (length_form (A --> B) = length_form B).
    rewrite e0 ; auto. simpl in H0 ; lia. repeat rewrite count_occ_app in Heqn. simpl in Heqn.
    destruct (eq_dec_form B (A --> B)). exfalso. assert (length_form (A --> B) = length_form B).
    rewrite <- e0 ; auto. simpl in H0 ; lia.
    unfold n_imp_subformS ; simpl. repeat rewrite n_imp_subformLF_dist_app ; simpl.
    assert (n_imp_subformLF x = (n_imp_subformLF Γ0 + n_imp_subformLF Γ1 + (n_imp_subformF A * S (S n)))%nat).
    pose (univ_gen_ext_n_imp_subform _ _ _ X). rewrite e0. repeat rewrite count_occ_app. simpl.
    destruct (eq_dec_form A A). 2: exfalso ; auto. repeat rewrite n_imp_subformLF_dist_app ; simpl. lia.
    rewrite H0.
    pose (n_imp_subformLF_replace Δ0 A B). rewrite e0. clear e0.
    pose (n_imp_subformLF_replace Δ1 A B). rewrite e0. clear e0.
    pose (count_occ_n_imp_subformLF Δ0 A B).
    pose (count_occ_n_imp_subformLF Δ1 A B). lia.
Qed.

  (* This lemma is crucial. *)

  Lemma mult_ImpR : forall s0 s1 A B,
          InT s1 (Canopy (repeat A (count_occ eq_dec_form (snd s0) (A --> B)) ++ (fst s0), replace (A --> B) B (snd s0))) ->
          InT s1 (Canopy s0).
  Proof.
  intros s0 s1 A B. remember (count_occ eq_dec_form (snd s0) (A --> B)) as n. revert Heqn. generalize dependent B.
  generalize dependent A. generalize dependent s1. generalize dependent s0. induction n ; simpl ; intros.
  - symmetry in Heqn. rewrite <- count_occ_not_In in Heqn. rewrite notin_replace in H ; auto. destruct s0 ; auto.
  - assert (count_occ eq_dec_form (snd s0) (A --> B) > 0). lia. apply count_occ_In in H0. destruct s0. simpl in H0.
    simpl in H. simpl in Heqn. apply In_InT in H0. apply InT_split in H0. destruct H0. destruct s ; subst.
    repeat rewrite count_occ_app in Heqn. simpl in Heqn. repeat rewrite replace_app in H.
    simpl in H. destruct (eq_dec_form (A --> B) (A --> B)). 2: exfalso ; auto.
    assert (n = count_occ eq_dec_form (x ++ x0) (A --> B)). repeat rewrite count_occ_app ; lia.
    pose (IHn (A :: l, x ++ B :: x0) s1 A B). simpl in i.
    repeat rewrite count_occ_app in i. simpl in i. repeat rewrite replace_app in i.
    simpl in i. destruct (eq_dec_form B (A --> B)). exfalso. assert (length_form (A --> B) = length_form B). rewrite <- e0 ; auto.
    simpl in H1 ; lia. destruct (eq_dec_form (A --> B) B). exfalso. assert (length_form (A --> B) = length_form B). rewrite e0 ; auto.
    simpl in H1 ; lia. repeat rewrite count_occ_app in H0. pose (i H0).
    assert (repeat A n ++ A :: l = A :: repeat A n ++ l). assert (repeat A n ++ A :: l = (repeat A n ++ [A]) ++ l).
    rewrite <- app_assoc. auto. rewrite H1. rewrite <- repeat_cons. simpl ; auto. rewrite H1 in i0. apply i0 in H.
    apply ImpRule_Canopy with (prems:=[(A :: l, x ++ B :: x0)]) (prem:=(A :: l, x ++ B :: x0)) ; auto.
     left. epose (ImpRRule_I _ _ []). simpl in i1 ; apply i1. apply InT_eq.
  Qed.





