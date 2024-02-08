Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import general_export.

Require Import GLS_export.

Require Import UIGL_Def_measure.
Require Import UIGL_Canopy.
Require Import UIGL_irred_short.
Require Import UIGL_basics.
Require Import UIGL_LexSeq.
Require Import UIGL_PermutationT.
Require Import UIGL_PermutationTS.

  Section nodupseq.

  Definition nodupseq (s : Seq) := (nodup eq_dec_form (fst s), nodup eq_dec_form (snd s)).

  End nodupseq.

  Lemma nodup_app : forall l0 l1 l2, (nodup eq_dec_form l0 = nodup eq_dec_form l1) -> (nodup eq_dec_form (l0 ++ l2) = nodup eq_dec_form (l1 ++ l2)).
  Proof.
  induction l0.
  - simpl ; intros. assert (l1 = []). destruct l1 ; auto. exfalso. simpl in H. destruct (in_dec eq_dec_form m l1).
    apply (nodup_In eq_dec_form) in i. rewrite <- H in i ; inversion i. inversion H. subst. simpl. auto.
  - induction l1.
    + simpl ; intros. destruct (in_dec eq_dec_form a l0) ; simpl in *.
       assert (l0 = []). apply (nodup_In eq_dec_form) in i. rewrite H in i. inversion i. subst. simpl. inversion i. inversion H.
    + simpl in * ; intros. destruct (in_dec eq_dec_form a l0) ; simpl in *. destruct (in_dec eq_dec_form a0 l1) ; simpl in *.
       destruct (in_dec eq_dec_form a (l0 ++ l2)) ; simpl in * ; auto. destruct (in_dec eq_dec_form a0 (l1 ++ l2)) ; simpl in * ; auto.
       exfalso. apply n. apply in_or_app ; auto. exfalso. apply n. apply in_or_app ; auto.
       destruct (in_dec eq_dec_form a (l0 ++ l2)). destruct (in_dec eq_dec_form a0 (l1 ++ l2)) ; simpl in * ; auto.
       apply in_app_or in i1. destruct i1. exfalso ; auto. pose (IHl0 (a0 :: l1) l2). simpl in e.
       assert (nodup eq_dec_form (l0 ++ l2) = (if in_dec eq_dec_form a0 (l1 ++ l2) then nodup eq_dec_form (l1 ++ l2) else a0 :: nodup eq_dec_form (l1 ++ l2))).
       apply e. clear e. destruct (in_dec eq_dec_form a0 l1) ; auto. exfalso ; auto. clear e. destruct (in_dec eq_dec_form a0 (l1 ++ l2)).
       auto. exfalso. apply n0 ; apply in_or_app ; auto. pose (IHl0 (a0 :: l1) l2). simpl in e.
       assert (nodup eq_dec_form (l0 ++ l2) = (if in_dec eq_dec_form a0 (l1 ++ l2) then nodup eq_dec_form (l1 ++ l2) else a0 :: nodup eq_dec_form (l1 ++ l2))).
       apply e. clear e. destruct (in_dec eq_dec_form a0 l1) ; auto. exfalso ; auto. clear e. destruct (in_dec eq_dec_form a0 (l1 ++ l2)) ; auto.
       exfalso ; auto. destruct (in_dec eq_dec_form a0 (l1 ++ l2)) ; simpl in * ; auto. apply in_app_or in i0. destruct i0.
       exfalso ; auto. exfalso. apply n0. apply in_or_app ; auto. exfalso. apply n0. apply in_or_app ; auto.
       destruct (in_dec eq_dec_form a0 l1) ; simpl in *. pose (IHl1 l2 H). rewrite e. destruct (in_dec eq_dec_form a0 (l1 ++ l2)) ; auto.
       exfalso ; apply n0 ; apply in_or_app ; auto. inversion H ; subst.
       destruct (in_dec eq_dec_form a0 (l0 ++ l2)) ; simpl in *. apply in_app_or in i ; destruct i. exfalso ; auto.
       destruct (in_dec eq_dec_form a0 (l1 ++ l2)) ; simpl in *. apply in_app_or in i ; destruct i. exfalso ; auto.
       apply IHl0 ; auto. exfalso ; apply n1 ; apply in_or_app ; auto.
       destruct (in_dec eq_dec_form a0 (l1 ++ l2)) ; simpl in *. apply in_app_or in i ; destruct i. exfalso ; auto.
       exfalso ; apply n1 ; apply in_or_app ; auto. rewrite IHl0 with (l1:=l1) ; auto.
  Qed.

  Lemma In_XBoxed_list : forall l A, In A (XBoxed_list (top_boxes l)) -> (In A (top_boxes l) \/ exists B, In B (top_boxes l) /\ B = Box A).
  Proof.
  induction l ; intros ; auto. destruct a ; simpl ; simpl in H ; auto.
  destruct H ; subst. right. exists (Box A) ; auto. destruct H ; subst. left ; auto.
  apply IHl in H. destruct H. left ; auto. right. firstorder.
  Qed.

  Lemma In_XBoxed_list_gen : forall l A, In A (XBoxed_list l) -> (In A l \/ exists B, In B l /\ B = Box A).
  Proof.
  induction l ; intros ; auto. destruct a ; simpl ; simpl in H ; auto.
  destruct H ; auto. destruct H ; auto. apply IHl in H ; destruct H ; auto. destruct H. destruct H ; subst. right.
  exists (Box A) ; split ; auto.
  destruct H ; auto. destruct H ; auto. apply IHl in H ; destruct H ; auto. destruct H. destruct H ; subst. right.
  exists (Box A) ; split ; auto.
  destruct H ; auto. destruct H ; auto. apply IHl in H ; destruct H ; auto. destruct H. destruct H ; subst. right.
  exists (Box A) ; split ; auto.
  destruct H ; subst ; auto. right. exists (Box A) ; split ; auto. destruct H ; subst ; auto.
  apply IHl in H. destruct H ; auto. destruct H. destruct H ; subst. right. exists (Box A) ; split ; auto.
  Qed.

  Lemma XBoxed_list_In : forall l A, In (Box A) (top_boxes l) -> In A (XBoxed_list (top_boxes l)).
  Proof.
  induction l ; simpl ; intros ; auto. destruct a ; simpl ; simpl in H ; auto. destruct H. inversion H ; subst. auto.
  apply IHl in H ; auto.
  Qed.

  Lemma XBoxed_list_In_gen : forall l A, In (Box A) l -> In A (XBoxed_list l).
  Proof.
  induction l ; simpl ; intros ; auto. destruct a ; simpl ; simpl in H ; auto. 1-3: destruct H ; [inversion H | subst ; auto].
  destruct H. inversion H ; subst. auto. right. right. apply IHl ; auto.
  Qed.

  Lemma XBoxed_list_In_unfold : forall l A, (exists B, In B (top_boxes l) /\ B = Box A) -> In A (XBoxed_list (top_boxes l)).
  Proof.
  induction l ; simpl ; intros ; auto. destruct H. destruct H ; auto.
  destruct a ; simpl ; simpl in H ; auto. destruct H. destruct H. subst. destruct H.
  inversion H ; subst ; auto. right. right. apply XBoxed_list_In ; auto.
  Qed.

Theorem critical_nodupseq: forall s, critical_Seq s <-> critical_Seq (nodupseq s).
Proof.
intros. split ; intro.
- intros A HA. destruct s ; simpl in HA. apply H ; simpl. apply in_app_or in HA. apply in_or_app.
  destruct HA. left ; apply nodup_In in H0 ; auto. right ; apply nodup_In in H0 ; auto.
- intros A HA. destruct s ; simpl in HA. apply H ; simpl. apply in_app_or in HA. apply in_or_app.
  destruct HA. left ; apply nodup_In ; auto. right ; apply nodup_In ; auto.
Qed.

Theorem is_init_nodupseq: forall s, (is_init s -> is_init (nodupseq s)) * (is_init (nodupseq s) -> is_init s).
Proof.
intros. split ; intro.
- destruct X. destruct s0.
  + inversion i ; subst. unfold nodupseq ; simpl. left. left.
     assert (InT (# P) (nodup eq_dec_form (Γ0 ++ # P :: Γ1))). apply In_InT. apply nodup_In.
     apply in_or_app ; right ; apply in_eq.
     assert (InT (# P) (nodup eq_dec_form (Δ0 ++ # P :: Δ1))). apply In_InT. apply nodup_In.
     apply in_or_app ; right ; apply in_eq.
     apply InT_split in H. destruct H. destruct s. rewrite e.
     apply InT_split in H0. destruct H0. destruct s. rewrite e0.
     apply IdPRule_I.
  + inversion i ; subst. unfold nodupseq ; simpl. left. right.
     assert (InT (Box A) (nodup eq_dec_form (Γ0 ++ Box A :: Γ1))). apply In_InT. apply nodup_In.
     apply in_or_app ; right ; apply in_eq.
     assert (InT (Box A) (nodup eq_dec_form (Δ0 ++ Box A:: Δ1))). apply In_InT. apply nodup_In.
     apply in_or_app ; right ; apply in_eq.
     apply InT_split in H. destruct H. destruct s. rewrite e.
     apply InT_split in H0. destruct H0. destruct s. rewrite e0.
     apply IdBRule_I.
  + inversion b ; subst. unfold nodupseq ; simpl. right.
     assert (InT Bot (nodup eq_dec_form (Γ0 ++ Bot :: Γ1))). apply In_InT. apply nodup_In.
     apply in_or_app ; right ; apply in_eq.
     apply InT_split in H. destruct H. destruct s. rewrite e.
     apply BotLRule_I.
- destruct X. destruct s. destruct s0.
  + inversion i ; subst. left. left.
     assert (InT (# P) l). apply In_InT. rewrite <- (nodup_In eq_dec_form). rewrite <- H.
     apply in_or_app ; right ; apply in_eq.
     assert (InT (# P) l0). apply In_InT. rewrite <- (nodup_In eq_dec_form). rewrite <- H1.
     apply in_or_app ; right ; apply in_eq.
     apply InT_split in H0. destruct H0. destruct s. rewrite e.
     apply InT_split in H2. destruct H2. destruct s. rewrite e0.
     apply IdPRule_I.
  + inversion i ; subst. left. right.
     assert (InT (Box A) l). apply In_InT. rewrite <- (nodup_In eq_dec_form). rewrite <- H.
     apply in_or_app ; right ; apply in_eq.
     assert (InT (Box A) l0). apply In_InT. rewrite <- (nodup_In eq_dec_form). rewrite <- H1.
     apply in_or_app ; right ; apply in_eq.
     apply InT_split in H0. destruct H0. destruct s. rewrite e.
     apply InT_split in H2. destruct H2. destruct s. rewrite e0.
     apply IdBRule_I.
  + inversion b ; subst. destruct s ; simpl in *. right.
     assert (InT Bot l). apply In_InT. rewrite <- (nodup_In eq_dec_form). rewrite <- H.
     apply in_or_app ; right ; apply in_eq.
     apply InT_split in H0. destruct H0. destruct s. rewrite e.
     apply BotLRule_I.
Qed.

  Lemma incl_nodup_subform_boxesLF : forall l,
              (incl (subform_boxesLF l) (subform_boxesLF (nodup eq_dec_form l))) *
              (incl (subform_boxesLF (nodup eq_dec_form l)) (subform_boxesLF l)).
  Proof.
  induction l ; simpl; intuition auto with *.
  - intros A HA. destruct (in_dec eq_dec_form a l). apply a0. apply in_app_or in HA.
    destruct HA. apply In_incl_subform_boxes with (A:=a) ; auto. apply In_remove_list_In_list in H ; auto.
    simpl. apply in_app_or in HA. destruct HA. apply in_or_app ; auto. apply In_remove_list_In_list_not_In_remove_list in H.
    destruct H. apply in_or_app ; right. apply not_removed_remove_list ; auto.
  - intros A HA. destruct (in_dec eq_dec_form a l). apply b in HA. apply remove_list_is_in ; auto.
    simpl in HA. apply in_app_or in HA. destruct HA. apply in_or_app ; auto. apply In_remove_list_In_list_not_In_remove_list in H.
    destruct H. apply b in H. apply remove_list_is_in ; auto.
  Qed.

  Lemma incl_nodupseq_subform_boxesS : forall s,
              (incl (subform_boxesS s) (subform_boxesS (nodupseq s))) *
              (incl (subform_boxesS (nodupseq s)) (subform_boxesS s)).
  Proof.
  destruct s. split ; intros A HA ; unfold subform_boxesS in * ; simpl in *.
  - apply in_app_or in HA ; destruct HA. apply in_or_app ; left.
    pose (incl_nodup_subform_boxesLF l). destruct p. auto.
    apply In_remove_list_In_list_not_In_remove_list in H. destruct H.
    apply remove_list_is_in ; auto. pose (incl_nodup_subform_boxesLF l0). destruct p. auto.
  - apply in_app_or in HA ; destruct HA. apply in_or_app ; left.
    pose (incl_nodup_subform_boxesLF l). destruct p. auto.
    apply In_remove_list_In_list_not_In_remove_list in H. destruct H.
    apply remove_list_is_in ; auto. pose (incl_nodup_subform_boxesLF l0). destruct p. auto.
  Qed.

  Lemma incl_nodup_top_boxes : forall l,
              (incl (top_boxes l) (top_boxes (nodup eq_dec_form l))) *
              (incl (top_boxes (nodup eq_dec_form l)) (top_boxes l)).
  Proof.
  induction l ; simpl ; intuition auto with *.
  - intros A HA. destruct (in_dec eq_dec_form a l). apply a0. destruct a ; auto. inversion HA ; subst ; auto.
    apply is_box_in_top_boxes ; auto. eexists ; auto.
    simpl. destruct a ; simpl in * ; auto. destruct HA ; auto.
  - intros A HA. destruct (in_dec eq_dec_form a l). apply b in HA. destruct a ; auto. apply in_cons ; auto.
    destruct a ; simpl in * ; auto. destruct HA ; auto.
  Qed.

  Lemma ub_nodupseq : forall s, length (usable_boxes s) = length (usable_boxes (nodupseq s)).
  Proof.
  intros. destruct s. unfold usable_boxes ; simpl.
  assert (J1: NoDup (subform_boxesS (l, l0))). apply NoDup_subform_boxesS.
  assert (J2: NoDup (subform_boxesS (nodupseq (l, l0)))). apply NoDup_subform_boxesS.
  assert (J3: incl (subform_boxesS (l, l0)) (subform_boxesS (nodupseq (l, l0)))).
  apply incl_nodupseq_subform_boxesS.
  pose (remove_list_incr_decr2 _ _ (top_boxes (nodup eq_dec_form l)) J1 J2 J3).
  assert (J4: incl (top_boxes (nodup eq_dec_form l)) (top_boxes l)). apply incl_nodup_top_boxes.
  pose (remove_list_incr_decr3 (subform_boxesS (l, l0)) _ _ J4).
  assert (J5: incl (subform_boxesS (nodupseq (l, l0))) (subform_boxesS (l, l0))).
  apply incl_nodupseq_subform_boxesS.
  pose (remove_list_incr_decr2 _ _ (top_boxes l) J2 J1 J5).
  assert (J6: incl (top_boxes l) (top_boxes (nodup eq_dec_form l))). apply incl_nodup_top_boxes.
  pose (remove_list_incr_decr3 (subform_boxesS (nodupseq (l, l0))) _ _ J6).
  lia.
  Qed.

  Lemma n_imp_subformLF_nodup : forall l, n_imp_subformLF (nodup eq_dec_form l) <= n_imp_subformLF l.
  Proof.
  induction l ; simpl ; intuition. destruct (in_dec eq_dec_form a l) ; simpl ; lia.
  Qed.

  Lemma n_imp_subformS_nodupseq : forall s, n_imp_subformS (nodupseq s) <= n_imp_subformS s.
  Proof.
  intro s. destruct s. unfold n_imp_subformS ; simpl. pose (n_imp_subformLF_nodup l).
  pose (n_imp_subformLF_nodup l0). lia.
  Qed.

Theorem LexSeq_nodupseq: forall s0 s1, LexSeq s0 (nodupseq s1) -> LexSeq s0 s1.
Proof.
pose (d:=LexSeq_ind (fun x => forall s1, LexSeq x (nodupseq s1) -> LexSeq x s1)).
apply d. clear d. intros s0 IH s1 H. inversion H ; subst ; intuition.
- rewrite <- ub_nodupseq in H3. unfold LexSeq. unfold less_thanS. unfold GLS_termination_measure.measure.
  rewrite H3. apply DLW_wf_lex.lex_skip. apply DLW_wf_lex.lex_cons ; auto. inversion H1 ; subst.
  inversion H2. apply Nat.lt_le_trans with (m:=n_imp_subformS (nodupseq s1)) ; auto.
  apply n_imp_subformS_nodupseq.
- rewrite <- ub_nodupseq in H5. unfold LexSeq. unfold measure.
  unfold less_thanS. unfold GLS_termination_measure.measure. apply DLW_wf_lex.lex_cons ; auto.
Qed.

Theorem LexSeq_nodupseq_case: forall s, LexSeq (nodupseq s) s +
  ((n_imp_subformS (nodupseq s) = n_imp_subformS s) * (length (usable_boxes s) = length (usable_boxes (nodupseq s)))).
Proof.
intro s. pose (ub_nodupseq s). pose (n_imp_subformS_nodupseq s).
unfold LexSeq. unfold less_thanS ;unfold GLS_termination_measure.measure. rewrite <- e.
destruct (lt_decT (n_imp_subformS (nodupseq s)) (n_imp_subformS s)).
- left. apply DLW_wf_lex.lex_skip. apply DLW_wf_lex.lex_cons ; auto.
- right. split ; auto. lia.
Qed.

Theorem fixpoint_nodupseq: forall s, nodupseq s = nodupseq (nodupseq s).
Proof.
unfold nodupseq. intros ; simpl.
assert (nodup eq_dec_form (fst s) = nodup eq_dec_form (nodup eq_dec_form (fst s))).
symmetry. apply nodup_fixed_point ; auto. apply NoDup_nodup.
assert (nodup eq_dec_form (snd s) = nodup eq_dec_form (nodup eq_dec_form (snd s))).
symmetry. apply nodup_fixed_point ; auto. apply NoDup_nodup. rewrite <- H ; rewrite <- H0 ; auto.
Qed.

Theorem nodup_nil : forall (l : list MPropF), l = nil <-> nodup eq_dec_form l = nil.
Proof.
induction l ; intuition ; simpl. inversion H1. simpl in H1. destruct (in_dec eq_dec_form a l) ; auto. apply H0 in H1.
exfalso. rewrite H1 in i ; apply in_nil in i ; auto. inversion H1.
Qed.

Theorem nodup_top_boxes : forall l, nodup eq_dec_form (top_boxes l) = top_boxes (nodup eq_dec_form l).
Proof.
induction l ; intuition ; simpl. destruct a ; simpl ; auto.
destruct (in_dec eq_dec_form # n l) ; auto. destruct (in_dec eq_dec_form ⊥ l) ; auto.
destruct (in_dec eq_dec_form (a1 --> a2) l) ; auto.
destruct (in_dec eq_dec_form (Box a) l) ; destruct (in_dec eq_dec_form (Box a) (top_boxes l)) ; auto.
exfalso. apply n. apply is_box_in_top_boxes ; auto. eexists ; auto.
exfalso. apply in_top_boxes in i. destruct i. destruct s. destruct s. destruct p ; subst ; auto.
 apply n. inversion e ; subst. apply in_or_app ; right ; apply in_eq.
simpl ; rewrite IHl ; auto.
Qed.

Theorem nodup_XBoxed_list : forall l, nodup eq_dec_form (XBoxed_list (nodup eq_dec_form l)) = nodup eq_dec_form (XBoxed_list l).
Proof.
induction l ; intuition ; simpl. destruct a ; simpl ; auto.
- destruct (eq_dec_form # n # n). destruct (in_dec eq_dec_form # n l).
  destruct (in_dec eq_dec_form # n (XBoxed_list l)) ; simpl ; auto. exfalso. apply n0.
  apply list_preserv_XBoxed_list ; auto. destruct (in_dec eq_dec_form # n) ; auto ; simpl.
  destruct (eq_dec_form # n # n) ; auto. destruct (in_dec eq_dec_form # n (XBoxed_list (nodup eq_dec_form l))) ; simpl ; auto.
  exfalso. apply n1. apply In_XBoxed_list_gen in i. destruct i ; auto. exfalso ; auto. destruct H. destruct H ; subst.
  apply XBoxed_list_In_gen. apply nodup_In ; auto. exfalso ; auto.
  destruct (eq_dec_form # n # n) ; simpl ; auto. destruct (in_dec eq_dec_form # n (XBoxed_list (nodup eq_dec_form l))) ; simpl ; auto.
  exfalso. apply In_XBoxed_list_gen in i. destruct i. apply n0. apply nodup_In in H ; auto.
  destruct H. destruct H ; subst. apply n1. apply XBoxed_list_In_gen. apply nodup_In in H ; auto.
  rewrite IHl ; auto. destruct (in_dec eq_dec_form # n (XBoxed_list (nodup eq_dec_form l))) ; simpl ; auto.
  exfalso. apply n1. apply In_XBoxed_list_gen in i. destruct i. apply nodup_In in H. apply list_preserv_XBoxed_list ; auto.
  destruct H. destruct H ; subst. apply XBoxed_list_In_gen. apply nodup_In in H ; auto.
  exfalso ; auto. exfalso ; auto.
- destruct (eq_dec_form Bot Bot). destruct (in_dec eq_dec_form Bot l).
  destruct (in_dec eq_dec_form Bot (XBoxed_list l)) ; simpl ; auto. exfalso. apply n.
  apply list_preserv_XBoxed_list ; auto. destruct (in_dec eq_dec_form Bot) ; auto ; simpl.
  destruct (eq_dec_form Bot Bot) ; auto. destruct (in_dec eq_dec_form Bot (XBoxed_list (nodup eq_dec_form l))) ; simpl ; auto.
  exfalso. apply n0. apply In_XBoxed_list_gen in i. destruct i ; auto. exfalso ; auto. destruct H. destruct H ; subst.
  apply XBoxed_list_In_gen. apply nodup_In ; auto. exfalso ; auto.
  destruct (eq_dec_form Bot Bot) ; simpl ; auto. destruct (in_dec eq_dec_form Bot (XBoxed_list (nodup eq_dec_form l))) ; simpl ; auto.
  exfalso. apply In_XBoxed_list_gen in i. destruct i. apply n. apply nodup_In in H ; auto.
  destruct H. destruct H ; subst. apply n0. apply XBoxed_list_In_gen. apply nodup_In in H ; auto.
  rewrite IHl ; auto. destruct (in_dec eq_dec_form Bot (XBoxed_list (nodup eq_dec_form l))) ; simpl ; auto.
  exfalso. apply n0. apply In_XBoxed_list_gen in i. destruct i. apply nodup_In in H. apply list_preserv_XBoxed_list ; auto.
  destruct H. destruct H ; subst. apply XBoxed_list_In_gen. apply nodup_In in H ; auto.
  exfalso ; auto. exfalso ; auto.
- destruct (eq_dec_form (a1 --> a2) (a1 --> a2)). destruct (in_dec eq_dec_form (a1 --> a2) l).
  destruct (in_dec eq_dec_form (a1 --> a2) (XBoxed_list l)) ; simpl ; auto. exfalso. apply n.
  apply list_preserv_XBoxed_list ; auto. destruct (in_dec eq_dec_form (a1 --> a2)) ; auto ; simpl.
  destruct (eq_dec_form (a1 --> a2) (a1 --> a2)) ; auto. destruct (in_dec eq_dec_form (a1 --> a2) (XBoxed_list (nodup eq_dec_form l))) ; simpl ; auto.
  exfalso. apply n0. apply In_XBoxed_list_gen in i. destruct i ; auto. exfalso ; auto. destruct H. destruct H ; subst.
  apply XBoxed_list_In_gen. apply nodup_In ; auto. exfalso ; auto.
  destruct (eq_dec_form (a1 --> a2) (a1 --> a2)) ; simpl ; auto. destruct (in_dec eq_dec_form (a1 --> a2) (XBoxed_list (nodup eq_dec_form l))) ; simpl ; auto.
  exfalso. apply In_XBoxed_list_gen in i. destruct i. apply n. apply nodup_In in H ; auto.
  destruct H. destruct H ; subst. apply n0. apply XBoxed_list_In_gen. apply nodup_In in H ; auto.
  rewrite IHl ; auto. destruct (in_dec eq_dec_form (a1 --> a2) (XBoxed_list (nodup eq_dec_form l))) ; simpl ; auto.
  exfalso. apply n0. apply In_XBoxed_list_gen in i. destruct i. apply nodup_In in H. apply list_preserv_XBoxed_list ; auto.
  destruct H. destruct H ; subst. apply XBoxed_list_In_gen. apply nodup_In in H ; auto.
  exfalso ; auto. exfalso ; auto.
- destruct (in_dec eq_dec_form (Box a)). destruct (eq_dec_form (Box a) a). exfalso.
  assert (size (Box a) = size a). rewrite e ; auto. destruct a ; simpl in H ; lia.
  destruct (in_dec eq_dec_form a (XBoxed_list l)) ; simpl ; auto. destruct (in_dec eq_dec_form (Box a) (XBoxed_list l)) ; simpl ; auto.
  exfalso. apply n0. apply list_preserv_XBoxed_list ; auto. exfalso. apply n0. apply XBoxed_list_In_gen ; auto.
  destruct (eq_dec_form (Box a) a). assert (size (Box a) = size a). rewrite e ; auto. destruct a ; simpl in H ; lia.
  destruct (in_dec eq_dec_form a (XBoxed_list l)) ; simpl ; auto. destruct ( eq_dec_form (Box a) a).
  assert (size (Box a) = size a). rewrite e ; auto. destruct a ; simpl in H ; lia.
  destruct (in_dec eq_dec_form a (XBoxed_list (nodup eq_dec_form l))).
  destruct (in_dec eq_dec_form (Box a) (XBoxed_list (nodup eq_dec_form l))) ; simpl ; auto.
  destruct (in_dec eq_dec_form (Box a) (XBoxed_list l)) ; simpl ; auto. exfalso. apply n2.
  apply In_XBoxed_list_gen in i1. destruct i1 ; auto. apply list_preserv_XBoxed_list ; apply nodup_In in H ; auto.
  destruct H. destruct H ; subst. apply XBoxed_list_In_gen. apply nodup_In in H ; auto.
  destruct (in_dec eq_dec_form (Box a) (XBoxed_list l)) ; simpl ; auto. 2: rewrite IHl ; auto.
  exfalso. apply n2. apply In_XBoxed_list_gen in i1. destruct i1 ; auto. apply list_preserv_XBoxed_list ; apply nodup_In ; auto.
  destruct H. destruct H ; subst. apply XBoxed_list_In_gen. apply nodup_In ; auto.
  exfalso. apply n2. apply In_XBoxed_list_gen in i. destruct i ; auto. apply list_preserv_XBoxed_list ; apply nodup_In ; auto.
  destruct H. destruct H ; subst. apply XBoxed_list_In_gen. apply nodup_In ; auto.
  destruct (eq_dec_form (Box a) a). assert (size (Box a) = size a). rewrite e ; auto. destruct a ; simpl in H ; lia.
  destruct (in_dec eq_dec_form a (XBoxed_list (nodup eq_dec_form l))). exfalso.
  apply n1. apply In_XBoxed_list_gen in i. destruct i ; auto. apply list_preserv_XBoxed_list ; apply nodup_In in H ; auto.
  destruct H. destruct H ; subst. apply XBoxed_list_In_gen. apply nodup_In in H ; auto.
  destruct (in_dec eq_dec_form (Box a) (XBoxed_list (nodup eq_dec_form l))) ; simpl ; auto.
  destruct (in_dec eq_dec_form (Box a) (XBoxed_list l)) ; simpl ; auto. rewrite IHl ; auto.
  exfalso. apply n4. apply In_XBoxed_list_gen in i. destruct i ; auto. apply list_preserv_XBoxed_list ; apply nodup_In in H ; auto.
  destruct H. destruct H ; subst. apply XBoxed_list_In_gen. apply nodup_In in H ; auto.
  destruct (in_dec eq_dec_form (Box a) (XBoxed_list l)) ; simpl ; auto. 2: rewrite IHl ; auto.
  exfalso. apply n4. apply In_XBoxed_list_gen in i. destruct i ; auto. apply list_preserv_XBoxed_list ; apply nodup_In ; auto.
  destruct H. destruct H ; subst. apply XBoxed_list_In_gen. apply nodup_In ; auto.
Qed.

Theorem fixpoint_nodup: forall l, nodup eq_dec_form l = nodup eq_dec_form (nodup eq_dec_form l).
Proof.
intros ; simpl. symmetry. apply nodup_fixed_point ; auto. apply NoDup_nodup.
Qed.

Theorem nodupseq_GLR_prems : forall s0 s1, InT s1 (GLR_prems (nodupseq s0)) ->
        existsT2 s2, (nodup eq_dec_form (fst s1) = nodup eq_dec_form (fst s2)) * (snd s1 = snd s2) * InT s2 (GLR_prems s0).
Proof.
intros s0 s1 H. unfold GLR_prems in *. destruct (finite_GLR_premises_of_S (nodupseq s0)) ; simpl in *.
apply InT_flatten_list_InT_elem in H. destruct H. destruct p0. apply p in i0. inversion i0 ; subst.
destruct s0 ; simpl in *. unfold nodupseq in * ; subst ; simpl in *. inversion i ; subst. 2: inversion H0. simpl.
assert (InT (Box A) l0). apply In_InT. apply (nodup_In eq_dec_form). rewrite <- H2. apply in_or_app ; right ; apply in_eq.
apply InT_split in H. destruct H. destruct s. subst. exists (XBoxed_list (top_boxes l) ++ [Box A], [A]). repeat split ; simpl ; auto.
pose (nobox_gen_ext_top_boxes_identity X). rewrite e ; auto. apply nodup_app.
rewrite <- nodup_top_boxes. rewrite nodup_XBoxed_list. auto.
apply InT_trans_flatten_list with (bs:=[(XBoxed_list (top_boxes l) ++ [Box A], [A])]). apply InT_eq.
destruct (finite_GLR_premises_of_S (l, x0 ++ Box A :: x1)) ; simpl in *. apply p0.
apply GLRRule_I. intros B HB. apply in_top_boxes in HB. destruct HB. destruct s. destruct s.
destruct p1 ; subst. eexists ; auto. apply top_boxes_nobox_gen_ext.
Qed.

  Theorem incl_ctr_L_hpadm : forall Γ0 Γ1 Δ (D: GLS_prv (Γ0 ++ Γ1, Δ)), incl Γ0 Γ1 ->
          existsT2 (D0: GLS_prv (Γ1, Δ)), derrec_height D0 <= derrec_height D.
  Proof.
  induction Γ0 ; simpl ; intros ; intuition. exists D ; auto.
  assert (InT a Γ1). apply In_InT. apply H. apply in_eq.
  apply InT_split in H0. destruct H0. destruct s ; subst.
  assert (J1: derrec_height D = derrec_height D). auto.
  assert (J2: ctr_L a (a :: Γ0 ++ x ++ a :: x0, Δ) (a :: Γ0 ++ x ++ x0, Δ)).
  pose (ctr_LI a [] (Γ0 ++ x) x0). simpl in c ; repeat rewrite <- app_assoc in c ; apply c.
  pose (GLS_hpadm_ctr_L _ J1 J2). destruct s.
  assert (J3: derrec_height x1 = derrec_height x1). auto.
  assert (J4: list_exch_L (a :: Γ0 ++ x ++ x0, Δ) (Γ0 ++ x ++ a :: x0, Δ)).
  pose (list_exch_LI [] [a] (Γ0 ++ x) [] x0). simpl in l0. repeat rewrite <- app_assoc in l0; auto.
  pose (GLS_hpadm_list_exch_L x1 J3 J4). destruct s.
  pose (IHΓ0 (x ++ a :: x0) Δ x2). destruct s.
  intros A HA. apply H. apply in_cons ; auto.
  exists x3. lia.
  Qed.

  Theorem incl_ctr_L : forall Γ0 Γ1 Δ, incl Γ0 Γ1 -> GLS_prv (Γ0 ++ Γ1, Δ) -> GLS_prv (Γ1, Δ).
  Proof.
  intros. pose (incl_ctr_L_hpadm _ _ _ X H). destruct s ; auto.
  Qed.

  Theorem incl_ctr_R_hpadm : forall Γ Δ0 Δ1 (D: GLS_prv (Γ, Δ0 ++ Δ1)), incl Δ0 Δ1 ->
        existsT2 (D0: GLS_prv (Γ, Δ1)), derrec_height D0 <= derrec_height D.
  Proof.
  intros Γ Δ0. revert Γ. induction Δ0 ; simpl ; intros ; intuition. exists D ; auto.
  assert (InT a Δ1). apply In_InT. apply H. apply in_eq.
  apply InT_split in H0. destruct H0. destruct s ; subst.
  assert (J1: derrec_height D = derrec_height D). auto.
  assert (J2: ctr_R a (Γ, a :: Δ0 ++ x ++ a :: x0) (Γ, a :: Δ0 ++ x ++ x0)).
  pose (ctr_RI a Γ [] (Δ0 ++ x) x0). simpl in c ; repeat rewrite <- app_assoc in c ; apply c.
  pose (GLS_hpadm_ctr_R _ J1 J2). destruct s.
  assert (J3: derrec_height x1 = derrec_height x1). auto.
  assert (J4: list_exch_R (Γ, a :: Δ0 ++ x ++ x0) (Γ, Δ0 ++ x ++ a :: x0)).
  pose (list_exch_RI Γ [] [a] (Δ0 ++ x) [] x0). simpl in l0. repeat rewrite <- app_assoc in l0; auto.
  pose (GLS_hpadm_list_exch_R x1 J3 J4). destruct s.
  pose (IHΔ0 Γ (x ++ a :: x0) x2). destruct s.
  intros A HA. apply H. apply in_cons ; auto.
  exists x3. lia.
  Qed.

  Theorem incl_ctr_R : forall Γ Δ0 Δ1, incl Δ0 Δ1 -> GLS_prv (Γ, Δ0 ++ Δ1) -> GLS_prv (Γ, Δ1).
  Proof.
  intros. pose (incl_ctr_R_hpadm _ _ _ X H). destruct s ; auto.
  Qed.

  Lemma nodup_id: forall l,
    existsT2 ln, (existsT2 l2, (PermutationT l (l2 ++ ln)) * (incl l2 ln)) *
                          (PermutationT ln (nodup eq_dec_form l)).
  Proof.
  induction l ; simpl ; intros ; intuition.
  - exists []. split ; auto. 2: apply Permutation_PermutationT ; apply Permutation_refl. exists [].
    rewrite <- app_nil_end. split ; auto. apply Permutation_PermutationT ; apply Permutation_refl.
    intro ; auto.
  - destruct IHl. destruct p. destruct s. destruct p0. destruct (in_dec eq_dec_form a l) ; simpl ; auto.
    exists x. split ; auto. exists (a :: x0). simpl. split. apply Permutation_PermutationT. apply perm_skip.
    apply Permutation_PermutationT ; auto. intros A HA. inversion HA ; subst ; auto.
    apply Permutation_PermutationT in p0. pose (Permutation_in _ p0 i0). apply in_app_or in i1 ; destruct i1 ; auto.
    exists (a :: x). split. exists x0. split. apply Permutation_PermutationT. apply Permutation_cons_app. apply Permutation_PermutationT ; auto.
    intros A HA. apply in_cons ; auto.
    apply Permutation_PermutationT. apply perm_skip. apply Permutation_PermutationT ; auto.
  Qed.

  Lemma nodupseq_id: forall s,
    existsT2 sn, (existsT2 LHS RHS, (PermutationTS s (LHS ++ fst sn, RHS ++ snd sn)) * (incl LHS (fst sn)) * (incl RHS (snd sn))) *
                          (PermutationTS sn (nodupseq s)).
  Proof.
  intros. unfold nodupseq in *.
  destruct (nodup_id (fst s)). destruct p. destruct s0. destruct p0.
  destruct (nodup_id (snd s)). destruct p1. destruct s0. destruct p2.
  unfold PermutationTS ; simpl. exists (x, x1) ; simpl. repeat split ; auto.
  exists x0. exists x2. split ; auto.
  Qed.

Lemma nodupseq_hpadm_prv_LR : forall s (D0: GLS_prv s), existsT2 (D1: GLS_prv (nodupseq s)), derrec_height D1 <= derrec_height D0.
Proof.
intros s D0.
destruct (nodupseq_id s). destruct p. destruct s0. destruct s0. destruct p0. destruct p0.
pose (PermutationTS_prv_hpadm _ D0 _ p0). destruct s0.
pose (incl_ctr_L_hpadm x0 (fst x) (x1 ++ snd x) x2 i0). destruct s0.
pose (incl_ctr_R_hpadm (fst x) x1 (snd x) x3 i). destruct s0. destruct x ; simpl in *.
pose (PermutationTS_prv_hpadm _ x4 _ p). destruct s0. exists x ; lia.
Qed.

Lemma nodupseq_hpadm_prv_RL : forall s (D0: GLS_prv (nodupseq s)), existsT2 (D1: GLS_prv s), derrec_height D1 <= derrec_height D0.
Proof.
intros s D0.
destruct (nodupseq_id s). destruct p. destruct s0. destruct s0. destruct p0. destruct p0.
pose (PermutationTS_prv_hpadm _ D0 _ (PermutationTS_sym _ _ p)). destruct s0. destruct x ; simpl in *.
assert (derrec_height x2 = derrec_height x2). auto.
pose (@GLS_list_wkn_L _ [] l0 _ x2 H). simpl in s0. destruct (s0 x0).
assert (derrec_height x = derrec_height x). auto.
pose (@GLS_list_wkn_R _ _ [] l1 x H0).  simpl in s1. destruct (s1 x1).
apply PermutationTS_sym in p0. pose (PermutationTS_prv_hpadm _ x3 _ p0). destruct s2. exists x4 ; lia.
Qed.

Lemma nodupseq_prv : forall s, ((GLS_prv s) -> (GLS_prv (nodupseq s))) * ((GLS_prv (nodupseq s)) -> (GLS_prv s)).
Proof.
intros s. split ; intro.
- destruct (nodupseq_id s). destruct p. destruct s0. destruct s0. destruct p0. destruct p0.
  apply (PermutationTS_prv _ _ p). destruct x. pose (incl_ctr_L x0 l). apply g ; auto.
  pose (incl_ctr_R (x0 ++ l) x1 l0). apply g0 ; auto. simpl in p0. apply (PermutationTS_prv _ _ p0) ; auto.
- destruct (nodupseq_id s). destruct p. destruct s0. destruct s0. destruct p0. destruct p0. apply PermutationTS_sym in p0.
  apply (PermutationTS_prv _ _ p0). pose (GLS_prv_list_wkn_L [] (fst x)). simpl in g. apply g.
  epose (@GLS_prv_list_wkn_R _ [] (snd x)). simpl in g0. apply g0. destruct x ; simpl in *.
  apply PermutationTS_sym in p. apply (PermutationTS_prv _ _ p) ; auto.
Qed.

Lemma nodupseq_prv_hpadm_LR : forall s (D0: GLS_prv s), existsT2 (D1: GLS_prv (nodupseq s)), derrec_height D1 <= derrec_height D0.
Proof.
intros s D0.
destruct (nodupseq_id s). destruct p. destruct s0. destruct s0. destruct p0. destruct p0.
pose (PermutationTS_prv_hpadm _ D0 _ p0). destruct s0.
pose (incl_ctr_L_hpadm _ _ _ x2 i0). destruct s0.
pose (incl_ctr_R_hpadm _ _ _ x3 i). destruct s0. destruct x.
pose (PermutationTS_prv_hpadm _ x4 _ p). destruct s0. exists x. lia.
Qed.

Lemma nodupseq_prv_hpadm_RL : forall s (D0: GLS_prv (nodupseq s)), existsT2 (D1: GLS_prv s), derrec_height D1 <= derrec_height D0.
Proof.
intros s D0.
destruct (nodupseq_id s). destruct p. destruct s0. destruct s0. destruct p0. destruct p0. apply PermutationTS_sym in p0.
pose (PermutationTS_prv_hpadm _ D0 _ (PermutationTS_sym _ _ p)). destruct s0.
assert (derrec_height x2 = derrec_height x2). auto. destruct x ; simpl in *.
pose (GLS_list_wkn_L [] l0 x2 H). simpl in s0. destruct (s0  x0).
assert (derrec_height x = derrec_height x). auto.
pose (GLS_list_wkn_R [] l1 x H0). simpl in s1. destruct (s1 x1).
pose (PermutationTS_prv_hpadm _ x3 _ p0). destruct s2. exists x4. lia.
Qed.

Lemma remove_Permutation : forall l a, In a l -> Permutation (nodup eq_dec_form l) (nodup eq_dec_form (a :: remove eq_dec_form a l)).
  Proof.
  induction l ; simpl ; intros ; intuition ; subst.
  - destruct (in_dec eq_dec_form a0 l) ; simpl ; auto. destruct (eq_dec_form a0 a0) ; auto.
    destruct (in_dec eq_dec_form a0 (remove eq_dec_form a0 l)) ; simpl ; auto. exfalso.
    apply remove_not_in_anymore in i0 ; auto. apply IHl in i. simpl in i. destruct (in_dec eq_dec_form a0 (remove eq_dec_form a0 l)) ; auto.
    exfalso ; auto. exfalso ; auto. destruct (eq_dec_form a0 a0) ; subst. 2: exfalso ; auto.
    destruct (in_dec eq_dec_form a0 (remove eq_dec_form a0 l)) ; simpl ; auto. exfalso.
    apply remove_not_in_anymore in i ; auto. apply perm_skip.
    assert ((remove eq_dec_form a0 l) = l). apply notin_remove ; auto. rewrite H ; apply Permutation_refl.
  - destruct (in_dec eq_dec_form a l) ; simpl ; auto. destruct (eq_dec_form a0 a) ; auto ; subst.
    destruct (in_dec eq_dec_form a (remove eq_dec_form a l)) ; simpl ; auto. exfalso.
    apply remove_not_in_anymore in i0 ; auto. apply IHl in i. simpl in i. destruct (in_dec eq_dec_form a (remove eq_dec_form a l)) ; auto.
    exfalso ; auto. destruct (in_dec eq_dec_form a0 (a :: remove eq_dec_form a0 l)). inversion i0 ;subst.
    exfalso ; auto. exfalso. apply remove_not_in_anymore in H ; auto. simpl.
    destruct (in_dec eq_dec_form a (remove eq_dec_form a0 l)) ; simpl ; auto. apply IHl in H0.
    simpl in H0. destruct (in_dec eq_dec_form a0 (remove eq_dec_form a0 l)) ; auto. exfalso.
    apply remove_not_in_anymore in i1 ; auto. exfalso. apply n1. apply in_not_touched_remove ; auto.
    destruct (eq_dec_form a0 a) ; subst. exfalso ; auto. destruct (in_dec eq_dec_form a0 (a :: remove eq_dec_form a0 l)) ; auto.
    inversion i ; auto. exfalso ; subst ; auto. exfalso. apply remove_not_in_anymore in H ; auto.
    simpl. destruct (in_dec eq_dec_form a (remove eq_dec_form a0 l)). exfalso.
    apply n. apply In_remove_In_list in i ; auto.
    apply Permutation_trans with (l':=(a :: a0 :: nodup eq_dec_form (remove eq_dec_form a0 l))).
    apply perm_skip. apply IHl in H0. simpl in H0. destruct (in_dec eq_dec_form a0 (remove eq_dec_form a0 l)) ; auto.
    exfalso. apply remove_not_in_anymore in i ; auto. apply perm_swap.
  Qed.

  Lemma incl_id: forall l0 l1, (incl l0 l1) ->
    existsT2 l0n, (existsT2 l2, (PermutationT (nodup eq_dec_form l1) (l2 ++ l0n))) *
                          (PermutationT l0n (nodup eq_dec_form l0)).
  Proof.
  induction l0 ; simpl ; intros ; intuition.
  - exists []. split ; auto. 2: apply Permutation_PermutationT ; apply Permutation_refl.
    exists (nodup eq_dec_form l1). rewrite <- app_nil_end. apply Permutation_PermutationT ; apply Permutation_refl.
  - assert (incl l0 l1). intros A HA. apply H. apply in_cons ; auto. destruct (in_dec eq_dec_form a l0).
    apply IHl0 in H0 ; auto. assert (incl l0 (remove eq_dec_form a l1)). intros A HA. apply in_not_touched_remove.
    apply H0 ; auto. intro ; subst ; auto. apply IHl0 in H1. destruct H1. destruct p. destruct s. exists (a::x) ; split.
    2: apply Permutation_PermutationT ; apply Permutation_PermutationT in p ; apply perm_skip ; auto.
    exists x0. apply Permutation_PermutationT. apply Permutation_PermutationT in p0.
    pose (Permutation_middle x0 x a). apply Permutation_trans with (l':=a :: x0 ++ x) ; auto.
    apply Permutation_trans with (l':=nodup eq_dec_form (a :: remove eq_dec_form a l1)) ; auto.
    apply remove_Permutation. apply H. apply in_eq.
    simpl. destruct (in_dec eq_dec_form a (remove eq_dec_form a l1)). exfalso. apply remove_not_in_anymore in i ; auto.
    apply perm_skip ; auto.
  Qed.

  Lemma incl_idS: forall s0 s1, (incl (fst s0) (fst s1)) -> (incl (snd s0) (snd s1)) ->
    existsT2 s0n, (existsT2 LHS RHS, (PermutationTS (nodupseq s1) (LHS ++ fst s0n, RHS ++ snd s0n))) *
                          (PermutationTS s0n (nodupseq s0)).
  Proof.
  intros. unfold nodupseq in *.
  pose (incl_id _ _ H). destruct s. destruct p. destruct s.
  pose (incl_id _ _ H0). destruct s. destruct p1. destruct s.
  unfold PermutationTS ; simpl. exists (x, x1) ; simpl. split.
  - exists x0. exists x2. split ; auto.
  - split ; auto.
  Qed.

Lemma PermutationTS_nodupseq : forall s0 s1, PermutationTS s0 s1 -> PermutationTS (nodupseq s0) (nodupseq s1).
Proof.
intros. split ; destruct H ; apply PermutationT_nodupseq ; auto.
Qed.
