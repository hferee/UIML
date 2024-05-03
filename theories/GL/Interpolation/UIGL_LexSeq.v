Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import general_export.

Require Import GLS_export.

Require Import UIGL_Def_measure.
Require Import UIGL_Canopy.
Require Import UIGL_irred_short.

  Section LogDefinition.

  (* Below is the measure which can be used to prove termination of
      the Fixpoint UI (order used: lexicographic on pairs of natural numbers). *)

  Definition measure (s : Seq) := [(length (usable_boxes s)) ; (n_imp_subformS s)].

  (* List of all premises through the GLR rule for a sequent s.
      Note that GLR is not invertible. *)

  Definition GLR_prems (s : Seq) := flatten_list (proj1_sigT2 (finite_GLR_premises_of_S s)).

  (* Property of being an initial sequent. *)

  Definition is_init s : Type := (IdPRule [] s) + (IdBRule [] s) + (BotLRule [] s).

  End LogDefinition.

  Section LexSeq_ind.

  Definition LexSeq := fun s0 s1 => (less_thanS s0 s1).

  Lemma wf_LexSeq : well_founded LexSeq.
  Proof.
  unfold LexSeq. apply less_thanS_wf.
  Qed.

  Variable (P : Seq -> Type).

  Theorem LexSeq_ind : (forall s0, (forall s1, LexSeq s1 s0 -> P s1) -> P s0) -> (forall s, P s).
  Proof.
  intros. induction s as [ s0 IHs0 ] using (well_founded_induction_type wf_LexSeq).
  apply X; intros; apply IHs0 ; auto.
  Qed.

  End LexSeq_ind.

  Section LexSeq_properties.

  Theorem LexSeq_trans : forall x y z, LexSeq x y -> LexSeq y z -> LexSeq x z.
  Proof.
  unfold LexSeq. apply less_thanS_trans.
  Qed.

  Lemma inv_prems_LexSeq : forall s0 s1, InT s1 (inv_prems s0) -> LexSeq s1 s0.
  Proof.
  intros. unfold inv_prems in H. apply InT_flatten_list_InT_elem in H.
  destruct H. destruct p. destruct (finite_ImpRules_premises_of_S s0). simpl in i0.
  apply p in i0. destruct i0 ; inversion i0 ; subst. inversion i ; subst. unfold LexSeq. 
  apply ImpR_applic_reduces_measure ; auto. inversion H0.
  unfold LexSeq. destruct (ImpL_applic_reduces_measure i0).
  inversion i ; subst ; auto. inversion H0 ; subst ; auto. inversion H1.
  Qed.

  Lemma GLR_prems_LexSeq : forall s0 s1, (IdBRule [] s0 -> False) ->
            InT s1 (GLR_prems s0) -> LexSeq s1 s0.
  Proof.
  intros s0 s1 H0 H. unfold GLR_prems in H. apply InT_flatten_list_InT_elem in H.
  destruct H. destruct p. destruct (finite_GLR_premises_of_S s0). simpl in i0.
  apply p in i0. inversion i0 ; subst. unfold LexSeq. apply GLR_applic_reduces_measure ; auto.
  inversion i ; subst ; auto. inversion H2.
  Qed.

  Lemma GLR_prems_less_ub : forall s0 s1, (IdBRule [] s0 -> False) ->
            InT s1 (GLR_prems s0) -> (length (usable_boxes s1) < length (usable_boxes s0)).
  Proof.
  intros s0 s1 H0 H. unfold GLR_prems in H. apply InT_flatten_list_InT_elem in H.
  destruct H. destruct p. destruct (finite_GLR_premises_of_S s0). simpl in i0.
  apply p in i0. inversion i0 ; subst. apply GLR_applic_less_usable_boxes in i0 ; auto.
  inversion i ; subst ; auto. inversion H2.
  Qed.

  Lemma top_boxes_XBoxed_list : forall l, incl (top_boxes l) (top_boxes (XBoxed_list (top_boxes l))).
  Proof.
  induction l ; intro ; intros ; auto. destruct a ; simpl ; simpl in H ; auto. destruct H. subst.
  destruct a ; auto. 1-3: apply in_eq. apply in_cons ;  apply in_eq. destruct a ; auto. all: apply in_cons ; auto.
  apply in_cons ; auto.
  Qed.

  Lemma subform_boxesLF_top_boxes : forall l a, In a (subform_boxesLF (top_boxes l)) -> In a (subform_boxesLF l).
  Proof.
  induction l ; simpl ; intros ; auto. destruct a ; simpl ; auto. apply remove_list_is_in. auto.
  simpl in H. destruct H ; auto. right. apply in_app_or in H. apply in_or_app. destruct H ; auto.
  right. apply in_not_touched_remove. 2: apply In_remove_diff in H ; auto.
  apply In_remove_In_list in H. apply not_removed_remove_list.
  apply In_remove_list_In_list in H ; auto. intro. apply remove_list_cont in H ; auto.
  Qed.

  Lemma leq_ub_unif : forall s, (length (usable_boxes (XBoxed_list (top_boxes (fst s)), []))) <= (length (usable_boxes s)).
  Proof.
  intros. destruct s. simpl. unfold usable_boxes. simpl.
  assert (J0: incl (top_boxes l) (top_boxes (XBoxed_list (top_boxes l)))). apply top_boxes_XBoxed_list.
  pose (remove_list_incr_decr3 (subform_boxesS (XBoxed_list (top_boxes l), []%list)) _ _ J0).
  assert (J1: NoDup (subform_boxesS (XBoxed_list (top_boxes l), []%list))). apply NoDup_subform_boxesS.
  assert (J2: NoDup (subform_boxesS (l, l0))). apply NoDup_subform_boxesS.
  assert (J3: incl (subform_boxesS (XBoxed_list (top_boxes l), []%list)) (subform_boxesS (l, l0))).
  intro ; intros. unfold subform_boxesS. simpl. unfold subform_boxesS in H. simpl in H.
  rewrite remove_list_of_nil in H. rewrite app_nil_r in H. apply in_or_app ; left.
  apply XBoxed_list_same_subform_boxes with (l:=(top_boxes l)) in H.
  apply subform_boxesLF_top_boxes ; auto.
  pose (remove_list_incr_decr2 _ _ (top_boxes l) J1 J2 J3). lia.
  Qed.

  Lemma Canopy_nil : forall s0, (inv_prems s0 = []) ->  (forall s1, InT s1 (Canopy s0) -> s1 = s0).
  Proof.
  intros. assert (Canopy s0 = [s0]). apply irred_nil. unfold inv_prems. unfold inv_prems in H. auto.
  rewrite H1 in H0. inversion H0. subst. auto. inversion H3.
  Qed.

  Lemma Canopy_LexSeq: forall s0 s1, InT s1 (Canopy s0) -> ((s0 = s1) + (LexSeq s1 s0)).
  Proof.
  intros s ; induction on s as IHs with measure (n_imp_subformS s).
  intros. remember (finite_ImpRules_premises_of_S s) as H0. destruct H0. destruct x.
  - left. assert (Canopy s = [s]). apply irred_nil. unfold inv_prems ; rewrite <- HeqH0 ; auto.
    rewrite H0 in H. inversion H ; subst ; auto. inversion H2.
  - apply fold_Canopy in H. destruct H ; auto. right. destruct s0. destruct p0. apply IHs in i0.
    destruct i0 ; subst ; auto. apply inv_prems_LexSeq in i ; auto. apply inv_prems_LexSeq in i.
    apply (LexSeq_trans _ _ _ l0 i). unfold inv_prems in i. apply InT_flatten_list_InT_elem in i.
    destruct i. destruct p0. rewrite <- HeqH0 in i1. simpl in i1. apply p in i1. destruct i1 ; inversion i1 ; subst.
    inversion i. subst. unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
    inversion H0. inversion i ; subst. unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
    inversion H0 ; subst. unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
    inversion H1.
  Qed.

  Lemma leq_ub_Canopy : forall s0 s1, InT s1 (Canopy s0) ->
                  (length (usable_boxes s1)) <= (length (usable_boxes s0)).
  Proof.
  intros s0 ; induction on s0 as IHs0 with measure (n_imp_subformS s0).
  intros. remember (finite_ImpRules_premises_of_S s0) as H0.
  destruct H0. destruct x.
  - assert (Canopy s0 = [s0]). apply irred_nil. unfold inv_prems. rewrite <- HeqH0.
    simpl. auto. rewrite H0 in H. inversion H. subst. auto. inversion H2.
  - apply fold_Canopy in H. destruct H ; auto. subst. auto.
    destruct s. destruct p0. unfold inv_prems in i. destruct (finite_ImpRules_premises_of_S s0).
    simpl in i. apply InT_flatten_list_InT_elem in i. destruct i. destruct p1.
    apply p0 in i1.
    assert ((length (usable_boxes x0) <= length (usable_boxes s0)) * ((n_imp_subformS x0) < (n_imp_subformS s0))).
    destruct i1. inversion i1 ; subst. apply ImpR_applic_reduces_ub_or_imp in i1. destruct i1.
    inversion i ; subst. split ; try lia. unfold n_imp_subformS ; simpl.
    repeat rewrite n_imp_subformLF_dist_app ; simpl ; repeat rewrite n_imp_subformLF_dist_app. lia.
    inversion H0. destruct p1. inversion i ; subst. split ; try lia. inversion H0.
    inversion i1 ; subst. inversion i ; subst. apply ImpL_applic_reduces_ub_or_imp in i1. destruct i1.
    destruct s. split ; try lia. unfold n_imp_subformS ; simpl.
    repeat rewrite n_imp_subformLF_dist_app ; simpl ; repeat rewrite n_imp_subformLF_dist_app. lia.
    destruct p1 ; split ; try lia. inversion H0 ; subst. 2: inversion H1.
    apply ImpL_applic_reduces_ub_or_imp in i1. destruct i1.
    destruct s0. split ; try lia. unfold n_imp_subformS ; simpl.
    repeat rewrite n_imp_subformLF_dist_app ; simpl ; repeat rewrite n_imp_subformLF_dist_app. lia.
    destruct p1. split ; try lia.
    destruct H. apply IHs0 in i0 ; lia.
  Qed.

  End LexSeq_properties.

  Section empty_seq.

  Lemma empty_seq_dec : forall (s: Seq), (s = ([],[])) + (s <> ([],[])).
  Proof.
  intros. destruct s. destruct l ; destruct l0 ; auto.
  all: right ; intro H ; inversion H.
  Qed.

  Lemma not_init_empty_seq : is_init ([],[]) -> False.
  Proof.
  intro. destruct X. destruct s. 1-2: inversion i ; destruct Γ0 ; inversion H.
  inversion b ; subst. destruct Γ0 ; inversion H.
  Qed.

  Lemma critical_empty_seq : critical_Seq ([],[]).
  Proof.
  intros A HA ; simpl in *. inversion HA.
  Qed.

  End empty_seq.