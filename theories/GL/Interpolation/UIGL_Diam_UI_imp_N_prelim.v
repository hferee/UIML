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
  Require Import UIGL_LexSeq.
  Require Import UIGL_nodupseq.
  Require Import UIGL_And_Or_rules.
  Require Import UIGL_UI_prelims.
  Require Import UIGL_UI_inter.

  (* Preliminary lemmas. *)

  Lemma top_boxes_Canopy_noless_ub : forall s0 s1, InT s1 (Canopy s0) ->
                        (length (usable_boxes s1) < length (usable_boxes s0) -> False) ->
                        (incl (top_boxes (fst s1)) (top_boxes (fst s0))) * (incl (top_boxes (fst s0)) (top_boxes (fst s1))) *
                        (incl (subform_boxesS s1) (subform_boxesS s0)) * (incl (subform_boxesS s0) (subform_boxesS s1)).
  Proof.
  intro s0. induction on s0 as IH with measure (n_imp_subformS s0).
  intros. pose (fold_Canopy _ _ H). destruct s ; subst.
  - assert (Canopy s0 = [s0]). apply Id_InT_Canopy ; auto. rewrite H1 in H. inversion H ; subst.
    repeat split ; intros a K ; auto. inversion H3.
  - destruct s. destruct p.
    assert (n_imp_subformS x < n_imp_subformS s0).
    unfold inv_prems in i. apply InT_flatten_list_InT_elem in i. destruct i. destruct p.
    destruct (finite_ImpRules_premises_of_S s0). simpl in i1. apply p in i1. destruct i1.
    inversion i1 ; subst. inversion i ; subst. 2: inversion H2.
    unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
    inversion i1 ; subst. inversion i ; subst.
    unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
    inversion H2 ; subst. 2: inversion H3.
    unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
    assert ((length (usable_boxes s1) < length (usable_boxes x) -> False)).
    intro. apply H0. unfold inv_prems in i. apply InT_flatten_list_InT_elem in i. destruct i. destruct p.
    destruct (finite_ImpRules_premises_of_S s0). simpl in i1. apply p in i1. destruct i1.
    inversion i1 ; subst. inversion i ; subst. apply ImpR_applic_reduces_ub_or_imp in i1. destruct i1.
    lia. destruct p0 ; lia. inversion H4.
    inversion i1 ; subst. inversion i ; subst. apply ImpL_applic_reduces_ub_or_imp in i1. destruct i1. destruct s.
    lia. destruct p0 ; lia. inversion H4 ; subst. 2: inversion H5. apply ImpL_applic_reduces_ub_or_imp in i1. destruct i1.
    destruct s0. lia. destruct p0 ; lia.
    pose (IH _ H1 _ i0 H2).
    assert ( length (usable_boxes x) < length (usable_boxes s0) -> False).
    intro. apply H0. destruct p. apply leq_ub_Canopy in i0 ; lia.
    unfold inv_prems in i. apply InT_flatten_list_InT_elem in i. destruct i. destruct p0.
    destruct (finite_ImpRules_premises_of_S s0). simpl in i1. apply p0 in i1. destruct i1.
    + inversion i1 ; subst ; simpl. inversion i ; subst. 2: inversion H5. simpl in p. repeat split.
       * intros C G. apply p in G. rewrite top_boxes_distr_app ; rewrite top_boxes_distr_app in G.
         apply in_or_app. apply in_app_or in G ; destruct G ; auto. destruct A ; simpl in H4 ; auto.
         destruct H4 ; auto. subst. destruct (In_dec (top_boxes (Γ0 ++ Γ1)) (Box A)).
         rewrite top_boxes_distr_app in i2 ; apply in_app_or in i2 ; auto. exfalso. apply H3.
         unfold usable_boxes ; simpl. apply remove_list_incr_decr ; auto. 1-2: apply NoDup_subform_boxesS.
         exists (Box A). repeat split ; auto. rewrite top_boxes_distr_app ; apply in_or_app ; simpl ; auto.
         unfold subform_boxesS. simpl. apply remove_list_is_in. apply In_incl_subform_boxes with (A:=(Box A --> B)).
         apply in_or_app ; right ; simpl ; auto. simpl ; auto.
         intros a G. rewrite top_boxes_distr_app ; rewrite top_boxes_distr_app in G.
         apply in_or_app. apply in_app_or in G ; destruct G ; auto. right. simpl ; auto.
         unfold subform_boxesS ; simpl. intros a G. apply in_app_or in G ; destruct G.
         rewrite subform_boxesLF_dist_app in H4. apply in_app_or in H4 ; destruct H4. apply in_or_app.
         left ; rewrite subform_boxesLF_dist_app ; apply in_or_app ; auto. apply In_remove_list_In_list_not_In_remove_list in H4.
         destruct H4. simpl in H4. destruct H4 ; subst. apply remove_list_is_in.
         rewrite subform_boxesLF_dist_app. apply remove_list_is_in. simpl ; auto.
         apply in_app_or in H4. destruct H4. apply remove_list_is_in. rewrite subform_boxesLF_dist_app.
         apply remove_list_is_in. simpl ; right ; apply in_or_app ; left ; apply in_or_app ; auto.
         apply in_remove in H4. destruct H4. apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4.
         apply in_or_app ; left ; rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4. apply remove_list_is_in.
         rewrite subform_boxesLF_dist_app in H4. apply in_app_or in H4 ; destruct H4.
         rewrite subform_boxesLF_dist_app ; apply in_or_app ; auto. apply In_remove_list_In_list_not_In_remove_list in H4.
         destruct H4. simpl in H4. apply in_app_or in H4 ; destruct H4.
         rewrite subform_boxesLF_dist_app. apply remove_list_is_in ; simpl. right. apply in_or_app ; left.
         apply in_or_app ; right ; apply in_not_touched_remove. apply not_removed_remove_list ; auto.
         intros. apply H5. rewrite subform_boxesLF_dist_app. apply remove_list_is_in ; simpl. right. apply in_or_app ; auto.
         intro. subst. apply H5. rewrite subform_boxesLF_dist_app. apply remove_list_is_in ; simpl ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4.
         rewrite subform_boxesLF_dist_app. apply remove_list_is_in. assert (Box A --> B :: Δ1 = [Box A --> B] ++ Δ1).
         auto. rewrite H8. rewrite subform_boxesLF_dist_app. apply remove_list_is_in ; auto.
       * intros C G. apply p. rewrite top_boxes_distr_app ; rewrite top_boxes_distr_app in G.
         apply in_or_app. apply in_app_or in G ; destruct G ; auto. right. destruct A ; simpl ; auto.
       * intros C G. apply p in G. unfold subform_boxesS ; unfold subform_boxesS in G ; simpl ; simpl in G.
         apply in_app_or in G ; destruct G. rewrite subform_boxesLF_dist_app in H4. apply in_app_or in H4 ; destruct H4.
         apply in_or_app ; left ; rewrite subform_boxesLF_dist_app ; apply in_or_app ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4. simpl in H4. apply in_app_or in H4 ; destruct H4.
         apply remove_list_is_in. rewrite subform_boxesLF_dist_app ; apply remove_list_is_in. simpl. apply in_or_app ; left ; apply in_or_app ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4.
         apply in_or_app ; left ; rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4. apply remove_list_is_in.
         rewrite subform_boxesLF_dist_app in H4. apply in_app_or in H4. destruct H4.
         rewrite subform_boxesLF_dist_app ; apply in_or_app ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4.
         rewrite subform_boxesLF_dist_app ; apply remove_list_is_in. simpl in H4. apply in_app_or in H4.
         destruct H4. simpl. apply in_or_app ; left. apply remove_list_is_in ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4. simpl. apply remove_list_is_in ; auto.
       * intros C G. apply p. unfold subform_boxesS ; unfold subform_boxesS in G ; simpl ; simpl in G.
         apply in_app_or in G ; destruct G. apply in_or_app ; left. rewrite subform_boxesLF_dist_app in H4.
         apply in_app_or in H4 ; destruct H4. rewrite subform_boxesLF_dist_app. apply in_or_app ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4.
         rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; simpl ; apply remove_list_is_in ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4.
         rewrite subform_boxesLF_dist_app in H4. apply in_app_or in H4. destruct H4.
         rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; rewrite subform_boxesLF_dist_app ; apply in_or_app ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4. simpl in H4. apply in_app_or in H4.
         destruct H4. apply in_app_or in H4. destruct H4. apply in_or_app ; left.
         rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; apply in_or_app ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4. apply remove_list_is_in.
         rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; apply in_or_app ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4. apply remove_list_is_in.
         rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; simpl ; apply remove_list_is_in ; auto.
    + inversion i1 ; subst ; simpl ; simpl in p. inversion i ; subst ; simpl in p.
       ++ repeat split.
       * intros C G. apply p in G. rewrite top_boxes_distr_app ; rewrite top_boxes_distr_app in G.
         apply in_or_app. apply in_app_or in G ; destruct G ; auto.
       * intros C G. apply p. rewrite top_boxes_distr_app ; rewrite top_boxes_distr_app in G.
         apply in_or_app. apply in_app_or in G ; destruct G ; auto.
       * intros C G. apply p in G. unfold subform_boxesS ; unfold subform_boxesS in G ; simpl ; simpl in G.
         apply in_app_or in G ; destruct G. rewrite subform_boxesLF_dist_app in H4. apply in_app_or in H4 ; destruct H4.
         apply in_or_app ; left ; rewrite subform_boxesLF_dist_app ; apply in_or_app ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4.
         apply in_or_app ; left ; rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; simpl ; apply remove_list_is_in ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4.
         rewrite subform_boxesLF_dist_app in H4. apply in_app_or in H4. destruct H4.
         apply remove_list_is_in ; rewrite subform_boxesLF_dist_app ; apply in_or_app ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4. simpl in H4. apply in_app_or in H4 ; destruct H4.
         apply in_or_app ; left ; rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; simpl ; apply in_or_app ; left ; apply in_or_app ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4.
         rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; auto.
       * intros C G. apply p. unfold subform_boxesS ; unfold subform_boxesS in G ; simpl ; simpl in G.
         apply in_app_or in G ; destruct G. rewrite subform_boxesLF_dist_app in H4.
         apply in_app_or in H4 ; destruct H4. apply in_or_app ; left. rewrite subform_boxesLF_dist_app. apply in_or_app ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4. simpl in H4. apply in_app_or in H4.
         destruct H4. apply in_app_or in H4. destruct H4.
         rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ;
         apply in_or_app ; auto. apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4.
         destruct (In_dec (subform_boxesLF (Γ0 ++ Γ1) ++ remove_list (subform_boxesLF (Γ0 ++ Γ1)) (subform_boxesLF (Δ0 ++ A :: Δ1))) C) ; auto.
         exfalso. apply H3. unfold usable_boxes ; simpl. repeat rewrite top_boxes_distr_app ; simpl.
         apply remove_list_incr_decr4 ; auto. 1-2: apply NoDup_subform_boxesS. unfold subform_boxesS ; simpl.
         intros a G. apply in_app_or in G ; destruct G. rewrite subform_boxesLF_dist_app in H7. apply in_app_or in H7 ; destruct H7.
         apply in_or_app ; left ; rewrite subform_boxesLF_dist_app ; apply in_or_app ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H7. destruct H7. apply in_or_app ; left.
         rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; apply remove_list_is_in ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H7. destruct H7. rewrite subform_boxesLF_dist_app in H7.
         apply in_app_or in H7. destruct H7. apply remove_list_is_in ;  rewrite subform_boxesLF_dist_app ; apply in_or_app ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H7. destruct H7. simpl in H7.
         apply in_app_or in H7. destruct H7. apply in_or_app ; left ; rewrite subform_boxesLF_dist_app ; apply remove_list_is_in.
         simpl. apply in_or_app ; left ; apply in_or_app ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H7. destruct H7.
         rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; auto.
         intro. assert (In C (subform_boxesS (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1))). unfold subform_boxesS ; simpl. apply in_or_app ; left.
         apply In_incl_subform_boxes with (A:=A --> B). apply in_or_app ; simpl ; auto. simpl. apply remove_list_is_in ; auto.
         apply H7 in H8. unfold subform_boxesS in H8 ; simpl in H8. auto.
         exists C. repeat split. unfold subform_boxesS ; simpl. apply in_or_app ; left.
         apply In_incl_subform_boxes with (A:=A --> B). apply in_or_app ; simpl ; auto. simpl. apply remove_list_is_in ; auto.
         intro. apply n. apply in_or_app ; left. apply in_app_or in H7. destruct H7. rewrite subform_boxesLF_dist_app ; apply in_or_app ; left.
         apply subform_boxesLF_top_boxes. pose (in_top_boxes _ _ H7). destruct s ; destruct s ; destruct s ; destruct p1 ; subst.
         repeat rewrite top_boxes_distr_app ; simpl. rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; simpl ; auto.
         rewrite subform_boxesLF_dist_app ; apply remove_list_is_in.
         apply subform_boxesLF_top_boxes. pose (in_top_boxes _ _ H7). destruct s ; destruct s ; destruct s ; destruct p1 ; subst.
         repeat rewrite top_boxes_distr_app ; simpl. rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; simpl ; auto.
         unfold subform_boxesS ; simpl ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4.
         apply in_or_app ; left. rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4.
         rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; rewrite subform_boxesLF_dist_app.
         rewrite subform_boxesLF_dist_app in H4. apply in_app_or in H4. destruct H4. apply in_or_app ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4. apply remove_list_is_in ; apply remove_list_is_in ; auto.
       ++ inversion H5 ; subst ; simpl in p. 2: inversion H6. repeat split.
       * intros C G. apply p in G. rewrite top_boxes_distr_app ; rewrite top_boxes_distr_app in G.
         apply in_or_app. apply in_app_or in G ; destruct G ; auto. simpl. destruct B ; simpl in H4 ; auto.
         destruct H4 ; subst ; auto. destruct (In_dec (top_boxes (Γ0 ++ Γ1)) (Box B)). rewrite top_boxes_distr_app in i2 ; apply in_app_or in i2 ; auto.
         exfalso. apply H3. unfold usable_boxes ; simpl. repeat rewrite top_boxes_distr_app ; simpl.
         apply remove_list_incr_decr ; auto. 1-2: apply NoDup_subform_boxesS.
         exists (Box B). repeat  split. apply in_or_app ; simpl ; auto. unfold subform_boxesS ; simpl.
         rewrite subform_boxesLF_dist_app ; apply in_or_app ; left ; apply remove_list_is_in ; simpl ; apply in_or_app ; left ; apply remove_list_is_in ; apply in_eq.
         rewrite top_boxes_distr_app in n ; auto.
         intros a G. apply in_app_or in G ; apply in_or_app ; simpl ; destruct G ; auto.
         unfold subform_boxesS ; simpl.
         intros a G. apply in_app_or in G ; destruct G. rewrite subform_boxesLF_dist_app in H4. apply in_app_or in H4 ; destruct H4.
         apply in_or_app ; left ; rewrite subform_boxesLF_dist_app ; apply in_or_app ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4. simpl in H4 ; destruct H4 ; subst. apply in_or_app ; left.
         rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; simpl ; apply in_or_app ; left ; apply remove_list_is_in ; apply in_eq.
         apply in_app_or in H4 ; destruct H4. apply in_or_app ; left.
         rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; simpl ; apply in_or_app ; left ; apply remove_list_is_in ; apply in_cons ; auto.
         apply in_remove in H4. destruct H4.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4. apply in_or_app ; left.
         rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; apply remove_list_is_in ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4. apply remove_list_is_in ; auto.
       * intros C G. apply p. rewrite top_boxes_distr_app ; rewrite top_boxes_distr_app in G ; simpl in G.
         apply in_or_app. apply in_app_or in G ; destruct G ; auto. simpl. destruct B ; auto. right ; apply in_cons ; auto.
       * intros C G. apply p in G. unfold subform_boxesS ; unfold subform_boxesS in G ; simpl ; simpl in G.
         apply in_app_or in G ; destruct G. rewrite subform_boxesLF_dist_app in H4. apply in_app_or in H4 ; destruct H4.
         apply in_or_app ; left ; rewrite subform_boxesLF_dist_app ; apply in_or_app ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4. apply in_or_app ; left. simpl in H4 ; apply in_app_or in H4 ; destruct H4.
         rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; simpl ; apply in_or_app ; left ; apply remove_list_is_in ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4.
         rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; simpl ; apply remove_list_is_in ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4. apply remove_list_is_in ; auto.
       * intros C G. apply p. unfold subform_boxesS ; unfold subform_boxesS in G ; simpl ; simpl in G.
         apply in_app_or in G ; destruct G. rewrite subform_boxesLF_dist_app in H4. apply in_app_or in H4 ; destruct H4.
         apply in_or_app ; left ; rewrite subform_boxesLF_dist_app ; apply in_or_app ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4. simpl in H4 ; apply in_app_or in H4 ; destruct H4.
         apply in_app_or in H4 ; destruct H4. destruct (In_dec (subform_boxesLF (Γ0 ++ B :: Γ1) ++ remove_list (subform_boxesLF (Γ0 ++ B :: Γ1)) (subform_boxesLF (Δ0 ++ Δ1))) C) ; auto.

         exfalso. apply H3. unfold usable_boxes ; simpl. repeat rewrite top_boxes_distr_app. simpl (top_boxes (A --> B :: Γ1)).
         assert (length (remove_list (top_boxes Γ0 ++ top_boxes (B :: Γ1)) (subform_boxesS (Γ0 ++ B :: Γ1, Δ0 ++ Δ1))) <=
         length (remove_list (top_boxes Γ0 ++ top_boxes Γ1) (subform_boxesS (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)))).
         destruct B ; simpl ; auto. apply remove_list_incr_decr3 ; auto. intros a G. apply in_or_app ; simpl ; apply in_app_or in G ; destruct G ; auto.
         assert (length (remove_list (top_boxes Γ0 ++ top_boxes Γ1) (subform_boxesS (Γ0 ++ B :: Γ1, Δ0 ++ Δ1))) <
         length (remove_list (top_boxes Γ0 ++ top_boxes Γ1) (subform_boxesS (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)))).
         apply remove_list_incr_decr4 ; auto. 1-2: apply NoDup_subform_boxesS.
         intros a G. unfold subform_boxesS ; simpl ; unfold subform_boxesS in G ; simpl in G. apply in_app_or in G ; destruct G.
         apply in_or_app ; left. rewrite subform_boxesLF_dist_app in H8 ; apply in_app_or in H8 ; destruct H8.
         rewrite subform_boxesLF_dist_app ; apply in_or_app ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H8. destruct H8. simpl in H8 ; apply in_app_or in H8 ; destruct H8.
         rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; simpl ; apply in_or_app ; left ; apply remove_list_is_in ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H8. destruct H8.
         rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; apply remove_list_is_in ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H8. destruct H8. apply remove_list_is_in ; auto.
         intro. apply n. apply H8. unfold subform_boxesS ; simpl. apply in_or_app ; left.
         rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; simpl ; apply in_or_app ; left ; apply in_or_app ; auto.
         exists (C). repeat  split. unfold subform_boxesS ; simpl. apply in_or_app ; left.
         rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; simpl ; apply in_or_app ; left ; apply in_or_app ; auto.
         intro. apply n. apply in_or_app ; left. apply subform_boxesLF_top_boxes. assert (In C (top_boxes (Γ0 ++ B :: Γ1))).
         repeat rewrite top_boxes_distr_app. apply in_or_app ; apply in_app_or in H8 ; destruct H8 ; auto. right. destruct B ; simpl ; auto.
         pose (in_top_boxes _ _ H9). destruct s ; destruct s ; destruct s ; destruct p1 ; subst. rewrite e0.
         repeat rewrite top_boxes_distr_app ; simpl. rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; simpl ; auto. auto.
         lia.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4.
         apply in_or_app ; left ; rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; apply in_or_app ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4.
         apply in_or_app ; left ; rewrite subform_boxesLF_dist_app ; apply remove_list_is_in ; apply remove_list_is_in ; auto.
         apply In_remove_list_In_list_not_In_remove_list in H4. destruct H4. apply remove_list_is_in ; auto.
  Qed.

  Lemma noless_ub_incl_subform_boxesS : forall s,
              (length (usable_boxes (XBoxed_list (top_boxes (fst s)), []%list)) < length (usable_boxes s) -> False) ->
              incl (subform_boxesS s) (subform_boxesS (XBoxed_list (top_boxes (fst s)), []%list)).
  Proof.
  intros s H. unfold subform_boxesS ; simpl. intros A H0. rewrite remove_list_of_nil. rewrite app_nil_r.
  apply InT_In. pose (InT_dec (subform_boxesLF (XBoxed_list (top_boxes (fst s)))) A).
  destruct s0 ; auto. exfalso. apply H. destruct s.
  simpl. simpl in f. simpl in H0. simpl in H. unfold usable_boxes. simpl. unfold subform_boxesS. simpl.
  rewrite remove_list_of_nil. rewrite app_nil_r.

  assert (length (remove_list (top_boxes l) (subform_boxesLF (XBoxed_list (top_boxes l)))) <
  length (remove_list (top_boxes l) (subform_boxesLF l ++ remove_list (subform_boxesLF l) (subform_boxesLF l0)))).
  apply remove_list_incr_decr4 ; simpl. apply NoDup_subform_boxesLF. apply add_remove_list_preserve_NoDup.
  1-2: apply NoDup_subform_boxesLF.
  intro. intros. apply in_or_app ; left.
  pose (XBoxed_list_same_subform_boxes (top_boxes l)). apply a0 in H1. apply In_subform_boxes in H1. destruct H1.
  destruct H1. apply In_incl_subform_boxes with (A:=x). apply top_boxes_incl_list ; auto. auto.
  intro. apply f. apply In_InT ; auto.
  exists A. repeat split ; auto. intro. apply f. apply In_InT. apply In_incl_subform_boxes with (A:=A).
  apply list_preserv_XBoxed_list ; auto. apply in_top_boxes in H1. destruct H1. destruct s. destruct s.
  destruct p. subst ; simpl ; auto. intro ; apply f ; apply In_InT ; auto.

  assert (length (remove_list (top_boxes (XBoxed_list (top_boxes l))) (subform_boxesLF (XBoxed_list (top_boxes l)))) <=
  length (remove_list (top_boxes l) (subform_boxesLF (XBoxed_list (top_boxes l))))).
  apply remove_list_incr_decr3 ; simpl.
  intro. intros. pose (XBoxed_list_same_subform_boxes (top_boxes l)). apply is_box_in_top_boxes.
  apply list_preserv_XBoxed_list ; auto. apply in_top_boxes in H2. destruct H2. destruct s. destruct s.
  destruct p ; subst ; eexists ; auto.
  lia.
  Qed.