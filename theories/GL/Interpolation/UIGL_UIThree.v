(* Uniform interpolation *)

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
Require Import UIGL_PermutationT.
Require Import UIGL_PermutationTS.
Require Import UIGL_And_Or_rules.
Require Import UIGL_UI_prelims.
Require Import UIGL_UI_inter.
Require Import UIGL_UIDiam_N.


  Section UIPThree.

  Theorem UI_Three : forall s (p : nat) X0 Y0,
                                    (In (Var p) (propvar_subform_list (X0 ++ Y0)) -> False) ->
                                    GLS_prv (fst s ++ X0, snd s ++ Y0) ->
                                    GLS_prv (X0, (UI p s) :: Y0).
  Proof.
  (* Setting up the strong induction on the height of the derivation (PIH) and
      on the measure of the sequent using LexSeq (SIH). *)
  intros s p X0 Y0 NotVar D. generalize dependent NotVar. remember (fst s ++ X0, snd s ++ Y0) as scomp.
  generalize dependent Heqscomp. remember (derrec_height D) as n. generalize dependent Heqn.
  generalize dependent Y0. generalize dependent X0. generalize dependent D.
  generalize dependent scomp. generalize dependent s. generalize dependent n.
  pose (d:=strong_inductionT (fun (x:nat) => forall (s : list MPropF * list MPropF) (scomp : list MPropF * list MPropF) (D : GLS_prv scomp) (X0 Y0 : list MPropF),
                x = derrec_height D ->
                scomp = (fst s ++ X0, snd s ++ Y0) -> (In # p (propvar_subform_list (X0 ++ Y0)) -> False) -> GLS_prv (X0, UI p s :: Y0))).
  apply d. clear d. intros n PIH.
  pose (d:=LexSeq_ind (fun (s:Seq) => forall (scomp : list MPropF * list MPropF) (D : GLS_prv scomp) (X0 Y0 : list MPropF),
                n = derrec_height D ->
                scomp = (fst s ++ X0, snd s ++ Y0) -> (In # p (propvar_subform_list (X0 ++ Y0)) -> False) -> GLS_prv (X0, UI p s :: Y0))).
  apply d. clear d. intros k SIH.

  (* Now we do the actual proof-theoretical work. *)
  intros s0 D0. remember D0 as D0'. destruct D0.
  (* D0 is a leaf *)
  - inversion f.
  (* D0 ends with an application of rule *)
  - intros X0 Y0 hei idseq propvar. destruct (empty_seq_dec k) as [ EE | NE].
    { subst ; simpl in *.
       assert (J1: GLS_prv (X0, Y0)). apply derI with ps ; auto. apply GLS_prv_wkn_R with (X0, Y0) (UI p ([], [])) ; auto.
       apply (wkn_RI _ _ []). }
    { inversion g ; subst.
    (* IdP *)
    * inversion H ; subst.
      assert (InT (# P) (fst k ++ X0)). rewrite <- H2. apply InT_or_app ; right ; apply InT_eq.
      apply InT_app_or in H0.
      assert (InT (# P) (snd k ++ Y0)). rewrite <- H3. apply InT_or_app ; right ; apply InT_eq.
      apply InT_app_or in H1. destruct H0 ; destruct H1.
      + assert ((X0, UI p k :: Y0) = (X0, [] ++ UI p k :: Y0)). auto. rewrite H0. apply is_init_UI.
         left ; left. destruct k. simpl in i ; simpl in i0. apply InT_split in i. destruct i. destruct s ; subst.
         apply InT_split in i0. destruct i0. destruct s ; subst. apply IdPRule_I.
      + destruct (critical_Seq_dec k).
         -- destruct (dec_init_rules k).
            ** assert (is_init k) ; auto. assert (J0: GUI p k (UI p k)). apply UI_GUI ; auto.
                pose (@GUI_inv_critic_init p k _ J0 c X). rewrite <- e.
                assert ((X0, Top :: Y0) = (X0, [] ++ Top :: Y0)). auto. rewrite H0. apply TopR.
            ** assert ((is_init k) -> False) ; auto. assert (J0: GUI p k (UI p k)). apply UI_GUI ; auto.
                assert (J1: Gimap (GUI p) (GLR_prems (nodupseq k)) (map (UI p) (GLR_prems (nodupseq k)))). apply Gimap_map. intros.
                apply UI_GUI ; auto.
                assert (J2: (Gimap (GN p (GUI p) k) (Canopy (nodupseq (XBoxed_list (top_boxes (fst k)), [])))
                (map (N p k) (Canopy (nodupseq (XBoxed_list (top_boxes (fst k)), [])))))). apply Gimap_map. intros.
                apply (N_spec p k x).
                assert (J40: fst k <> []). intro. rewrite H1 in i ; inversion i.
                pose (@GUI_inv_critic_not_init p k _ _ _ J0 c NE H0 J1 J2). rewrite <- e.
                pose (OrR (X0,Y0)). simpl in g0. apply g0.
                apply (@GLS_adm_list_exch_R (X0,
                Or (list_disj (map Neg (restr_list_prop p (fst k))))
                   (Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq k)))))
                      (Diam
                         (list_conj
                            (map (N p k) (Canopy (nodupseq (XBoxed_list (top_boxes (fst k)), []%list)))))))
                 :: list_disj (restr_list_prop p (snd k)) :: Y0)).
                2: epose (list_exch_RI _ [] [Or (list_disj (map Neg (restr_list_prop p (fst k)))) (Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq k)))))
                (Diam (list_conj (map (N p k) (Canopy (nodupseq (XBoxed_list (top_boxes (fst k)), []%list)))))))] [] [list_disj (restr_list_prop p (snd k))] Y0) ; simpl in l ; apply l.
                pose (OrR (X0,list_disj (restr_list_prop p (snd k)) :: Y0)). simpl in g1. apply g1.
                assert (J3: InT (Neg # P) (map Neg (restr_list_prop p (fst k)))). unfold restr_list_prop. apply InT_map_iff.
                exists (# P) ; split ; auto. apply In_InT. apply in_not_touched_remove. apply In_list_In_list_prop_LF ; apply InT_In ; auto.
                intro. apply propvar. rewrite <- H1. rewrite propvar_subform_list_app. apply in_or_app ; right.
                apply In_list_In_propvar_subform_list ; apply InT_In ; auto.
                remember (Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq k))))) (Diam (list_conj
                       (map (N p k) (Canopy (nodupseq (XBoxed_list (top_boxes (fst k)), []%list))))))
                 :: list_disj (restr_list_prop p (snd k)) :: Y0) as Y.
                pose (list_disj_wkn_R (map Neg (restr_list_prop p (fst k))) (X0, Y) (Neg # P) J3). apply g2. simpl.
                unfold Neg. apply derI with (ps:=[([] ++ # P :: X0, [] ++ ⊥ :: Y)]). apply ImpR. assert ((X0, # P --> ⊥ :: Y) = ([] ++ X0, [] ++ # P --> ⊥ :: Y)).
                auto. rewrite H1. apply ImpRRule_I. apply dlCons. 2: apply dlNil.
                assert (InT (# P) ([] ++ ⊥ :: Y)). simpl. apply InT_cons. rewrite HeqY. repeat apply InT_cons ; auto.
                apply InT_split in H1. destruct H1. destruct s. rewrite e0. apply derI with (ps:=[]). apply IdP. apply IdPRule_I.
                apply dlNil.
         -- assert (J0: GUI p k (UI p k)). apply UI_GUI ; auto.
            assert (J1: Gimap (GUI p) (Canopy (nodupseq k)) (map (UI p) (Canopy (nodupseq k)))). apply Gimap_map. intros.
            apply UI_GUI ; auto.
            pose (@GUI_inv_not_critic p k _ _ J0 f J1). rewrite <- e.
            pose (list_conj_R (map (UI p) (Canopy (nodupseq k))) (X0,Y0)). simpl in g0. apply g0. intros.
            apply InT_map_iff in H0. destruct H0. destruct p0. subst.
            assert (LexSeq x k). pose (Canopy_LexSeq _ _ i1). destruct s ; subst ; auto. exfalso.
            apply f ; apply Canopy_critical in i1 ; auto. apply critical_nodupseq ; auto. apply LexSeq_nodupseq in l ; auto.
            simpl in SIH.
            assert (J2: GLS_rules [] (fst x ++ X0, snd x ++ Y0)).
            apply IdP. assert (InT (# P) (snd x ++ Y0)). apply InT_or_app ; auto. apply InT_split in H1.
            destruct H1. destruct s. rewrite e0. assert (InT (# P) (fst x ++ X0)). apply InT_or_app ; left.
            apply Canopy_neg_var with (q:=P) in i1 ; auto. apply In_InT. destruct k ; simpl. apply nodup_In ; simpl in i ; apply InT_In in i ; auto.
            apply InT_split in H1. destruct H1. destruct s. rewrite e1.
            apply IdPRule_I. pose (derI _ J2 d).
            assert (J3: S (dersrec_height d) = derrec_height d0). simpl. lia.
            assert (J4: (fst x ++ X0, snd x ++ Y0) = (fst x ++ X0, snd x ++ Y0)). auto.
            pose (SIH _ H0 _ _ _ _ J3 J4 propvar). auto.
      + destruct (critical_Seq_dec k).
         -- destruct (dec_init_rules k).
            ** assert (is_init k) ; auto. assert (J0: GUI p k (UI p k)). apply UI_GUI ; auto.
                pose (@GUI_inv_critic_init p k _ J0 c X). rewrite <- e.
                assert ((X0, Top :: Y0) = (X0, [] ++ Top :: Y0)). auto. rewrite H0. apply TopR.
            ** assert ((is_init k) -> False) ; auto. assert (J0: GUI p k (UI p k)). apply UI_GUI ; auto.
                assert (J1: Gimap (GUI p) (GLR_prems (nodupseq k)) (map (UI p) (GLR_prems (nodupseq k)))). apply Gimap_map. intros.
                apply UI_GUI ; auto.
                assert (J2: (Gimap (GN p (GUI p) k) (Canopy (nodupseq (XBoxed_list (top_boxes (fst k)), [])))
                (map (N p k) (Canopy (nodupseq (XBoxed_list (top_boxes (fst k)), [])))))). apply Gimap_map. intros.
                apply (N_spec p k x).
                pose (@GUI_inv_critic_not_init p k _ _ _ J0 c NE H0 J1 J2). rewrite <- e.
                pose (OrR (X0,Y0)). simpl in g0. apply g0.
                assert (J3: InT (# P)  (restr_list_prop p (snd k))). unfold restr_list_prop. apply In_InT.
                apply in_not_touched_remove. apply In_list_In_list_prop_LF ; apply InT_In ; auto.
                intro. apply propvar. rewrite <- H1. rewrite propvar_subform_list_app. apply in_or_app ; left.
                apply In_list_In_propvar_subform_list ; apply InT_In ; auto.
                remember (Or (list_disj (map Neg (restr_list_prop p (fst k)))) (Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq k))))) (Diam
                (list_conj  (map (N p k) (Canopy (nodupseq (XBoxed_list (top_boxes (fst k)), []%list))))))) :: Y0) as Y.
                pose (list_disj_wkn_R (restr_list_prop p (snd k)) (X0, Y) (# P) J3). apply g1. simpl.
                apply InT_split in i. destruct i. destruct s. rewrite e0. apply derI with (ps:=[]). apply IdP. 2: apply dlNil.
                assert ((x ++ # P :: x0, # P :: Y) = (x ++ # P :: x0, [] ++ # P :: Y)). auto. rewrite H1 ; apply IdPRule_I.
         -- assert (J0: GUI p k (UI p k)). apply UI_GUI ; auto.
            assert (J1: Gimap (GUI p) (Canopy (nodupseq k)) (map (UI p) (Canopy (nodupseq k)))). apply Gimap_map. intros.
            apply UI_GUI ; auto.
            pose (@GUI_inv_not_critic p k _ _ J0 f J1). rewrite <- e.
            pose (list_conj_R (map (UI p) (Canopy (nodupseq k))) (X0,Y0)). simpl in g0. apply g0. intros.
            apply InT_map_iff in H0. destruct H0. destruct p0. subst.
            assert (LexSeq x k). pose (Canopy_LexSeq _ _ i1). destruct s ; subst ; auto. exfalso.
            apply f ; apply Canopy_critical in i1 ; auto. apply critical_nodupseq ; auto. apply LexSeq_nodupseq in l ; auto. simpl in SIH.
            assert (J2: GLS_rules [] (fst x ++ X0, snd x ++ Y0)).
            apply IdP. assert (InT (# P) (fst x ++ X0)). apply InT_or_app ; auto. apply InT_split in H1.
            destruct H1. destruct s. rewrite e0. assert (InT (# P) (snd x ++ Y0)). apply InT_or_app ; left.
            apply Canopy_pos_var with (q:=P) in i1 ; auto. auto. apply In_InT. destruct k ; simpl. apply nodup_In ; simpl in i0 ; apply InT_In in i0 ; auto.
            apply InT_split in H1. destruct H1. destruct s. rewrite e1.
            apply IdPRule_I. pose (derI _ J2 d).
            assert (J3: S (dersrec_height d) = derrec_height d0). simpl. lia.
            assert (J4: (fst x ++ X0, snd x ++ Y0) = (fst x ++ X0, snd x ++ Y0)). auto.
            pose (SIH _ H0 _ _ _ _ J3 J4 propvar). auto.
      + apply derI with (ps:=[]). 2: apply dlNil. apply IdP. apply InT_split in i. destruct i. destruct s ; subst.
         apply InT_split in i0. destruct i0. destruct s ; subst. assert (UI p k :: x1 ++ # P :: x2 = (UI p k :: x1) ++ # P :: x2).
         auto. rewrite H0. apply IdPRule_I.

    (* BotL *)
    * inversion H ; subst.
      assert (InT ⊥ (fst k ++ X0)). rewrite <- H2. apply InT_or_app ; right ; apply InT_eq.
      apply InT_app_or in H0. destruct H0.
      + assert ((X0, UI p k :: Y0) = (X0, [] ++ UI p k :: Y0)). auto. rewrite H0. apply is_init_UI.
         right. destruct k. simpl in i. apply InT_split in i. destruct i. destruct s ; subst. apply BotLRule_I.
      + apply derI with (ps:=[]). 2: apply dlNil. apply BotL. apply InT_split in i. destruct i. destruct s ; subst.
         apply BotLRule_I.

    (* ImpR *)
    * destruct (critical_Seq_dec k).
      (* If critical, then the rule ImpR was applied on a formula in X0 or Y0.
          So, apply PIH omn the premise and then the rule. *)
      + inversion H ; subst. assert (J0: dersrec_height d = dersrec_height d) ; auto.
         apply dersrec_derrec_height in J0. destruct J0.
         assert (J1: derrec_height x = derrec_height x). auto.
         assert (J2: list_exch_L (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) (A :: fst k ++ X0, Δ0 ++ B :: Δ1)).
         assert ((Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) = ([] ++ [] ++ Γ0 ++ [A] ++ Γ1, Δ0 ++ B :: Δ1)). auto.
         rewrite H0.
         assert ((A :: fst k ++ X0, Δ0 ++ B :: Δ1) = ([] ++ [A] ++ Γ0 ++ [] ++ Γ1, Δ0 ++ B :: Δ1)).
         simpl. rewrite H2. auto. rewrite H1. apply list_exch_LI.
         pose (GLS_hpadm_list_exch_L x J1 J2). destruct s.
         assert (J3: derrec_height x0 = derrec_height x0). auto.
         assert (J4: list_exch_L (A :: fst k ++ X0, Δ0 ++ B :: Δ1) (fst k ++ A :: X0, Δ0 ++ B :: Δ1)).
         assert ((fst k ++ A :: X0, Δ0 ++ B :: Δ1) = ([] ++ [] ++ fst k ++ [A] ++ X0, Δ0 ++ B :: Δ1)). auto.
         rewrite H0.
         assert ((A :: fst k ++ X0, Δ0 ++ B :: Δ1) = ([] ++ [A] ++ fst k ++ [] ++ X0, Δ0 ++ B :: Δ1)).
         auto. rewrite H1. apply list_exch_LI.
         pose (GLS_hpadm_list_exch_L x0 J3 J4). destruct s. simpl in PIH.
         apply app2_find_hole in H3. destruct H3.
         repeat destruct s ; destruct p0 ; subst.
         assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
         assert (J6: derrec_height x1 = derrec_height x1). auto.
         assert (J7: (fst k ++ A :: X0, snd k ++ B :: Δ1) = (fst k ++ A:: X0, snd k ++ B :: Δ1)). auto.
         assert (J8: (In # p (propvar_subform_list ((A :: X0) ++ B :: Δ1)) -> False)).
         intro. apply propvar. repeat rewrite propvar_subform_list_app.
         repeat rewrite propvar_subform_list_app in H0. simpl in H0. simpl.
         repeat rewrite <- app_assoc in H0.
         apply in_app_or in H0 ; destruct H0. apply in_or_app ; right ; apply in_or_app ;
         left ; apply in_or_app ; auto.
         apply in_app_or in H0 ; destruct H0. apply in_or_app ; auto.
         apply in_app_or in H0 ; destruct H0. apply in_or_app ; right ; apply in_or_app ;
         left ; apply in_or_app ; auto. apply in_or_app ; right ; apply in_or_app ; auto.
         pose (PIH _ J5 _ _ _ _ _ J6 J7 J8).
         apply derI with (ps:=[([] ++ A :: X0, [UI p k] ++ B :: Δ1)]). apply ImpR.
         assert ((X0, UI p k :: A --> B :: Δ1) = ([] ++ X0, [UI p k] ++ A --> B :: Δ1)). auto. rewrite H0.
         apply ImpRRule_I. apply dlCons ; [ simpl ; auto | apply dlNil].
         destruct x2 ; simpl in e1 ; subst. rewrite <- app_nil_end in e0 ; subst.
         assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
         assert (J6: derrec_height x1 = derrec_height x1). auto.
         assert (J7: (fst k ++ A :: X0, snd k ++ B :: Δ1) = (fst k ++ A:: X0, snd k ++ B :: Δ1)). auto.
         assert (J8: (In # p (propvar_subform_list ((A :: X0) ++ B :: Δ1)) -> False)).
         intro. apply propvar. repeat rewrite propvar_subform_list_app.
         repeat rewrite propvar_subform_list_app in H0. simpl in H0. simpl.
         repeat rewrite <- app_assoc in H0.
         apply in_app_or in H0 ; destruct H0. apply in_or_app ; right ; apply in_or_app ;
         left ; apply in_or_app ; auto.
         apply in_app_or in H0 ; destruct H0. apply in_or_app ; auto.
         apply in_app_or in H0 ; destruct H0. apply in_or_app ; right ; apply in_or_app ;
         left ; apply in_or_app ; auto. apply in_or_app ; right ; apply in_or_app ; auto.
         pose (PIH _ J5 _ _ _ _ _ J6 J7 J8).
         apply derI with (ps:=[([] ++ A :: X0, [UI p k] ++ B :: Δ1)]). apply ImpR.
         assert ((X0, UI p k :: A --> B :: Δ1) = ([] ++ X0, [UI p k] ++ A --> B :: Δ1)). auto. rewrite H0.
         apply ImpRRule_I. apply dlCons ; [ simpl ; auto | apply dlNil].
         exfalso. destruct k ; simpl in e0 ; subst. unfold critical_Seq in c ; unfold is_Prime in c ; simpl in c.
         assert (In m (l1 ++ Δ0 ++ m :: x2)). apply in_or_app ; right ; apply in_or_app ; right ; apply in_eq.
         apply c in H0. inversion e1 ; subst. destruct H0 ; destruct H0 ; inversion H0 ; inversion H1.
         assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
         assert (J6: derrec_height x1 = derrec_height x1). auto.
         assert (J7: (fst k ++ A :: X0, (snd k ++ x2) ++ B :: Δ1) = (fst k ++ A:: X0, snd k ++ x2 ++ B :: Δ1)).
         repeat rewrite <- app_assoc. auto.
         assert (J8: (In # p (propvar_subform_list ((A :: X0) ++ (x2 ++ B :: Δ1))) -> False)).
         intro. apply propvar. repeat rewrite propvar_subform_list_app.
         repeat rewrite propvar_subform_list_app in H0. simpl in H0. simpl.
         repeat rewrite <- app_assoc in H0.
         apply in_app_or in H0 ; destruct H0. apply in_or_app ; right ; apply in_or_app ;
         right ; apply in_or_app ; left ; apply in_or_app ; auto.
         apply in_app_or in H0 ; destruct H0. apply in_or_app ; auto.
         apply in_app_or in H0 ; destruct H0. apply in_or_app ; right ; apply in_or_app ; auto.
         apply in_app_or in H0 ; destruct H0. apply in_or_app ; right ; apply in_or_app ;
         right ; apply in_or_app ; left ; apply in_or_app ; auto.
         apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
         pose (PIH _ J5 _ _ _ _ _ J6 J7 J8).
         apply derI with (ps:=[([] ++ A :: X0, (UI p k :: x2) ++ B :: Δ1)]). apply ImpR.
         assert ((X0, UI p k :: x2 ++ A --> B :: Δ1) = ([] ++ X0, (UI p k :: x2) ++ A --> B :: Δ1)). auto. rewrite H0.
         apply ImpRRule_I. apply dlCons ; [ simpl ; auto | apply dlNil].
      (*  If not critical, consider the conjunction that UI p k is. *)
      + assert (J0: GUI p k (UI p k)). apply UI_GUI ; auto.
         assert (J1: Gimap (GUI p) (Canopy (nodupseq k)) (map (UI p) (Canopy (nodupseq k)))). apply Gimap_map. intros.
         apply UI_GUI ; auto.
         pose (@GUI_inv_not_critic p k (UI p k) (map (UI p) (Canopy (nodupseq k))) J0 f J1). rewrite <- e.

         assert (J2: forall s1, InT s1 (Canopy (nodupseq k)) -> GLS_prv (X0, UI p s1 :: Y0)).
         intros. pose (fold_Canopy _ _ H0). destruct s ; subst.
         exfalso. apply f. apply Canopy_critical in H0 ; auto. apply critical_nodupseq in H0 ; auto.
         destruct s. destruct p0. unfold inv_prems in i.
         apply InT_flatten_list_InT_elem in i. destruct i. destruct p0. simpl in PIH. simpl in SIH.
         pose (derI _ g d).
         assert (existsT2 (d1: GLS_prv (fst (nodupseq k) ++ X0, snd (nodupseq k) ++ Y0)), derrec_height d1 <= derrec_height d0).
         destruct (nodupseq_id k). destruct p0. destruct s. destruct s. destruct p1. destruct p1.
         pose (PermutationTS_prv_hpadm _ d0 (x2 ++ fst x1 ++ X0, x3 ++ snd x1 ++ Y0)). destruct s.
         split ; simpl ; apply Permutation_PermutationT. destruct p1.
         pose (@Permutation_app _ (fst k) X0 (x2 ++ fst x1) X0). rewrite <- app_assoc in p3 ; apply p3 ; auto.
         apply Permutation_PermutationT ; auto. destruct p1.
         pose (@Permutation_app _ (snd k) Y0 (x3 ++ snd x1) Y0). rewrite <- app_assoc in p3 ; apply p3 ; auto.
         apply Permutation_PermutationT ; auto.
         epose (incl_ctr_R_hpadm _ x3 _ x4). destruct s. intros A HA ; apply in_or_app ; left ; auto.
         epose (incl_ctr_L_hpadm x2 _ _ x5). destruct s. intros A HA ; apply in_or_app ; left ; auto.
         pose (PermutationTS_prv_hpadm _ x6 (fst (nodupseq k) ++ X0, snd (nodupseq k) ++ Y0)). destruct s.
         split ; simpl ; apply Permutation_PermutationT. destruct p0. apply Permutation_app ; auto.
         unfold nodupseq in p0. apply Permutation_PermutationT ; auto. destruct p0.
         apply Permutation_app ; auto. unfold nodupseq in p2. apply Permutation_PermutationT ; auto.
         exists x7. lia. destruct X.
         assert (J2: derrec_height x1 = derrec_height x1). auto.
         assert (J3: (fst (nodupseq k) ++ X0, snd (nodupseq k) ++ Y0) = (fst (nodupseq k) ++ X0, snd (nodupseq k) ++ Y0)). auto.
         pose (Canopy_hp_inv_ctx (nodupseq k) _ _ x1 X0 Y0 J2 J3 _ H0). destruct s.
         destruct (lt_decT (derrec_height x2) (S (dersrec_height d))).
         (* Use PIH. *)
         pose (fold_Canopy _ _ H0). destruct s ; subst.
         exfalso. apply f. apply Canopy_critical in H0 ; auto. apply critical_nodupseq in H0 ; auto.
         destruct s. destruct p0. unfold inv_prems in i2.
         apply InT_flatten_list_InT_elem in i2. destruct i2. destruct p0.
         assert (J4: derrec_height x2 = derrec_height x2). auto.
         assert (J5: (fst s1 ++ X0, snd s1 ++ Y0) = (fst s1 ++ X0, snd s1 ++ Y0)). auto.
         pose (PIH _ l1 s1 _ x2 X0 Y0 J4 J5). apply g0 ; auto.
         (* Use SIH. *)
         assert (derrec_height x2 = S (dersrec_height d)). assert (derrec_height d0 = S (dersrec_height d)). simpl. auto. lia.
         assert (J4: LexSeq s1 k). pose (Canopy_LexSeq _ _ H0).
         destruct s ; subst ; auto. exfalso. apply f. apply Canopy_critical in H0 ; apply critical_nodupseq in H0 ; auto.
         apply LexSeq_nodupseq in l1 ; auto. symmetry in H1.
         assert (J5: (fst s1 ++ X0, snd s1 ++ Y0) = (fst s1 ++ X0, snd s1 ++ Y0)). auto.
         pose (SIH _ J4 _ _ _ _ H1 J5 propvar). auto.

         assert (J3: (forall A : MPropF, InT A (map (UI p) (Canopy (nodupseq k))) -> GLS_prv (fst (X0, Y0), A :: snd (X0, Y0)))).
         intros. simpl. apply InT_map_iff in H0. destruct H0. destruct p0 ; subst. apply J2 in i ; auto.
         pose (list_conj_R _ _ J3). simpl in g0. auto.

    (* ImpL *)
    * destruct (critical_Seq_dec k).
      (* If critical, then the rule ImpL was applied on a formula in X0 or Y0.
          So, apply PIH on the premises and then the rule. *)
      + inversion H ; subst. assert (J0: dersrec_height d = dersrec_height d) ; auto.
         apply dersrec_derrec2_height in J0. destruct J0. destruct s. simpl in PIH.
         assert (J1: derrec_height x = derrec_height x). auto.
         assert (J2: list_exch_R (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) (Γ0 ++ Γ1, A :: snd k ++ Y0)).
         assert ((Γ0 ++ Γ1, Δ0 ++ A :: Δ1) = (Γ0 ++ Γ1, [] ++ [] ++ Δ0 ++ [A] ++ Δ1)). auto.
         rewrite H0.
         assert ((Γ0 ++ Γ1, A :: snd k ++ Y0) = (Γ0 ++ Γ1, [] ++ [A] ++ Δ0 ++ [] ++ Δ1)).
         simpl. rewrite H3. auto. rewrite H1. apply list_exch_RI.
         pose (GLS_hpadm_list_exch_R x J1 J2). destruct s.
         assert (J3: derrec_height x1 = derrec_height x1). auto.
         assert (J4: list_exch_R (Γ0 ++ Γ1, A :: snd k ++ Y0) (Γ0 ++ Γ1, snd k ++ A :: Y0)).
         assert ((Γ0 ++ Γ1, snd k ++ A :: Y0) = (Γ0 ++ Γ1, [] ++ [] ++ snd k ++ [A] ++ Y0)). auto.
         rewrite H0.
         assert ((Γ0 ++ Γ1, A :: snd k ++ Y0) = (Γ0 ++ Γ1, [] ++ [A] ++ snd k ++ [] ++ Y0)).
         auto. rewrite H1. apply list_exch_RI.
         pose (GLS_hpadm_list_exch_R x1 J3 J4). destruct s.
         apply app2_find_hole in H2. destruct H2.
         repeat destruct s ; destruct p0 ; subst.
         assert (J5: derrec_height x2 < S (dersrec_height d)). lia.
         assert (J6: derrec_height x2 = derrec_height x2). auto.
         assert (J7: (fst k ++ Γ1, snd k ++ A :: Y0) = (fst k ++ Γ1, snd k ++ A :: Y0)). auto.
         assert (J8: In # p (propvar_subform_list (Γ1 ++ A :: Y0)) -> False).
         intro. apply propvar. repeat rewrite propvar_subform_list_app.
         repeat rewrite propvar_subform_list_app in H0. simpl in H0. simpl.
         repeat rewrite <- app_assoc.
         apply in_app_or in H0 ; destruct H0. apply in_or_app ; right ; apply in_or_app ;
         right ; apply in_or_app ; auto.
         apply in_app_or in H0 ; destruct H0. apply in_or_app ; auto. apply in_or_app ; right ; apply in_or_app ;
         right ; apply in_or_app ; auto.
         pose (PIH _ J5 _ _ _ _ _ J6 J7 J8).
         assert (J9: derrec_height x0 < S (dersrec_height d)). lia.
         assert (J10: derrec_height x0 = derrec_height x0). auto.
         assert (J11: (fst k ++ B :: Γ1, Δ0 ++ Δ1) = (fst k ++ B :: Γ1, snd k ++ Y0)). rewrite H3 ; auto.
         assert (J12: In # p (propvar_subform_list ((B :: Γ1) ++ Y0)) -> False).
         intro. apply propvar. repeat rewrite propvar_subform_list_app.
         repeat rewrite propvar_subform_list_app in H0. simpl in H0. simpl.
         repeat rewrite <- app_assoc. repeat rewrite <- app_assoc in H0.
         apply in_app_or in H0 ; destruct H0. apply in_or_app ; right ; apply in_or_app ; auto.
         apply in_app_or in H0 ; destruct H0. apply in_or_app ; right ; apply in_or_app ;
         right ; apply in_or_app ; auto. apply in_or_app ; right ; apply in_or_app ;
         right ; apply in_or_app ; auto.
         pose (PIH _ J9 _ _ _ _ _ J10 J11 J12).
         apply derI with (ps:=[([] ++ Γ1, [UI p k] ++ A :: Y0);([] ++ B :: Γ1, [UI p k] ++ Y0)]). apply ImpL.
         assert ((A --> B :: Γ1, UI p k :: Y0) = ([] ++ A --> B :: Γ1, [UI p k] ++ Y0)). auto. rewrite H0.
         apply ImpLRule_I. apply dlCons. auto. apply dlCons. auto. apply dlNil.
         destruct x3 ; simpl in e1 ; subst. rewrite <- app_nil_end in e0 ; subst.
         assert (J5: derrec_height x2 < S (dersrec_height d)). lia.
         assert (J6: derrec_height x2 = derrec_height x2). auto.
         assert (J7: (fst k ++ Γ1, snd k ++ A :: Y0) = (fst k ++ Γ1, snd k ++ A :: Y0)). auto.
         assert (J8: In # p (propvar_subform_list (Γ1 ++ A :: Y0)) -> False).
         intro. apply propvar. repeat rewrite propvar_subform_list_app.
         repeat rewrite propvar_subform_list_app in H0. simpl in H0. simpl.
         repeat rewrite <- app_assoc.
         apply in_app_or in H0 ; destruct H0. apply in_or_app ; right ; apply in_or_app ;
         right ; apply in_or_app ; auto.
         apply in_app_or in H0 ; destruct H0. apply in_or_app ; auto. apply in_or_app ; right ; apply in_or_app ;
         right ; apply in_or_app ; auto.
         pose (PIH _ J5 _ _ _ _ _ J6 J7 J8).
         assert (J9: derrec_height x0 < S (dersrec_height d)). lia.
         assert (J10: derrec_height x0 = derrec_height x0). auto.
         assert (J11: (fst k ++ B :: Γ1, Δ0 ++ Δ1) = (fst k ++ B :: Γ1, snd k ++ Y0)). rewrite H3 ; auto.
         assert (J12: In # p (propvar_subform_list ((B :: Γ1) ++ Y0)) -> False).
         intro. apply propvar. repeat rewrite propvar_subform_list_app.
         repeat rewrite propvar_subform_list_app in H0. simpl in H0. simpl.
         repeat rewrite <- app_assoc. repeat rewrite <- app_assoc in H0.
         apply in_app_or in H0 ; destruct H0. apply in_or_app ; right ; apply in_or_app ; auto.
         apply in_app_or in H0 ; destruct H0. apply in_or_app ; right ; apply in_or_app ;
         right ; apply in_or_app ; auto. apply in_or_app ; right ; apply in_or_app ;
         right ; apply in_or_app ; auto.
         pose (PIH _ J9 _ _ _ _ _ J10 J11 J12).
         apply derI with (ps:=[([] ++ Γ1, [UI p k] ++ A :: Y0);([] ++ B :: Γ1, [UI p k] ++ Y0)]). apply ImpL.
         assert ((A --> B :: Γ1, UI p k :: Y0) = ([] ++ A --> B :: Γ1, [UI p k] ++ Y0)). auto. rewrite H0.
         apply ImpLRule_I. apply dlCons. auto. apply dlCons. auto. apply dlNil.
         exfalso. destruct k ; simpl in e0 ; subst. unfold critical_Seq in c ; unfold is_Prime in c ; simpl in c.
         assert (In m ((Γ0 ++ m :: x3) ++ l2)). repeat rewrite <- app_assoc. apply in_or_app ; right ; apply in_or_app ; left ; apply in_eq.
         apply c in H0. inversion e1 ; subst. destruct H0 ; destruct H0 ; inversion H0 ; inversion H1.
         assert (J5: derrec_height x2 < S (dersrec_height d)). lia.
         assert (J6: derrec_height x2 = derrec_height x2). auto.
         assert (J7: ((fst k ++ x3) ++ Γ1, snd k ++ A :: Y0) = (fst k ++ x3 ++ Γ1, snd k ++ A :: Y0)).
         rewrite <- app_assoc ; auto.
         assert (J8: In # p (propvar_subform_list ((x3 ++ Γ1) ++ A :: Y0)) -> False).
         intro. apply propvar. repeat rewrite propvar_subform_list_app.
         repeat rewrite propvar_subform_list_app in H0. simpl in H0. simpl.
         repeat rewrite <- app_assoc. repeat rewrite <- app_assoc in H0.
         apply in_app_or in H0 ; destruct H0. apply in_or_app ; auto. apply in_app_or in H0 ; destruct H0.
         apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
         apply in_app_or in H0 ; destruct H0. apply in_or_app ; right ; apply in_or_app ; auto.
         apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
         pose (PIH _ J5 _ _ _ _ _ J6 J7 J8).
         assert (J9: derrec_height x0 < S (dersrec_height d)). lia.
         assert (J10: derrec_height x0 = derrec_height x0). auto.
         assert (J11: ((fst k ++ x3) ++ B :: Γ1, Δ0 ++ Δ1) = (fst k ++ x3 ++ B :: Γ1, snd k ++ Y0)).
         rewrite H3 ; rewrite <- app_assoc ; auto.
         assert (J12: In # p (propvar_subform_list ((x3 ++ B :: Γ1) ++ Y0)) -> False).
         intro. apply propvar. repeat rewrite propvar_subform_list_app.
         repeat rewrite propvar_subform_list_app in H0. simpl in H0. simpl.
         repeat rewrite <- app_assoc. repeat rewrite <- app_assoc in H0.
         apply in_app_or in H0 ; destruct H0. apply in_or_app ; auto. apply in_or_app ; right ; apply in_or_app ; auto.
         pose (PIH _ J9 _ _ _ _ _ J10 J11 J12).
         apply derI with (ps:=[(x3 ++ Γ1, [UI p k] ++ A :: Y0);(x3 ++ B :: Γ1, [UI p k] ++ Y0)]). apply ImpL.
         assert ((x3 ++ A --> B :: Γ1, UI p k :: Y0) = (x3 ++ A --> B :: Γ1, [UI p k] ++ Y0)). auto. rewrite H0.
         apply ImpLRule_I. apply dlCons. auto. apply dlCons. auto. apply dlNil.
      (*  If not critical, consider the conjunction that UI p k is. *)
      + assert (J0: GUI p k (UI p k)). apply UI_GUI ; auto.
         assert (J1: Gimap (GUI p) (Canopy (nodupseq k)) (map (UI p) (Canopy (nodupseq k)))). apply Gimap_map. intros.
         apply UI_GUI ; auto.
         pose (@GUI_inv_not_critic p k (UI p k) (map (UI p) (Canopy (nodupseq k))) J0 f J1). rewrite <- e.

         assert (J2: forall s1, InT s1 (Canopy (nodupseq k)) -> GLS_prv (X0, UI p s1 :: Y0)).
         intros. pose (fold_Canopy _ _ H0). destruct s ; subst.
         exfalso. apply f. apply Canopy_critical in H0 ; auto. apply critical_nodupseq in H0 ; auto.
         destruct s. destruct p0. unfold inv_prems in i.
         apply InT_flatten_list_InT_elem in i. destruct i. destruct p0. simpl in PIH. simpl in SIH.
         pose (derI _ g d).

         assert (existsT2 (d1: GLS_prv (fst (nodupseq k) ++ X0, snd (nodupseq k) ++ Y0)), derrec_height d1 <= derrec_height d0).
         destruct (nodupseq_id k). destruct p0. destruct s. destruct s. destruct p1. destruct p1.
         pose (PermutationTS_prv_hpadm _ d0 (x2 ++ fst x1 ++ X0, x3 ++ snd x1 ++ Y0)). destruct s.
         split ; simpl ; apply Permutation_PermutationT. destruct p1.
         pose (@Permutation_app _ (fst k) X0 (x2 ++ fst x1) X0). rewrite <- app_assoc in p3 ; apply p3 ; auto.
         apply Permutation_PermutationT ; auto. destruct p1.
         pose (@Permutation_app _ (snd k) Y0 (x3 ++ snd x1) Y0). rewrite <- app_assoc in p3 ; apply p3 ; auto.
         apply Permutation_PermutationT ; auto.
         epose (incl_ctr_R_hpadm _ x3 _ x4). destruct s. intros A HA ; apply in_or_app ; left ; auto.
         epose (incl_ctr_L_hpadm x2 _ _ x5). destruct s. intros A HA ; apply in_or_app ; left ; auto.
         pose (PermutationTS_prv_hpadm _ x6 (fst (nodupseq k) ++ X0, snd (nodupseq k) ++ Y0)). destruct s.
         split ; simpl ; apply Permutation_PermutationT. destruct p0. apply Permutation_app ; auto.
         unfold nodupseq in p0. apply Permutation_PermutationT ; auto. destruct p0.
         apply Permutation_app ; auto. unfold nodupseq in p2. apply Permutation_PermutationT ; auto.
         exists x7. lia. destruct X.
         assert (J2: derrec_height x1 = derrec_height x1). auto.
         assert (J3: (fst (nodupseq k) ++ X0, snd (nodupseq k) ++ Y0) = (fst (nodupseq k) ++ X0, snd (nodupseq k) ++ Y0)). auto.
         pose (Canopy_hp_inv_ctx (nodupseq k) _ _ x1 X0 Y0 J2 J3 _ H0). destruct s.
         destruct (lt_decT (derrec_height x2) (S (dersrec_height d))).
         (* Use PIH. *)
         pose (fold_Canopy _ _ H0). destruct s ; subst.
         exfalso. apply f. apply Canopy_critical in H0 ; auto. apply critical_nodupseq in H0 ; auto.
         destruct s. destruct p0. unfold inv_prems in i2.
         apply InT_flatten_list_InT_elem in i2. destruct i2. destruct p0.
         assert (J4: derrec_height x2 = derrec_height x2). auto.
         assert (J5: (fst s1 ++ X0, snd s1 ++ Y0) = (fst s1 ++ X0, snd s1 ++ Y0)). auto.
         pose (PIH _ l1 s1 _ x2 X0 Y0 J4 J5). apply g0 ; auto.
         (* Use SIH. *)
         assert (derrec_height x2 = S (dersrec_height d)). assert (derrec_height d0 = S (dersrec_height d)). simpl. auto. lia.
         assert (J4: LexSeq s1 k). pose (Canopy_LexSeq _ _ H0).
         destruct s ; subst ; auto. exfalso. apply f. apply Canopy_critical in H0 ; apply critical_nodupseq in H0 ; auto.
         apply LexSeq_nodupseq in l1 ; auto. symmetry in H1.
         assert (J5: (fst s1 ++ X0, snd s1 ++ Y0) = (fst s1 ++ X0, snd s1 ++ Y0)). auto.
         pose (SIH _ J4 _ _ _ _ H1 J5 propvar). auto.

         assert (J3: (forall A : MPropF, InT A (map (UI p) (Canopy (nodupseq k))) -> GLS_prv (fst (X0, Y0), A :: snd (X0, Y0)))).
         intros. simpl. apply InT_map_iff in H0. destruct H0. destruct p0 ; subst. apply J2 in i ; auto.
         pose (list_conj_R _ _ J3). simpl in g0. auto.

    (* GLR *)
    * destruct (critical_Seq_dec k).
      (* If critical. *)
      + inversion X ; subst. (* Not sure the two lines below are useful. *)
         assert (J0: dersrec_height d = dersrec_height d) ; auto.
         apply dersrec_derrec_height in J0. destruct J0. simpl in PIH. simpl in SIH.
         destruct (dec_init_rules k).
         (* If initial. *)
        ** assert (is_init k) ; auto. assert (J0: GUI p k (UI p k)). apply UI_GUI ; auto.
         pose (@GUI_inv_critic_init p k _ J0 c X2). rewrite <- e0.
         assert ((X0, Top :: Y0) = (X0, [] ++ Top :: Y0)). auto. rewrite H. apply TopR.
         (* If not initial. *)
        ** apply univ_gen_ext_splitR in X1. destruct X1. destruct s. destruct p0. destruct p0.
         apply app2_find_hole in H2. destruct H2.
         assert ((is_init k) -> False) ; auto.
         assert (J0: GUI p k (UI p k)). apply UI_GUI ; auto.
         assert (J1: Gimap (GUI p) (GLR_prems (nodupseq k)) (map (UI p) (GLR_prems (nodupseq k)))). apply Gimap_map. intros.
         apply UI_GUI ; auto.
         assert (J2: (Gimap (GN p (GUI p) k) (Canopy (nodupseq (XBoxed_list (top_boxes (fst k)), [])))
         (map (N p k) (Canopy (nodupseq (XBoxed_list (top_boxes (fst k)), [])))))). apply Gimap_map. intros.
         apply (N_spec p k x3).
         pose (@GUI_inv_critic_not_init p k _ _ _ J0 c NE H J1 J2). rewrite <- e1. clear e1.
         repeat destruct s ; destruct p0 ; subst.
         (* If Box A is in Y0. *)
         -- pose (OrR (X0,Box A :: Δ1)). simpl in g0. apply g0. clear g0.
            apply GLS_prv_wkn_R with (A:=list_disj (restr_list_prop p (snd k))) (s:=(X0,
            Or (list_disj (map Neg (restr_list_prop p (fst k))))(Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq k))))) (Diam
            (list_conj (map (N p k) (Canopy (nodupseq (XBoxed_list (top_boxes (fst k)), []%list)))))))
            :: Box A :: Δ1)).
            2: epose (wkn_RI (list_disj (restr_list_prop p (snd k))) _ [] _) ; simpl in w ; apply w.
            pose (OrR (X0,Box A :: Δ1)). simpl in g0. apply g0. clear g0.
            apply GLS_prv_wkn_R with (A:=list_disj (map Neg (restr_list_prop p (fst k)))) (s:=(X0,
            Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq k))))) (Diam
            (list_conj (map (N p k) (Canopy (nodupseq (XBoxed_list (top_boxes (fst k)), []%list))))))
            :: Box A :: Δ1)).
            2: epose (wkn_RI (list_disj (map Neg (restr_list_prop p (fst k)))) _ [] _) ; simpl in w ; apply w.
            pose (OrR (X0,Box A :: Δ1)). simpl in g0. apply g0. clear g0.
            apply GLS_prv_wkn_R with (A:=list_disj (map Box (map (UI p) (GLR_prems (nodupseq k))))) (s:=(X0,
            (Diam (list_conj (map (N p k) (Canopy (nodupseq (XBoxed_list (top_boxes (fst k)), []%list))))))
            :: Box A :: Δ1)).
            2: epose (wkn_RI (list_disj (map Box (map (UI p) (GLR_prems (nodupseq k))))) _ [] _) ; simpl in w ; apply w.
            apply Diam_rec_UI ; auto.
            assert (J5: derrec_height x < S (dersrec_height d)). lia.
            assert (J6: derrec_height x = derrec_height x). auto.
            assert (J7: (XBoxed_list (x0 ++ x1) ++ [Box A], [A]) = (fst (XBoxed_list x0, @nil MPropF) ++ XBoxed_list x1 ++ [Box A], snd (XBoxed_list x0, []) ++ [A])).
            simpl ; rewrite XBox_app_distrib. repeat rewrite <- app_assoc ; auto.
            assert (J8: (In # p (propvar_subform_list ((XBoxed_list x1 ++ [Box A]) ++ [A])) -> False)).
            intro. apply propvar. repeat rewrite propvar_subform_list_app.
            repeat rewrite propvar_subform_list_app in H0. simpl in H0. repeat rewrite <- app_nil_end in H0. simpl.
            repeat rewrite <- app_assoc in H0. apply in_app_or in H0 ; destruct H0.
            apply in_or_app ; left. apply propvar_subform_list_XBoxed_list in H0.
            apply propvar_subform_list_nobox_gen_ext with (l0:=x1); auto.
            apply in_or_app ; right ; apply in_or_app ; left. apply in_app_or in H0 ; destruct H0 ; auto.
            pose (PIH _ J5 _ _ _ _ _ J6 J7 J8).
            apply derI with (ps:=[(X0 ++ Box (Neg (UI p (XBoxed_list (top_boxes (fst k)), []%list))) :: [], [] ++ Bot :: Box A :: Δ1)]).
            apply ImpR. assert ((X0, Diam (UI p (XBoxed_list (top_boxes (fst k)), []%list)) :: Box A :: Δ1) =
            (X0 ++ [], [] ++ Diam (UI p (XBoxed_list (top_boxes (fst k)), []%list)) :: Box A :: Δ1)). rewrite <- app_nil_end. auto. rewrite H0.
            apply ImpRRule_I. apply dlCons. 2: apply dlNil.
            apply derI with (ps:=[(XBoxed_list (x1 ++ [Box (Neg (UI p (XBoxed_list (top_boxes (fst k)), []%list)))]) ++ [Box A], [A])]).
            apply GLR. assert (([] ++ ⊥ :: Box A :: Δ1) = [⊥] ++ Box A :: Δ1). auto. rewrite H0. apply GLRRule_I ; auto.
            intro. intros. apply in_app_or in H2 ; destruct H2. apply H1 ; apply in_or_app ; auto. exists (Neg (UI p (XBoxed_list (top_boxes (fst k)), []%list))).
            inversion H2 ; subst ; auto. inversion H3. apply univ_gen_ext_combine ; auto. apply univ_gen_ext_cons. apply univ_gen_ext_nil.
            apply dlCons. 2: apply dlNil. rewrite XBox_app_distrib. simpl. repeat rewrite <- app_assoc. simpl.
            apply GLS_prv_wkn_L with (A:=Box (Neg (UI p (XBoxed_list (top_boxes (fst k)), []%list)))) (s:=(XBoxed_list x1 ++
            [Neg (UI p (XBoxed_list (top_boxes (fst k)), []%list)); Box A], [A])).
            2: epose (wkn_LI (Box (Neg (UI p (XBoxed_list (top_boxes (fst k)), []%list)))) (XBoxed_list x1 ++ [Neg (UI p (XBoxed_list (top_boxes (fst k)), []%list))]) [Box A] _) ; 
            simpl in w ; repeat rewrite <- app_assoc in w ; simpl in w ; apply w.
            apply derI with (ps:=[(XBoxed_list x1 ++ [Box A], [] ++ (UI p (XBoxed_list (top_boxes (fst k)), []%list)) :: [A]);
            (XBoxed_list x1 ++ Bot :: [Box A], [] ++ [A])]). apply ImpL. apply ImpLRule_I. apply dlCons. 2: apply dlCons.
            3: apply dlNil. 2: apply derI with (ps:=[]) ; [apply BotL ; apply BotLRule_I | apply dlNil].
            simpl. assert ((top_boxes (fst k)) = x0). symmetry. apply nobox_gen_ext_top_boxes_identity ; auto.
            intro. intros. apply H1 ; apply in_or_app ; auto. rewrite H0. auto.
        -- destruct x2 ; simpl in e2 ; subst.
            (* If Box A is in Y0 (bis). *)
            +++ rewrite <- app_nil_end in e1 ; subst.
                pose (OrR (X0,Box A :: Δ1)). simpl in g0. apply g0. clear g0.
                apply GLS_prv_wkn_R with (A:=list_disj (restr_list_prop p (snd k))) (s:=(X0,
                Or (list_disj (map Neg (restr_list_prop p (fst k))))(Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq k))))) (Diam
                (list_conj (map (N p k) (Canopy (nodupseq (XBoxed_list (top_boxes (fst k)), []%list)))))))
                :: Box A :: Δ1)).
                2: epose (wkn_RI (list_disj (restr_list_prop p (snd k))) _ [] _) ; simpl in w ; apply w.
                pose (OrR (X0,Box A :: Δ1)). simpl in g0. apply g0. clear g0.
                apply GLS_prv_wkn_R with (A:=list_disj (map Neg (restr_list_prop p (fst k)))) (s:=(X0,
                Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq k))))) (Diam
                (list_conj (map (N p k) (Canopy (nodupseq (XBoxed_list (top_boxes (fst k)), []%list))))))
                :: Box A :: Δ1)).
                2: epose (wkn_RI (list_disj (map Neg (restr_list_prop p (fst k)))) _ [] _) ; simpl in w ; apply w.
                pose (OrR (X0,Box A :: Δ1)). simpl in g0. apply g0. clear g0.
                apply GLS_prv_wkn_R with (A:=list_disj (map Box (map (UI p) (GLR_prems (nodupseq k))))) (s:=(X0,
                (Diam (list_conj (map (N p k) (Canopy (nodupseq (XBoxed_list (top_boxes (fst k)), []%list))))))
                :: Box A :: Δ1)).
                2: epose (wkn_RI (list_disj (map Box (map (UI p) (GLR_prems (nodupseq k))))) _ [] _) ; simpl in w ; apply w.
                apply Diam_rec_UI ; auto.
                assert (J5: derrec_height x < S (dersrec_height d)). lia.
                assert (J6: derrec_height x = derrec_height x). auto.
                assert (J7: (XBoxed_list (x0 ++ x1) ++ [Box A], [A]) = (fst (XBoxed_list x0, @nil MPropF) ++ XBoxed_list x1 ++ [Box A], snd (XBoxed_list x0, []) ++ [A])).
                simpl ; rewrite XBox_app_distrib. repeat rewrite <- app_assoc ; auto.
                assert (J8: (In # p (propvar_subform_list ((XBoxed_list x1 ++ [Box A]) ++ [A])) -> False)).
                intro. apply propvar. repeat rewrite propvar_subform_list_app.
                repeat rewrite propvar_subform_list_app in H0. simpl in H0. repeat rewrite <- app_nil_end in H0. simpl.
                repeat rewrite <- app_assoc in H0. apply in_app_or in H0 ; destruct H0.
                apply in_or_app ; left. apply propvar_subform_list_XBoxed_list in H0.
                apply propvar_subform_list_nobox_gen_ext with (l0:=x1); auto.
                apply in_or_app ; right ; apply in_or_app ; left. apply in_app_or in H0 ; destruct H0 ; auto.
                pose (PIH _ J5 _ _ _ _ _ J6 J7 J8).
                apply derI with (ps:=[(X0 ++ Box (Neg (UI p (XBoxed_list (top_boxes (fst k)), []%list))) :: [], [] ++ Bot :: Box A :: Δ1)]).
                apply ImpR. assert ((X0, Diam (UI p (XBoxed_list (top_boxes (fst k)), []%list)) :: Box A :: Δ1) =
                (X0 ++ [], [] ++ Diam (UI p (XBoxed_list (top_boxes (fst k)), []%list)) :: Box A :: Δ1)). rewrite <- app_nil_end. auto. rewrite H0.
                apply ImpRRule_I. apply dlCons. 2: apply dlNil.
                apply derI with (ps:=[(XBoxed_list (x1 ++ [Box (Neg (UI p (XBoxed_list (top_boxes (fst k)), []%list)))]) ++ [Box A], [A])]).
                apply GLR. assert (([] ++ ⊥ :: Box A :: Δ1) = [⊥] ++ Box A :: Δ1). auto. rewrite H0. apply GLRRule_I ; auto.
                intro. intros. apply in_app_or in H2 ; destruct H2. apply H1 ; apply in_or_app ; auto. exists (Neg (UI p (XBoxed_list (top_boxes (fst k)), []%list))).
                inversion H2 ; subst ; auto. inversion H3. apply univ_gen_ext_combine ; auto. apply univ_gen_ext_cons. apply univ_gen_ext_nil.
                apply dlCons. 2: apply dlNil. rewrite XBox_app_distrib. simpl. repeat rewrite <- app_assoc. simpl.
                apply GLS_prv_wkn_L with (A:=Box (Neg (UI p (XBoxed_list (top_boxes (fst k)), []%list)))) (s:=(XBoxed_list x1 ++
                [Neg (UI p (XBoxed_list (top_boxes (fst k)), []%list)); Box A], [A])).
                2: epose (wkn_LI (Box (Neg (UI p (XBoxed_list (top_boxes (fst k)), []%list)))) (XBoxed_list x1 ++ [Neg (UI p (XBoxed_list (top_boxes (fst k)), []%list))]) [Box A] _) ; 
                simpl in w ; repeat rewrite <- app_assoc in w ; simpl in w ; apply w.
                apply derI with (ps:=[(XBoxed_list x1 ++ [Box A], [] ++ (UI p (XBoxed_list (top_boxes (fst k)), []%list)) :: [A]);
                (XBoxed_list x1 ++ Bot :: [Box A], [] ++ [A])]). apply ImpL. apply ImpLRule_I. apply dlCons. 2: apply dlCons.
                3: apply dlNil. 2: apply derI with (ps:=[]) ; [apply BotL ; apply BotLRule_I | apply dlNil].
                simpl. assert ((top_boxes (fst k)) = x0). symmetry. apply nobox_gen_ext_top_boxes_identity ; auto.
                intro. intros. apply H1 ; apply in_or_app ; auto. rewrite H0. auto.
           (* If Box A is in (snd k). *)
           +++ inversion e2 ; subst.
                assert (J10:derrec_height x = derrec_height x) ; auto.
                assert (J11: list_exch_L (XBoxed_list (x0 ++ x1) ++ [Box A], [A]) ((XBoxed_list x0 ++ [Box A]) ++ XBoxed_list x1, [A])).
                assert (XBoxed_list (x0 ++ x1) ++ [Box A] = XBoxed_list x0 ++ [] ++ XBoxed_list x1 ++ [Box A] ++ []). rewrite XBox_app_distrib.
                repeat rewrite <- app_assoc. auto. rewrite H0.
                assert ((XBoxed_list x0 ++ [Box A]) ++ XBoxed_list x1 = XBoxed_list x0 ++ [Box A] ++ XBoxed_list x1 ++ [] ++ []).
                repeat rewrite <- app_assoc. auto. repeat rewrite <- app_nil_end. auto. rewrite H2. apply list_exch_LI.
                pose (GLS_hpadm_list_exch_L _ J10 J11). destruct s.
                pose (incl_hpadm_prv _ ((XBoxed_list (top_boxes (fst (nodupseq k))) ++ [Box A]) ++ XBoxed_list x1, [A]) x3). simpl in s. destruct s.
                intros B HB. apply in_app_or in HB ; destruct HB. apply in_app_or in H0 ; destruct H0.
                apply in_or_app ; left. apply in_or_app ; left. destruct (In_XBoxed_list_gen _ _ H0).
                apply list_preserv_XBoxed_list. apply is_box_in_top_boxes. apply nodup_In.
                apply (univ_gen_ext_In _ u) ; auto. apply H1. apply in_or_app ; auto. destruct H2. destruct H2 ; subst.
                apply XBoxed_list_In. apply is_box_in_top_boxes. apply nodup_In. apply (univ_gen_ext_In _ u) ; auto.
                apply H1. apply in_or_app ; auto. inversion H0 ; subst. apply in_or_app ; left ; apply in_or_app ; auto. inversion H2.
                apply in_or_app ; auto. intros B HB ; auto.
                assert (J5: derrec_height x4 < S (dersrec_height d)). lia.
                assert (J6: derrec_height x4 = derrec_height x4). auto.
                assert (J7: ((XBoxed_list (top_boxes (nodup eq_dec_form (fst k))) ++ [Box A]) ++ XBoxed_list x1, [A]) = (fst (XBoxed_list (top_boxes (nodup eq_dec_form (fst k))) ++[Box A], [A]) ++ XBoxed_list x1, snd (XBoxed_list x0 ++[Box A], [A]) ++ [])).
                simpl. repeat rewrite <- app_assoc ; auto.
                assert (J8: (In # p (propvar_subform_list ((XBoxed_list x1 ++ [])))) -> False).
                intro. apply propvar. repeat rewrite propvar_subform_list_app.
                repeat rewrite propvar_subform_list_app in H0. simpl in H0. repeat rewrite <- app_nil_end in H0. simpl.
                repeat rewrite <- app_assoc in H0. apply in_or_app ; left. apply propvar_subform_list_XBoxed_list in H0.
                apply propvar_subform_list_nobox_gen_ext with (l0:=x1); auto.
                pose (PIH _ J5 _ _ _ _ _ J6 J7 J8).
                apply GLS_prv_wkn_L with (A:=Box (UI p (XBoxed_list (top_boxes (nodup eq_dec_form (fst k))) ++ [Box A], [A])))
                (sw:=(XBoxed_list x1 ++ [Box (UI p (XBoxed_list (top_boxes (nodup eq_dec_form (fst k))) ++ [Box A], [A]))] , [UI p (XBoxed_list (top_boxes (nodup eq_dec_form (fst k))) ++ [Box A], [A])])) in g0.
                2: epose (wkn_LI (Box (UI p (XBoxed_list (top_boxes (nodup eq_dec_form (fst k))) ++ [Box A], [A]))) _ [] _) ; rewrite app_nil_r in w ; simpl in w ; apply w.
                assert (J20: GLS_rules [(XBoxed_list x1 ++ [Box (UI p (XBoxed_list (top_boxes (nodup eq_dec_form (fst k))) ++ [Box A], [A]))], [UI p (XBoxed_list (top_boxes (nodup eq_dec_form (fst k))) ++ [Box A], [A])])]
                (X0, Box (UI p (XBoxed_list (top_boxes (nodup eq_dec_form (fst k))) ++ [Box A], [A])) :: Y0)). apply GLR.
                assert (Box (UI p (XBoxed_list (top_boxes (nodup eq_dec_form (fst k))) ++ [Box A], [A])) :: Y0 = [] ++ Box (UI p (XBoxed_list (top_boxes (nodup eq_dec_form (fst k))) ++ [Box A], [A])) :: Y0).
                auto. rewrite H0. apply GLRRule_I ;auto. intro. intros. apply H1. apply in_or_app ;auto.
                pose (dlNil GLS_rules (fun _ : Seq => False)).
                pose (dlCons g0 d0). pose (derI _ J20 d1).
                pose (OrR (X0,Y0)). simpl in g1. apply g1. clear g1.
                apply GLS_prv_wkn_R with (A:=list_disj (restr_list_prop p (snd k))) (s:=(X0,
                Or (list_disj (map Neg (restr_list_prop p (fst k))))(Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq k))))) (Diam
                (list_conj (map (N p k) (Canopy (nodupseq (XBoxed_list (top_boxes (fst k)), []%list)))))))
                :: Y0)).
                2: epose (wkn_RI (list_disj (restr_list_prop p (snd k))) _ [] _) ; simpl in w ; apply w.
                pose (OrR (X0,Y0)). simpl in g1. apply g1. clear g1.
                apply GLS_prv_wkn_R with (A:=list_disj (map Neg (restr_list_prop p (fst k)))) (s:=(X0,
                Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq k))))) (Diam
                (list_conj (map (N p k) (Canopy (nodupseq (XBoxed_list (top_boxes (fst k)), []%list))))))
                :: Y0)).
                2: epose (wkn_RI (list_disj (map Neg (restr_list_prop p (fst k)))) _ [] _) ; simpl in w ; apply w.
                pose (OrR (X0,Y0)). simpl in g1. apply g1. clear g1.
                pose (list_disj_wkn_R (map Box (map (UI p) (GLR_prems (nodupseq k)))) (X0, Diam
                 (list_conj (map (N p k) (Canopy (nodupseq (XBoxed_list (top_boxes (fst k)), []%list))))) :: Y0)).
                (* The next UI does not have the correct LHS, which we expect to use x0, to link up with d1. *)
                apply g1 with (A:=Box (UI p (XBoxed_list (top_boxes (fst (nodupseq k))) ++ [Box A], [A]))) ; clear g1 ; simpl ; auto.
                apply InT_map_iff.
                exists (UI p (XBoxed_list (top_boxes (fst (nodupseq k))) ++ [Box A], [A])) ; split ; auto. apply InT_map_iff.
                exists (XBoxed_list (top_boxes (fst (nodupseq k))) ++ [Box A], [A]) ; split ; auto. unfold GLR_prems.
                apply InT_trans_flatten_list with (bs:=[(XBoxed_list (top_boxes (fst (nodupseq k))) ++ [Box A], [A])]) ; auto. apply InT_eq.
                destruct (finite_GLR_premises_of_S (nodupseq k)) ; subst. simpl. apply p0. assert (k = (fst k,Δ0 ++ Box A :: x2)).
                rewrite <- e1. destruct k ; auto. rewrite H0. unfold nodupseq ; simpl.
                assert (InT (Box A) (nodup eq_dec_form (Δ0 ++ Box A :: x2))). apply In_InT ; apply nodup_In ; apply in_or_app ; right ; simpl ; auto.
                apply InT_split in H2 ; destruct H2. destruct s. rewrite e0.
                apply GLRRule_I ; auto. intro. intros. apply in_top_boxes in H2 ; destruct H2. destruct s ; destruct s. destruct p1.
                eexists ; subst ; auto. apply nobox_top_boxes.
                apply GLS_prv_wkn_R with (A:=Diam (list_conj (map (N p k) (Canopy (nodupseq (XBoxed_list (top_boxes (fst k)), []%list))))))
                (s:=(X0, Box (UI p (XBoxed_list (top_boxes (nodup eq_dec_form (fst k))) ++ [Box A], [A])) :: Y0)) ; auto.
                assert ((X0, Box (UI p (XBoxed_list (top_boxes (nodup eq_dec_form (fst k))) ++ [Box A], [A])) :: Y0) = (X0, [Box (UI p (XBoxed_list (top_boxes (nodup eq_dec_form (fst k))) ++ [Box A], [A]))] ++ Y0)).
                repeat rewrite <- app_assoc ; auto. rewrite H0. apply wkn_RI.
         (* If Box A is in Y0 (ter). *)
         -- pose (OrR (X0,x2 ++ Box A :: Δ1)). simpl in g0. apply g0. clear g0.
            apply GLS_prv_wkn_R with (A:=list_disj (restr_list_prop p (snd k))) (s:=(X0,
            Or (list_disj (map Neg (restr_list_prop p (fst k))))(Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq k))))) (Diam
            (list_conj (map (N p k) (Canopy (nodupseq (XBoxed_list (top_boxes (fst k)), []%list)))))))
            :: x2 ++ Box A :: Δ1)).
            2: epose (wkn_RI (list_disj (restr_list_prop p (snd k))) _ [] _) ; simpl in w ; apply w.
            pose (OrR (X0,x2 ++ Box A :: Δ1)). simpl in g0. apply g0. clear g0.
            apply GLS_prv_wkn_R with (A:=list_disj (map Neg (restr_list_prop p (fst k)))) (s:=(X0,
            Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq k))))) (Diam
            (list_conj (map (N p k) (Canopy (nodupseq (XBoxed_list (top_boxes (fst k)), []%list))))))
            :: x2 ++ Box A :: Δ1)).
            2: epose (wkn_RI (list_disj (map Neg (restr_list_prop p (fst k)))) _ [] _) ; simpl in w ; apply w.
            pose (OrR (X0,x2 ++ Box A :: Δ1)). simpl in g0. apply g0. clear g0.
            apply GLS_prv_wkn_R with (A:=list_disj (map Box (map (UI p) (GLR_prems (nodupseq k))))) (s:=(X0,
            (Diam (list_conj (map (N p k) (Canopy (nodupseq (XBoxed_list (top_boxes (fst k)), []%list))))))
            :: x2 ++ Box A :: Δ1)).
            2: epose (wkn_RI (list_disj (map Box (map (UI p) (GLR_prems (nodupseq k))))) _ [] _) ; simpl in w ; apply w.
            apply Diam_rec_UI ; auto.
            assert (J5: derrec_height x < S (dersrec_height d)). lia.
            assert (J6: derrec_height x = derrec_height x). auto.
            assert (J7: (XBoxed_list (x0 ++ x1) ++ [Box A], [A]) = (fst (XBoxed_list x0, @nil MPropF) ++ XBoxed_list x1 ++ [Box A], snd (XBoxed_list x0, []) ++ [A])).
            simpl ; rewrite XBox_app_distrib. repeat rewrite <- app_assoc ; auto.
            assert (J8: (In # p (propvar_subform_list ((XBoxed_list x1 ++ [Box A]) ++ [A])) -> False)).
            intro. apply propvar. repeat rewrite propvar_subform_list_app.
            repeat rewrite propvar_subform_list_app in H0. simpl in H0. repeat rewrite <- app_nil_end in H0. simpl.
            repeat rewrite <- app_assoc in H0. apply in_app_or in H0 ; destruct H0.
            apply in_or_app ; left. apply propvar_subform_list_XBoxed_list in H0.
            apply propvar_subform_list_nobox_gen_ext with (l0:=x1); auto.
            apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; left. apply in_app_or in H0 ; destruct H0 ; auto.
            pose (PIH _ J5 _ _ _ _ _ J6 J7 J8).
            apply derI with (ps:=[(X0 ++ Box (Neg (UI p (XBoxed_list (top_boxes (fst k)), []%list))) :: [], [] ++ Bot :: x2 ++ Box A :: Δ1)]).
            apply ImpR. assert ((X0, Diam (UI p (XBoxed_list (top_boxes (fst k)), []%list)) :: x2 ++ Box A :: Δ1) =
            (X0 ++ [], [] ++ Diam (UI p (XBoxed_list (top_boxes (fst k)), []%list)) :: x2 ++ Box A :: Δ1)). rewrite <- app_nil_end. auto. rewrite H0.
            apply ImpRRule_I. apply dlCons. 2: apply dlNil.
            apply derI with (ps:=[(XBoxed_list (x1 ++ [Box (Neg (UI p (XBoxed_list (top_boxes (fst k)), []%list)))]) ++ [Box A], [A])]).
            apply GLR. assert (([] ++ ⊥ :: x2 ++ Box A :: Δ1) = (⊥ :: x2) ++ Box A :: Δ1). auto. rewrite H0. apply GLRRule_I ; auto.
            intro. intros. apply in_app_or in H2 ; destruct H2. apply H1 ; apply in_or_app ; auto. exists (Neg (UI p (XBoxed_list (top_boxes (fst k)), []%list))).
            inversion H2 ; subst ; auto. inversion H3. apply univ_gen_ext_combine ; auto. apply univ_gen_ext_cons. apply univ_gen_ext_nil.
            apply dlCons. 2: apply dlNil. rewrite XBox_app_distrib. simpl. repeat rewrite <- app_assoc. simpl.
            apply GLS_prv_wkn_L with (A:=Box (Neg (UI p (XBoxed_list (top_boxes (fst k)), []%list)))) (s:=(XBoxed_list x1 ++
            [Neg (UI p (XBoxed_list (top_boxes (fst k)), []%list)); Box A], [A])).
            2: epose (wkn_LI (Box (Neg (UI p (XBoxed_list (top_boxes (fst k)), []%list)))) (XBoxed_list x1 ++ [Neg (UI p (XBoxed_list (top_boxes (fst k)), []%list))]) [Box A] _) ; 
            simpl in w ; repeat rewrite <- app_assoc in w ; simpl in w ; apply w.
            apply derI with (ps:=[(XBoxed_list x1 ++ [Box A], [] ++ (UI p (XBoxed_list (top_boxes (fst k)), []%list)) :: [A]);
            (XBoxed_list x1 ++ Bot :: [Box A], [] ++ [A])]). apply ImpL. apply ImpLRule_I. apply dlCons. 2: apply dlCons.
            3: apply dlNil. 2: apply derI with (ps:=[]) ; [apply BotL ; apply BotLRule_I | apply dlNil].
            simpl. assert ((top_boxes (fst k)) = x0). symmetry. apply nobox_gen_ext_top_boxes_identity ; auto.
            intro. intros. apply H1 ; apply in_or_app ; auto. rewrite H0. auto.
      (*  If not critical, consider the conjunction that UI p k is. *)
      + assert (J0: GUI p k (UI p k)). apply UI_GUI ; auto.
         assert (J1: Gimap (GUI p) (Canopy (nodupseq k)) (map (UI p) (Canopy (nodupseq k)))). apply Gimap_map. intros.
         apply UI_GUI ; auto.
         pose (@GUI_inv_not_critic p k (UI p k) (map (UI p) (Canopy (nodupseq k))) J0 f J1). rewrite <- e.

         assert (J2: forall s1, InT s1 (Canopy (nodupseq k)) -> GLS_prv (X0, UI p s1 :: Y0)).
         intros. pose (fold_Canopy _ _ H). destruct s ; subst.
         exfalso. apply f. apply Canopy_critical in H ; auto. apply critical_nodupseq in H ; auto.
         destruct s. destruct p0. unfold inv_prems in i.
         apply InT_flatten_list_InT_elem in i. destruct i. destruct p0. simpl in PIH. simpl in SIH.
         pose (derI _ g d).

         assert (existsT2 (d1: GLS_prv (fst (nodupseq k) ++ X0, snd (nodupseq k) ++ Y0)), derrec_height d1 <= derrec_height d0).
         destruct (nodupseq_id k). destruct p0. destruct s. destruct s. destruct p1. destruct p1.
         pose (PermutationTS_prv_hpadm _ d0 (x2 ++ fst x1 ++ X0, x3 ++ snd x1 ++ Y0)). destruct s.
         split ; simpl ; apply Permutation_PermutationT. destruct p1.
         pose (@Permutation_app _ (fst k) X0 (x2 ++ fst x1) X0). rewrite <- app_assoc in p3 ; apply p3 ; auto.
         apply Permutation_PermutationT ; auto. destruct p1.
         pose (@Permutation_app _ (snd k) Y0 (x3 ++ snd x1) Y0). rewrite <- app_assoc in p3 ; apply p3 ; auto.
         apply Permutation_PermutationT ; auto.
         epose (incl_ctr_R_hpadm _ x3 _ x4). destruct s. intros A HA ; apply in_or_app ; left ; auto.
         epose (incl_ctr_L_hpadm x2 _ _ x5). destruct s. intros A HA ; apply in_or_app ; left ; auto.
         pose (PermutationTS_prv_hpadm _ x6 (fst (nodupseq k) ++ X0, snd (nodupseq k) ++ Y0)). destruct s.
         split ; simpl ; apply Permutation_PermutationT. destruct p0. apply Permutation_app ; auto.
         unfold nodupseq in p0. apply Permutation_PermutationT ; auto. destruct p0.
         apply Permutation_app ; auto. unfold nodupseq in p2. apply Permutation_PermutationT ; auto.
         exists x7. lia. destruct X1.
         assert (J2: derrec_height x1 = derrec_height x1). auto.
         assert (J3: (fst (nodupseq k) ++ X0, snd (nodupseq k) ++ Y0) = (fst (nodupseq k) ++ X0, snd (nodupseq k) ++ Y0)). auto.
         pose (Canopy_hp_inv_ctx (nodupseq k) _ _ x1 X0 Y0 J2 J3 _ H). destruct s.
         destruct (lt_decT (derrec_height x2) (S (dersrec_height d))).
         (* Use PIH. *)
         pose (fold_Canopy _ _ H). destruct s ; subst.
         exfalso. apply f. apply Canopy_critical in H ; auto. apply critical_nodupseq in H ; auto.
         destruct s. destruct p0. unfold inv_prems in i2.
         apply InT_flatten_list_InT_elem in i2. destruct i2. destruct p0.
         assert (J4: derrec_height x2 = derrec_height x2). auto.
         assert (J5: (fst s1 ++ X0, snd s1 ++ Y0) = (fst s1 ++ X0, snd s1 ++ Y0)). auto.
         pose (PIH _ l1 s1 _ x2 X0 Y0 J4 J5). apply g0 ; auto.
         (* Use SIH. *)
         assert (derrec_height x2 = S (dersrec_height d)). assert (derrec_height d0 = S (dersrec_height d)). simpl. auto. lia.
         assert (J4: LexSeq s1 k). pose (Canopy_LexSeq _ _ H).
         destruct s ; subst ; auto. exfalso. apply f. apply Canopy_critical in H ; apply critical_nodupseq in H ; auto.
         apply LexSeq_nodupseq in l1 ; auto. symmetry in H0.
         assert (J5: (fst s1 ++ X0, snd s1 ++ Y0) = (fst s1 ++ X0, snd s1 ++ Y0)). auto.
         pose (SIH _ J4 _ _ _ _ H0 J5 propvar). auto.

         assert (J3: (forall A : MPropF, InT A (map (UI p) (Canopy (nodupseq k))) -> GLS_prv (fst (X0, Y0), A :: snd (X0, Y0)))).
         intros. simpl. apply InT_map_iff in H. destruct H. destruct p0 ; subst. apply J2 in i ; auto.
         pose (list_conj_R _ _ J3). simpl in g0. auto. }
  Qed.

  End UIPThree.