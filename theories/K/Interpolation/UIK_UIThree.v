Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import general_export.

Require Import KS_export.

Require Import UIK_Def_measure.
Require Import UIK_Canopy.
Require Import UIK_irred_short.
Require Import UIK_braga.
Require Import UIK_UI_prelims.

  Section UIPThree.

  Theorem UI_Three : forall s (p : nat) X0 Y0,
                                    (In (Var p) (propvar_subform_list (X0 ++ Y0)) -> False) ->
                                    KS_prv (fst s ++ X0, snd s ++ Y0) ->
                                    KS_prv (X0, (UI p s) :: Y0).
  Proof.
  (* Setting up the strong induction on the height of the derivation (PIH) and
      on the measure of the sequent using LexSeq (SIH). *)
  intros s p X0 Y0 NotVar D. generalize dependent NotVar. remember (fst s ++ X0, snd s ++ Y0) as scomp.
  generalize dependent Heqscomp. remember (derrec_height D) as n. generalize dependent Heqn.
  generalize dependent Y0. generalize dependent X0. generalize dependent D.
  generalize dependent scomp. generalize dependent s. generalize dependent n.
  pose (d:=strong_inductionT (fun (x:nat) => forall (s : list MPropF * list MPropF) (scomp : list MPropF * list MPropF) (D : KS_prv scomp) (X0 Y0 : list MPropF),
                x = derrec_height D ->
                scomp = (fst s ++ X0, snd s ++ Y0) -> (In # p (propvar_subform_list (X0 ++ Y0)) -> False) -> KS_prv (X0, UI p s :: Y0))).
  apply d. clear d. intros n PIH.
  intro s. remember (measure s) as m. revert Heqm. revert s. revert m.
  pose (strong_inductionT (fun (x:nat) =>
  forall  (s : list MPropF * list MPropF),
  x = measure s ->
  forall (scomp : list MPropF * list MPropF) (D : KS_prv scomp) (X0 Y0 : list MPropF),
  n = derrec_height D ->
  scomp = (fst s ++ X0, snd s ++ Y0) -> (In # p (propvar_subform_list (X0 ++ Y0)) -> False) -> KS_prv (X0, UI p s :: Y0))).
  apply k. intros m SIH. clear k. intros k Heqm.

  (* Now we do the actual proof-theoretical work. *)
  intros s0 D0. remember D0 as D0'. destruct D0.
  (* D0 is a leaf *)
  - inversion f.
  (* D0 ends with an application of rule *)
  - intros X0 Y0 hei idseq propvar. destruct (empty_seq_dec k) as [ EE | NE].
    { subst ; simpl in *.
       assert (J1: KS_prv (X0, Y0)). apply derI with ps ; auto.
       pose (KS_hpadm_wkn_R _ J1 (X0, UI p ([], []) :: Y0) (UI p ([],[]))). destruct s ; auto.
       apply (wkn_RI _ _ []). }
    { inversion k0 ; subst.
    (* IdP *)
    * inversion H ; subst.
      assert (InT (# P) (fst k ++ X0)). rewrite <- H2. apply InT_or_app ; right ; apply InT_eq.
      apply InT_app_or in H0.
      assert (InT (# P) (snd k ++ Y0)). rewrite <- H3. apply InT_or_app ; right ; apply InT_eq.
      apply InT_app_or in H1. destruct H0 ; destruct H1.
      + assert ((X0, UI p k :: Y0) = (X0, [] ++ UI p k :: Y0)). auto. rewrite H0. apply is_init_UI.
         left. destruct k. simpl in i ; simpl in i0. apply InT_split in i. destruct i. destruct s ; subst.
         apply InT_split in i0. destruct i0. destruct s ; subst. apply IdPRule_I.
      + destruct (critical_Seq_dec k).
         -- destruct (dec_KS_init_rules k).
            ** assert (is_init k) ; auto. assert (J0: GUI p k (UI p k)). apply UI_GUI ; auto.
                pose (@GUI_inv_critic_init p k _ J0 c X). rewrite <- e.
                assert ((X0, Top :: Y0) = (X0, [] ++ Top :: Y0)). auto. rewrite H0. apply TopR.
            ** assert ((is_init k) -> False) ; auto. assert (J0: GUI p k (UI p k)). apply UI_GUI ; auto.
                assert (J1: Gimap (GUI p) (KR_prems k) (map (UI p) (KR_prems k))). apply Gimap_map. intros.
                apply UI_GUI ; auto.
                assert (k <> ([],[])). intro. rewrite H1 in i. inversion i.
                assert (J2: GUI p (unboxed_list (top_boxes (fst k)), []) (UI p (unboxed_list (top_boxes (fst k)), []))). apply UI_GUI ; auto.
                pose (@GUI_inv_critic_not_init p k _ _ _ J0 c H1 H0 J1 J2). rewrite <- e.
                pose (OrR (X0,Y0)). simpl in k1. apply k1.
                apply (@KS_adm_list_exch_R (X0,
                Or (list_disj (map Neg (restr_list_prop p (fst k))))
                   (Or (list_disj (map Box (map (UI p) (KR_prems k))))
                      (Diam (UI p (unboxed_list (top_boxes (fst k)), []%list))))
                 :: list_disj (restr_list_prop p (snd k)) :: Y0)).
                2: epose (list_exch_RI _ [] [Or (list_disj (map Neg (restr_list_prop p (fst k)))) (Or (list_disj (map Box (map (UI p) (KR_prems k))))
                (Diam (UI p (unboxed_list (top_boxes (fst k)), []%list))))] [] [list_disj (restr_list_prop p (snd k))] Y0) ; simpl in l ; apply l.
                pose (OrR (X0,list_disj (restr_list_prop p (snd k)) :: Y0)). simpl in k2. apply k2.
                assert (J3: InT (Neg # P) (map Neg (restr_list_prop p (fst k)))). unfold restr_list_prop. apply InT_map_iff.
                exists (# P) ; split ; auto. apply In_InT. apply in_not_touched_remove. apply In_list_In_list_prop_LF ; apply InT_In ; auto.
                intro. apply propvar. rewrite <- H4. rewrite propvar_subform_list_app. apply in_or_app ; right.
                apply In_list_In_propvar_subform_list ; apply InT_In ; auto.
                remember (Or (list_disj (map Box (map (UI p) (KR_prems k)))) (Diam (UI p (unboxed_list (top_boxes (fst k)), []%list)))
                 :: list_disj (restr_list_prop p (snd k)) :: Y0) as Y.
                pose (list_disj_wkn_R (map Neg (restr_list_prop p (fst k))) (X0, Y) (Neg # P) J3). apply k3. simpl.
                unfold Neg. apply derI with (ps:=[([] ++ # P :: X0, [] ++ Bot :: Y)]). apply ImpR. assert ((X0, # P --> Bot :: Y) = ([] ++ X0, [] ++ # P --> Bot :: Y)).
                auto. rewrite H4. apply ImpRRule_I. apply dlCons. 2: apply dlNil.
                assert (InT (# P) ([] ++ Bot :: Y)). simpl. apply InT_cons. rewrite HeqY. repeat apply InT_cons ; auto.
                apply InT_split in H4. destruct H4. destruct s. rewrite e0. apply derI with (ps:=[]). apply IdP. apply IdPRule_I.
                apply dlNil.
         -- assert (J0: GUI p k (UI p k)). apply UI_GUI ; auto.
            assert (J1: Gimap (GUI p) (Canopy k) (map (UI p) (Canopy k))). apply Gimap_map. intros.
            apply UI_GUI ; auto.
            pose (@GUI_inv_not_critic p k _ _ J0 f J1). rewrite <- e.
            pose (list_conj_R (map (UI p) (Canopy k)) (X0,Y0)). simpl in k1. apply k1. intros.
            apply InT_map_iff in H0. destruct H0. destruct p0. subst.
            assert (measure x < measure k). pose (Canopy_measure _ _ i1). destruct s ; subst ; auto. exfalso.
            apply f ; apply Canopy_critical in i1 ; auto. simpl in SIH.
            assert (J2: KS_rules [] (fst x ++ X0, snd x ++ Y0)).
            apply IdP. assert (InT (# P) (snd x ++ Y0)). apply InT_or_app ; auto. apply InT_split in H1.
            destruct H1. destruct s. rewrite e0. assert (InT (# P) (fst x ++ X0)). apply InT_or_app ; left.
            apply Canopy_neg_var with (q:=P) in i1 ; auto. apply InT_split in H1. destruct H1. destruct s. rewrite e1.
            apply IdPRule_I. pose (derI _ J2 d).
            assert (J3: S (dersrec_height d) = derrec_height d0). simpl. lia.
            assert (J4: (fst x ++ X0, snd x ++ Y0) = (fst x ++ X0, snd x ++ Y0)). auto.
            assert (J5 : measure x = measure x). auto.
            pose (SIH _ H0 _ J5 _ _ _ _ J3 J4 propvar). auto.
      + destruct (critical_Seq_dec k).
         -- destruct (dec_KS_init_rules k).
            ** assert (is_init k) ; auto. assert (J0: GUI p k (UI p k)). apply UI_GUI ; auto.
                pose (@GUI_inv_critic_init p k _ J0 c X). rewrite <- e.
                assert ((X0, Top :: Y0) = (X0, [] ++ Top :: Y0)). auto. rewrite H0. apply TopR.
            ** assert ((is_init k) -> False) ; auto. assert (J0: GUI p k (UI p k)). apply UI_GUI ; auto.
                assert (J1: Gimap (GUI p) (KR_prems k) (map (UI p) (KR_prems k))). apply Gimap_map. intros.
                apply UI_GUI ; auto.
                assert (J2: GUI p (unboxed_list (top_boxes (fst k)), []) (UI p (unboxed_list (top_boxes (fst k)), []))). apply UI_GUI ; auto.
                remember (fst k) as LHS. destruct LHS.
                ++  pose (@GUI_inv_critic_not_init p k _ (UI p (unboxed_list (top_boxes []), [])) _ J0 c NE H0 J1). 
                      simpl in e. rewrite <- HeqLHS in *. apply e in J2. rewrite <- J2. simpl in *.
                      assert (GUI p ([],[]) Bot). apply GUI_empty_seq ; auto. apply UI_GUI in H1. rewrite H1 in *.
                      pose (OrR (X0,Y0)). simpl in k1. apply k1.
                      assert (J3: InT (# P)  (restr_list_prop p (snd k))). unfold restr_list_prop. apply In_InT.
                      apply in_not_touched_remove. apply In_list_In_list_prop_LF ; apply InT_In ; auto.
                      intro. apply propvar. rewrite <- H4. rewrite propvar_subform_list_app. apply in_or_app ; left.
                      apply In_list_In_propvar_subform_list ; apply InT_In ; auto.
                      remember (Or ⊥ (Or (list_disj (map Box (map (UI p) (KR_prems k)))) (Diam ⊥)) :: Y0) as Y.
                      pose (list_disj_wkn_R (restr_list_prop p (snd k)) (X0, Y) (# P) J3). apply k2. simpl.
                      apply InT_split in i. destruct i. destruct s. rewrite e0. apply derI with (ps:=[]). apply IdP. 2: apply dlNil.
                      assert ((x ++ # P :: x0, # P :: Y) = (x ++ # P :: x0, [] ++ # P :: Y)). auto. rewrite H4 ; apply IdPRule_I.
                ++  assert (J4 : fst k <> []). intro. rewrite H1 in HeqLHS. inversion HeqLHS. rewrite HeqLHS in J2.
                      pose (@GUI_inv_critic_not_init p k _ _ _ J0 c NE H0 J1 J2). rewrite <- e.
                      pose (OrR (X0,Y0)). simpl in k1. apply k1.
                      assert (J3: InT (# P)  (restr_list_prop p (snd k))). unfold restr_list_prop. apply In_InT.
                      apply in_not_touched_remove. apply In_list_In_list_prop_LF ; apply InT_In ; auto.
                      intro. apply propvar. rewrite <- H1. rewrite propvar_subform_list_app. apply in_or_app ; left.
                      apply In_list_In_propvar_subform_list ; apply InT_In ; auto.
                      remember (Or (list_disj (map Neg (restr_list_prop p (fst k)))) (Or (list_disj (map Box (map (UI p) (KR_prems k)))) (Diam
                      (UI p (unboxed_list (top_boxes (fst k)), []%list)))) :: Y0) as Y.
                      pose (list_disj_wkn_R (restr_list_prop p (snd k)) (X0, Y) (# P) J3). apply k2. simpl.
                      apply InT_split in i. destruct i. destruct s. rewrite e0. apply derI with (ps:=[]). apply IdP. 2: apply dlNil.
                      assert ((x ++ # P :: x0, # P :: Y) = (x ++ # P :: x0, [] ++ # P :: Y)). auto. rewrite H1 ; apply IdPRule_I.
         -- assert (J0: GUI p k (UI p k)). apply UI_GUI ; auto.
            assert (J1: Gimap (GUI p) (Canopy k) (map (UI p) (Canopy k))). apply Gimap_map. intros.
            apply UI_GUI ; auto.
            pose (@GUI_inv_not_critic p k _ _ J0 f J1). rewrite <- e.
            pose (list_conj_R (map (UI p) (Canopy k)) (X0,Y0)). simpl in k1. apply k1. intros.
            apply InT_map_iff in H0. destruct H0. destruct p0. subst.
            assert (measure x < measure k). pose (Canopy_measure _ _ i1). destruct s ; subst ; auto. exfalso.
            apply f ; apply Canopy_critical in i1 ; auto. simpl in SIH.
            assert (J2: KS_rules [] (fst x ++ X0, snd x ++ Y0)).
            apply IdP. assert (InT (# P) (fst x ++ X0)). apply InT_or_app ; auto. apply InT_split in H1.
            destruct H1. destruct s. rewrite e0. assert (InT (# P) (snd x ++ Y0)). apply InT_or_app ; left.
            apply Canopy_pos_var with (q:=P) in i1 ; auto. apply InT_split in H1. destruct H1. destruct s. rewrite e1.
            apply IdPRule_I. pose (derI _ J2 d).
            assert (J3: S (dersrec_height d) = derrec_height d0). simpl. lia.
            assert (J4: (fst x ++ X0, snd x ++ Y0) = (fst x ++ X0, snd x ++ Y0)). auto.
            assert (J5: measure x = measure x). auto.
            pose (SIH _ H0 _ J5 _ _ _ _ J3 J4 propvar). auto.
      + apply derI with (ps:=[]). 2: apply dlNil. apply IdP. apply InT_split in i. destruct i. destruct s ; subst.
         apply InT_split in i0. destruct i0. destruct s ; subst. assert (UI p k :: x1 ++ # P :: x2 = (UI p k :: x1) ++ # P :: x2).
         auto. rewrite H0. apply IdPRule_I.

    (* BotL *)
    * inversion H ; subst.
      assert (InT Bot (fst k ++ X0)). rewrite <- H2. apply InT_or_app ; right ; apply InT_eq.
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
         pose (KS_hpadm_list_exch_L _ x _ J2). destruct s.
         assert (J3: derrec_height x0 = derrec_height x0). auto.
         assert (J4: list_exch_L (A :: fst k ++ X0, Δ0 ++ B :: Δ1) (fst k ++ A :: X0, Δ0 ++ B :: Δ1)).
         assert ((fst k ++ A :: X0, Δ0 ++ B :: Δ1) = ([] ++ [] ++ fst k ++ [A] ++ X0, Δ0 ++ B :: Δ1)). auto.
         rewrite H0.
         assert ((A :: fst k ++ X0, Δ0 ++ B :: Δ1) = ([] ++ [A] ++ fst k ++ [] ++ X0, Δ0 ++ B :: Δ1)).
         auto. rewrite H1. apply list_exch_LI.
         pose (KS_hpadm_list_exch_L _ x0 _ J4). destruct s. simpl in PIH.
         apply app2_find_hole in H3. destruct H3.
         repeat destruct s ; destruct p0 ; subst.
         assert (J5: derrec_height x1 < S (dersrec_height d)). rewrite <- e. apply Arith_prebase.le_lt_n_Sm.
         apply (Nat.le_trans _ _ _ l0 l).
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
         assert (J5: derrec_height x1 < S (dersrec_height d)). rewrite <- e. apply Arith_prebase.le_lt_n_Sm.
         apply (Nat.le_trans _ _ _ l0 l).
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
         assert (J5: derrec_height x1 < S (dersrec_height d)). rewrite <- e. apply Arith_prebase.le_lt_n_Sm.
         apply (Nat.le_trans _ _ _ l0 l).
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
         assert (J1: Gimap (GUI p) (Canopy k) (map (UI p) (Canopy k))). apply Gimap_map. intros.
         apply UI_GUI ; auto.
         pose (@GUI_inv_not_critic p k (UI p k) (map (UI p) (Canopy k)) J0 f J1). rewrite <- e.

         assert (J2: forall s1, InT s1 (Canopy k) -> KS_prv (X0, UI p s1 :: Y0)).
         intros. pose (fold_Canopy _ _ H0). destruct s ; subst.
         exfalso. apply f. apply Canopy_critical in H0 ; auto. destruct s. destruct p0. unfold inv_prems in i.
         apply InT_flatten_list_InT_elem in i. destruct i. destruct p0. simpl in PIH. simpl in SIH.
         pose (derI _ k0 d). assert (J2: derrec_height d0 = derrec_height d0). auto.
         assert (J3: (fst k ++ X0, snd k ++ Y0) = (fst k ++ X0, snd k ++ Y0)). auto.
         pose (Canopy_hp_inv_ctx k _ _ d0 X0 Y0 J2 J3 _ H0). destruct s.
         assert (derrec_height d0 = S (dersrec_height d)). auto. rewrite H1 in l.
         destruct (lt_decT (derrec_height x1) (S (dersrec_height d))).
         (* Use PIH. *)
         pose (fold_Canopy _ _ H0). destruct s ; subst.
         exfalso. apply f. apply Canopy_critical in H0 ; auto. destruct s. destruct p0. unfold inv_prems in i2.
         apply InT_flatten_list_InT_elem in i2. destruct i2. destruct p0.
         assert (J4: derrec_height x1 = derrec_height x1). auto.
         assert (J5: (fst s1 ++ X0, snd s1 ++ Y0) = (fst s1 ++ X0, snd s1 ++ Y0)). auto.
         pose (PIH _ l0 s1 _ x1 X0 Y0 J4 J5). apply k1 ; auto.
         (* Use SIH. *)
         assert (derrec_height x1 = S (dersrec_height d)). lia.
         assert (J4: measure s1 < measure k). pose (Canopy_measure _ _ H0).
         destruct s ; subst ; auto. exfalso. apply f. apply Canopy_critical in H0 ; auto. symmetry in H2.
         assert (J5: (fst s1 ++ X0, snd s1 ++ Y0) = (fst s1 ++ X0, snd s1 ++ Y0)). auto.
         assert (J6: measure s1 = measure s1). auto.
         pose (SIH _ J4 _ J6 _ _ _ _ H2 J5 propvar). auto.
         assert (J3: (forall A : MPropF, InT A (map (UI p) (Canopy k)) -> KS_prv (fst (X0, Y0), A :: snd (X0, Y0)))).
         intros. simpl. apply InT_map_iff in H0. destruct H0. destruct p0 ; subst. apply J2 in i ; auto.
         pose (list_conj_R _ _ J3). simpl in k1. auto.

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
         pose (KS_hpadm_list_exch_R _ x _ J2). destruct s.
         assert (J3: derrec_height x1 = derrec_height x1). auto.
         assert (J4: list_exch_R (Γ0 ++ Γ1, A :: snd k ++ Y0) (Γ0 ++ Γ1, snd k ++ A :: Y0)).
         assert ((Γ0 ++ Γ1, snd k ++ A :: Y0) = (Γ0 ++ Γ1, [] ++ [] ++ snd k ++ [A] ++ Y0)). auto.
         rewrite H0.
         assert ((Γ0 ++ Γ1, A :: snd k ++ Y0) = (Γ0 ++ Γ1, [] ++ [A] ++ snd k ++ [] ++ Y0)).
         auto. rewrite H1. apply list_exch_RI.
         pose (KS_hpadm_list_exch_R _ x1 _ J4). destruct s.
         apply app2_find_hole in H2. destruct H2.
         repeat destruct s ; destruct p0 ; subst.
         assert (J5: derrec_height x2 < S (dersrec_height d)). rewrite e. apply Arith_prebase.le_lt_n_Sm.
         apply Nat.max_le_iff. left ; apply (Nat.le_trans _ _ _ l0 l).
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
         assert (J5: derrec_height x2 < S (dersrec_height d)). rewrite e. apply Arith_prebase.le_lt_n_Sm.
         apply Nat.max_le_iff. left ; apply (Nat.le_trans _ _ _ l0 l).
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
         assert (J5: derrec_height x2 < S (dersrec_height d)). rewrite e. apply Arith_prebase.le_lt_n_Sm.
         apply Nat.max_le_iff. left ; apply (Nat.le_trans _ _ _ l0 l).
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
         assert (J1: Gimap (GUI p) (Canopy k) (map (UI p) (Canopy k))). apply Gimap_map. intros.
         apply UI_GUI ; auto.
         pose (@GUI_inv_not_critic p k (UI p k) (map (UI p) (Canopy k)) J0 f J1). rewrite <- e.

         assert (J2: forall s1, InT s1 (Canopy k) -> KS_prv (X0, UI p s1 :: Y0)).
         intros. pose (fold_Canopy _ _ H0). destruct s ; subst.
         exfalso. apply f. apply Canopy_critical in H0 ; auto. destruct s. destruct p0. unfold inv_prems in i.
         apply InT_flatten_list_InT_elem in i. destruct i. destruct p0. simpl in PIH. simpl in SIH.
         pose (derI _ k0 d). assert (J2: derrec_height d0 = derrec_height d0). auto.
         assert (J3: (fst k ++ X0, snd k ++ Y0) = (fst k ++ X0, snd k ++ Y0)). auto.
         pose (Canopy_hp_inv_ctx k _ _ d0 X0 Y0 J2 J3 _ H0). destruct s.
         assert (derrec_height d0 = S (dersrec_height d)). auto. rewrite H1 in l.
         destruct (lt_decT (derrec_height x1) (S (dersrec_height d))).
         (* Use PIH. *)
         pose (fold_Canopy _ _ H0). destruct s ; subst.
         exfalso. apply f. apply Canopy_critical in H0 ; auto. destruct s. destruct p0. unfold inv_prems in i2.
         apply InT_flatten_list_InT_elem in i2. destruct i2. destruct p0.
         assert (J4: derrec_height x1 = derrec_height x1). auto.
         assert (J5: (fst s1 ++ X0, snd s1 ++ Y0) = (fst s1 ++ X0, snd s1 ++ Y0)). auto.
         pose (PIH _ l0 s1 _ x1 X0 Y0 J4 J5). apply k1 ; auto.
         (* Use SIH. *)
         assert (derrec_height x1 = S (dersrec_height d)). lia.
         assert (J4: measure s1 < measure k). pose (Canopy_measure _ _ H0).
         destruct s ; subst ; auto. exfalso. apply f. apply Canopy_critical in H0 ; auto. symmetry in H2.
         assert (J5: (fst s1 ++ X0, snd s1 ++ Y0) = (fst s1 ++ X0, snd s1 ++ Y0)). auto.
         assert (J6: measure s1 = measure s1). auto.
         pose (SIH _ J4 _ J6 _ _ _ _ H2 J5 propvar). auto.
         assert (J3: (forall A : MPropF, InT A (map (UI p) (Canopy k)) -> KS_prv (fst (X0, Y0), A :: snd (X0, Y0)))).
         intros. simpl. apply InT_map_iff in H0. destruct H0. destruct p0 ; subst. apply J2 in i ; auto.
         pose (list_conj_R _ _ J3). simpl in k1. auto.


    (* KR *)
    * destruct (critical_Seq_dec k).
      (* If critical. *)
      + inversion X ; subst.
         assert (J0: dersrec_height d = dersrec_height d) ; auto.
         apply dersrec_derrec_height in J0. destruct J0. simpl in PIH. simpl in SIH.
         destruct (dec_KS_init_rules k).
         (* If initial. *)
        ** assert (is_init k) ; auto. assert (J0: GUI p k (UI p k)). apply UI_GUI ; auto.
         pose (@GUI_inv_critic_init p k _ J0 c X2). rewrite <- e0.
         assert ((X0, Top :: Y0) = (X0, [] ++ Top :: Y0)). auto. rewrite H. apply TopR.
         (* If not initial. *)
        ** apply univ_gen_ext_splitR in X1. destruct X1. destruct s. destruct p0. destruct p0.
           apply app2_find_hole in H2. destruct H2.
           assert ((is_init k) -> False) ; auto.
           assert (J0: GUI p k (UI p k)). apply UI_GUI ; auto.
           assert (J1: Gimap (GUI p) (KR_prems k) (map (UI p) (KR_prems k))). apply Gimap_map. intros.
           apply UI_GUI ; auto.
           assert (J2: GUI p (unboxed_list (top_boxes (fst k)), []) (UI p (unboxed_list (top_boxes (fst k)), []))). apply UI_GUI ; auto.

           pose (@GUI_inv_critic_not_init p k _ _ _ J0 c NE H J1 J2).
           rewrite <- e1. clear e1.
           repeat destruct s ; destruct p0 ; subst.
           (* If Box A is in Y0. *)
           -- pose (OrR (X0,Box A :: Δ1)). simpl in k1. apply k1. clear k1.
              apply KS_hpadm_wkn_R with (A:=list_disj (restr_list_prop p (snd k))) (s:=(X0,
              Or (list_disj (map Neg (restr_list_prop p (fst k))))(Or (list_disj (map Box (map (UI p) (KR_prems k)))) (Diam
              (UI p (unboxed_list (top_boxes (fst k)), []%list)))) :: Box A :: Δ1)).
              2: epose (wkn_RI (list_disj (restr_list_prop p (snd k))) _ [] _) ; simpl in w ; apply w.
              pose (OrR (X0,Box A :: Δ1)). simpl in k1. apply k1. clear k1.
              apply KS_hpadm_wkn_R with (A:=list_disj (map Neg (restr_list_prop p (fst k)))) (s:=(X0,
              Or (list_disj (map Box (map (UI p) (KR_prems k)))) (Diam (UI p (unboxed_list (top_boxes (fst k)), []%list)))
              :: Box A :: Δ1)).
              2: epose (wkn_RI (list_disj (map Neg (restr_list_prop p (fst k)))) _ [] _) ; simpl in w ; apply w.
              pose (OrR (X0,Box A :: Δ1)). simpl in k1. apply k1. clear k1.
              apply KS_hpadm_wkn_R with (A:=list_disj (map Box (map (UI p) (KR_prems k)))) (s:=(X0,
              (Diam (UI p (unboxed_list (top_boxes (fst k)), []%list))) :: Box A :: Δ1)).
              2: epose (wkn_RI (list_disj (map Box (map (UI p) (KR_prems k)))) _ [] _) ; simpl in w ; apply w.
              assert (J5: derrec_height x < S (dersrec_height d)). lia.
              assert (J6: derrec_height x = derrec_height x). auto.
              assert (J7: (unboxed_list (x0 ++ x1), [A]) = (fst (unboxed_list x0, @nil MPropF) ++ unboxed_list x1, snd (unboxed_list x0, []) ++ [A])).
              simpl ; rewrite unbox_app_distrib. repeat rewrite <- app_assoc ; auto.
              assert (J8: (In # p (propvar_subform_list ((unboxed_list x1) ++ [A])) -> False)).
              intro. apply propvar. repeat rewrite propvar_subform_list_app.
              repeat rewrite propvar_subform_list_app in H0. simpl in H0. repeat rewrite <- app_nil_end in H0. simpl.
              repeat rewrite <- app_assoc in H0. apply in_app_or in H0 ; destruct H0.
              apply in_or_app ; left. apply propvar_subform_list_unboxed_list in H0.
              apply propvar_subform_list_nobox_gen_ext with (l0:=x1); auto.
              apply in_or_app ; right ; apply in_or_app ; left. auto.
              pose (PIH _ J5 _ _ _ _ _ J6 J7 J8).
              apply derI with (ps:=[(X0 ++ Box (Neg (UI p (unboxed_list (top_boxes (fst k)), []%list))) :: [], [] ++ Bot :: Box A :: Δ1)]).
              apply ImpR. assert ((X0, Diam (UI p (unboxed_list (top_boxes (fst k)), []%list)) :: Box A :: Δ1) =
              (X0 ++ [], [] ++ Diam (UI p (unboxed_list (top_boxes (fst k)), []%list)) :: Box A :: Δ1)). rewrite <- app_nil_end. auto. rewrite H0.
              apply ImpRRule_I. apply dlCons. 2: apply dlNil.
              apply derI with (ps:=[(unboxed_list (x1 ++ [Box (Neg (UI p (unboxed_list (top_boxes (fst k)), []%list)))]) , [A])]).
              apply KR. assert (([] ++ Bot :: Box A :: Δ1) = [Bot] ++ Box A :: Δ1). auto. rewrite H0. apply KRRule_I ; auto.
              intro. intros. apply in_app_or in H2 ; destruct H2. apply H1 ; apply in_or_app ; auto. exists (Neg (UI p (unboxed_list (top_boxes (fst k)), []%list))).
              inversion H2 ; subst ; auto. inversion H3. apply univ_gen_ext_combine ; auto. apply univ_gen_ext_cons. apply univ_gen_ext_nil.
              apply dlCons. 2: apply dlNil. rewrite unbox_app_distrib. simpl. repeat rewrite <- app_assoc. simpl.
              apply derI with (ps:=[(unboxed_list x1, [] ++ (UI p (unboxed_list (top_boxes (fst k)), []%list)) :: [A]);
              (unboxed_list x1 ++ Bot :: [], [] ++ [A])]). apply ImpL.
              pose (ImpLRule_I (UI p (unboxed_list (top_boxes (fst k)), []%list)) Bot (unboxed_list x1) [] [] [A]). simpl ; simpl in i.
              rewrite <- app_nil_end in i. auto. apply dlCons. 2: apply dlCons.
              3: apply dlNil. 2: apply derI with (ps:=[]) ; [apply BotL ; apply BotLRule_I | apply dlNil].
              simpl. assert ((top_boxes (fst k)) = x0). symmetry. apply nobox_gen_ext_top_boxes_identity ; auto.
              intro. intros. apply H1 ; apply in_or_app ; auto. rewrite H0. auto.
          -- destruct x2 ; simpl in e2 ; subst.
              (* If Box A is in Y0 (bis). *)
              +++ rewrite <- app_nil_end in e1 ; subst.
                  pose (OrR (X0,Box A :: Δ1)). simpl in k1. apply k1. clear k1.
                  apply KS_hpadm_wkn_R with (A:=list_disj (restr_list_prop p (snd k))) (s:=(X0,
                  Or (list_disj (map Neg (restr_list_prop p (fst k))))(Or (list_disj (map Box (map (UI p) (KR_prems k)))) (Diam (UI p (unboxed_list (top_boxes (fst k)), []%list))))
                  :: Box A :: Δ1)).
                  2: epose (wkn_RI (list_disj (restr_list_prop p (snd k))) _ [] _) ; simpl in w ; apply w.
                  pose (OrR (X0,Box A :: Δ1)). simpl in k1. apply k1. clear k1.
                  apply KS_hpadm_wkn_R with (A:=list_disj (map Neg (restr_list_prop p (fst k)))) (s:=(X0,
                  Or (list_disj (map Box (map (UI p) (KR_prems k)))) (Diam (UI p (unboxed_list (top_boxes (fst k)), []%list)))
                  :: Box A :: Δ1)).
                  2: epose (wkn_RI (list_disj (map Neg (restr_list_prop p (fst k)))) _ [] _) ; simpl in w ; apply w.
                  pose (OrR (X0,Box A :: Δ1)). simpl in k1. apply k1. clear k1.
                  apply KS_hpadm_wkn_R with (A:=list_disj (map Box (map (UI p) (KR_prems k)))) (s:=(X0,
                  (Diam (UI p (unboxed_list (top_boxes (fst k)), []%list)))
                  :: Box A :: Δ1)).
                  2: epose (wkn_RI (list_disj (map Box (map (UI p) (KR_prems k)))) _ [] _) ; simpl in w ; apply w.
                  assert (J5: derrec_height x < S (dersrec_height d)). lia.
                  assert (J6: derrec_height x = derrec_height x). auto.
                  assert (J7: (unboxed_list (x0 ++ x1), [A]) = (fst (unboxed_list x0, @nil MPropF) ++ unboxed_list x1, snd (unboxed_list x0, []) ++ [A])).
                  simpl ; rewrite unbox_app_distrib. repeat rewrite <- app_assoc ; auto.
                  assert (J8: (In # p (propvar_subform_list (unboxed_list x1 ++ [A])) -> False)).
                  intro. apply propvar. repeat rewrite propvar_subform_list_app.
                  repeat rewrite propvar_subform_list_app in H0. simpl in H0. repeat rewrite <- app_nil_end in H0. simpl.
                  repeat rewrite <- app_assoc in H0. apply in_app_or in H0 ; destruct H0.
                  apply in_or_app ; left. apply propvar_subform_list_unboxed_list in H0.
                  apply propvar_subform_list_nobox_gen_ext with (l0:=x1); auto.
                  apply in_or_app ; right ; apply in_or_app ; left. auto.
                  pose (PIH _ J5 _ _ _ _ _ J6 J7 J8).
                  apply derI with (ps:=[(X0 ++ Box (Neg (UI p (unboxed_list (top_boxes (fst k)), []%list))) :: [], [] ++ Bot :: Box A :: Δ1)]).
                  apply ImpR. assert ((X0, Diam (UI p (unboxed_list (top_boxes (fst k)), []%list)) :: Box A :: Δ1) =
                  (X0 ++ [], [] ++ Diam (UI p (unboxed_list (top_boxes (fst k)), []%list)) :: Box A :: Δ1)). rewrite <- app_nil_end. auto. rewrite H0.
                  apply ImpRRule_I. apply dlCons. 2: apply dlNil.
                  apply derI with (ps:=[(unboxed_list (x1 ++ [Box (Neg (UI p (unboxed_list (top_boxes (fst k)), []%list)))]), [A])]).
                  apply KR. assert (([] ++ Bot :: Box A :: Δ1) = [Bot] ++ Box A :: Δ1). auto. rewrite H0. apply KRRule_I ; auto.
                  intro. intros. apply in_app_or in H2 ; destruct H2. apply H1 ; apply in_or_app ; auto. exists (Neg (UI p (unboxed_list (top_boxes (fst k)), []%list))).
                  inversion H2 ; subst ; auto. inversion H3. apply univ_gen_ext_combine ; auto. apply univ_gen_ext_cons. apply univ_gen_ext_nil.
                  apply dlCons. 2: apply dlNil. rewrite unbox_app_distrib. simpl. repeat rewrite <- app_assoc. simpl.
                  apply derI with (ps:=[(unboxed_list x1, [] ++ (UI p (unboxed_list (top_boxes (fst k)), []%list)) :: [A]);
                  (unboxed_list x1 ++ Bot :: [], [] ++ [A])]). apply ImpL.
                  pose (ImpLRule_I (UI p (unboxed_list (top_boxes (fst k)), []%list)) Bot (unboxed_list x1) [] [] [A]). simpl ; simpl in i.
                  rewrite <- app_nil_end in i. auto. apply dlCons. 2: apply dlCons.
                  3: apply dlNil. 2: apply derI with (ps:=[]) ; [apply BotL ; apply BotLRule_I | apply dlNil].
                  simpl. assert ((top_boxes (fst k)) = x0). symmetry. apply nobox_gen_ext_top_boxes_identity ; auto.
                  intro. intros. apply H1 ; apply in_or_app ; auto. rewrite H0. auto.
             (* If Box A is in (snd k). *)
             +++ inversion e2 ; subst.
                  assert (J10:derrec_height x = derrec_height x) ; auto.
                  assert (J5: derrec_height x < S (dersrec_height d)). lia.
                  assert (J6: derrec_height x = derrec_height x). auto.
                  assert (J7: (unboxed_list (x0 ++ x1), [A]) = (fst (unboxed_list x0, [A]) ++ unboxed_list x1, snd (unboxed_list x0, [A]) ++ [])).
                  simpl. rewrite unbox_app_distrib. repeat rewrite <- app_assoc ; auto.
                  assert (J8: (In # p (propvar_subform_list ((unboxed_list x1 ++ [])))) -> False).
                  intro. apply propvar. repeat rewrite propvar_subform_list_app.
                  repeat rewrite propvar_subform_list_app in H0. simpl in H0. repeat rewrite <- app_nil_end in H0. simpl.
                  repeat rewrite <- app_assoc in H0. apply in_or_app ; left. apply propvar_subform_list_unboxed_list in H0.
                  apply propvar_subform_list_nobox_gen_ext with (l0:=x1); auto.
                  pose (PIH _ J5 _ _ _ _ _ J6 J7 J8).
                  assert (J20: KS_rules [(unboxed_list x1, [UI p (unboxed_list x0, [A])])]
                  (X0, Box (UI p (unboxed_list x0, [A])) :: Y0)). apply KR.
                  assert (Box (UI p (unboxed_list x0, [A])) :: Y0 = [] ++ Box (UI p (unboxed_list x0, [A])) :: Y0).
                  auto. rewrite H0. apply KRRule_I ;auto. intro. intros. apply H1. apply in_or_app ;auto.
                  pose (dlNil KS_rules (fun _ : Seq => False)).
                  pose (dlCons k1 d0). pose (derI _ J20 d1).
                  pose (OrR (X0,Y0)). simpl in k2. apply k2. clear k2.
                  apply KS_hpadm_wkn_R with (A:=list_disj (restr_list_prop p (snd k))) (s:=(X0,
                  Or (list_disj (map Neg (restr_list_prop p (fst k))))(Or (list_disj (map Box (map (UI p) (KR_prems k)))) (Diam (UI p (unboxed_list (top_boxes (fst k)), []%list))))
                  :: Y0)).
                  2: epose (wkn_RI (list_disj (restr_list_prop p (snd k))) _ [] _) ; simpl in w ; apply w.
                  pose (OrR (X0,Y0)). simpl in k2. apply k2. clear k2.
                  apply KS_hpadm_wkn_R with (A:=list_disj (map Neg (restr_list_prop p (fst k)))) (s:=(X0,
                  Or (list_disj (map Box (map (UI p) (KR_prems k)))) (Diam (UI p (unboxed_list (top_boxes (fst k)), []%list)))
                  :: Y0)).
                  2: epose (wkn_RI (list_disj (map Neg (restr_list_prop p (fst k)))) _ [] _) ; simpl in w ; apply w.
                  pose (OrR (X0,Y0)). simpl in k2. apply k2. clear k2.
                  pose (list_disj_wkn_R (map Box (map (UI p) (KR_prems k))) (X0, Diam (UI p (unboxed_list (top_boxes (fst k)), []%list)) :: Y0)).
                  apply k2 with (A:=Box (UI p (unboxed_list x0, [A]))) ; clear k2 ; simpl ; auto.
                  apply InT_map_iff. exists (UI p (unboxed_list x0, [A])) ; split ; auto. apply InT_map_iff.
                  exists (unboxed_list x0, [A]) ; split ; auto. unfold KR_prems.
                  apply InT_trans_flatten_list with (bs:=[(unboxed_list x0, [A])]) ; auto. apply InT_eq.
                  destruct (finite_KR_premises_of_S k) ; subst. simpl. apply p0. assert (k = (fst k,Δ0 ++ Box A :: x2)).
                  rewrite <- e1. destruct k ; auto. rewrite H0. apply KRRule_I ; auto. intro. intros. apply H1 ; apply in_or_app ; auto.
                  apply KS_hpadm_wkn_R with (A:=Diam (UI p (unboxed_list (top_boxes (fst k)), []%list)))
                  (s:=(X0, Box (UI p (unboxed_list x0, [A])) :: Y0)) ; auto.
                  assert ((X0, Box (UI p (unboxed_list x0, [A])) :: Y0) = (X0, [Box (UI p (unboxed_list x0, [A]))] ++ Y0)).
                  repeat rewrite <- app_assoc ; auto. rewrite H0. apply wkn_RI.
           (* If Box A is in Y0 (ter). *)
           -- pose (OrR (X0,x2 ++ Box A :: Δ1)). simpl in k1. apply k1. clear k1.
              apply KS_hpadm_wkn_R with (A:=list_disj (restr_list_prop p (snd k))) (s:=(X0,
              Or (list_disj (map Neg (restr_list_prop p (fst k))))(Or (list_disj (map Box (map (UI p) (KR_prems k)))) (Diam
              (UI p (unboxed_list (top_boxes (fst k)), []%list)))) :: x2 ++ Box A :: Δ1)).
              2: epose (wkn_RI (list_disj (restr_list_prop p (snd k))) _ [] _) ; simpl in w ; apply w.
              pose (OrR (X0,x2 ++ Box A :: Δ1)). simpl in k1. apply k1. clear k1.
              apply KS_hpadm_wkn_R with (A:=list_disj (map Neg (restr_list_prop p (fst k)))) (s:=(X0,
              Or (list_disj (map Box (map (UI p) (KR_prems k)))) (Diam
              (UI p (unboxed_list (top_boxes (fst k)), []%list)))
              :: x2 ++ Box A :: Δ1)).
              2: epose (wkn_RI (list_disj (map Neg (restr_list_prop p (fst k)))) _ [] _) ; simpl in w ; apply w.
              pose (OrR (X0,x2 ++ Box A :: Δ1)). simpl in k1. apply k1. clear k1.
              apply KS_hpadm_wkn_R with (A:=list_disj (map Box (map (UI p) (KR_prems k)))) (s:=(X0,
              (Diam (UI p (unboxed_list (top_boxes (fst k)), []%list)))
              :: x2 ++ Box A :: Δ1)).
              2: epose (wkn_RI (list_disj (map Box (map (UI p) (KR_prems k)))) _ [] _) ; simpl in w ; apply w.
              assert (J5: derrec_height x < S (dersrec_height d)). lia.
              assert (J6: derrec_height x = derrec_height x). auto.
              assert (J7: (unboxed_list (x0 ++ x1), [A]) = (fst (unboxed_list x0, @nil MPropF) ++ unboxed_list x1, snd (unboxed_list x0, []) ++ [A])).
              simpl ; rewrite unbox_app_distrib. repeat rewrite <- app_assoc ; auto.
              assert (J8: (In # p (propvar_subform_list ((unboxed_list x1) ++ [A])) -> False)).
              intro. apply propvar. repeat rewrite propvar_subform_list_app.
              repeat rewrite propvar_subform_list_app in H0. simpl in H0. repeat rewrite <- app_nil_end in H0. simpl.
              repeat rewrite <- app_assoc in H0. apply in_app_or in H0 ; destruct H0.
              apply in_or_app ; left. apply propvar_subform_list_unboxed_list in H0.
              apply propvar_subform_list_nobox_gen_ext with (l0:=x1); auto.
              apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; left. auto.
              pose (PIH _ J5 _ _ _ _ _ J6 J7 J8).
              apply derI with (ps:=[(X0 ++ Box (Neg (UI p (unboxed_list (top_boxes (fst k)), []%list))) :: [], [] ++ Bot :: x2 ++ Box A :: Δ1)]).
              apply ImpR. assert ((X0, Diam (UI p (unboxed_list (top_boxes (fst k)), []%list)) :: x2 ++ Box A :: Δ1) =
              (X0 ++ [], [] ++ Diam (UI p (unboxed_list (top_boxes (fst k)), []%list)) :: x2 ++ Box A :: Δ1)). rewrite <- app_nil_end. auto. rewrite H0.
              apply ImpRRule_I. apply dlCons. 2: apply dlNil.
              apply derI with (ps:=[(unboxed_list (x1 ++ [Box (Neg (UI p (unboxed_list (top_boxes (fst k)), []%list)))]), [A])]).
              apply KR. assert (([] ++ Bot :: x2 ++ Box A :: Δ1) = (Bot :: x2) ++ Box A :: Δ1). auto. rewrite H0. apply KRRule_I ; auto.
              intro. intros. apply in_app_or in H2 ; destruct H2. apply H1 ; apply in_or_app ; auto. exists (Neg (UI p (unboxed_list (top_boxes (fst k)), []%list))).
              inversion H2 ; subst ; auto. inversion H3. apply univ_gen_ext_combine ; auto. apply univ_gen_ext_cons. apply univ_gen_ext_nil.
              apply dlCons. 2: apply dlNil. rewrite unbox_app_distrib. simpl. repeat rewrite <- app_assoc. simpl.
              apply derI with (ps:=[(unboxed_list x1, [] ++ (UI p (unboxed_list (top_boxes (fst k)), []%list)) :: [A]);
              (unboxed_list x1 ++ Bot :: [], [] ++ [A])]). apply ImpL.
              pose (ImpLRule_I (UI p (unboxed_list (top_boxes (fst k)), []%list)) Bot (unboxed_list x1) [] [] [A]). simpl ; simpl in i.
              rewrite <- app_nil_end in i. auto. apply dlCons. 2: apply dlCons.
              3: apply dlNil. 2: apply derI with (ps:=[]) ; [apply BotL ; apply BotLRule_I | apply dlNil].
              simpl. assert ((top_boxes (fst k)) = x0). symmetry. apply nobox_gen_ext_top_boxes_identity ; auto.
              intro. intros. apply H1 ; apply in_or_app ; auto. rewrite H0. auto.
      (*  If not critical, consider the conjunction that UI p k is. *)
      + assert (J0: GUI p k (UI p k)). apply UI_GUI ; auto.
         assert (J1: Gimap (GUI p) (Canopy k) (map (UI p) (Canopy k))). apply Gimap_map. intros.
         apply UI_GUI ; auto.
         pose (@GUI_inv_not_critic p k (UI p k) (map (UI p) (Canopy k)) J0 f J1). rewrite <- e.

         assert (J2: forall s1, InT s1 (Canopy k) -> KS_prv (X0, UI p s1 :: Y0)).
         intros. pose (fold_Canopy _ _ H). destruct s ; subst.
         exfalso. apply f. apply Canopy_critical in H ; auto. destruct s. destruct p0. unfold inv_prems in i.
         apply InT_flatten_list_InT_elem in i. destruct i. destruct p0. simpl in PIH. simpl in SIH.
         pose (derI _ k0 d). assert (J2: derrec_height d0 = derrec_height d0). auto.
         assert (J3: (fst k ++ X0, snd k ++ Y0) = (fst k ++ X0, snd k ++ Y0)). auto.
         pose (Canopy_hp_inv_ctx k _ _ d0 X0 Y0 J2 J3 _ H). destruct s.
         assert (derrec_height d0 = S (dersrec_height d)). auto. rewrite H0 in l.
         destruct (lt_decT (derrec_height x1) (S (dersrec_height d))).
         (* Use PIH. *)
         pose (fold_Canopy _ _ H). destruct s ; subst.
         exfalso. apply f. apply Canopy_critical in H ; auto. destruct s. destruct p0. unfold inv_prems in i2.
         apply InT_flatten_list_InT_elem in i2. destruct i2. destruct p0.
         assert (J4: derrec_height x1 = derrec_height x1). auto.
         assert (J5: (fst s1 ++ X0, snd s1 ++ Y0) = (fst s1 ++ X0, snd s1 ++ Y0)). auto.
         pose (PIH _ l0 s1 _ x1 X0 Y0 J4 J5). apply k1 ; auto.
         (* Use SIH. *)
         assert (derrec_height x1 = S (dersrec_height d)). lia.
         assert (J4: measure s1 < measure k). pose (Canopy_measure _ _ H).
         destruct s ; subst ; auto. exfalso. apply f. apply Canopy_critical in H ; auto. symmetry in H1.
         assert (J5: (fst s1 ++ X0, snd s1 ++ Y0) = (fst s1 ++ X0, snd s1 ++ Y0)). auto.
         assert (J6: measure s1 = measure s1). auto.
         pose (SIH _ J4 _ J6 _ _ _ _ H1 J5 propvar). auto.
         assert (J3: (forall A : MPropF, InT A (map (UI p) (Canopy k)) -> KS_prv (fst (X0, Y0), A :: snd (X0, Y0)))).
         intros. simpl. apply InT_map_iff in H. destruct H. destruct p0 ; subst. apply J2 in i ; auto.
         pose (list_conj_R _ _ J3). simpl in k1. auto. }
  Qed.

  End UIPThree.