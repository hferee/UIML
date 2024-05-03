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

  Theorem PermutationTS_UI : forall s sp p, PermutationTS s sp -> GLS_prv ([UI p s], [UI p sp]).
  Proof.
  pose (d:=LexSeq_ind (fun (s:Seq) => forall sp p, PermutationTS s sp -> GLS_prv ([UI p s], [UI p sp]))).
  apply d. clear d. intros s IH sp p perm.
  destruct (empty_seq_dec s) as [EE | DE].
  { subst. assert (J0: GUI p ([],[]) Bot). apply GUI_empty_seq ; auto. apply UI_GUI in J0. 
     rewrite J0 in *. apply derI with []. apply BotL ; apply (BotLRule_I [] []). apply dlNil. }
  { destruct (critical_Seq_dec s).
  (* Sequents are critical. *)
  - pose (PermutationTS_critic _ _ perm c).
    destruct (dec_init_rules s).
    (* Sequents are initial. *)
    * assert (is_init s) ; auto. pose (PermutationTS_is_init _ _ perm X).
      assert (J0: GUI p sp (UI p sp)). apply UI_GUI ; auto.
      pose (@GUI_inv_critic_init p sp _ J0 c0 i). rewrite <- e. epose (TopR _ [] []). simpl in g ; apply g.
    (* Sequents are not initial. *)
    * assert ((is_init s) -> False) ; auto. assert ((is_init sp) -> False). intro. apply H.
      pose (PermutationTS_sym _ _ perm). apply (PermutationTS_is_init _ _ p0) ; auto.
      assert (J0: GUI p s (UI p s)). apply UI_GUI ; auto.
      assert (J00: GUI p sp (UI p sp)). apply UI_GUI ; auto.
      assert (J1: Gimap (GUI p) (GLR_prems (nodupseq s)) (map (UI p) (GLR_prems (nodupseq s)))). apply Gimap_map. intros.
      apply UI_GUI ; auto.
      assert (J10: Gimap (GUI p) (GLR_prems (nodupseq sp)) (map (UI p) (GLR_prems (nodupseq sp)))). apply Gimap_map. intros.
      apply UI_GUI ; auto.
      assert (J2: (Gimap (GN p (GUI p) s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), [])))
      (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), [])))))). apply Gimap_map. intros.
      pose (N_spec p s x) ; auto.
      assert (J20: (Gimap (GN p (GUI p) sp) (Canopy (nodupseq (XBoxed_list (top_boxes (fst sp)), [])))
      (map (N p sp) (Canopy (nodupseq (XBoxed_list (top_boxes (fst sp)), [])))))). apply Gimap_map. intros.
      apply (N_spec p sp x).
      assert (J41: sp <> ([], [])). intro. destruct sp ; destruct s ; inversion H1 ; subst. apply DE. destruct perm. simpl in *.
      destruct (Permutation_PermutationT l1 []). pose (p3 p0). apply Permutation_sym in p4 ; apply Permutation_nil in p4.
      destruct (Permutation_PermutationT l2 []). pose (p6 p1). apply Permutation_sym in p7 ; apply Permutation_nil in p7 ; subst ; auto.
       pose (@GUI_inv_critic_not_init p s _ _ _ J0 c DE H J1 J2). rewrite <- e ; clear e.
       pose (@GUI_inv_critic_not_init p sp _ _ _ J00 c0 J41 H0 J10 J20). rewrite <- e ; clear e.
        epose (OrR (_,[])). simpl in g. apply g ; clear g.
        epose (OrL ([],_)). simpl in g. apply g ; clear g.
        epose (list_disj_L _ (_,_)). apply g ; clear g. simpl ; intros.
        pose (PermutationTS_restr_list_prop_snd _ _ _ _ perm H1).
        epose (list_disj_wkn_R _ ([_],[_]) _ i). simpl in g. apply g ; clear g.
        epose (Id_all_form _ [] _ []). simpl in d ; apply d.
        eapply GLS_prv_wkn_R with (s:=([Or (list_disj (map Neg (restr_list_prop p (fst s)))) (Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq s)))))
       (Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))))))], [Or (list_disj (map Neg (restr_list_prop p (fst sp)))) (Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq sp)))))
        (Diam (list_conj (map (N p sp) (Canopy (nodupseq (XBoxed_list (top_boxes (fst sp)), []%list)))))))])) (A:=list_disj (restr_list_prop p (snd sp))).
        2: epose (wkn_RI (list_disj (restr_list_prop p (snd sp))) _ [] _) ; simpl in w ; apply w.
        epose (OrR (_,[])). simpl in g. apply g ; clear g.
        epose (OrL ([],_)). simpl in g. apply g ; clear g.
        epose (list_disj_L _ (_,_)). apply g ; clear g. simpl ; intros.
        apply InT_map_iff in H1. destruct H1. destruct p0 ; subst.
        pose (@PermutationTS_restr_list_prop_fst _ _ p x perm i).
        epose (list_disj_wkn_R _ ([_],[_]) _). simpl in g. apply g ; clear g. apply InT_map_iff. exists x ; split ; auto.
        epose (Id_all_form _ [] _ []). simpl in d ; apply d.
        eapply GLS_prv_wkn_R with (s:=([Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq s))))) (Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))))],
        [(Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq sp)))))
        (Diam (list_conj (map (N p sp) (Canopy (nodupseq (XBoxed_list (top_boxes (fst sp)), []%list)))))))])) (A:=list_disj (map Neg (restr_list_prop p (fst sp)))).
        2: epose (wkn_RI (list_disj (map Neg (restr_list_prop p (fst sp)))) _ [] _) ; simpl in w ; apply w.
        epose (OrR (_,[])). simpl in g. apply g ; clear g.
        epose (OrL ([],_)). simpl in g. apply g ; clear g.
        epose (list_disj_L _ (_,_)). apply g ; clear g. simpl ; intros. apply InT_map_iff in H1.
        destruct H1. destruct p0 ; subst. apply InT_map_iff in i. destruct i. destruct p0 ; subst.
        destruct (PermutationTS_GLR_prems _ _ (PermutationTS_nodupseq _ _ perm) _ i). destruct p0.
        epose (list_disj_wkn_R _ ([_],_) (Box (UI p x))). simpl in g. apply g ; clear g.
        apply InT_map_iff. exists (UI p x). split ; auto. apply InT_map_iff. exists x ; split ; auto.
        apply derI with (ps:=[([(UI p x0);Box (UI p x0);Box (UI p x)], [UI p x])]). apply GLR.
        epose (@GLRRule_I _ [Box (UI p x0)] _ []). simpl in g. apply g. intros A HA. inversion HA ; subst.
        eexists ; auto. inversion H1. apply univ_gen_ext_refl. apply dlCons. 2: apply dlNil.
        assert (J50: GLS_prv ([UI p x0], [UI p x])).
        apply IH ; auto. apply GLR_prems_LexSeq in i ; auto. apply LexSeq_nodupseq in i ; auto.
        intro. assert (is_init (nodupseq s)) ; auto. unfold is_init ; auto. apply H. apply is_init_nodupseq ; auto.
        epose (GLS_prv_list_wkn_L [UI p x0] [] J50 _). simpl in g ; rewrite app_nil_r in g. apply g.
        eapply GLS_prv_wkn_R with (s:=([Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))))],
        [Diam (list_conj (map (N p sp) (Canopy (nodupseq (XBoxed_list (top_boxes (fst sp)), []%list)))))])) (A:=list_disj (map Box (map (UI p) (GLR_prems (nodupseq sp))))).
        2: epose (wkn_RI (list_disj (map Box (map (UI p) (GLR_prems (nodupseq sp))))) _ [] _) ; simpl in w ; apply w.
        remember (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))) as conjL.
        remember (list_conj (map (N p sp) (Canopy (nodupseq (XBoxed_list (top_boxes (fst sp)), []%list))))) as conjR.
        apply derI with (ps:=[([Box (Neg conjR) ; Diam conjL], [Bot])]). apply ImpR. epose (ImpRRule_I _ _ [] [_] [] []). simpl in i ; apply i.
        apply dlCons. 2: apply dlNil.
        apply derI with (ps:=[([Box (Neg conjR)], [Box (Neg conjL);⊥]);([Box (Neg conjR); ⊥], [⊥])]).
        apply ImpL. epose (ImpLRule_I _ _ [_] [] [] [_]). simpl in i. apply i. apply dlCons. 2: apply dlCons. 3: apply dlNil.
        2: apply derI with (ps:=[]) ; [ apply BotL ; epose (BotLRule_I [_] []) ; simpl in b ; auto | apply dlNil].
        apply derI with (ps:=[([Neg conjR;Box (Neg conjR);Box (Neg conjL)], [Neg conjL])]). apply GLR.
        epose (@GLRRule_I _ [Box (Neg conjR)] _ [] [_]). simpl in g ; apply g ; clear g ; auto. intros A HA. inversion HA ; subst.
        eexists ; auto. inversion H1. apply univ_gen_ext_refl. apply dlCons. 2: apply dlNil.
        apply derI with (ps:=[([conjL;Neg conjR; Box (Neg conjR); Box (Neg conjL)], [Bot])]). apply ImpR. epose (ImpRRule_I _ _ [] _ [] []). simpl in i ; apply i.
        apply dlCons. 2: apply dlNil.
        apply derI with (ps:=[([conjL; Box (Neg conjR); Box (Neg conjL)], [conjR;⊥]);([conjL; Bot; Box (Neg conjR); Box (Neg conjL)], [⊥])]).
        apply ImpL. epose (ImpLRule_I _ _ [_] _ [] [_]). simpl in i. apply i. apply dlCons. 2: apply dlCons. 3: apply dlNil.
        2: apply derI with (ps:=[]) ; [ apply BotL ; epose (BotLRule_I [_] _) ; simpl in b ; auto | apply dlNil].
        remember ([Box (Neg conjR); Box (Neg conjL)]) as LHS0. rewrite HeqconjL. rewrite HeqconjR.
        epose (list_conj_R _ (_,_)). apply g ; clear g. simpl ; intros. apply InT_map_iff in H1.
        destruct H1. destruct p0 ; subst.
        assert (PermutationTS (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)) (nodupseq (XBoxed_list (top_boxes (fst sp)), []%list))).
        apply PermutationTS_nodupseq. split ; simpl ; auto. apply PermutationT_XBoxed_list. apply PermutationT_top_boxes. destruct perm ; auto.
        apply PermutationT_refl. apply PermutationTS_sym in H1.
        pose (PermutationTS_Canopy _ _ H1 _ i). destruct s0. destruct p0.
        epose (list_conj_wkn_L _ (_,_) (N p s x0)). simpl in g. apply g ; clear g.
        apply InT_map_iff. exists x0 ; split ; auto.

        assert (J100: GLS_prv ([N p s x0], [N p sp x])).
        { (* Massage the Ns. *)
          assert ((forall (x : Seq) (l m : MPropF), (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x l -> (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x m -> l = m)).
          intros. subst. auto.
          destruct (dec_init_rules x0).
          (* The sequents x0 and x are initial. *)
           assert (is_init x0) ; auto. pose (PermutationTS_is_init _ _ (PermutationTS_sym _ _ p0) X).
           pose (N_spec p sp x).
           pose (GN_inv_init _ g i1). rewrite <- e.
           epose (TopR _ [] []). simpl in g0 ; apply g0.
          (* The sequent x0 and x are not initial. *)
           assert (is_init x0 -> False) ; auto.
           assert (is_init x -> False). intro. apply H3. apply (PermutationTS_is_init _ _ p0 X).
           assert (J200: GUI p x0 (UI p x0)). apply UI_GUI ; auto.
           assert (J300: GUI p x (UI p x)). apply UI_GUI ; auto.
           pose (Canopy_critical _ _ i0).
           pose (Canopy_critical _ _ i).
           assert (J80: length (usable_boxes s) = length (usable_boxes sp)).
           assert (incl (usable_boxes s) (usable_boxes sp)). intros A HA. apply InT_In. apply In_InT in HA.
           apply (PermutationTS_usable_boxes _ _ perm) ; auto.
           epose (NoDup_incl_length (NoDup_usable_boxes s) H5).
           assert (incl (usable_boxes sp) (usable_boxes s)). intros A HA. apply InT_In. apply In_InT in HA.
           apply (PermutationTS_usable_boxes _ _ (PermutationTS_sym _ _ perm)) ; auto.
           epose (NoDup_incl_length (NoDup_usable_boxes sp) H6). lia.
           assert (J81: length (usable_boxes x) = length (usable_boxes x0)).
           assert (incl (usable_boxes x) (usable_boxes x0)). intros A HA. apply InT_In. apply In_InT in HA.
           apply (PermutationTS_usable_boxes _ _ p0) ; auto.
           epose (NoDup_incl_length (NoDup_usable_boxes x) H5).
           assert (incl (usable_boxes x0) (usable_boxes x)). intros A HA. apply InT_In. apply In_InT in HA.
           apply (PermutationTS_usable_boxes _ _ (PermutationTS_sym _ _ p0)) ; auto.
           epose (NoDup_incl_length (NoDup_usable_boxes x0) H6). lia.
           destruct (lt_decT (length (usable_boxes x0)) (length (usable_boxes s))).
           (* The sequent x0 has less usable boxes than s. *)
           pose (N_spec p s x0).
           epose (@GN_inv_noinit_lessub _ _ _ _ _ g H3 l J200). rewrite <- e ; auto.
           assert (J500: length (usable_boxes x) < length (usable_boxes sp)). lia.
           pose (N_spec p sp x).
           epose (@GN_inv_noinit_lessub _ _ _ _ _ g0 H4 J500 J300). rewrite <- e0 ; auto.
           apply IH. apply DLW_wf_lex.lex_cons ; auto. apply PermutationTS_sym ; auto.
           (* The sequent x0 does not have less usable boxes than s. *)
           pose (N_spec p s x0).
           assert (J410: Gimap (GUI p) (GLR_prems (nodupseq x0)) (map (UI p) (GLR_prems (nodupseq x0)))).
           apply Gimap_map ; auto. intros. apply UI_GUI ; auto.
           epose (@GN_inv_noinit_nolessub _ _ _ _ _ g H3 f1 J410). rewrite <- e ; auto.
           assert (J42: (length (usable_boxes x) < length (usable_boxes sp)) -> False). lia.
           pose (N_spec p sp x).
           assert (J43: Gimap (GUI p) (GLR_prems (nodupseq x)) (map (UI p) (GLR_prems (nodupseq x)))).
           apply Gimap_map ; auto. intros. apply UI_GUI ; auto.
           epose (@GN_inv_noinit_nolessub _ _ _ _ _ g0 H4 J42 J43). rewrite <- e0 ; auto.
           epose (OrR (_,[])). simpl in g1. apply g1 ; clear g1.
           epose (OrL ([],_)). simpl in g1. apply g1 ; clear g1.
           epose (list_disj_L _ (_,_)). apply g1 ; clear g1. simpl ; intros.
           pose (PermutationTS_restr_list_prop_snd _ _ _ _ (PermutationTS_sym _ _ p0) H5).
           epose (list_disj_wkn_R _ ([_],[_]) _ i1). simpl in g1. apply g1 ; clear g1.
           epose (Id_all_form _ [] _ []). simpl in d ; apply d.
           eapply GLS_prv_wkn_R with (s:=([Or (list_disj (map Neg (restr_list_prop p (fst x0)))) (list_disj (map Box (map (UI p) (GLR_prems (nodupseq x0)))))],
           [Or (list_disj (map Neg (restr_list_prop p (fst x)))) (list_disj (map Box (map (UI p) (GLR_prems (nodupseq x)))))])) (A:=list_disj (restr_list_prop p (snd x))).
           2: epose (wkn_RI (list_disj (restr_list_prop p (snd x))) _ [] _) ; simpl in w ; apply w.
           epose (OrR (_,[])). simpl in g1. apply g1 ; clear g1.
           epose (OrL ([],_)). simpl in g1. apply g1 ; clear g1.
           epose (list_disj_L _ (_,_)). apply g1 ; clear g1. simpl ; intros.
           apply InT_map_iff in H5. destruct H5. destruct p1 ; subst.
           pose (@PermutationTS_restr_list_prop_fst _ _ p x1 (PermutationTS_sym _ _ p0) i1).
           epose (list_disj_wkn_R _ ([_],[_]) _). simpl in g1. apply g1 ; clear g1. apply InT_map_iff. exists x1 ; split ; auto.
           epose (Id_all_form _ [] _ []). simpl in d ; apply d.
           eapply GLS_prv_wkn_R with (s:=([list_disj (map Box (map (UI p) (GLR_prems (nodupseq x0))))],
           [list_disj (map Box (map (UI p) (GLR_prems (nodupseq x))))])) (A:=list_disj (map Neg (restr_list_prop p (fst x)))).
           2: epose (wkn_RI (list_disj (map Neg (restr_list_prop p (fst x)))) _ [] _) ; simpl in w ; apply w.
            epose (list_disj_L _ (_,_)). apply g1 ; clear g1. simpl ; intros. apply InT_map_iff in H5.
            destruct H5. destruct p1 ; subst. apply InT_map_iff in i1. destruct i1. destruct p1 ; subst.
            destruct (PermutationTS_GLR_prems _ _ (PermutationTS_nodupseq _ _ (PermutationTS_sym _ _ p0)) _ i1). destruct p1.
            epose (list_disj_wkn_R _ ([_],_) (Box (UI p x1))). simpl in g1. apply g1 ; clear g1.
            apply InT_map_iff. exists (UI p x1). split ; auto. apply InT_map_iff. exists x1 ; split ; auto.
            apply derI with (ps:=[([(UI p x2);Box (UI p x2);Box (UI p x1)], [UI p x1])]). apply GLR.
            epose (@GLRRule_I _ [Box (UI p x2)] _ []). simpl in g1. apply g1 ; clear g1. intros A HA. inversion HA ; subst.
            eexists ; auto. inversion H5. apply univ_gen_ext_refl. apply dlCons. 2: apply dlNil.
            assert (J50: GLS_prv ([UI p x2], [UI p x1])). apply IH ; auto.
            pose (leq_ub_unif s). pose (leq_ub_Canopy _ _ i0). apply DLW_wf_lex.lex_cons ; auto.
            unfold GLR_prems in i1. destruct (finite_GLR_premises_of_S (nodupseq x0)). simpl in i1. apply InT_flatten_list_InT_elem in i1.
            destruct i1. destruct p3. apply p2 in i3. inversion i3 ; subst. inversion i1 ; subst.
            assert ((IdBRule []%list (nodupseq x0)) -> False). intro. assert (is_init (nodupseq x0)).
            destruct x0 ; simpl in H5 ; simpl in H8 ; unfold nodupseq ; simpl ; unfold is_init ; subst ; auto.
            apply is_init_nodupseq in X0 ; auto. pose (GLR_applic_less_usable_boxes i3 H5).
            assert (J30:length (usable_boxes (XBoxed_list (top_boxes (fst s)), []%list)) = length (usable_boxes (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))).
            apply ub_nodupseq. rewrite <- J30 in l0. pose (ub_nodupseq x0). lia. inversion H6.
            epose (@GLS_prv_list_wkn_L [_] [] _). rewrite app_nil_r in g1 ; simpl in g1. epose (g1 J50 [_;_]). simpl in g2. apply g2. }

        epose (@GLS_prv_list_wkn_R _ _ []). rewrite app_nil_r in g ; simpl in g. pose (g J100 [Bot]). simpl in g0.
        epose (@GLS_prv_list_wkn_L [_] [] _). rewrite app_nil_r in g1 ; simpl in g1. epose (g1 g0 [_;_]). simpl in g2. apply g2.
  (* Sequents are not critical. *)
  - assert (J0: GUI p s (UI p s)). apply UI_GUI ; auto. assert (J00: GUI p sp (UI p sp)). apply UI_GUI ; auto.
    assert (J1: Gimap (GUI p) (Canopy (nodupseq s)) (map (UI p) (Canopy (nodupseq s)))). apply Gimap_map. intros.
    apply UI_GUI ; auto.
    assert (J10: Gimap (GUI p) (Canopy (nodupseq sp)) (map (UI p) (Canopy (nodupseq sp)))). apply Gimap_map. intros.
    apply UI_GUI ; auto.
    pose (@GUI_inv_not_critic p s _ _ J0 f J1). rewrite <- e ; clear e.
    assert (critical_Seq sp -> False). intro. apply f. apply (PermutationTS_critic _ _ (PermutationTS_sym _ _ perm) H).
    pose (@GUI_inv_not_critic p sp _ _ J00 H J10). rewrite <- e ; clear e.
    epose (list_conj_R _ (_,_)). simpl in g. apply g ; clear g. intros.
    apply InT_map_iff in H0. destruct H0. destruct p0. subst.
    pose (PermutationTS_nodupseq _ _ perm). apply PermutationTS_sym in p0.
    pose (PermutationTS_Canopy _ _ p0 _ i). destruct s0. destruct p1.
    epose (list_conj_wkn_L _ (_,_) (UI p x0)). simpl in g. apply g ; clear g.
    apply InT_map_iff. exists x0 ; split ; auto.
    assert (LexSeq x0 s). pose (Canopy_LexSeq _ _ i0). destruct s0 ; subst ; auto. exfalso.
    apply f ; apply Canopy_critical in i0 ; auto. apply critical_nodupseq ; auto. apply LexSeq_nodupseq in l ; auto.
    apply (IH _ H0 _ p (PermutationTS_sym _ _ p1)). }
  Qed.

  Lemma UI_nodupseq : forall s p X Y, GLS_prv (UI p (nodupseq s) :: X, UI p s :: Y).
  Proof.
  pose (d:=LexSeq_ind (fun (s:Seq) => forall p X Y, GLS_prv (UI p (nodupseq s) :: X, UI p s :: Y))).
  apply d. clear d. intros s IH p X Y.
  destruct (empty_seq_dec s) as [EE | DE].
  { subst. unfold nodupseq. simpl. assert (J0: GUI p ([],[]) Bot). apply GUI_empty_seq ; auto. apply UI_GUI in J0. 
     rewrite J0 in *. apply derI with []. apply BotL ; apply (BotLRule_I []). apply dlNil. }
  { destruct (critical_Seq_dec s).
  (* Sequents are critical. *)
  - assert (critical_Seq (nodupseq s)). apply (critical_nodupseq s) ; auto.
    destruct (dec_init_rules s).
    (* Sequents are initial. *)
    * assert (is_init s) ; auto. assert (is_init (nodupseq s)). apply (is_init_nodupseq s) ; auto.
      assert (J0: GUI p s (UI p s)). apply UI_GUI ; auto.
      pose (@GUI_inv_critic_init p s _ J0 c X0). rewrite <- e. epose (TopR _ [] _). simpl in g ; apply g.
    (* Sequents are not initial. *)
    * assert ((is_init s) -> False) ; auto. assert ((is_init (nodupseq s)) -> False). intro. apply H0.
      apply (is_init_nodupseq s) ; auto.
      assert (J0: GUI p s (UI p s)). apply UI_GUI ; auto.
      assert (J00: GUI p (nodupseq s) (UI p (nodupseq s))). apply UI_GUI ; auto.
      assert (J1: Gimap (GUI p) (GLR_prems (nodupseq s)) (map (UI p) (GLR_prems (nodupseq s)))). apply Gimap_map. intros.
      apply UI_GUI ; auto.
      assert (J10: Gimap (GUI p) (GLR_prems (nodupseq (nodupseq s))) (map (UI p) (GLR_prems (nodupseq (nodupseq s))))). apply Gimap_map. intros.
      apply UI_GUI ; auto.
      assert (J2: (Gimap (GN p (GUI p) s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), [])))
      (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), [])))))). apply Gimap_map. intros.
      apply (N_spec p s x).
      assert (J20: (Gimap (GN p (GUI p) (nodupseq s)) (Canopy (nodupseq (XBoxed_list (top_boxes (fst (nodupseq s))), [])))
      (map (N p (nodupseq s)) (Canopy (nodupseq (XBoxed_list (top_boxes (fst (nodupseq s))), [])))))). apply Gimap_map. intros.
      apply (N_spec p (nodupseq s) x).
      assert (J41: (nodupseq s) <> ([],[])). intro. apply DE. destruct s. simpl in *. unfold nodupseq in *. simpl in H2. inversion H2 ; subst.
      apply nodup_nil in H4 ; rewrite H4 in H5 ; apply nodup_nil in H5 ; subst ; auto.
       pose (@GUI_inv_critic_not_init p s _ _ _ J0 c DE H0 J1 J2). rewrite <- e ; clear e.
       pose (@GUI_inv_critic_not_init p (nodupseq s) _ _ _ J00 H J41 H1 J10 J20). rewrite <- e ; clear e.
       repeat rewrite <- fixpoint_nodupseq.
        epose (OrR (_,_)). simpl in g. apply g ; clear g.
        epose (OrL (_,_)). simpl in g. apply g ; clear g.
        epose (list_disj_L _ (_,_)). apply g ; clear g. simpl ; intros.
        epose (restr_list_prop_nodup (snd s) A p). apply p0 in H2.
        epose (list_disj_wkn_R _ (_,_) _ H2). simpl in g. apply g ; clear g.
        epose (Id_all_form _ [] _ []). simpl in d ; apply d.
        eapply GLS_prv_wkn_R with (s:=((Or (list_disj (map Neg (restr_list_prop p (fst (nodupseq s))))) (Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq s)))))
        (Diam (list_conj (map (N p (nodupseq s)) (Canopy (nodupseq (XBoxed_list (top_boxes (fst (nodupseq s))), []%list)))))))) :: X, Or (list_disj (map Neg (restr_list_prop p (fst s))))
        (Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq s))))) (Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))))) :: Y)) (A:=list_disj (restr_list_prop p (snd s))).
        2: epose (wkn_RI (list_disj (restr_list_prop p (snd s))) _ [] _) ; simpl in w ; apply w.
        epose (OrR (_,_)). simpl in g. apply g ; clear g.
        epose (OrL (_,_)). simpl in g. apply g ; clear g.
        epose (list_disj_L _ (_,_)). apply g ; clear g. simpl ; intros.
        apply InT_map_iff in H2. destruct H2. destruct p0 ; subst.
        epose (restr_list_prop_nodup (fst s) x p). apply p0 in i.
        epose (list_disj_wkn_R _ (_,_) _). simpl in g. apply g ; clear g. apply InT_map_iff. exists x ; split ; auto.
        epose (Id_all_form _ [] _ []). simpl in d ; apply d.
        eapply GLS_prv_wkn_R with (s:=((Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq s))))) (Diam (list_conj (map (N p (nodupseq s)) (Canopy (nodupseq (XBoxed_list (top_boxes (fst (nodupseq s))), []%list))))))) :: X,
        (Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq s)))))
        (Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))))) :: Y)) (A:=list_disj (map Neg (restr_list_prop p (fst s)))).
        2: epose (wkn_RI (list_disj (map Neg (restr_list_prop p (fst s)))) _ [] _) ; simpl in w ; apply w.
        epose (OrR (_,_)). simpl in g. apply g ; clear g.
        epose (OrL (_,_)). simpl in g. apply g ; clear g.
        epose (list_disj_L _ (_,_)). apply g ; clear g. simpl ; intros. apply InT_map_iff in H2.
        destruct H2. destruct p0 ; subst. apply InT_map_iff in i. destruct i. destruct p0 ; subst.
        epose (list_disj_wkn_R _ (_,_) (Box (UI p x0))). simpl in g. apply g ; clear g.
        apply InT_map_iff. exists (UI p x0). split ; auto. apply InT_map_iff. exists x0 ; split ; auto.
        epose (Id_all_form _ [] _ []). simpl in d ; apply d.
        eapply GLS_prv_wkn_R with (s:=((Diam (list_conj (map (N p (nodupseq s)) (Canopy (nodupseq (XBoxed_list (top_boxes (fst (nodupseq s))), []%list)))))) :: X,
        Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))) :: Y)) (A:=list_disj (map Box (map (UI p) (GLR_prems (nodupseq s))))).
        2: epose (wkn_RI (list_disj (map Box (map (UI p) (GLR_prems (nodupseq s))))) _ [] _) ; simpl in w ; apply w.
        remember (list_conj (map (N p (nodupseq s)) (Canopy (nodupseq (XBoxed_list (top_boxes (fst (nodupseq s))), []%list))))) as conjL.
        remember (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))) as conjR.
        apply derI with (ps:=[(Box (Neg conjR) :: Diam conjL :: X, Bot :: Y)]). apply ImpR. epose (ImpRRule_I _ _ [] _ [] _). simpl in i ; apply i.
        apply dlCons. 2: apply dlNil.
        apply derI with (ps:=[(Box (Neg conjR) :: X, Box (Neg conjL) :: ⊥ :: Y);(Box (Neg conjR) :: ⊥ :: X, ⊥ :: Y)]).
        apply ImpL. epose (ImpLRule_I _ _ [_] _ [] _). simpl in i. apply i. apply dlCons. 2: apply dlCons. 3: apply dlNil.
        2: apply derI with (ps:=[]) ; [ apply BotL ; epose (BotLRule_I [_] _) ; simpl in b ; auto | apply dlNil].
        apply derI with (ps:=[(Neg conjR :: Box (Neg conjR) :: XBoxed_list (top_boxes X) ++ [Box (Neg conjL)], [Neg conjL])]). apply GLR.
        epose (@GLRRule_I _ (Box (Neg conjR) :: (top_boxes X)) _ [] _). simpl in g ; apply g ; clear g ; auto. intros A HA. inversion HA ; subst.
        eexists ; auto. apply in_top_boxes in H2. destruct H2. destruct s0. destruct s0. destruct p0 ; subst. eexists ; auto.
        apply univ_gen_ext_cons. apply nobox_top_boxes. apply dlCons. 2: apply dlNil.
        apply derI with (ps:=[(conjL :: Neg conjR :: Box (Neg conjR) :: XBoxed_list (top_boxes X) ++ [Box (Neg conjL)], [Bot])]). apply ImpR. epose (ImpRRule_I _ _ [] _ [] []). simpl in i ; apply i.
        apply dlCons. 2: apply dlNil.
        apply derI with (ps:=[(conjL :: Box (Neg conjR) :: XBoxed_list (top_boxes X) ++ [Box (Neg conjL)], [conjR;⊥]);(conjL :: Bot :: Box (Neg conjR) :: XBoxed_list (top_boxes X) ++ [Box (Neg conjL)], [⊥])]).
        apply ImpL. epose (ImpLRule_I _ _ [_] _ [] [_]). simpl in i. apply i. apply dlCons. 2: apply dlCons. 3: apply dlNil.
        2: apply derI with (ps:=[]) ; [ apply BotL ; epose (BotLRule_I [_] _) ; simpl in b ; auto | apply dlNil].
        remember (Box (Neg conjR) :: XBoxed_list (top_boxes X) ++ [Box (Neg conjL)]) as LHS0. rewrite HeqconjL. rewrite HeqconjR.
        epose (list_conj_R _ (_,_)). apply g ; clear g. simpl ; intros. apply InT_map_iff in H2.
        destruct H2. destruct p0 ; subst.
        assert (J70: (nodupseq (XBoxed_list (top_boxes (nodup eq_dec_form (fst s))), []%list)) = (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))).
        unfold nodupseq ; simpl. rewrite <- nodup_top_boxes. rewrite nodup_XBoxed_list ; auto. rewrite J70.
        epose (list_conj_wkn_L _ (_,_) (N p (nodupseq s) x)). simpl in g. apply g ; clear g.
        apply InT_map_iff. exists x ; split ; auto.

        assert (J100: GLS_prv ([N p (nodupseq s) x], [N p s x])).
        { (* Massage the Ns. *)
          assert ((forall (x : Seq) (l m : MPropF), (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x l -> (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x m -> l = m)).
          intros. subst. auto.
          destruct (dec_init_rules x).
          (* The sequent x is initial. *)
           assert (is_init x) ; auto.
           pose (N_spec p s x).
           pose (GN_inv_init _ g). rewrite <- e ; auto.
           epose (TopR _ [] []). simpl in g0 ; apply g0.
          (* The sequent x is not initial. *)
           assert (is_init x -> False) ; auto.
           assert (J300: GUI p x (UI p x)). apply UI_GUI ; auto.
           pose (Canopy_critical _ _ i).
           pose (ub_nodupseq s).
           destruct (lt_decT (length (usable_boxes x)) (length (usable_boxes s))).
           (* The sequent x0 has less usable boxes than s. *)
           pose (N_spec p s x).
           epose (@GN_inv_noinit_lessub _ _ _ _ _ g H3 l J300). rewrite <- e0 ; auto.
           assert (J500: length (usable_boxes x) < length (usable_boxes (nodupseq s))). lia.
           pose (N_spec p (nodupseq s) x).
           epose (@GN_inv_noinit_lessub _ _ _ _ _ g0 H3 J500 J300). rewrite <- e1 ; auto.
           epose (Id_all_form _ [] _ []). simpl in d ; apply d.
           (* The sequent x does not have less usable boxes than s. *)
           pose (N_spec p s x).
           assert (J410: Gimap (GUI p) (GLR_prems (nodupseq x)) (map (UI p) (GLR_prems (nodupseq x)))).
           apply Gimap_map ; auto. intros ; apply UI_GUI ; auto.
           epose (@GN_inv_noinit_nolessub _ _ _ _ _ g H3 f1 J410). rewrite <- e0 ; auto.
           assert (J42: (length (usable_boxes x) < length (usable_boxes (nodupseq s))) -> False). lia.
           pose (N_spec p (nodupseq s) x).
           assert (J43: Gimap (GUI p) (GLR_prems (nodupseq x)) (map (UI p) (GLR_prems (nodupseq x)))).
           apply Gimap_map ; auto. intros ; apply UI_GUI ; auto.
           epose (@GN_inv_noinit_nolessub _ _ _ _ _ g0 H3 J42 J43). rewrite <- e1 ; auto.
           epose (Id_all_form _ [] _ []). simpl in d ; apply d. }

        epose (@GLS_prv_list_wkn_R _ _ _). rewrite app_nil_r in g ; simpl in g. pose (g J100 [Bot]). simpl in g0.
        epose (@GLS_prv_list_wkn_L [_] _ _). rewrite app_nil_r in g1 ; simpl in g1. epose (g1 g0 _).
        simpl in g2 ; rewrite app_nil_r in g2. apply g2.
  (* Sequents are not critical. *)
  - assert (J0: GUI p s (UI p s)). apply UI_GUI ; auto. assert (J00: GUI p (nodupseq s) (UI p (nodupseq s))). apply UI_GUI ; auto.
    assert (J1: Gimap (GUI p) (Canopy (nodupseq s)) (map (UI p) (Canopy (nodupseq s)))). apply Gimap_map. intros.
    apply UI_GUI ; auto.
    assert (J10: Gimap (GUI p) (Canopy (nodupseq (nodupseq s))) (map (UI p) (Canopy (nodupseq (nodupseq s))))). apply Gimap_map. intros.
    apply UI_GUI ; auto.
    pose (@GUI_inv_not_critic p s _ _ J0 f J1). rewrite <- e ; clear e.
    assert (critical_Seq (nodupseq s) -> False). intro. apply f. apply critical_nodupseq ; auto.
    pose (@GUI_inv_not_critic p (nodupseq s) _ _ J00 H J10). rewrite <- e ; clear e.
    rewrite <- fixpoint_nodupseq.
    epose (Id_all_form _ [] _ []). simpl in d ; apply d. }
Qed.

  Lemma UI_nodupseq_converse : forall s p X Y, GLS_prv (UI p s :: X, UI p (nodupseq s) :: Y).
  Proof.
  pose (d:=LexSeq_ind (fun (s:Seq) => forall p X Y, GLS_prv (UI p s :: X, UI p (nodupseq s) :: Y))).
  apply d. clear d. intros s IH p X Y.
  destruct (empty_seq_dec s) as [EE | DE].
  { subst. unfold nodupseq. simpl. assert (J0: GUI p ([],[]) Bot). apply GUI_empty_seq ; auto. apply UI_GUI in J0. 
     rewrite J0 in *. apply derI with []. apply BotL ; apply (BotLRule_I []). apply dlNil. }
  { destruct (critical_Seq_dec s).
  (* Sequents are critical. *)
  - assert (critical_Seq (nodupseq s)). apply (critical_nodupseq s) ; auto.
    destruct (dec_init_rules s).
    (* Sequents are initial. *)
    * assert (is_init s) ; auto. assert (is_init (nodupseq s)). apply (is_init_nodupseq s) ; auto.
      assert (J0: GUI p (nodupseq s) (UI p (nodupseq s))). apply UI_GUI ; auto.
      pose (@GUI_inv_critic_init p (nodupseq s) _ J0 H X1). rewrite <- e. epose (TopR _ [] _). simpl in g ; apply g.
    (* Sequents are not initial. *)
    * assert ((is_init s) -> False) ; auto. assert ((is_init (nodupseq s)) -> False). intro. apply H0.
      apply (is_init_nodupseq s) ; auto.
      assert (J0: GUI p s (UI p s)). apply UI_GUI ; auto.
      assert (J00: GUI p (nodupseq s) (UI p (nodupseq s))). apply UI_GUI ; auto.
      assert (J1: Gimap (GUI p) (GLR_prems (nodupseq s)) (map (UI p) (GLR_prems (nodupseq s)))). apply Gimap_map. intros.
      apply UI_GUI ; auto.
      assert (J10: Gimap (GUI p) (GLR_prems (nodupseq (nodupseq s))) (map (UI p) (GLR_prems (nodupseq (nodupseq s))))). apply Gimap_map. intros.
      apply UI_GUI ; auto.
      assert (J2: (Gimap (GN p (GUI p) s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), [])))
      (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), [])))))). apply Gimap_map. intros.
      apply (N_spec p s x).
      assert (J20: (Gimap (GN p (GUI p) (nodupseq s)) (Canopy (nodupseq (XBoxed_list (top_boxes (fst (nodupseq s))), [])))
      (map (N p (nodupseq s)) (Canopy (nodupseq (XBoxed_list (top_boxes (fst (nodupseq s))), [])))))). apply Gimap_map. intros.
      apply (N_spec p (nodupseq s) x).
      assert (J41: (nodupseq s) <> ([],[])). intro. apply DE. destruct s. simpl in *. unfold nodupseq in *. simpl in H2. inversion H2 ; subst.
      apply nodup_nil in H4 ; rewrite H4 in H5 ; apply nodup_nil in H5 ; subst ; auto.
       pose (@GUI_inv_critic_not_init p s _ _ _ J0 c DE H0 J1 J2). rewrite <- e ; clear e.
       pose (@GUI_inv_critic_not_init p (nodupseq s) _ _ _ J00 H J41 H1 J10 J20). rewrite <- e ; clear e.
       repeat rewrite <- fixpoint_nodupseq.
        epose (OrR (_,_)). simpl in g. apply g ; clear g.
        epose (OrL (_,_)). simpl in g. apply g ; clear g.
        epose (list_disj_L _ (_,_)). apply g ; clear g. simpl ; intros.
        epose (restr_list_prop_nodup (snd s) A p). apply p0 in H2.
        epose (list_disj_wkn_R _ (_,_) _ H2). simpl in g. apply g ; clear g.
        epose (Id_all_form _ [] _ []). simpl in d ; apply d.
        eapply GLS_prv_wkn_R with (s:=((Or (list_disj (map Neg (restr_list_prop p (fst s)))) (Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq s)))))
        (Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))))))) :: X, Or (list_disj (map Neg (restr_list_prop p (fst (nodupseq s)))))
        (Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq s))))) (Diam (list_conj (map (N p (nodupseq s)) (Canopy (nodupseq (XBoxed_list (top_boxes (fst (nodupseq s))), []%list))))))) :: Y)) (A:=list_disj (restr_list_prop p (snd (nodupseq s)))).
        2: epose (wkn_RI (list_disj (restr_list_prop p (snd (nodupseq s)))) _ [] _) ; simpl in w ; apply w.
        epose (OrR (_,_)). simpl in g. apply g ; clear g.
        epose (OrL (_,_)). simpl in g. apply g ; clear g.
        epose (list_disj_L _ (_,_)). apply g ; clear g. simpl ; intros.
        apply InT_map_iff in H2. destruct H2. destruct p0 ; subst.
        epose (restr_list_prop_nodup (fst s) x p). apply p0 in i.
        epose (list_disj_wkn_R _ (_,_) _). simpl in g. apply g ; clear g. apply InT_map_iff. exists x ; split ; auto.
        epose (Id_all_form _ [] _ []). simpl in d ; apply d.
        eapply GLS_prv_wkn_R with (s:=((Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq s))))) (Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))))) :: X,
        (Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq s)))))
        (Diam (list_conj (map (N p (nodupseq s)) (Canopy (nodupseq (XBoxed_list (top_boxes (fst (nodupseq s))), []%list))))))) :: Y)) (A:=list_disj (map Neg (restr_list_prop p (fst (nodupseq s))))).
        2: epose (wkn_RI (list_disj (map Neg (restr_list_prop p (fst (nodupseq s))))) _ [] _) ; simpl in w ; apply w.
        epose (OrR (_,_)). simpl in g. apply g ; clear g.
        epose (OrL (_,_)). simpl in g. apply g ; clear g.
        epose (list_disj_L _ (_,_)). apply g ; clear g. simpl ; intros. apply InT_map_iff in H2.
        destruct H2. destruct p0 ; subst. apply InT_map_iff in i. destruct i. destruct p0 ; subst.
        epose (list_disj_wkn_R _ (_,_) (Box (UI p x0))). simpl in g. apply g ; clear g.
        apply InT_map_iff. exists (UI p x0). split ; auto. apply InT_map_iff. exists x0 ; split ; auto.
        epose (Id_all_form _ [] _ []). simpl in d ; apply d.
        eapply GLS_prv_wkn_R with (s:=((Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))))) :: X,
        Diam (list_conj (map (N p (nodupseq s)) (Canopy (nodupseq (XBoxed_list (top_boxes (fst (nodupseq s))), []%list))))) :: Y)) (A:=list_disj (map Box (map (UI p) (GLR_prems (nodupseq s))))).
        2: epose (wkn_RI (list_disj (map Box (map (UI p) (GLR_prems (nodupseq s))))) _ [] _) ; simpl in w ; apply w.
        remember (list_conj (map (N p (nodupseq s)) (Canopy (nodupseq (XBoxed_list (top_boxes (fst (nodupseq s))), []%list))))) as conjR.
        remember (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))) as conjL.
        apply derI with (ps:=[(Box (Neg conjR) :: Diam conjL :: X, Bot :: Y)]). apply ImpR. epose (ImpRRule_I _ _ [] _ [] _). simpl in i ; apply i.
        apply dlCons. 2: apply dlNil.
        apply derI with (ps:=[(Box (Neg conjR) :: X, Box (Neg conjL) :: ⊥ :: Y);(Box (Neg conjR) :: ⊥ :: X, ⊥ :: Y)]).
        apply ImpL. epose (ImpLRule_I _ _ [_] _ [] _). simpl in i. apply i. apply dlCons. 2: apply dlCons. 3: apply dlNil.
        2: apply derI with (ps:=[]) ; [ apply BotL ; epose (BotLRule_I [_] _) ; simpl in b ; auto | apply dlNil].
        apply derI with (ps:=[(Neg conjR :: Box (Neg conjR) :: XBoxed_list (top_boxes X) ++ [Box (Neg conjL)], [Neg conjL])]). apply GLR.
        epose (@GLRRule_I _ (Box (Neg conjR) :: (top_boxes X)) _ [] _). simpl in g ; apply g ; clear g ; auto. intros A HA. inversion HA ; subst.
        eexists ; auto. apply in_top_boxes in H2. destruct H2. destruct s0. destruct s0. destruct p0 ; subst. eexists ; auto.
        apply univ_gen_ext_cons. apply nobox_top_boxes. apply dlCons. 2: apply dlNil.
        apply derI with (ps:=[(conjL :: Neg conjR :: Box (Neg conjR) :: XBoxed_list (top_boxes X) ++ [Box (Neg conjL)], [Bot])]). apply ImpR. epose (ImpRRule_I _ _ [] _ [] []). simpl in i ; apply i.
        apply dlCons. 2: apply dlNil.
        apply derI with (ps:=[(conjL :: Box (Neg conjR) :: XBoxed_list (top_boxes X) ++ [Box (Neg conjL)], [conjR;⊥]);(conjL :: Bot :: Box (Neg conjR) :: XBoxed_list (top_boxes X) ++ [Box (Neg conjL)], [⊥])]).
        apply ImpL. epose (ImpLRule_I _ _ [_] _ [] [_]). simpl in i. apply i. apply dlCons. 2: apply dlCons. 3: apply dlNil.
        2: apply derI with (ps:=[]) ; [ apply BotL ; epose (BotLRule_I [_] _) ; simpl in b ; auto | apply dlNil].
        remember (Box (Neg conjR) :: XBoxed_list (top_boxes X) ++ [Box (Neg conjL)]) as LHS0. rewrite HeqconjL. rewrite HeqconjR.
        epose (list_conj_R _ (_,_)). apply g ; clear g. simpl ; intros. apply InT_map_iff in H2.
        destruct H2. destruct p0 ; subst.
        assert (J70: (nodupseq (XBoxed_list (top_boxes (nodup eq_dec_form (fst s))), []%list)) = (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))).
        unfold nodupseq ; simpl. rewrite <- nodup_top_boxes. rewrite nodup_XBoxed_list ; auto. rewrite <- J70.
        epose (list_conj_wkn_L _ (_,_) (N p s x)). simpl in g. apply g ; clear g.
        apply InT_map_iff. exists x ; split ; auto.

        assert (J100: GLS_prv ([N p s x], [N p (nodupseq s) x])).
        { (* Massage the Ns. *)
          assert ((forall (x : Seq) (l m : MPropF), (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x l -> (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x m -> l = m)).
          intros. subst. auto.
          destruct (dec_init_rules x).
          (* The sequent x is initial. *)
           assert (is_init x) ; auto.
           pose (N_spec p (nodupseq s) x).
           pose (GN_inv_init _ g). rewrite <- e ; auto.
           epose (TopR _ [] []). simpl in g0 ; apply g0.
          (* The sequent x is not initial. *)
           assert (is_init x -> False) ; auto.
           assert (J300: GUI p x (UI p x)). apply UI_GUI ; auto.
           pose (Canopy_critical _ _ i).
           pose (ub_nodupseq s).
           destruct (lt_decT (length (usable_boxes x)) (length (usable_boxes s))).
           (* The sequent x0 has less usable boxes than s. *)
           pose (N_spec p s x).
           epose (@GN_inv_noinit_lessub _ _ _ _ _ g H3 l J300). rewrite <- e0 ; auto.
           assert (J500: length (usable_boxes x) < length (usable_boxes (nodupseq s))). lia.
           pose (N_spec p (nodupseq s) x).
           epose (@GN_inv_noinit_lessub _ _ _ _ _ g0 H3 J500 J300). rewrite <- e1 ; auto.
           epose (Id_all_form _ [] _ []). simpl in d ; apply d.
           (* The sequent x does not have less usable boxes than s. *)
           pose (N_spec p s x).
           assert (J410: Gimap (GUI p) (GLR_prems (nodupseq x)) (map (UI p) (GLR_prems (nodupseq x)))).
           apply Gimap_map ; auto. intros ; apply UI_GUI ; auto.
           epose (@GN_inv_noinit_nolessub _ _ _ _ _ g H3 f1 J410). rewrite <- e0 ; auto.
           assert (J42: (length (usable_boxes x) < length (usable_boxes (nodupseq s))) -> False). lia.
           pose (N_spec p (nodupseq s) x).
           assert (J43: Gimap (GUI p) (GLR_prems (nodupseq x)) (map (UI p) (GLR_prems (nodupseq x)))).
           apply Gimap_map ; auto. intros ; apply UI_GUI ; auto.
           epose (@GN_inv_noinit_nolessub _ _  _ _ _ g0 H3 J42 J43). rewrite <- e1 ; auto.
           epose (Id_all_form _ [] _ []). simpl in d ; apply d. }

        epose (@GLS_prv_list_wkn_R _ _ _). rewrite app_nil_r in g ; simpl in g. pose (g J100 [Bot]). simpl in g0.
        epose (@GLS_prv_list_wkn_L [_] _ _). rewrite app_nil_r in g1 ; simpl in g1. epose (g1 g0 _).
        simpl in g2 ; rewrite app_nil_r in g2. apply g2.
  (* Sequents are not critical. *)
  - assert (J0: GUI p s (UI p s)). apply UI_GUI ; auto. assert (J00: GUI p (nodupseq s) (UI p (nodupseq s))). apply UI_GUI ; auto.
    assert (J1: Gimap (GUI p) (Canopy (nodupseq s)) (map (UI p) (Canopy (nodupseq s)))). apply Gimap_map. intros.
    apply UI_GUI ; auto.
    assert (J10: Gimap (GUI p) (Canopy (nodupseq (nodupseq s))) (map (UI p) (Canopy (nodupseq (nodupseq s))))). apply Gimap_map. intros.
    apply UI_GUI ; auto.
    pose (@GUI_inv_not_critic p s _ _ J0 f J1). rewrite <- e ; clear e.
    assert (critical_Seq (nodupseq s) -> False). intro. apply f. apply critical_nodupseq ; auto.
    pose (@GUI_inv_not_critic p (nodupseq s) _ _ J00 H J10). rewrite <- e ; clear e.
    rewrite <- fixpoint_nodupseq.
    epose (Id_all_form _ [] _ []). simpl in d ; apply d. }
  Qed.

  Lemma UI_nodupseq_gen : forall s0 s1 p X Y, (nodupseq s0 = nodupseq s1) -> GLS_prv (UI p s0 :: X, UI p s1 :: Y).
  Proof.
  intros.
  pose (UI_nodupseq s1 p X Y).
  pose (UI_nodupseq_converse s0 p X Y). rewrite H in *.
  pose (GLS_cut_adm (UI p (nodupseq s1)) [] (UI p s0 :: X) [] (UI p s1 :: Y)). simpl in g1. apply g1 ; auto.
  eapply GLS_prv_wkn_R with (s:=(UI p s0 :: X, UI p (nodupseq s1) :: Y)) (A:=UI p s1) ; auto.
  epose (wkn_RI (UI p s1) _ [_] _) ; simpl in w ; apply w.
  eapply GLS_prv_wkn_L with (s:=(UI p (nodupseq s1) :: X, UI p s1 :: Y)) (A:=UI p s0) ; auto.
  epose (wkn_LI (UI p s0) [_] _ _) ; simpl in w ; apply w.
  Qed.

  Lemma N_nodupseq : forall s0 s1 p X Y, critical_Seq s1 -> GLS_prv (N p s0 s1 :: X, N p s0 (nodupseq s1) :: Y).
  Proof.
  intros s0 s1. revert s0. revert s1.
  pose (d:=LexSeq_ind (fun (s:Seq) => forall s0 p X Y, critical_Seq s -> GLS_prv (N p s0 s :: X, N p s0 (nodupseq s) :: Y))).
  apply d. clear d. intros s1 IH s0 p X Y crit.
  assert ((forall (x : Seq) (l m : MPropF), (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x l -> (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x m -> l = m)).
  intros. subst. auto.
  destruct (dec_init_rules s1).
  (* The sequent s1 is initial. *)
   - assert (is_init s1) ; auto. assert (is_init (nodupseq s1)). apply is_init_nodupseq in X0; auto.
     pose (N_spec p s0 (nodupseq s1)).
     pose (GN_inv_init _ g). rewrite <- e ; auto.
     epose (TopR _ [] _). simpl in g0 ; apply g0.
  (* The sequent s1 is not initial. *)
   - assert (is_init s1 -> False) ; auto. assert (is_init (nodupseq s1) -> False). intro ; apply H0 ; apply is_init_nodupseq ; auto.
     assert (J300: GUI p s1 (UI p s1)). apply UI_GUI ; auto.
     assert (J400: GUI p (nodupseq s1) (UI p (nodupseq s1))). apply UI_GUI ; auto.
     assert (critical_Seq (nodupseq s1)). apply (critical_nodupseq s1) ; auto.
     pose (ub_nodupseq s1).
     destruct (lt_decT (length (usable_boxes s1)) (length (usable_boxes s0))).
     (* The sequent x0 has less usable boxes than s. *)
     * pose (N_spec p s0 s1).
       epose (@GN_inv_noinit_lessub _ _ _ _ _ g H0 l J300). rewrite <- e0 ; auto.
       assert (J500: length (usable_boxes (nodupseq s1)) < length (usable_boxes s0)). rewrite <- ub_nodupseq ; auto.
       pose (N_spec p s0 (nodupseq s1)).
       epose (@GN_inv_noinit_lessub _ _ _ _ _ g0 H1 J500 J400). rewrite <- e1 ; auto.
       apply UI_nodupseq_converse.
     (* The sequent x does not have less usable boxes than s. *)
     * pose (N_spec p s0 s1).
       assert (J410: Gimap (GUI p) (GLR_prems (nodupseq s1)) (map (UI p) (GLR_prems (nodupseq s1)))).
       apply Gimap_map ; auto. intros ; apply UI_GUI ; auto.
       epose (@GN_inv_noinit_nolessub _ _ _ _ _ g H0 f0 J410). rewrite <- e0 ; auto.
       assert (J42: (length (usable_boxes (nodupseq s1)) < length (usable_boxes s0)) -> False). rewrite <- ub_nodupseq ; auto.
       pose (N_spec p s0 (nodupseq s1)).
       assert (J43: Gimap (GUI p) (GLR_prems (nodupseq (nodupseq s1))) (map (UI p) (GLR_prems (nodupseq (nodupseq s1))))).
       apply Gimap_map ; auto. intros ; apply UI_GUI ; auto.
       epose (@GN_inv_noinit_nolessub _ _ _ _ _ g0 H1 J42 J43). rewrite <- e1 ; auto.
       repeat rewrite <- fixpoint_nodupseq.
       epose (OrR (_,_)). simpl in g1. apply g1 ; clear g1.
       epose (OrL (_,_)). simpl in g1. apply g1 ; clear g1.
       epose (list_disj_L _ (_,_)). apply g1 ; clear g1. simpl ; intros.
       epose (restr_list_prop_nodup (snd s1) A p). apply p0 in H3 ; clear p0.
       epose (list_disj_wkn_R _ (_,_) _ H3). simpl in g1. apply g1 ; clear g1.
       epose (Id_all_form _ [] _ []). simpl in d ; apply d.
       eapply GLS_prv_wkn_R with (s:=(Or (list_disj (map Neg (restr_list_prop p (fst s1)))) (list_disj (map Box (map (UI p) (GLR_prems (nodupseq s1))))) :: X,
       Or (list_disj (map Neg (restr_list_prop p (fst (nodupseq s1))))) (list_disj (map Box (map (UI p) (GLR_prems (nodupseq s1))))) :: Y)) (A:=list_disj (restr_list_prop p (snd (nodupseq s1)))).
       2: epose (wkn_RI (list_disj (restr_list_prop p (snd (nodupseq s1)))) _ [] _) ; simpl in w ; apply w.
       epose (OrR (_,_)). simpl in g1. apply g1 ; clear g1.
       epose (OrL (_,_)). simpl in g1. apply g1 ; clear g1.
       epose (list_disj_L _ (_,_)). apply g1 ; clear g1. simpl ; intros.
       apply InT_map_iff in H3. destruct H3. destruct p0 ; subst.
       epose (restr_list_prop_nodup (fst s1) x p). apply p0 in i ; clear p0.
       epose (list_disj_wkn_R _ (_,_) _). simpl in g1. apply g1 ; clear g1. apply InT_map_iff. exists x ; split ; auto.
       epose (Id_all_form _ [] _ []). simpl in d ; apply d.
       eapply GLS_prv_wkn_R with (s:=(list_disj (map Box (map (UI p) (GLR_prems (nodupseq s1)))) :: X,
       list_disj (map Box (map (UI p) (GLR_prems (nodupseq s1)))) :: Y)) (A:=list_disj (map Neg (restr_list_prop p (fst (nodupseq s1))))).
       2: epose (wkn_RI (list_disj (map Neg (restr_list_prop p (fst (nodupseq s1))))) _ [] _) ; simpl in w ; apply w.
       epose (Id_all_form _ [] _ []). simpl in d ; apply d.
  Qed.