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

Theorem gen_rec_UI_imp : forall s sr p X Y,
              GLS_prv (X, (list_conj (map (N p sr) (Canopy (nodupseq s)))) --> (UI p s) :: Y).
  Proof.
  pose (d:=LexSeq_ind (fun (s:Seq) => forall sr p X Y,
              GLS_prv (X, (list_conj (map (N p sr) (Canopy (nodupseq s)))) --> (UI p s) :: Y))).
  apply d. clear d. intros s IH.
  intros.
  destruct (empty_seq_dec s) as [EE | DE].
  (* s is the empty sequent. *)
  { subst ; simpl in *. unfold nodupseq ; simpl.
    assert ((Canopy ([], [])) = [([], [])]). apply Id_InT_Canopy ; auto.
    apply critical_Seq_InT_Canopy ; auto. apply critical_empty_seq. rewrite H ; simpl.
    assert (GUI p ([],[]) Bot). apply GUI_empty_seq ; auto. apply UI_GUI in H0.
    rewrite H0 in *. pose critical_empty_seq. pose not_init_empty_seq.
    unfold N. destruct (N_pwc p sr ([], [])). simpl.
    assert ((forall (x : Seq) (l m : MPropF), (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x l -> (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x m -> l = m)).
    intros. subst. auto.
    assert (J11: Gimap (GUI p) (GLR_prems (nodupseq ([],[]))) (map (UI p) (GLR_prems (nodupseq ([],[]))))).
    apply Gimap_map. intros. apply UI_GUI ; auto.
    assert (J41: Gimap (GUI p) (GLR_prems (nodupseq (nodupseq ([],[])))) (map (UI p) (GLR_prems (nodupseq (nodupseq ([],[])))))).
    apply Gimap_map. intros. apply UI_GUI ; auto.
    destruct (lt_decT (length (usable_boxes ([],[]))) (length (usable_boxes sr))).
    + assert (J0: GUI p (nodupseq ([],[])) (UI p (nodupseq ([],[])))). apply UI_GUI ; auto. apply UI_GUI in J0.
       rewrite ub_nodupseq in l.
       epose (GN_inv_noinit_lessub p g f l (UI_spec p _)). rewrite <- e. rewrite H0.
       apply derI with (ps:=[([] ++ (And Bot Top) :: X, [] ++ Bot :: Y)]). apply ImpR. apply ImpRRule_I.
       apply dlCons. 2: apply dlNil. simpl.
       pose (AndL (X, Bot :: Y) Bot Top). simpl in g0. apply g0. clear g0.
       apply derI with []. 2: apply dlNil. apply BotL ; apply (BotLRule_I []).
    +  rewrite ub_nodupseq in f0. pose (GN_inv_noinit_nolessub _ g f f0 J41). rewrite <- e. clear e. simpl.
        unfold nodupseq in * ; simpl in *. destruct (GLR_prems ([], [])) eqn:E; simpl.
        { apply derI with (ps:=[([] ++ (And (Or ⊥ (Or ⊥ ⊥)) Top) :: X, [] ++ Bot :: Y)]). apply ImpR. apply ImpRRule_I.
          apply dlCons. 2: apply dlNil. simpl.
          pose (AndL (X, Bot :: Y) (Or ⊥ (Or ⊥ ⊥)) Top). simpl in g0. apply g0. clear g0.
          pose (OrL (Top :: X, ⊥ :: Y)). simpl in g0. apply g0 ; clear g0.
          apply derI with []. 2: apply dlNil. apply BotL ; apply (BotLRule_I []).
          pose (OrL (Top :: X, ⊥ :: Y)). simpl in g0. apply g0 ; clear g0.
          all: apply derI with [] ; [apply BotL ; apply (BotLRule_I []) | apply dlNil]. }
        { exfalso. unfold GLR_prems in E. destruct (finite_GLR_premises_of_S ([], [])).
           simpl in *. destruct x0. simpl in E. inversion E. simpl in E. pose (p0 l0).
           destruct p1. assert (InT l0 (l0 :: x0)). apply InT_eq. apply g0 in H2. inversion H2.
           destruct Δ0 ; subst ; inversion H6. } }
  (* s is not the empty sequent. *)
  { destruct (critical_Seq_dec s).
  (* If s is critical. *)
  - assert ((Canopy (nodupseq s)) = [nodupseq s]). apply Id_InT_Canopy ; auto.
    apply critical_Seq_InT_Canopy ; auto. apply critical_nodupseq in c ; auto.
    destruct (dec_init_rules s).
    (* If s is initial. *)
    * assert (is_init s). auto.
      assert (J0: GUI p s (UI p s)). apply UI_GUI ; auto.
      pose (@GUI_inv_critic_init p s (UI p s) J0 c X0). rewrite <- e. rewrite H. simpl. unfold N.
      destruct (N_pwc p sr (nodupseq s)).
      simpl. assert (is_init (nodupseq s)). pose (is_init_nodupseq s) ; destruct p0 ; auto. pose (GN_inv_init _ g).
      apply derI with (ps:=[([] ++ And x Top :: X, [] ++ Top :: Y)]).
      apply ImpR. apply ImpRRule_I. apply dlCons. 2: apply dlNil. simpl.
      epose (TopR _ []). simpl in g0 ; apply g0.
    (* If s is not initial. *)
    * rewrite H. simpl. unfold N.
      destruct (N_pwc p sr (nodupseq s)). simpl.
      assert (is_init s -> False). auto.
      assert (J40: is_init (nodupseq s) -> False). intro. apply H0. pose (is_init_nodupseq s) ; destruct p0 ; auto.
      assert ((forall (x : Seq) (l m : MPropF), (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x l -> (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x m -> l = m)).
      intros. subst. auto.
      assert (J11: Gimap (GUI p) (GLR_prems (nodupseq s)) (map (UI p) (GLR_prems (nodupseq s)))).
      apply Gimap_map. intros. apply UI_GUI ; auto.
      assert (J41: Gimap (GUI p) (GLR_prems (nodupseq (nodupseq s))) (map (UI p) (GLR_prems (nodupseq (nodupseq s))))).
      apply Gimap_map. intros. apply UI_GUI ; auto.
      destruct (lt_decT (length (usable_boxes s)) (length (usable_boxes sr))).
      (* If s has less usable boxes than sr. *)
      + assert (J0: GUI p (nodupseq s) (UI p (nodupseq s))). apply UI_GUI ; auto. apply UI_GUI in J0.
         rewrite ub_nodupseq in l.
         epose (GN_inv_noinit_lessub p g J40 l (UI_spec p _)). rewrite <- e.
         apply derI with (ps:=[([] ++ (And (UI p (nodupseq s)) Top) :: X, [] ++ UI p s :: Y)]). apply ImpR. apply ImpRRule_I.
         apply dlCons. 2: apply dlNil. simpl.
         pose (AndL (X, UI p s :: Y) (UI p (nodupseq s)) Top). simpl in g0. apply g0. clear g0.
         apply UI_nodupseq.
      (* If s does not have less usable boxes than sr. *)
      +  rewrite ub_nodupseq in f0. pose (GN_inv_noinit_nolessub _ g J40 f0 J41). rewrite <- e. clear e.
          assert (J0: GUI p s (UI p s)). apply UI_GUI ; auto.
          assert (J1: Gimap (GUI p) (GLR_prems (nodupseq s)) (map (UI p) (GLR_prems (nodupseq s)))). apply Gimap_map. intros.
          apply UI_GUI ; auto.
          assert (J2: Gimap (GN p (GUI p) s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))
          (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))).
          simpl. apply Gimap_map. intros. apply (N_spec p s x0).
          assert (J42: Gimap (GN p (GUI p) s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))
          (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))).
          simpl. apply Gimap_map. intros. apply (N_spec p s x0).
          pose (@GUI_inv_critic_not_init p s _ _ _ J0 c DE H0 J1 J42). rewrite <- e. clear e. simpl.
          remember (Or (list_disj (restr_list_prop p (nodup eq_dec_form (snd s)))) (Or (list_disj (map Neg (restr_list_prop p (nodup eq_dec_form (fst s))))) (list_disj (map Box (map (UI p) (GLR_prems (nodupseq (nodupseq s)))))))) as disj1.
          remember (Or (list_disj (restr_list_prop p (snd s))) (Or (list_disj (map Neg (restr_list_prop p (fst s))))
          (Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq s))))) (Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))))))))
          as disj2.
          apply derI with (ps:=[([] ++ (And disj1 Top) :: X, [] ++ disj2 :: Y)]). apply ImpR. apply ImpRRule_I.
          apply dlCons. 2: apply dlNil. simpl.
          pose (AndL (X, disj2 :: Y) disj1 Top). simpl in g0. apply g0. clear g0.
          pose (@GLS_prv_list_wkn_L [disj1] [] [disj2]).
          pose (@GLS_prv_list_wkn_R (disj1 :: Top :: X) [disj2] []). simpl in g1. simpl in g0.
          assert (GLS_prv (disj1 :: Top :: X, [disj2])).
          assert (GLS_prv ([disj1], [disj2])).
          rewrite Heqdisj2.
          pose (OrR ([disj1],[])). simpl in g2. apply g2 ; clear g2. subst.
          epose (OrL (_,_)). simpl in g2. apply g2 ; clear g2.
          eapply (list_disj_L) with (s:=([],_)). intros. simpl.
          epose (list_disj_wkn_R _ ([A], _) A). simpl in g2. apply g2 ; clear g2. subst.
          apply restr_list_prop_nodup ; auto.
          epose (Id_all_form A [] [] []). simpl in d. apply d.
          epose (OrL (_,_)). simpl in g2. apply g2 ; clear g2.
          apply GLS_prv_wkn_R with
          (s:= ([list_disj (map Neg (restr_list_prop p (nodup eq_dec_form (fst s))))], [Or (list_disj (map Neg (restr_list_prop p (fst s))))
          (Or (list_disj (map Box (map (UI p) (GLR_prems ( nodupseq s)))))
          (Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))))))]))
          (A:=list_disj (restr_list_prop p (snd s))).
          2: epose (wkn_RI (list_disj (restr_list_prop p (snd s))) _ [] _) ; simpl in w ; apply w.
          epose (OrR (_,_)). simpl in g2. apply g2 ; clear g2.
          eapply (list_disj_L) with (s:=([],_)). intros. simpl.
          epose (list_disj_wkn_R _ ([A], _) A). simpl in g2. apply g2 ; clear g2. subst.
          apply InT_map_iff. apply InT_map_iff in H2. destruct H2. exists x0.
          destruct p0 ; split ; auto. apply restr_list_prop_nodup ; auto.
          epose (Id_all_form A [] [] []). simpl in d. apply d. clear g0. clear g1.
          apply GLS_prv_wkn_R with
          (s:= ([list_disj (map Box (map (UI p) (GLR_prems (nodupseq (nodupseq s)))))], [Or (list_disj (map Neg (restr_list_prop p (fst s))))
          (Or (list_disj (map Box (map (UI p) (GLR_prems ( nodupseq s)))))
          (Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))))))]))
          (A:=list_disj (restr_list_prop p (snd s))).
          2: epose (wkn_RI (list_disj (restr_list_prop p (snd s))) _ [] _) ; simpl in w ; apply w.
          epose (OrR (_,_)). simpl in g0. apply g0 ; clear g0.
          apply GLS_prv_wkn_R with
          (s:= ([list_disj (map Box (map (UI p) (GLR_prems (nodupseq (nodupseq s)))))], [(Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq s)))))
          (Diam (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list)))))))]))
          (A:=list_disj (map Neg (restr_list_prop p (fst s)))).
          2: epose (wkn_RI (list_disj (map Neg (restr_list_prop p (fst s)))) _ [] _) ; simpl in w ; apply w.
          epose (OrR (_,_)). simpl in g0. apply g0 ; clear g0.
          eapply (list_disj_L) with (s:=([],_)). intros. simpl.
          apply InT_map_iff in H2. destruct H2. destruct p0 ; subst. apply InT_map_iff in i.
          destruct i. destruct p0 ; subst.
          apply nodupseq_GLR_prems in i. destruct i. destruct p0. destruct p0. subst.
          epose (list_disj_wkn_R _ (_,[_]) (Box (UI p x0))). apply g0 ; clear g0. apply InT_map_iff.
          exists (UI p x0). split ; auto. apply InT_map_iff. exists x0 ; auto.
          simpl. apply derI with (ps:=[([UI p x1;Box (UI p x1);Box (UI p x0)], [UI p x0])]).
          apply GLR. epose (@GLRRule_I _ [Box (UI p x1)] _ [] [_]). simpl in g0. apply g0.
          intros A H3. inversion H3 ; subst. eexists ; auto. inversion H2. apply univ_gen_ext_refl.
          apply dlCons. 2: apply dlNil. eapply (UI_nodupseq_gen x1 x0 p _ []).
          unfold nodupseq ; simpl. rewrite e. rewrite e0 ; auto.
          epose (g0 X0 (Top :: X)). rewrite app_nil_r in g2. apply g2.
          epose (g1 X0 Y). rewrite app_nil_r in g2. apply g2.
  (* If s is not critical. *)
  - assert (J0: GUI p s (UI p s)). apply UI_GUI ; auto.
    assert (J1: Gimap (GUI p) (Canopy (nodupseq s)) (map (UI p) (Canopy (nodupseq s)))). apply Gimap_map. intros.
    apply UI_GUI ; auto.
    pose (@GUI_inv_not_critic p s (UI p s) _ J0 f J1). rewrite <- e.
    apply derI with (ps:=[(list_conj (map (N p sr) (Canopy (nodupseq s))) :: X, list_conj (map (UI p) (Canopy (nodupseq s))) :: Y)]).
    apply ImpR. epose (ImpRRule_I _ _ [] _ []). simpl in i. apply i. apply dlCons. 2: apply dlNil.
    epose (list_conj_R _ (_,_)). simpl in g. apply g. clear g. intros. apply InT_map_iff in H. destruct H.
    destruct p0 ; subst.
    epose (list_conj_wkn_L _ (_,_) (N p sr x)). simpl in g. apply g ; clear g.
    apply InT_map_iff. exists x ; split ; auto.
    pose (Canopy_LexSeq _ _ i). destruct s0.
    exfalso. subst. apply Canopy_critical in i. apply critical_nodupseq in i ; auto.
    assert (J20: LexSeq x s). pose (LexSeq_nodupseq_case s). destruct s0. apply LexSeq_trans with (y:=nodupseq s) ; auto.
    destruct p0. unfold LexSeq ; unfold less_thanS ; unfold GLS_termination_measure.measure ; inversion l ; subst.
    rewrite <- e1 in H2. rewrite H2. apply DLW_wf_lex.lex_skip ; auto. rewrite <- e0 ; auto.
    apply DLW_wf_lex.lex_cons ; auto. rewrite e1 ; auto.
    pose (IH _ J20 sr p X Y). pose (Canopy_critical _ _ i).
    assert (Canopy (nodupseq x) = [nodupseq x]). apply Id_InT_Canopy ; auto.
    apply critical_Seq_InT_Canopy ; auto. rewrite <- critical_nodupseq ; auto.
    rewrite H in g. simpl in g.
    epose (ImpRRule_I _ _ [] _ [] _). simpl in i0.
    pose (@ImpR_inv _ (And (N p sr (nodupseq x)) Top :: X, UI p x :: Y) g i0).
    epose (TopL_remove _ [] (N p sr x :: X)). simpl in g1. apply g1. clear g1.
    epose (GLS_cut_adm (And (N p sr x) Top) [] (Top :: N p sr x :: X) [] (UI p x :: Y)).
    simpl in g1. apply g1 ; clear g1.
    epose (AndR (_,_)). simpl in g1. apply g1 ; clear g1.
    epose (Id_all_form (N p sr x) [Top] X []). simpl in d. apply d.
    epose (TopR _ []). simpl in g1 ; apply g1.
    pose (@GLS_prv_list_wkn_L [And (N p sr x) Top] X (UI p x :: Y)).
    simpl in g1. apply g1 with (l:=(Top :: [N p sr x])) ; clear g1.
    eapply AndL with (s:=(X,_)) ; simpl.
    eapply AndL_inv with (s:=(_,_)) in g0. simpl in g0.
    pose (N_nodupseq sr x p (Top :: X) (UI p x :: Y)).
    epose (GLS_cut_adm (N p sr (nodupseq x)) [] (N p sr x :: Top :: X) [] (UI p x :: Y)).
    simpl in g2. apply g2 ; clear g2 ; auto.
    apply GLS_prv_wkn_L with (s:= (N p sr (nodupseq x) :: Top :: X, UI p x :: Y))
    (A:=N p sr x) ; auto.
    epose (wkn_LI (N p sr x) [_] _ _) ; simpl in w ; apply w. }
  Qed.

  Theorem rec_UI_imp : forall s p X Y, (is_init s -> False) -> (critical_Seq s) -> 
              GLS_prv (X,
        (list_conj (map (N p s) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s)), []%list))))) -->
        (UI p (XBoxed_list (top_boxes (fst s)), []%list)) :: Y).
  Proof.
  intros. apply gen_rec_UI_imp.
  Qed.
