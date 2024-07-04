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
Require Import UIGL_And_Or_rules.
Require Import UIGL_UI_prelims.
Require Import UIGL_UI_inter.


  Section UIPTwo.

  Theorem UI_Two : forall (s : Seq), forall p, GLS_prv ((UI p s) :: fst s, snd s).
  Proof.
  pose (LexSeq_ind (fun s => forall p, GLS_prv (UI p s :: fst s, snd s))).
  apply g. clear g. intros.
  destruct (empty_seq_dec s0).
  (* s is the empty sequent. *)
  { subst ; simpl in *. assert (GUI p ([],[]) Bot). apply GUI_empty_seq ; auto. apply UI_GUI in H.
    rewrite H in *. apply derI with []. apply BotL ; apply (BotLRule_I [] []). apply dlNil. }
  (* s is not the empty sequent. *)
  { destruct (critical_Seq_dec s0).
  (* s0 is a critical sequent *)
  - destruct (dec_init_rules s0).
    (* s0 is an initial sequent *)
    + assert (GLS_prv (fst s0, snd s0)). destruct s0 ; destruct s. destruct s.
      1,3: apply derI with (ps:=[]) ; try apply dlNil.
      apply IdP ; auto. apply BotL ; auto. inversion i ; subst. apply Id_all_form.
      destruct s0. simpl. simpl in X0.
      assert (J0: derrec_height X0 = derrec_height X0). auto.
      assert (J1: wkn_L (UI p (l, l0)) (l, l0) (UI p (l, l0) :: l, l0)).
      assert ((l, l0) = ([] ++ l, l0)). auto. rewrite H.
      assert ((UI p ([] ++ l, l0) :: l, l0) = ([] ++ UI p ([] ++ l, l0) :: l, l0)). auto. rewrite H0. apply wkn_LI.
      pose (GLS_wkn_L X0 J0 J1). destruct s0. auto.
    (* s0 is not an initial sequent *)
   + assert (P1: GLS_prv (list_disj (map Neg (restr_list_prop p (fst s0))) :: fst s0, snd s0)).
      apply list_disj_L. intros. apply InT_map_iff in H. destruct H. destruct p0. subst. unfold Neg.
      apply derI with (ps:=[([] ++ fst s0, [] ++ x :: snd s0);([] ++ ⊥ :: fst s0, [] ++ snd s0)]).
      assert ((x --> ⊥ :: fst s0, snd s0) = ([] ++ x --> ⊥ :: fst s0, [] ++ snd s0)). auto. rewrite H. apply ImpL. apply ImpLRule_I.
      apply dlCons. 2: apply dlCons. 3: apply dlNil. unfold restr_list_prop in i.
      apply InT_In in i. apply In_remove_In_list in i. apply In_list_prop_LF in i. destruct i. apply In_InT in i.
      apply InT_split in i. destruct i. destruct s1. destruct s. rewrite e. assert ([] ++ x0 ++ x :: x1 = x0 ++ x :: x1). auto.
      rewrite H. apply Id_all_form. apply derI with (ps:=[]). apply BotL. apply BotLRule_I. apply dlNil.

      assert (P2: GLS_prv (list_disj (restr_list_prop p (snd s0)) :: fst s0, snd s0)).
      apply list_disj_L. intros. unfold restr_list_prop in H. apply InT_In in H. apply In_remove_In_list in H.
      apply In_list_prop_LF in H. destruct H. apply In_InT in i. apply InT_split in i. destruct i. destruct s1.
      rewrite e. assert (A :: fst s0 = [] ++ A :: fst s0). auto. rewrite H. apply Id_all_form.

      assert (P3: GLS_prv (list_disj (map Box (map (UI p) (GLR_prems (nodupseq s0)))) :: fst s0, snd s0)).
      apply list_disj_L. intros. apply InT_map_iff in H. destruct H. destruct p0. subst. apply InT_map_iff in i.
      destruct i. destruct p0 ; subst. unfold GLR_prems in i. destruct (finite_GLR_premises_of_S (nodupseq s0)).
      simpl in i. apply InT_flatten_list_InT_elem in i. destruct i. destruct p1. apply p0 in i0.
      inversion i0 ; subst. inversion i ; subst. simpl. remember (UI p (XBoxed_list BΓ ++ [Box A], [A])) as Interp.
      apply derI with (ps:=[(XBoxed_list (Box Interp :: top_boxes (fst s0)) ++ [Box A], [A])]). apply GLR.
      assert (InT (Box A) (snd s0)).
      apply In_InT ; apply (nodup_In eq_dec_form) ; rewrite <- H2 ; apply in_or_app ; right ; simpl ; auto.
      apply InT_split in H. destruct H. destruct s. rewrite e. apply GLRRule_I.
      intro. intros. inversion H ; simpl. exists Interp ; auto. apply in_top_boxes in H0. destruct H0.
      destruct s. destruct s. destruct p1 ; subst. eexists ; auto. apply univ_gen_ext_cons.
      apply nobox_top_boxes. apply dlCons. 2: apply dlNil. simpl.
      pose (incl_prv (Interp :: Box Interp :: XBoxed_list BΓ ++ [Box A], [A])). apply g ; clear g ; simpl ; auto. 1-2: intros B HB ; auto.
      inversion HB ; simpl ; subst ; auto. inversion HB ; simpl ; subst ; auto. inversion H0 ; simpl ; subst ; auto.
      apply in_app_or in H3 ; destruct H3. right. right. apply in_or_app ; left. apply In_XBoxed_list_gen in H3.
      destruct H3. apply list_preserv_XBoxed_list. destruct (is_box_is_in_boxed_list _ H3 H1) ; subst.
      apply is_box_in_top_boxes ; auto. 2: eexists ; auto. apply (nodup_In eq_dec_form).
      apply (univ_gen_ext_In _ X0 H3). destruct H3. destruct H3 ; subst. apply XBoxed_list_In.
      apply is_box_in_top_boxes ; auto. 2: eexists ; auto. apply (nodup_In eq_dec_form).
      apply (univ_gen_ext_In _ X0 H3). right. right. apply in_or_app ; auto.
      assert (J2: length (usable_boxes (XBoxed_list BΓ ++ [Box A], [A])) < length (usable_boxes s0)).
      assert (J300: length (usable_boxes (XBoxed_list BΓ ++ [Box A], [A])) < length (usable_boxes (nodupseq s0))).
      apply (GLR_applic_less_usable_boxes i0) ; auto. intro. assert (is_init s0).
      apply is_init_nodupseq ; unfold is_init ; auto. apply f ; auto.
      pose (ub_nodupseq s0). lia.
      assert (J3: LexSeq (XBoxed_list BΓ ++ [Box A], [A]) s0).
      apply DLW_wf_lex.lex_cons ; auto.
      pose (X (XBoxed_list BΓ ++ [Box A], [A]) J3 p). simpl in g. rewrite <- HeqInterp in g.
      assert (J4: derrec_height g = derrec_height g). auto.
      assert (J5: wkn_L (Box Interp) (Interp :: XBoxed_list BΓ ++ [Box A], [A]) (Interp :: Box Interp :: XBoxed_list BΓ ++ [Box A], [A])).
      assert (Interp :: XBoxed_list BΓ ++ [Box A] = [Interp] ++ XBoxed_list BΓ ++ [Box A]) ; auto. rewrite H.
      assert (Interp :: Box Interp :: XBoxed_list BΓ ++ [Box A] = [Interp] ++ Box Interp :: XBoxed_list BΓ ++ [Box A]) ; auto. rewrite H0.
      apply wkn_LI. pose (GLS_wkn_L g J4 J5). destruct s. auto. inversion H0.

      assert (P4: GLS_prv (Diam (list_conj (map (N p s0) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s0)), []))))) :: fst s0, snd s0)).
      apply DiamL_lim with (BΓ:=top_boxes (fst s0)). apply is_Boxed_list_top_boxes. apply nobox_top_boxes.
      apply incl_prv with (s0:=(list_conj (map (N p s0) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s0)), []%list))))
      :: fst ((nodupseq (XBoxed_list (top_boxes (fst s0)), []%list))), []%list)) ; simpl ; auto.
      intros A HIn ; simpl. destruct HIn ; auto. right. apply nodup_In in H ; auto. intros A HA ; inversion HA.
      pose (Canopy_nodupseq_equiprv_genL (nodupseq (XBoxed_list (top_boxes (fst s0)), []%list))
      (list_conj (map (N p s0) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s0)), []%list)))))).
      apply p0. clear p0. intros.
      apply list_conj_wkn_L with (A:=N p s0 leaf).
      apply InT_map_iff. exists leaf ; split ; auto. rewrite <- fixpoint_nodupseq in H ; auto.
      destruct (dec_init_rules leaf).
      (* If leaf is initial. *)
      assert (GLS_prv leaf). destruct leaf. repeat destruct s. 1,3: apply derI with (ps:=[]) ; try apply dlNil.
      apply IdP ; auto. apply BotL ; auto. inversion i. subst. apply Id_all_form.
      rewrite <- fixpoint_nodupseq in H ; auto.
      assert (J0: derrec_height X0 = derrec_height X0). auto.
      assert (J1:wkn_L (N p s0 leaf) leaf (N p s0 leaf :: fst leaf, snd leaf)).
      epose (wkn_LI _ [] (fst leaf) (snd leaf)). destruct leaf ; simpl ; simpl in w. apply w.
      pose (GLS_wkn_L X0 J0 J1). destruct s1. auto.
      (* If leaf is not initial. *)
      destruct (Compare_dec.lt_dec (length (usable_boxes leaf)) (length (usable_boxes s0))).
      (* If leaf has less usable boxes than (XBoxed_list (top_boxes (fst s0)), []). *)
      unfold N. destruct (N_pwc p s0 leaf).
      simpl. assert (J0: is_init leaf -> False). auto.
      assert ((forall (x : Seq) (l m : MPropF), (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x l -> (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x m -> l = m)).
      intros. subst. auto.
      epose (@GN_inv_noinit_lessub p _ _ _ _ g J0 l (UI_spec p leaf)). rewrite <- e ; auto. clear e.
      clear H0. apply X. apply DLW_wf_lex.lex_cons ; auto.
      (* If leaf does not have less usable boxes than (XBoxed_list (top_boxes (fst s0)), []). *)
      unfold N. destruct (N_pwc p s0 leaf).
      simpl. assert (J0: is_init leaf -> False). auto.
      assert ((forall (x : Seq) (l m : MPropF), (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x l -> (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x m -> l = m)).
      intros. subst. auto.
      assert (J1: Gimap (GUI p) (GLR_prems (nodupseq leaf)) (map (UI p) (GLR_prems (nodupseq leaf)))).
      apply Gimap_map ; auto. intros ; apply UI_GUI ; auto.
      pose (@GN_inv_noinit_nolessub p _ _ _ _ g J0 n0 J1).
      rewrite <- e ; auto. clear e. clear J1. clear H0. apply OrL. 2: apply OrL.
      1-3: apply list_disj_L ; intros. 1-2: unfold restr_list_prop in H0.
      apply InT_In in H0. apply In_remove_In_list in H0.
      apply In_list_prop_LF in H0. destruct H0. apply In_InT in i. apply InT_split in i. destruct i. destruct s1.
      rewrite e. assert (A :: fst leaf = [] ++ A :: fst leaf). auto. rewrite H0. apply Id_all_form.
      apply InT_map_iff in H0. destruct H0. destruct p0. subst. unfold Neg.
      apply derI with (ps:=[([] ++ fst leaf, [] ++ x0 :: snd leaf);([] ++ ⊥ :: fst leaf, [] ++ snd leaf)]).
      assert ((x0 --> ⊥ :: fst leaf, snd leaf) = ([] ++ x0 --> ⊥ :: fst leaf, [] ++ snd leaf)). auto. rewrite H0. apply ImpL. apply ImpLRule_I.
      apply dlCons. 2: apply dlCons. 3: apply dlNil.
      apply InT_In in i. apply In_remove_In_list in i. apply In_list_prop_LF in i. destruct i. apply In_InT in i.
      apply InT_split in i. destruct i. destruct s1. rewrite e. assert ([] ++ x1 ++ x0 :: x2 = x1 ++ x0 :: x2). auto.
      rewrite H0. apply Id_all_form. apply derI with (ps:=[]). apply BotL. apply BotLRule_I. apply dlNil.
      apply InT_map_iff in H0. destruct H0. destruct p0. subst. apply InT_map_iff in i. destruct i. destruct p0.
      subst. unfold GLR_prems in i. destruct (finite_GLR_premises_of_S (nodupseq leaf)).
      simpl in i. apply InT_flatten_list_InT_elem in i. destruct i. destruct p1. apply p0 in i0.
      inversion i0 ; subst. inversion i ; subst. simpl. remember (UI p (XBoxed_list BΓ ++ [Box A], [A])) as Interp.
      apply derI with (ps:=[(XBoxed_list (Box Interp :: (top_boxes (fst leaf))) ++ [Box A], [A])]). apply GLR.
      assert (InT (Box A) (snd leaf)).
      apply In_InT ; apply (nodup_In eq_dec_form) ; rewrite <- H3 ; apply in_or_app ; right ; simpl ; auto.
      apply InT_split in H0. destruct H0. destruct s. rewrite e. apply GLRRule_I.
      intro. intros. inversion H0 ; simpl. exists Interp ; auto. apply in_top_boxes in H1. destruct H1.
      destruct s. destruct s. destruct p1 ; subst. eexists ; auto. apply univ_gen_ext_cons.
      apply nobox_top_boxes. apply dlCons. 2: apply dlNil. simpl.
      pose (incl_prv (Interp :: Box Interp :: XBoxed_list BΓ ++ [Box A], [A])). apply g0 ; clear g0 ; simpl ; auto. 1-2: intros B HB ; auto.
      inversion HB ; simpl ; subst ; auto. inversion HB ; simpl ; subst ; auto. inversion H1 ; simpl ; subst ; auto.
      apply in_app_or in H4 ; destruct H4. right. right. apply in_or_app ; left. apply In_XBoxed_list_gen in H4.
      destruct H4. apply list_preserv_XBoxed_list. destruct (is_box_is_in_boxed_list _ H4 H2) ; subst.
      apply is_box_in_top_boxes ; auto. 2: eexists ; auto. apply (nodup_In eq_dec_form).
      apply (univ_gen_ext_In _ X0 H4). destruct H4. destruct H4 ; subst. apply XBoxed_list_In.
      apply is_box_in_top_boxes ; auto. 2: eexists ; auto. apply (nodup_In eq_dec_form).
      apply (univ_gen_ext_In _ X0 H4). right. right. apply in_or_app ; auto.
      assert (J2: length (usable_boxes (XBoxed_list BΓ ++ [Box A], [A])) < length (usable_boxes leaf)).
      assert (J300: length (usable_boxes (XBoxed_list BΓ ++ [Box A], [A])) < length (usable_boxes (nodupseq leaf))).
      apply (GLR_applic_less_usable_boxes i0) ; auto. intro. apply J0. apply is_init_nodupseq ; unfold is_init ; auto.
      pose (ub_nodupseq leaf). lia.
      assert (J3: LexSeq (XBoxed_list BΓ ++ [Box A], [A]) s0).
      apply DLW_wf_lex.lex_cons ; auto. pose (leq_ub_unif s0). apply leq_ub_Canopy in H.
      rewrite <- fixpoint_nodupseq in H.
      assert (J30:length (usable_boxes (XBoxed_list (top_boxes (fst s0)), []%list)) = length (usable_boxes (nodupseq (XBoxed_list (top_boxes (fst s0)), []%list)))).
      apply ub_nodupseq. lia.
      pose (X (XBoxed_list BΓ ++ [Box A], [A]) J3 p). simpl in g0. rewrite <- HeqInterp in g0.
      assert (J4: derrec_height g0 = derrec_height g0). auto.
      assert (J5: wkn_L (Box Interp) (Interp :: XBoxed_list BΓ ++ [Box A], [A]) (Interp :: Box Interp :: XBoxed_list BΓ ++ [Box A], [A])).
      assert (Interp :: XBoxed_list BΓ ++ [Box A] = [Interp] ++ XBoxed_list BΓ ++ [Box A]) ; auto. rewrite H0.
      assert (Interp :: Box Interp :: XBoxed_list BΓ ++ [Box A] = [Interp] ++ Box Interp :: XBoxed_list BΓ ++ [Box A]) ; auto. rewrite H1.
      apply wkn_LI. pose (GLS_wkn_L g0 J4 J5). destruct s. auto. inversion H1.
      remember (fst s0) as LHS.
      assert (GUI p s0
      (Or (list_disj (restr_list_prop p (snd s0)))
      (Or (list_disj (map Neg (restr_list_prop p (fst s0))))
      (Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq s0)))))
      (Diam (list_conj (map (N p s0) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s0)), []%list)))))))))).
      apply GUI_critic_not_init ; auto. 1-2: apply Gimap_map ; intros. apply UI_GUI ; auto.
      apply (@N_spec p s0 x). apply (UI_GUI p s0) in H. rewrite H. rewrite HeqLHS in *. repeat apply OrL ; auto.
  (* s0 is not a critical sequent *)
  - assert (J0: GUI p s0 (UI p s0)). apply UI_GUI ; auto.
    assert (J1: Gimap (GUI p) (Canopy (nodupseq s0)) (map (UI p) (Canopy (nodupseq s0)))). apply Gimap_map. intros.
    apply UI_GUI ; auto.
    pose (@GUI_inv_not_critic p s0 (UI p s0) (map (UI p) (Canopy (nodupseq s0))) J0 f J1). rewrite <- e.
    destruct (LexSeq_nodupseq_case s0).
    + assert (J2: forall s1, InT s1 (Canopy (nodupseq s0)) -> GLS_prv (UI p s1 :: fst s1, snd s1)).
       intros. apply X. pose (Canopy_LexSeq _ _ H). destruct s ; subst ; auto. apply LexSeq_trans with (y:=nodupseq s0) ; auto.
       assert (J3 : forall s1 : Seq, InT s1 (Canopy (nodupseq s0)) -> GLS_prv (list_conj (map (UI p) (Canopy (nodupseq s0))) :: fst s1, snd s1)).
       intros. apply list_conj_wkn_L with (A:=UI p s1) ; auto. apply InT_mapI. exists s1 ; auto.
       apply Canopy_nodupseq_equiprv_genL ; auto.
    + destruct p0. assert (J2: forall s1, InT s1 (Canopy (nodupseq s0)) -> GLS_prv (UI p s1 :: fst s1, snd s1)).
       intros. apply X. pose (Canopy_LexSeq _ _ H). destruct s ; subst ; auto. exfalso.
       apply f. apply critical_nodupseq. apply Canopy_critical in H ; auto. unfold LexSeq in *.
       inversion l ; subst. unfold less_thanS. unfold GLS_termination_measure.measure. rewrite <- e1 in *. rewrite H3. apply DLW_wf_lex.lex_skip ; auto.
       rewrite e0 in *. apply DLW_wf_lex.lex_cons ; auto. inversion H1 ; subst ; auto. inversion H2. apply DLW_wf_lex.lex_cons ; auto. lia.
       assert (J3 : forall s1 : Seq, InT s1 (Canopy (nodupseq s0)) -> GLS_prv (list_conj (map (UI p) (Canopy (nodupseq s0))) :: fst s1, snd s1)).
       intros. apply list_conj_wkn_L with (A:=UI p s1) ; auto. apply InT_mapI. exists s1 ; auto.
       apply Canopy_nodupseq_equiprv_genL ; auto. }
  Qed.

  End UIPTwo.