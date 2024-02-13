Require Import List.
Export ListNotations.
Require Import PeanoNat Arith.
Require Import Lia.

Require Import general_export.

Require Import KS_export.

Require Import UIK_Def_measure.
Require Import UIK_Canopy.
Require Import UIK_irred_short.
Require Import UIK_braga.
Require Import UIK_UI_prelims.


  Section UIPTwo.

  Theorem UI_Two : forall (s : Seq), forall p, KS_prv ((UI p s) :: fst s, snd s).
  Proof.
  intro s. remember (measure s) as n. revert Heqn. revert s. revert n.
  induction n as [n IH] using (well_founded_induction_type lt_wf).
  intros.
  destruct (empty_seq_dec s).
  (* s is the empty sequent. *)
  { subst ; simpl in *. assert (GUI p ([],[]) Bot). apply GUI_empty_seq ; auto. apply UI_GUI in H.
    rewrite H in *. apply derI with []. apply BotL ; apply (BotLRule_I [] []). apply dlNil. }
  (* s is not the empty sequent. *)
  { destruct (critical_Seq_dec s).
  (* s is a critical sequent *)
  - destruct (dec_KS_init_rules s).
    (* s is an initial sequent *)
    + assert (KS_prv (fst s, snd s)). destruct s0. destruct s.
      1,2: apply derI with (ps:=[]) ; try apply dlNil.
      apply IdP ; auto. destruct s ; apply BotL ; auto.
      destruct s. simpl. simpl in X.
      assert (J0: derrec_height X = derrec_height X). auto.
      assert (J1: wkn_L (UI p (l, l0)) (l, l0) (UI p (l, l0) :: l, l0)).
      replace (l, l0) with ([] ++ l, l0) by auto.
      replace (UI p ([] ++ l, l0) :: l, l0) with ([] ++ UI p ([] ++ l, l0) :: l, l0) by auto.
      apply wkn_LI.
      pose (KS_wkn_L _ _ X J0 _ _ J1). destruct s. auto.
    (* s is not an initial sequent *)
    +  assert (P1: KS_prv (list_disj (map Neg (restr_list_prop p (fst s))) :: fst s, snd s)).
        apply list_disj_L. intros A H0. apply InT_map_iff in H0. destruct H0. destruct p0. subst. unfold Neg.
        apply derI with (ps:=[([] ++ fst s, [] ++ x :: snd s);([] ++ Bot :: fst s, [] ++ snd s)]).
        assert ((x --> Bot :: fst s, snd s) = ([] ++ x --> Bot :: fst s, [] ++ snd s)). auto. rewrite H. apply ImpL. apply ImpLRule_I.
        apply dlCons. 2: apply dlCons. 3: apply dlNil. unfold restr_list_prop in i.
        apply InT_In in i. apply In_remove_In_list in i. apply In_list_prop_LF in i. destruct i. apply In_InT in i.
        apply InT_split in i. destruct i. destruct s1. destruct s. rewrite e. assert ([] ++ x0 ++ x :: x1 = x0 ++ x :: x1). auto.
        rewrite H. apply Id_all_form. apply derI with (ps:=[]). apply BotL. apply BotLRule_I. apply dlNil.

         assert (P2: KS_prv (list_disj (restr_list_prop p (snd s)) :: fst s, snd s)).
         apply list_disj_L. intros A H0. unfold restr_list_prop in H0. apply InT_In in H0. apply In_remove_In_list in H0.
         apply In_list_prop_LF in H0. destruct H0 as [s0 i]. apply In_InT in i. apply InT_split in i. destruct i. destruct s1.
         rewrite e. replace (A :: fst s) with ([] ++ A :: fst s) by auto. apply Id_all_form.

         assert (P3: KS_prv (list_disj (map Box (map (UI p) (KR_prems s))) :: fst s, snd s)).
         apply list_disj_L. intros A H0. apply InT_map_iff in H0. destruct H0. destruct p0. subst. apply InT_map_iff in i.
         destruct i. destruct p0 ; subst. unfold KR_prems in i. destruct (finite_KR_premises_of_S s).
         simpl in i. apply InT_flatten_list_InT_elem in i. destruct i. destruct p1. apply p0 in i0.
         inversion i0 ; subst. inversion i ; subst. simpl. remember (UI p (unboxed_list BΓ, [A])) as Interp.
         apply derI with (ps:=[(unboxed_list (Box Interp :: BΓ), [A])]). apply KR. apply KRRule_I.
         intro. intros. inversion H0 ; simpl. exists Interp ; auto. apply H ; auto. apply univ_gen_ext_cons ; auto.
         apply dlCons. 2: apply dlNil. simpl.
         assert (J0: measure (unboxed_list BΓ, [A]) < measure (Γ0, Δ0 ++ Box A :: Δ1)).
         unfold measure. simpl. repeat rewrite size_LF_dist_app. simpl.
         pose (size_nobox_gen_ext _ _ X). simpl in l.
         pose (size_unboxed BΓ). lia.
         assert (J30: measure (unboxed_list BΓ, [A]) = measure (unboxed_list BΓ, [A])) ; auto.
         pose (IH _ J0 _ J30 p). simpl in k. rewrite <- HeqInterp in k. auto. inversion H1.

         assert (P4: KS_prv (Diam (UI p (unboxed_list (top_boxes (fst s)), [])) :: fst s, snd s)).
         { destruct s. destruct l ; subst.
           - assert (GUI p ([],[]) Bot). apply GUI_empty_seq ; auto. apply UI_GUI in H. simpl in *. rewrite H in *.
             apply DiamL_lim with (BΓ:=[]). intros A HA ; inversion HA. apply univ_gen_ext_nil. apply derI with [].
             apply BotL. apply (BotLRule_I []). apply dlNil.
           - apply DiamL_lim with (BΓ:=top_boxes (m :: l)). apply is_Boxed_list_top_boxes. apply nobox_top_boxes.
             assert (J0: measure (unboxed_list (top_boxes (m :: l)), []%list) < measure (m :: l, l0)).
             unfold measure. simpl. simpl in * ; simpl. subst ; simpl.
             destruct m ; simpl ; subst ; pose (size_unboxed (top_boxes l)) ; pose (size_top_boxes l) ; lia.
             assert (J30: measure (unboxed_list (top_boxes (m :: l)), []%list) = measure (unboxed_list (top_boxes (m :: l)), []%list)) ; auto.
             subst. pose (IH _ J0 _ J30 p). simpl in k. auto. }

         assert (H0: GUI p s
         (Or (list_disj (restr_list_prop p (snd s)))
         (Or (list_disj (map Neg (restr_list_prop p (fst s))))
         (Or (list_disj (map Box (map (UI p) (KR_prems s))))
         (Diam (UI p (unboxed_list (top_boxes (fst s)), []%list))))))).
         apply GUI_critic_not_init ; auto. apply Gimap_map ; intros. 1-2: apply UI_GUI ; auto.
         apply (UI_GUI p s) in H0. rewrite H0. repeat apply OrL ; auto.
  (* s is not a critical sequent *)
  - assert (J0: GUI p s (UI p s)). apply UI_GUI ; auto.
    assert (J1: Gimap (GUI p) (Canopy s) (map (UI p) (Canopy s))). apply Gimap_map. intros.
    apply UI_GUI ; auto.
    pose (@GUI_inv_not_critic p s (UI p s) (map (UI p) (Canopy s)) J0 f J1). rewrite <- e.
    assert (J2: forall s1, InT s1 (Canopy s) -> KS_prv (UI p s1 :: fst s1, snd s1)).
    intros s1 H0. apply IH with (y:= measure s1) ; auto. pose (Canopy_measure _ _ H0). destruct s0 ; subst ; auto. exfalso.
    apply f. apply Canopy_critical in H0 ; auto.
    assert (J3 : forall s1 : Seq, InT s1 (Canopy s) -> KS_prv (list_conj (map (UI p) (Canopy s)) :: fst s1, snd s1)).
    intros. apply list_conj_wkn_L with (A:=UI p s1) ; auto. apply InT_mapI. exists s1 ; auto.
    apply Canopy_equiprv_genL ; auto. }
  Qed.

  End UIPTwo.