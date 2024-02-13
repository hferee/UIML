(* First property of uniform interpolation *)

Require Import List.
Export ListNotations.
Require Import PeanoNat Arith.
Require Import Lia.
Require Import String.

Require Import general_export.

Require Import KS_export.

Require Import UIK_Def_measure.
Require Import UIK_Canopy.
Require Import UIK_irred_short.
Require Import UIK_braga.
Require Import UIK_UI_prelims.

  Section UIPOne.

  (* The formula defined by the function UI satisfies all the properties of
      uniform interpolation. *)

  Theorem UI_One : forall s p q, In (# q) (propvar_subform (UI p (fst s, snd s))) ->
                                                      ((q <> p) * (In (# q) (propvar_subform_list (fst s ++ snd s)))).
  Proof.
  intro s. remember (measure s) as n. revert Heqn. revert s. revert n.
  induction n as [n IH] using (well_founded_induction_type lt_wf).
  intros s Heqn p q H0. rewrite propvar_subform_list_app.
  destruct (empty_seq_dec s).
  (* s is the empty sequent. *)
  { subst ; simpl in *. assert (H : GUI p ([],[]) Bot) by (apply GUI_empty_seq ; auto). apply UI_GUI in H.
    rewrite H in *. simpl in H0. inversion H0. }
  (* s is not the empty sequent. *)
  { destruct (critical_Seq_dec s).
  (* s is a critical sequent *)
  - destruct (dec_KS_init_rules s).
    (* s is an initial sequent *)
    + assert (is_init s) ; auto.
       assert (H1 : GUI p s Top) by (apply GUI_critic_init ; auto). apply UI_GUI in H1.
       destruct s. simpl in H0. rewrite H1 in H0. simpl in H0. inversion H0.
    (* s is not an initial sequent *)
    + remember (fst s) as LHS.
       assert (H1 : GUI p s
       (Or (list_disj (restr_list_prop p (snd s)))
       (Or (list_disj (map Neg (restr_list_prop p (fst s))))
       (Or (list_disj (map Box (map (UI p) (KR_prems s))))
       (Diam (UI p (unboxed_list (top_boxes (fst s)), []%list))))))).
       apply GUI_critic_not_init ; auto. apply Gimap_map ; intros. 1-2: apply UI_GUI ; auto.
       destruct s. simpl in *. apply UI_GUI in H1. simpl in HeqLHS. subst. rewrite H1 in H0. simpl in H0.
       repeat rewrite <- app_nil_end in H0. clear H1.
       apply in_app_or in H0. destruct H0 as [H0 | H0].

       apply propvar_subform_list_disj in H0.
       apply propvar_subform_list_restr_list_prop in H0. destruct H0 ; split ; auto. apply in_or_app ; auto.

       apply in_app_or in H0 ; destruct H0 as [H0 | H0]. apply propvar_subform_list_disj in H0. apply propvar_subform_list_witness in H0.
       destruct H0. destruct H.  apply in_map_iff in H. destruct H. destruct H ; subst. simpl in H0.
       rewrite <- app_nil_end in H0. unfold restr_list_prop in H1. apply in_remove in H1. destruct H1.
       pose (In_list_prop_LF _ _ H). destruct p0. destruct s. subst. simpl in H0. destruct H0. inversion H0. subst.
       destruct (string_dec q p). exfalso ; apply H1 ; subst ; auto. split ; auto. apply in_or_app ; left.
       apply list_prop_LF_propvar_subform_list in H ; auto. inversion H0.

       apply in_app_or in H0 ; destruct H0. apply propvar_subform_list_disj in H. apply propvar_subform_list_witness in H.
       destruct H. destruct H. apply in_map_iff in H. destruct H. destruct H ; subst. simpl in H0.
       apply in_map_iff in H1. destruct H1. destruct H ; subst. assert (In # q (propvar_subform (UI p (fst x, snd x)))).
       destruct x ; auto.
       unfold KR_prems in H1. destruct (finite_KR_premises_of_S (l, l0)). simpl in H1.
       apply In_InT_seqs in H1. apply InT_flatten_list_InT_elem in H1. destruct H1. destruct p1.
       apply p0 in i0. inversion i0 ; subst. inversion i ; subst. 2: inversion X0. simpl in H. repeat rewrite propvar_subform_list_app.
       simpl ;  repeat rewrite propvar_subform_list_app.
       assert (J0: measure (unboxed_list BΓ, [A]) < measure (l, Δ0 ++ Box A :: Δ1)).
       unfold measure. simpl. repeat rewrite size_LF_dist_app. simpl.
       pose (size_nobox_gen_ext _ _ X). simpl in l.
       pose (size_unboxed BΓ). lia.
       assert (J1: measure (unboxed_list BΓ, [A]) = measure (unboxed_list BΓ, [A])). auto.
       pose (IH _ J0 _ J1 _ _ H0). destruct p1. split ; auto. simpl in i1.
       rewrite propvar_subform_list_app in i1. apply in_app_or in i1. destruct i1.
       apply in_or_app ; left. apply propvar_subform_list_unboxed_list in H1.
       pose (propvar_subform_list_nobox_gen_ext _ _ X). simpl in i1. apply i1 ; auto.
       simpl in H1. rewrite <- app_nil_end in H1.
       apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.

       destruct l ; subst ; simpl in *.
       { assert (GUI p ([],[]) Bot). apply GUI_empty_seq ; auto. apply UI_GUI in H0.
         rewrite H0 in *. simpl in H. inversion H. }
       { assert (J0: measure (unboxed_list (top_boxes (m :: l)), []%list) < measure (m :: l, l0)).
         unfold measure. simpl. destruct m ; simpl.
         1-4: pose (size_unboxed (top_boxes l)) ; pose (size_top_boxes l) ; lia.
         assert (J1: measure (unboxed_list (top_boxes (m :: l)), []%list) = measure (unboxed_list (top_boxes (m :: l)), []%list)). auto.
         pose (IH _ J0 _ J1). simpl in p0. pose (p0 _ _ H). destruct p1. split ; auto. simpl in i. clear p0.
         rewrite propvar_subform_list_app in i. apply in_app_or in i. destruct i.
         apply in_or_app ; left. apply propvar_subform_list_unboxed_list in H0.
         apply in_or_app. destruct m ; simpl in H0 ; auto.
         1-3: right ; apply propvar_subform_list_top_boxes ; auto. simpl.
         apply in_app_or in H0 ; destruct H0 ; auto. right. apply propvar_subform_list_top_boxes ; auto.
         simpl in H0. inversion H0. }
  (* s is not a critical sequent *)
  - assert (H1 : GUI p s (list_conj (map (UI p) (Canopy s)))). apply GUI_not_critic ; auto.
    apply Gimap_map ; intros ; apply UI_GUI ; auto. apply UI_GUI in H1. destruct s.
    simpl in H0. rewrite H1 in H0. apply propvar_subform_list_conj in H0.
    apply propvar_subform_list_witness in H0. destruct H0 as [s [H0 H3]].
    apply in_map_iff in H0.
    destruct H0 as [x0 H0]. destruct H0 as [H0 Hc]; subst. simpl.
    assert (H2 : In # q (propvar_subform (UI p (fst x0, snd x0)))) by (destruct x0 ; auto).
    pose (i := In_InT_seqs _ _ Hc). apply Canopy_measure in i. destruct i ; subst.
    simpl in *. exfalso. apply f. apply In_InT_seqs in Hc ; apply Canopy_critical in Hc ; auto.
    assert (measure x0 = measure x0) ; auto.
    pose (IH _ l1 _ H _ _ H2). destruct p0 ; split ; auto.
    apply propvar_subform_list_Canopy with (A:=# q) in Hc ; auto.
    simpl in H3 ; rewrite propvar_subform_list_app in Hc ; auto. }
  Qed.

  End UIPOne.