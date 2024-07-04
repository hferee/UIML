(* First property of uniform interpolation *)

Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import String.
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


  Section UIPOne.

  (* The formula defined by the function UI satisfies all the properties of
      uniform interpolation. *)

  Theorem UI_One : forall s p q, In (Var q) (propvar_subform (UI p (fst s, snd s))) ->
                                                      ((q <> p) * (In (Var q) (propvar_subform_list (fst s ++ snd s)))).
  Proof.
  pose (LexSeq_ind (fun s => forall p q, In (Var q) (propvar_subform (UI p (fst s, snd s))) ->
                                                      ((q <> p) * (In (Var q) (propvar_subform_list (fst s ++ snd s)))))).
  apply p. clear p.
  intros s0 H p q H0. rewrite propvar_subform_list_app.
  destruct (empty_seq_dec s0).
  (* s is the empty sequent. *)
  { subst ; simpl in *. assert (GUI p ([],[]) Bot). apply GUI_empty_seq ; auto. apply UI_GUI in H1.
    rewrite H1 in *. simpl in H0. inversion H0. }
  { destruct (critical_Seq_dec s0).
  (* s0 is a critical sequent *)
  - destruct (dec_init_rules s0).
    (* s0 is an initial sequent *)
    + assert (is_init s0) ; auto.
       assert (GUI p s0 Top). apply GUI_critic_init ; auto. apply UI_GUI in H1.
       destruct s0. simpl in H0. rewrite H1 in H0. simpl in H0. inversion H0.
    (* s0 is not an initial sequent *)
    + remember (fst s0) as LHS.
       assert (GUI p s0
       (Or (list_disj (restr_list_prop p (snd s0)))
       (Or (list_disj (map Neg (restr_list_prop p (fst s0))))
       (Or (list_disj (map Box (map (UI p) (GLR_prems (nodupseq s0)))))
       (Diam (list_conj (map (N p s0) (Canopy (nodupseq (XBoxed_list (top_boxes (fst s0)), []%list)))))))))).
       apply GUI_critic_not_init ; auto. 1-2: apply Gimap_map ; intros. apply UI_GUI ; auto.
       apply (@N_spec p s0 x). apply UI_GUI in H1. destruct s0. rewrite HeqLHS in H0 ; simpl in H0. rewrite H1 in H0. simpl in H0.
       repeat rewrite app_nil_r in H0. clear H1. rewrite HeqLHS ; simpl.
       apply in_app_or in H0. destruct H0.

       apply propvar_subform_list_disj in H0.
       apply propvar_subform_list_restr_list_prop in H0. destruct H0 ; split ; auto. apply in_or_app ; auto.

       apply in_app_or in H0 ; destruct H0. apply propvar_subform_list_disj in H0. apply propvar_subform_list_witness in H0.
       destruct H0. destruct H0. apply in_map_iff in H0. destruct H0. destruct H0 ; subst. simpl in H1.
       rewrite app_nil_r in H1. unfold restr_list_prop in H2. apply in_remove in H2. destruct H2.
       pose (In_list_prop_LF _ _ H0). destruct p0. destruct s. subst. simpl in H1. destruct H1. inversion H1. subst.
       destruct (string_dec q p). exfalso ; apply H2 ; subst ; auto. split ; auto. apply in_or_app ; left.
       apply list_prop_LF_propvar_subform_list in H0 ; auto. inversion H1.

       apply in_app_or in H0 ; destruct H0. apply propvar_subform_list_disj in H0. apply propvar_subform_list_witness in H0.
       destruct H0. destruct H0. apply in_map_iff in H0. destruct H0. destruct H0 ; subst. simpl in H1.
       apply in_map_iff in H2. destruct H2. destruct H0 ; subst. assert (In # q (propvar_subform (UI p (fst x, snd x)))).
       destruct x ; auto. apply H in H0. destruct H0 ; split ; auto.
       unfold GLR_prems in H2. destruct (finite_GLR_premises_of_S (nodupseq (l, l0))). simpl in H2.
       apply In_InT_seqs in H2. apply InT_flatten_list_InT_elem in H2. destruct H2. destruct p1.
       apply p0 in i1. inversion i1 ; subst. inversion i0 ; subst. 2: inversion X0. simpl in i. repeat rewrite propvar_subform_list_app.
       simpl ;  repeat rewrite propvar_subform_list_app.
       repeat rewrite propvar_subform_list_app in i. apply in_app_or in i ; destruct i. apply in_app_or in H0 ; destruct H0.
       apply in_or_app ; left. apply propvar_subform_list_XBoxed_list in H0.
       pose (propvar_subform_list_nobox_gen_ext _ _ X _ H0). apply propvar_subform_list_nodup ; auto.
       simpl in H0. rewrite app_nil_r in H0.
       apply in_or_app ; right. apply propvar_subform_list_nodup ; rewrite <- H4 ; repeat rewrite propvar_subform_list_app ; 
       apply in_or_app ; right ; apply in_or_app ; auto. simpl in H0. rewrite app_nil_r in H0.
       apply in_or_app ; right. apply propvar_subform_list_nodup ; rewrite <- H4 ; repeat rewrite propvar_subform_list_app ; 
       apply in_or_app ; right ; apply in_or_app ; auto.
       unfold GLR_prems in H2. destruct (finite_GLR_premises_of_S (nodupseq (l, l0))). simpl in H2.
       apply In_InT_seqs in H2. apply InT_flatten_list_InT_elem in H2. destruct H2. destruct p1.
       apply p0 in i0. inversion i0 ; subst. inversion i ; subst. 2: inversion X0. apply DLW_wf_lex.lex_cons ; auto.
       pose (GLR_applic_less_usable_boxes i0). rewrite <- ub_nodupseq in l1. apply l1 ; auto.
       assert (is_init (l,l0) -> False) ; auto. pose (is_init_nodupseq (l,l0)). destruct p1. intro.
       assert (is_init (nodupseq (l, l0))) ; auto. unfold is_init ; auto.

       apply propvar_subform_list_conj in H0. apply propvar_subform_list_witness in H0.
       destruct H0. destruct H0. apply in_map_iff in H0. destruct H0. destruct H0 ; subst.

       pose (@N_spec p (l,l0) x0). destruct (dec_init_rules x0).
       (* If x0 is initial. *)
       assert (is_init x0) ; unfold is_init ; auto. pose (GN_inv_init _ g). rewrite <- e in H1 ; auto. simpl in H1. inversion H1.
       (* If x0 is not initial. *)
       destruct (Compare_dec.lt_dec (length (usable_boxes x0)) (length (usable_boxes (l, l0)))).
       (* If x0 has less usable boxes than (XBoxed_list (top_boxes l), []). *)
       assert ((forall (x : Seq) (l m : MPropF), (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x l -> (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x m -> l = m)).
       intros. subst. auto. assert ((is_init x0 -> False)) ; auto.
       epose (@GN_inv_noinit_lessub _ _ _ _ _ g H3 l1 (UI_spec p x0)). rewrite <- e in H1 ; auto. clear e.
       assert (In # q (propvar_subform (UI p (fst x0, snd x0)))). destruct x0 ; simpl ; auto.
       apply H in H4. destruct H4 ; split ; auto.
       apply propvar_subform_list_Canopy with (A:=# q) in H2 ; auto. simpl in H2. rewrite app_nil_r in H2.
       apply in_or_app ; left.
       assert (J30: In # q (propvar_subform_list (XBoxed_list (top_boxes l)))). apply propvar_subform_list_nodup ; auto.
       apply propvar_subform_list_XBoxed_list in J30. apply propvar_subform_list_top_boxes ; auto.
       apply DLW_wf_lex.lex_cons ; auto.
       (* If x0 does not have less usable boxes than (XBoxed_list (top_boxes l), []). *)
       assert ((forall (x : Seq) (l m : MPropF), (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x l -> (fun (s1 : Seq) (A : MPropF) => UI p s1 = A) x m -> l = m)).
       intros. subst. auto.
       assert (J1: Gimap (GUI p) (GLR_prems (nodupseq x0)) (map (UI p) (GLR_prems (nodupseq x0)))).
       apply Gimap_map ; auto. intros ; apply UI_GUI ; auto. assert ((is_init x0 -> False)) ; auto.
       pose (@GN_inv_noinit_nolessub p _ _ _ _ g H3 n0 J1).
       rewrite <- e in H1. clear e. clear J1. clear H0. simpl in H1. repeat rewrite app_nil_r in H1. apply in_app_or in H1.
       destruct H1. apply propvar_subform_list_disj in H0. apply propvar_subform_list_restr_list_prop in H0. destruct H0 ; split ; auto.
       apply propvar_subform_list_Canopy with (A:=# q) in H2 ; auto. simpl in H2. rewrite app_nil_r in H2.
       apply in_or_app ; left.
       assert (J30: In # q (propvar_subform_list (XBoxed_list (top_boxes l)))). apply propvar_subform_list_nodup ; auto.
       apply propvar_subform_list_XBoxed_list in J30. apply propvar_subform_list_top_boxes ; auto.
       rewrite propvar_subform_list_app. apply in_or_app ;auto.
       apply in_app_or in H0. destruct H0. apply propvar_subform_list_disj in H0. apply propvar_subform_list_witness in H0.
       destruct H0. destruct H0. apply In_InT in H0. apply InT_map_iff in H0. destruct H0. destruct p0 ; subst. simpl in H1.
       rewrite app_nil_r in H1. unfold restr_list_prop in i. apply InT_In in i. apply in_remove in i. destruct i.
       pose (In_list_prop_LF _ _ H0). destruct p0. destruct s. subst. simpl in H1. destruct H1. inversion H1. subst.
       destruct (string_dec q p). exfalso ; apply H4 ; subst ; auto. split ; auto. apply in_or_app ; left.
       apply list_prop_LF_propvar_subform_list in H0 ; auto. apply propvar_subform_list_Canopy with (A:=# q) in H2 ; auto.
       simpl in H2. rewrite app_nil_r in H2.
       assert (J30: In # q (propvar_subform_list (XBoxed_list (top_boxes l)))). apply propvar_subform_list_nodup ; auto.
       apply propvar_subform_list_XBoxed_list in J30. apply propvar_subform_list_top_boxes ; auto.
       rewrite propvar_subform_list_app. apply in_or_app ;auto. inversion H1.
       apply propvar_subform_list_disj in H0. apply propvar_subform_list_witness in H0.
       destruct H0. destruct H0. apply In_InT in H0. apply InT_map_iff in H0. destruct H0. destruct p0 ; subst. simpl in H1.
       apply InT_map_iff in i. destruct i. destruct p0 ; subst. assert (In # q (propvar_subform (UI p (fst x, snd x)))).
       destruct x ; simpl ; auto. apply H in H0. destruct H0 ; split ; auto.
       unfold GLR_prems in i. destruct (finite_GLR_premises_of_S (nodupseq x0)). simpl in i.
       apply InT_flatten_list_InT_elem in i. destruct i. destruct p1.
       apply p0 in i1. inversion i1 ; subst. inversion i ; subst. 2: inversion H4. simpl in i0.
       repeat rewrite propvar_subform_list_app in i0. simpl in i0. repeat rewrite app_nil_r in i0.
       apply in_app_or in i0 ; destruct i0. apply in_app_or in H0 ; destruct H0.
       apply in_or_app ; left. apply propvar_subform_list_XBoxed_list in H0.
       pose (propvar_subform_list_nobox_gen_ext _ _ X _ H0). rewrite propvar_subform_list_nodup in i0 ; auto.
       apply propvar_subform_list_Canopy with (A:=# q) in H2 ; auto. simpl in H2. rewrite app_nil_r in H2.
       assert (J30: In # q (propvar_subform_list (XBoxed_list (top_boxes l)))). apply propvar_subform_list_nodup ; auto.
       apply propvar_subform_list_XBoxed_list in J30. apply propvar_subform_list_top_boxes ; auto.
       rewrite propvar_subform_list_app. apply in_or_app ;auto.
       apply propvar_subform_list_Canopy with (A:=# q) in H2 ; auto. simpl in H2. rewrite app_nil_r in H2.
       assert (J30: In # q (propvar_subform_list (XBoxed_list (top_boxes l)))). apply propvar_subform_list_nodup ; auto.
       apply propvar_subform_list_XBoxed_list in J30. apply in_or_app ; left. apply propvar_subform_list_top_boxes ; auto.
       simpl. repeat rewrite propvar_subform_list_app ; simpl. apply in_or_app ; right. apply propvar_subform_list_nodup ; auto.
       rewrite <- H6. repeat rewrite propvar_subform_list_app ; simpl. apply in_or_app ; right ; apply in_or_app ; auto.
       apply propvar_subform_list_Canopy with (A:=# q) in H2 ; auto. simpl in H2. rewrite app_nil_r in H2.
       assert (J30: In # q (propvar_subform_list (XBoxed_list (top_boxes l)))). apply propvar_subform_list_nodup ; auto.
       apply propvar_subform_list_XBoxed_list in J30. apply in_or_app ; left. apply propvar_subform_list_top_boxes ; auto.
       simpl. repeat rewrite propvar_subform_list_app ; simpl. apply in_or_app ; right. apply propvar_subform_list_nodup ; auto.
       rewrite <- H6. repeat rewrite propvar_subform_list_app ; simpl. apply in_or_app ; right ; apply in_or_app ; auto.
       apply DLW_wf_lex.lex_cons ; auto. unfold GLR_prems in i. destruct (finite_GLR_premises_of_S (nodupseq x0)). simpl in i.
       apply InT_flatten_list_InT_elem in i. destruct i. destruct p1.
       apply p0 in i0. inversion i0 ; subst. inversion i ; subst. 2: inversion H5.
       pose (GLR_applic_less_usable_boxes i0). rewrite <- ub_nodupseq in l1.
       apply In_InT_seqs in H2 ; apply leq_ub_Canopy in H2. pose (set_leq_ub_unif (l, l0)). simpl in l1. simpl in l2.
       assert (length (usable_boxes (XBoxed_list BΓ ++ [Box A], [A])) < length (usable_boxes x0)). apply l1 ; auto.
       pose (is_init_nodupseq x0). destruct p1. intro. assert (is_init (nodupseq x0)) ; auto. unfold is_init ; auto.
       lia.
  (* s0 is not a critical sequent *)
  - assert (GUI p s0 (list_conj (map (UI p) (Canopy (nodupseq s0))))). apply GUI_not_critic ; auto.
    apply Gimap_map ; intros ; apply UI_GUI ; auto. apply UI_GUI in H1. destruct s0.
    simpl in H0. rewrite H1 in H0. apply propvar_subform_list_conj in H0.
    apply propvar_subform_list_witness in H0. destruct H0. destruct H0. apply in_map_iff in H0.
    destruct H0. destruct H0 ; subst. simpl. assert (In # q (propvar_subform (UI p (fst x0, snd x0)))).
    destruct x0 ; auto. pose (In_InT_seqs _ _ H3). apply Canopy_LexSeq in i. destruct i ; subst.
    simpl in H0. exfalso. apply f. apply In_InT_seqs in H3 ; apply Canopy_critical in H3 ; auto.
    apply critical_nodupseq ; auto.
    apply H in H0 ; auto. destruct H0 ; split ; auto.
    apply propvar_subform_list_Canopy with (A:=# q) in H3 ; auto.
    simpl in H3 ; rewrite propvar_subform_list_app in H3 ; auto.
    apply in_app_or in H3 ; destruct H3. apply in_or_app ; left. apply propvar_subform_list_nodup ; auto.
    apply in_or_app ; right. apply propvar_subform_list_nodup ; auto.
    apply LexSeq_nodupseq ; auto. }
  Qed.

  End UIPOne.