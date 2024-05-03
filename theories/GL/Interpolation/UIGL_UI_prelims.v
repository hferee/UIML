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
Require Import UIGL_PermutationT.
Require Import UIGL_PermutationTS.
Require Import UIGL_And_Or_rules.
Require Import UIGL_Canopy_nodupseq_perm.

  Section Prop_Subform.

  (* This is copied from the Craig interpolation file. Make a syntax file for interpolations. *)

  Fixpoint propvar_subform (A : MPropF) : list MPropF :=
  match A with
    | Var p => (Var p) :: nil 
    | Bot => nil
    | Imp B C => (propvar_subform B) ++ ( propvar_subform C)
    | Box B => ( propvar_subform B)
  end.

  Fixpoint propvar_subform_list (l : list MPropF) : list MPropF :=
  match l with
    | nil => nil
    | A :: t => (propvar_subform A) ++ (propvar_subform_list t)
  end.

  (* Lemmas about propvar_subform_list. *)

  Lemma propvar_subform_list_app: forall l0 l1,
        propvar_subform_list (l0 ++ l1) = (propvar_subform_list l0) ++ (propvar_subform_list l1).
  Proof.
  induction l0.
  - simpl. auto.
  - intros. simpl. rewrite (IHl0). rewrite <- app_assoc ; auto.
  Qed.

  Lemma propvar_subform_list_XBoxed_list : forall l A, In A (propvar_subform_list (XBoxed_list l)) -> In A (propvar_subform_list l).
  Proof.
  induction l.
  - auto.
  - simpl. intros. apply in_app_or in H. destruct H. apply in_or_app ; left. destruct a ; auto.
    apply in_app_or in H. destruct H. apply in_or_app ; auto. apply in_or_app ; right ; auto.
  Qed.

  Lemma propvar_subform_list_nobox_gen_ext : forall l0 l1, nobox_gen_ext l0 l1 ->
            (forall A, In A (propvar_subform_list l0) -> In A (propvar_subform_list l1)).
  Proof.
  intros l0 l1 H. induction H ; auto.
  - simpl ; intros. apply in_or_app. apply in_app_or in H0 ; destruct H0 ; auto.
  - simpl ; intros. apply in_or_app ; auto.
  Qed.

  Lemma propvar_subform_list_top_boxes : forall l A, In A (propvar_subform_list (top_boxes l)) -> In A (propvar_subform_list l).
  Proof.
  induction l ; simpl ; intros ; auto. destruct a ; simpl in H ; auto. 1-2: apply in_or_app ; apply IHl in H ; auto.
  apply in_or_app ; apply in_app_or in H ; destruct H ; simpl ; auto.
  Qed.

  Lemma propvar_subform_list_conj : forall l A,
            In A (propvar_subform (list_conj l)) -> In A (propvar_subform_list l).
  Proof.
  induction l ; simpl ; intros ; auto. repeat rewrite app_nil_r in H.
  apply in_app_or in H. apply in_or_app. destruct H ; auto.
  Qed.

  Lemma propvar_subform_list_disj : forall l A,
            In A (propvar_subform (list_disj l)) -> In A (propvar_subform_list l).
  Proof.
  induction l ; simpl ; intros ; auto. repeat rewrite app_nil_r in H.
  apply in_app_or in H. apply in_or_app. destruct H ; auto.
  Qed.

  Lemma propvar_subform_list_witness : forall l A,
            In A (propvar_subform_list l) -> (exists B, In B l /\ In A (propvar_subform B)).
  Proof.
  induction l ; simpl ; intros ; auto. inversion H. apply in_app_or in H. destruct H.
  exists a ; auto. apply IHl in H. destruct H. exists x  ; firstorder.
  Qed.


  Lemma propvar_subform_list_witnessT : forall l A,
            InT A (propvar_subform_list l) -> (existsT2 B, (InT B l) * (InT A (propvar_subform B))).
  Proof.
  induction l ; simpl ; intros ; auto. inversion H. apply InT_app_or in H. destruct H.
  exists a ; auto. split ; auto. apply InT_eq. apply IHl in i. destruct i. exists x  ; firstorder. apply InT_cons ; auto.
  Qed.

  Lemma propvar_subform_list_Canopy : forall s ir A,
            In ir (Canopy s) ->
            In A (propvar_subform_list (fst ir ++ snd ir)) ->
            In A (propvar_subform_list (fst s ++ snd s)).
  Proof.
  intros s ; induction on s as IHs with measure (n_imp_subformS s).
  intros. remember (finite_ImpRules_premises_of_S s) as H1.
  destruct H1. destruct x.
  - assert (Canopy s = [s]). apply irred_nil. unfold inv_prems. rewrite <- HeqH1.
    simpl. auto. rewrite H1 in H. inversion H. subst. auto. inversion H2.
  - apply In_InT_seqs in H. apply fold_Canopy in H. destruct H ; subst ; auto.
    destruct s0. destruct p0. unfold inv_prems in i. destruct (finite_ImpRules_premises_of_S s).
    simpl in i. apply InT_flatten_list_InT_elem in i. destruct i. destruct p1. apply p0 in i1.
    apply IHs with (y:=x0) in H0. 3: apply InT_In ; auto.
    destruct i1. inversion i1 ; subst. simpl. inversion i ; subst. 2: inversion H1. simpl in H0.
    repeat rewrite <- app_assoc in H0. repeat rewrite <- app_assoc.
    repeat rewrite propvar_subform_list_app in H0. repeat rewrite propvar_subform_list_app.
    simpl in H0. simpl. repeat rewrite <- app_assoc in H0. repeat rewrite <- app_assoc.
    apply in_or_app. apply in_app_or in H0 ; destruct H0 ; auto. right. apply in_or_app.
    apply in_app_or in H ; destruct H ; auto. right ; apply in_or_app ;  right ; apply in_or_app ; auto.
    apply in_app_or in H ; destruct H ; auto. right. apply in_or_app ; apply in_app_or in H ; destruct H ; auto.
    right ; apply in_or_app ; right ; auto.
    inversion i1 ; subst. simpl. inversion i ; subst. simpl in H0.
    repeat rewrite <- app_assoc in H0. repeat rewrite <- app_assoc.
    repeat rewrite propvar_subform_list_app in H0. repeat rewrite propvar_subform_list_app.
    simpl in H0. simpl. repeat rewrite <- app_assoc in H0. repeat rewrite <- app_assoc.
    apply in_or_app. apply in_app_or in H0 ; destruct H0 ; auto. right. apply in_or_app.
    apply in_app_or in H ; destruct H ; auto. right ; apply in_or_app ;  right ; apply in_or_app ; auto.
    apply in_app_or in H ; destruct H ; auto. right. apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
    apply in_app_or in H ; destruct H ; auto. right ; apply in_or_app ; right ; apply in_or_app ; right ; apply in_or_app ; auto.
    inversion H1 ; subst. 2: inversion H2. simpl in H0.
    repeat rewrite <- app_assoc in H0. repeat rewrite <- app_assoc.
    repeat rewrite propvar_subform_list_app in H0. repeat rewrite propvar_subform_list_app.
    simpl in H0. simpl. repeat rewrite <- app_assoc in H0. repeat rewrite <- app_assoc.
    apply in_or_app. apply in_app_or in H0 ; destruct H0 ; auto. right. apply in_or_app.
    apply in_app_or in H ; destruct H ; auto. right ; apply in_or_app ; auto.
    apply in_app_or in H ; destruct H ; auto. right. apply in_or_app ; right ; apply in_or_app ; auto.
    right ; apply in_or_app ; right ; apply in_or_app ; right ; auto.
    destruct i1. inversion i1 ; subst. simpl. inversion i ; subst. 2: inversion H1. unfold n_imp_subformS ; simpl.
    repeat rewrite n_imp_subformLF_dist_app ; simpl ; repeat rewrite n_imp_subformLF_dist_app. lia.
    inversion i1. subst. inversion i ; subst. unfold n_imp_subformS ; simpl.
    repeat rewrite n_imp_subformLF_dist_app ; simpl ; repeat rewrite n_imp_subformLF_dist_app. lia.
    inversion H1. subst. 2: inversion H2. unfold n_imp_subformS ; simpl.
    repeat rewrite n_imp_subformLF_dist_app ; simpl ; repeat rewrite n_imp_subformLF_dist_app. lia.
  Qed.

  Lemma propvar_subform_list_restr_list_prop : forall l (p q : string), In # q (propvar_subform_list (restr_list_prop p l)) ->
                        ((q <> p) * (In # q (propvar_subform_list l))).
  Proof.
  induction l ; simpl ; intros ; auto. unfold restr_list_prop in H. destruct a as [n | | |]; simpl ; simpl in H ; auto.
  destruct (eq_dec_form (# p) (# n)) ; subst. apply IHl in H. destruct H ; auto.
  simpl in H. destruct H ; subst ; auto. split ; auto. rewrite H in n0. destruct (string_dec p q) ; subst; auto.
  all: apply IHl in H ; destruct H ; auto.
  all: split ; auto. all: apply in_or_app ; auto.
 Qed.

  Lemma In_list_prop_LF: forall l A, In A (list_prop_LF l) -> ((existsT2 q, A = # q) * In A l).
  Proof.
  induction l ; simpl ; intros ; auto. inversion H. apply In_InT in H. apply InT_app_or in H.
  destruct H. destruct a as [n | | |]; simpl in i ; inversion i ; subst ; auto. split ; [exists n ; auto | auto]. inversion H0.
  apply InT_In in i ; apply IHl in i ; auto. destruct i ; split ; auto.
  Qed.

  Lemma list_prop_LF_propvar_subform_list : forall l q, In # q (list_prop_LF l) -> In # q (propvar_subform_list l).
  Proof.
  induction l ; simpl ; intros ; auto. apply in_app_or in H ; destruct H ; auto. apply in_or_app ; left. destruct a ; simpl ; simpl in H ; try firstorder.
  apply in_or_app ; right ; apply IHl in H ; auto.
  Qed.

  Lemma In_list_In_list_prop_LF : forall l P, In # P l -> In # P (list_prop_LF l).
  Proof.
  induction l ; simpl ; subst ; auto. intros. destruct H. subst ; simpl ; auto. apply in_or_app; right ; auto.
  Qed.

  Lemma In_list_In_propvar_subform_list : forall l P, In # P l -> In # P (propvar_subform_list l).
  Proof.
  induction l ; simpl ; subst ; auto. intros. destruct H. subst ; simpl ; auto. apply in_or_app; right ; auto.
  Qed.

  End Prop_Subform.



  Section Diam_help.

  Lemma In_subform_boxes:
  forall (l : list MPropF) (A : MPropF), In A (subform_boxesLF l) -> exists B : MPropF, In A (subform_boxesF B) /\ In B l.
  Proof.
  induction l ; simpl ; intros ; auto. inversion H. apply in_app_or in H. destruct H. pose (In_subform_boxesF_box _ _ H).
  unfold is_boxedT in i. destruct i. subst. exists a ; auto. apply In_remove_list_In_list in H. apply IHl in H. firstorder.
  Qed.

  Lemma nolessub_In : forall s A, (length (usable_boxes (XBoxed_list (top_boxes (fst s)), []%list)) < length (usable_boxes s) -> False) ->
                                      (In (Box A) (top_boxes (XBoxed_list (top_boxes (fst s))))) -> In (Box A) (top_boxes (fst s)).
  Proof.
  intros. apply InT_In. pose (InT_dec (top_boxes (fst s)) (Box A)). destruct s0 ; auto. exfalso. apply H. destruct s.
  simpl. simpl in f. simpl in H0. simpl in H. unfold usable_boxes. simpl. unfold subform_boxesS. simpl.
  apply remove_list_incr_decr ; simpl. apply add_remove_list_preserve_NoDup. 2: apply NoDup_nil.
  apply NoDup_subform_boxesLF. apply add_remove_list_preserve_NoDup. 1-2: apply NoDup_subform_boxesLF.
  exists (Box A). repeat split ; auto.
  apply in_or_app ; left. apply XBoxed_list_same_subform_boxes. apply top_boxes_incl_list in H0.
  apply In_XBoxed_list in H0. destruct H0. apply In_incl_subform_boxes with (A:=Box A) ; auto. exfalso. apply f ; apply In_InT ; auto.
  simpl ; auto. destruct H0. destruct H0. subst. apply XBoxed_list_same_subform_boxes. apply top_boxes_incl_list in H0.
  apply In_incl_subform_boxes with (A:=(Box (Box A))) ; simpl ; auto.
  intro ; apply f ; apply In_InT ; auto. intro. intros. pose (in_top_boxes _ _ H1). destruct s. destruct s.
  destruct s. destruct p ; subst. rewrite top_boxes_distr_app. simpl. rewrite XBox_app_distrib. simpl.
  rewrite top_boxes_distr_app. simpl. destruct x ; simpl. 1-3: apply in_or_app ; right ; apply in_eq.
  apply in_or_app ; right ; apply in_cons ; apply in_eq.
  intro. intros. apply in_app_or in H1. destruct H1. apply in_or_app. left.
  pose (XBoxed_list_same_subform_boxes (top_boxes l)). apply a0 in H1. apply In_subform_boxes in H1. destruct H1.
  destruct H1. apply In_incl_subform_boxes with (A:=x). apply top_boxes_incl_list ; auto. auto.
  apply remove_list_is_in. rewrite remove_list_of_nil in H1. inversion H1.
 Qed.

  Lemma remove_list_decr_in: forall [l2 l1 l3 l4: list MPropF], NoDup l4 -> NoDup l3 ->
    incl l1 l2 -> incl l3 l4 -> length (remove_list l2 l4) < length (remove_list l1 l3) ->
    (exists A : MPropF, In A l2 /\ (In A l1 -> False)).
  Proof.
  induction l2 ; simpl.
  - intros. destruct l1. simpl. simpl in H3. exfalso. pose (NoDup_incl_length H0 H2). simpl in l. lia.
    exfalso. pose (H1 m). simpl in i ; apply i ; auto.
  - intros. destruct (In_dec l2 a).
    + assert (incl l1 l2). intro. intros. apply H1 in H4. inversion H4 ; subst ; auto.
       pose (In_remove_list_remove_redund _ l4 _ i). rewrite e in H3.
       pose (IHl2 _ _ _ H H0 H4 H2 H3). destruct e0. destruct H5. exists x ; split ; auto.
    + destruct (In_dec l1 a).
        * destruct (In_dec l4 a).
          -- destruct (In_dec l3 a).
            ++ assert (incl (remove eq_dec_form a l1) l2). intro. intros. apply in_remove in H4. destruct H4.
                 apply H1 in H4. inversion H4 ; subst ; auto. exfalso ; apply H5 ; auto.
                 assert ((remove_list l1 l3) = (remove_list (remove eq_dec_form a l1) (remove eq_dec_form a l3))).
                 rewrite <- In_remove_list_remove_redund with (a:=a). rewrite permut_remove_remove_list.
                 pose (permut_remove_remove_list a (remove eq_dec_form a l1) l3). rewrite <- e.
                 pose (redund_remove_remove_list a l1 l3). rewrite e0. rewrite permut_remove_remove_list. auto. auto.
                 assert (J0: NoDup (remove eq_dec_form a l4)). apply remove_preserv_NoDup ; auto.
                 assert (J1: NoDup (remove eq_dec_form a l3)). apply remove_preserv_NoDup ; auto.
                 assert (J2: incl (remove eq_dec_form a l3) (remove eq_dec_form a l4)). intro. intros.
                 apply in_remove in H6. destruct H6. apply in_in_remove ; auto.
                 rewrite H5 in H3. rewrite permut_remove_remove_list in H3.
                 pose (IHl2 (remove eq_dec_form a l1) _ _ J0 J1 H4 J2 H3). destruct e. destruct H6.
                 exists x ; split ; auto. intro. apply H7. apply in_in_remove ; auto. intro ; subst. auto.
            ++ assert (incl (remove eq_dec_form a l1) l2). intro. intros. apply in_remove in H4. destruct H4.
                 apply H1 in H4. inversion H4 ; subst ; auto. exfalso ; apply H5 ; auto.
                 rewrite permut_remove_remove_list in H3.
                 assert (J0: NoDup (remove eq_dec_form a l4)). apply remove_preserv_NoDup ; auto.
                 assert (J1: incl l3 (remove eq_dec_form a l4)). intro. intros. apply in_in_remove ; auto.
                 intro ; subst ; auto.
                 assert (J:length (remove_list l2 (remove eq_dec_form a l4)) < length (remove_list (remove eq_dec_form a l1) l3)).
                 assert ((remove_list l1 l3) = (remove_list (remove eq_dec_form a l1) l3)).
                 pose (redund_remove_remove_list a l1 l3). rewrite notin_remove in e.
                 symmetry in e. rewrite notin_remove in e. auto.
                 1-2: intro ; apply In_remove_list_In_list in H5 ; auto. rewrite H5 in H3. auto.
                 pose (IHl2 (remove eq_dec_form a l1) _ _ J0 H0 H4 J1 J). destruct e. destruct H5.
                 exists x ; split ; auto. intro. apply H6. apply in_in_remove ; auto. intro ; subst. auto.
          -- assert (In a l3 -> False). intro. apply f0 ; auto. rewrite permut_remove_remove_list in H3.
              rewrite notin_remove in H3 ; auto.
              assert (incl (remove eq_dec_form a l1) l2). intro. intros. apply in_remove in H5. destruct H5.
              apply H1 in H5. inversion H5 ; subst ; auto. exfalso ; apply H6 ; auto.
              assert (length (remove_list l2 l4) < length (remove_list (remove eq_dec_form a l1) l3)).
              pose (redund_remove_remove_list a l1 l3). rewrite notin_remove in e. rewrite e. rewrite notin_remove ; auto.
              intro. apply In_remove_list_In_list in H6 ; auto. intro. apply In_remove_list_In_list in H6 ; auto.
              pose (IHl2 (remove eq_dec_form a l1) _ _ H H0 H5 H2 H6). destruct e. destruct H7.
              exists x ; split ; auto. intro. apply H8. apply in_in_remove ; auto. intro ; subst. auto.
        * exists a ; split ; auto.
  Qed.

  Lemma less_ub_witness : forall l, length (usable_boxes (XBoxed_list (top_boxes (XBoxed_list (top_boxes l))), []%list)) <
    length (usable_boxes (XBoxed_list (top_boxes l), []%list)) ->
    exists A, In (Box A) (top_boxes (XBoxed_list (top_boxes (XBoxed_list (top_boxes l))))) /\
                  (In (Box A) (top_boxes (XBoxed_list (top_boxes l))) -> False).
  Proof.
  intros. unfold usable_boxes in H. simpl in H. unfold subform_boxesS in H. simpl in H.
  repeat rewrite remove_list_of_nil in H. repeat rewrite app_nil_r in H.
  apply remove_list_decr_in in H ; auto. destruct H. destruct H.
  pose (in_top_boxes _ _ H). destruct s. destruct s. destruct s. destruct p. subst. exists x0 ; auto.
  1-2: apply NoDup_subform_boxesLF.
  intro. intros. pose (in_top_boxes _ _ H0). destruct s. destruct s. destruct s. destruct p ; subst.
  apply is_box_in_top_boxes. apply top_boxes_incl_list in H0. apply In_XBoxed_list in H0.
  destruct H0. apply list_preserv_XBoxed_list. apply is_box_in_top_boxes. 2,4: exists x ; auto.
  apply list_preserv_XBoxed_list ; auto. destruct H0. destruct H0 ; subst. apply XBoxed_list_In_unfold.
  exists (Box (Box x)) ; split ; auto. apply is_box_in_top_boxes. 2: exists (Box x) ; auto.
  apply list_preserv_XBoxed_list ; auto.
  intro. intros. apply In_subform_boxes in H0. destruct H0. destruct H0. apply In_XBoxed_list in H1.
  destruct H1. apply In_incl_subform_boxes with (A:=x) ; auto. apply list_preserv_XBoxed_list.
  apply is_box_in_top_boxes. apply list_preserv_XBoxed_list ; auto. apply in_top_boxes in H1.
  destruct H1. destruct s. destruct s. destruct p ; subst. exists x0 ; auto.
  destruct H1. destruct H1 ; subst. apply In_incl_subform_boxes with (A:= x) ; auto.
  apply XBoxed_list_In_unfold. exists (Box x) ; split ; auto.
  apply is_box_in_top_boxes. apply list_preserv_XBoxed_list ; auto. exists x ; auto.
  Qed.

  Lemma ub_stable : forall s, length (usable_boxes (XBoxed_list (top_boxes (XBoxed_list (top_boxes (fst s)))), []%list)) <
     length (usable_boxes (XBoxed_list (top_boxes (fst s)), []%list)) ->
    length (usable_boxes (XBoxed_list (top_boxes (fst s)), []%list)) < length (usable_boxes s).
  Proof.
  intros. unfold usable_boxes. simpl. unfold subform_boxesS. simpl. destruct s. simpl in H. simpl.
  apply remove_list_incr_decr ; simpl. apply add_remove_list_preserve_NoDup. 2: apply NoDup_nil.
  apply NoDup_subform_boxesLF. apply add_remove_list_preserve_NoDup. 1-2: apply NoDup_subform_boxesLF.
  apply less_ub_witness in H. destruct H. destruct H.
  assert (J0: In (Box (Box (Box x))) (top_boxes l)). apply top_boxes_incl_list in H. apply In_XBoxed_list in H.
  destruct H. exfalso ; auto. destruct H. destruct H ; subst. apply top_boxes_incl_list in H. apply In_XBoxed_list in H.
  destruct H. exfalso ; apply H0. apply is_box_in_top_boxes. apply XBoxed_list_In ; auto. unfold is_boxedT ; exists x ; auto.
  destruct H. destruct H ; subst ; auto.
  exists (Box (Box x)). repeat split.
  apply is_box_in_top_boxes. 2: unfold is_boxedT ; eexists ; auto. apply XBoxed_list_In_unfold.
  exists (Box (Box (Box x))) ; split ; auto. apply in_or_app ; left. apply In_incl_subform_boxes with (A:=Box (Box (Box x))) ; auto.
  apply top_boxes_incl_list ; auto. simpl ; auto. intro. apply H0. apply is_box_in_top_boxes.
  2: unfold is_boxedT ; exists x ; auto. apply XBoxed_list_In_unfold. exists (Box (Box x)) ; split ; auto.
  intro. intros. apply is_box_in_top_boxes. apply list_preserv_XBoxed_list ; auto.
  apply in_top_boxes in H0. destruct H0. destruct s. destruct s. destruct p ; subst. exists x ; auto.
  intro. intros. apply in_app_or in H0. destruct H0. apply in_or_app. left.
  pose (XBoxed_list_same_subform_boxes (top_boxes l)). apply a0 in H0. apply In_subform_boxes in H0. destruct H0.
  destruct H0. apply In_incl_subform_boxes with (A:=x). apply top_boxes_incl_list ; auto. auto.
  apply remove_list_is_in. rewrite remove_list_of_nil in H0. inversion H0.
  Qed.

  End Diam_help.



  Section logic.

  Lemma DiamL_lim : forall A BΓ Γ0 Δ, (is_Boxed_list BΓ) ->
                                                                      (nobox_gen_ext BΓ Γ0) ->
                                                                      (GLS_prv (A :: XBoxed_list BΓ, [])) ->
                                                                      (GLS_prv (Diam A :: Γ0, Δ)).
  Proof.
  intros. unfold Diam. unfold Neg.
  apply derI with (ps:=[([] ++ Γ0, [] ++ Box (A --> ⊥) :: Δ);([] ++ ⊥ :: Γ0, [] ++ Δ)]).
  apply ImpL. assert ((Box (A --> ⊥) --> ⊥ :: Γ0, Δ) = ([] ++ Box (A --> ⊥) --> ⊥ :: Γ0, [] ++ Δ)). auto.
  rewrite H0. apply ImpLRule_I. apply dlCons. 2: apply dlCons. 3: apply dlNil.
  2: apply derI with (ps:=[]) ; try apply dlNil ; try apply BotL ; apply BotLRule_I.
  apply derI with (ps:=[(XBoxed_list BΓ ++ [Box (A --> ⊥)], [A --> ⊥])]).
  apply GLR. apply GLRRule_I ; auto. apply dlCons. 2: apply dlNil.
  apply derI with (ps:=[([] ++ A :: XBoxed_list BΓ ++ [Box (A --> ⊥)], [] ++ ⊥ :: [])]).
  apply ImpR. assert ((XBoxed_list BΓ ++ [Box (A --> ⊥)], [A --> ⊥]) = ([] ++ XBoxed_list BΓ ++ [Box (A --> ⊥)], [] ++ A --> ⊥ :: [])). auto.
  rewrite H0. apply ImpRRule_I. apply dlCons. 2: apply dlNil.
  assert (J0: derrec_height X0 = derrec_height X0) ; auto.
  assert (J1: wkn_L (Box (A --> ⊥)) (A :: XBoxed_list BΓ, []%list) (A :: XBoxed_list BΓ++ [Box (A --> ⊥)], []%list)).
  assert (A :: XBoxed_list BΓ =  (A :: XBoxed_list BΓ) ++ []). rewrite app_nil_r. auto. rewrite H0.
  assert (A :: XBoxed_list BΓ ++ [Box (A --> ⊥)] =  (A :: XBoxed_list BΓ) ++ Box (A --> ⊥) :: []). auto. rewrite H1.
  apply wkn_LI. pose (GLS_wkn_L X0 J0 J1). destruct s.
  assert (J2: derrec_height x = derrec_height x) ; auto.
  assert (J3: wkn_R ⊥ (A :: XBoxed_list BΓ ++ [Box (A --> ⊥)], []%list) (A :: XBoxed_list BΓ ++ [Box (A --> ⊥)], [⊥])).
  assert ((A :: XBoxed_list BΓ ++ [Box (A --> ⊥)], @nil MPropF) =  (A :: XBoxed_list BΓ ++ [Box (A --> ⊥)], [] ++ [])).
  rewrite app_nil_r. auto. rewrite H0.
  assert ((A :: XBoxed_list BΓ ++ [Box (A --> ⊥)], [⊥]) =  (A :: XBoxed_list BΓ ++ [Box (A --> ⊥)], [] ++ ⊥ :: [])). auto. rewrite H1.
  apply wkn_RI. pose (GLS_wkn_R x J2 J3). destruct s. simpl. auto.
  Qed.

  Lemma nobox_top_boxes : forall l, nobox_gen_ext (top_boxes l) l.
  Proof.
  induction l ; simpl ; auto. apply univ_gen_ext_nil. destruct a.
  1-3: apply univ_gen_ext_extra ; auto ; intro ; inversion X ; inversion H.
  apply univ_gen_ext_cons ; auto.
  Qed.

  Lemma top_boxes_nodup : forall l, incl (top_boxes l) (top_boxes (nodup eq_dec_form l)).
  Proof.
  induction l ; intro ; intros ; auto. destruct a as [n | | |]; simpl ; simpl in H ; auto ; simpl ; subst.
  destruct (in_dec eq_dec_form # n l) ; auto. destruct (in_dec eq_dec_form Bot l) ; auto.
  destruct (in_dec eq_dec_form (a1 --> a2) l) ; auto. destruct (in_dec eq_dec_form (Box a) l) ; simpl ; auto.
  destruct H ; subst ; auto. apply IHl. apply is_box_in_top_boxes ; auto. exists a ; auto. destruct H ; subst ; auto.
  Qed.

  Lemma subform_boxesLF_nodup : forall l a, In a (subform_boxesLF l) <-> In a (subform_boxesLF (nodup eq_dec_form l)).
  Proof.
  induction l ; simpl ; intros ; auto. intuition. split.
  - destruct a as [n | | |]; simpl ; auto ; intros.
    destruct (in_dec eq_dec_form # n l) ; apply IHl ; auto. destruct (in_dec eq_dec_form Bot l) ; apply IHl ; auto.
    destruct (in_dec eq_dec_form (a1 --> a2) l) ; auto. apply in_app_or in H. destruct H.
    apply IHl. apply In_incl_subform_boxes with (A:=a1 --> a2) ; auto. apply IHl.
    apply In_remove_list_In_list in H ; auto. apply in_app_or in H. destruct H.
    simpl. apply in_or_app. left. simpl in H. auto. simpl. apply in_or_app ; right.
    apply not_removed_remove_list. apply IHl ; auto. apply In_remove_list_In_list in H ; auto.
    intro. simpl in H. pose (remove_list_cont _ _ H0 _ H). auto.
    destruct (in_dec eq_dec_form (Box a) l) ; auto. destruct H ; simpl ; auto.
    apply IHl ; auto. subst. apply In_incl_subform_boxes with (A:=Box a) ; auto. simpl ; auto. apply IHl.
    apply in_app_or in H ; destruct H. apply In_incl_subform_boxes with (A:=Box a) ; auto. simpl ; auto.
    apply in_remove in H. destruct H. apply In_remove_list_In_list in H ; auto.
    destruct H ; subst. simpl ; auto. simpl. right. apply in_or_app ; auto.
    apply in_app_or in H ; destruct H ; auto. apply in_remove in H. destruct H. right.
    apply in_not_touched_remove ; auto.
    apply In_remove_list_In_list_not_In_remove_list in H ; auto. destruct H.
    apply not_removed_remove_list ; auto.
    apply IHl ; auto.
  - destruct a as [n | | |]; simpl ; auto ; intros.
    destruct (in_dec eq_dec_form # n l) ; apply IHl ; auto. destruct (in_dec eq_dec_form Bot l) ; apply IHl ; auto.
    destruct (in_dec eq_dec_form (a1 --> a2) l) ; auto. destruct (in_dec eq_dec_form a0 (subform_boxesF a1 ++ remove_list (subform_boxesF a1) (subform_boxesF a2))) ; auto.
    apply in_or_app ; auto. apply in_or_app ; right.
    apply not_removed_remove_list ; auto. apply IHl ; auto. simpl in H. apply in_or_app ; apply in_app_or in H ; destruct H ; auto.
    right. apply In_remove_list_In_list_not_In_remove_list in H ; auto. destruct H.
    apply not_removed_remove_list ; auto. apply IHl ; auto.
    destruct (in_dec eq_dec_form (Box a) l) ; auto.
    destruct (in_dec eq_dec_form a0 (subform_boxesF (Box a))) ; auto. simpl in i0 ; destruct i0 ; auto.
    right. apply in_or_app ; auto. right. simpl in n. apply in_or_app ; right. apply in_not_touched_remove ; auto.
    apply not_removed_remove_list ; auto. apply IHl ; auto. simpl in H. destruct H ; auto. right.
    apply in_or_app ; apply in_app_or in H ; destruct H ; auto.
    right. apply in_remove in H. destruct H. apply In_remove_list_In_list_not_In_remove_list in H ; auto. destruct H.
    apply in_not_touched_remove ; auto. apply not_removed_remove_list ; auto. apply IHl ; auto.
  Qed.

  Lemma set_leq_ub_unif : forall s, (length (usable_boxes (nodupseq (XBoxed_list (top_boxes (fst s)), [])))) <= (length (usable_boxes s)).
  Proof.
  intros. destruct s. simpl. unfold usable_boxes. simpl.
  assert (J0: incl (top_boxes l) (top_boxes (XBoxed_list (top_boxes l)))). apply top_boxes_XBoxed_list.
  assert (J01: incl (top_boxes (XBoxed_list (top_boxes l))) (top_boxes (nodup eq_dec_form (XBoxed_list (top_boxes l))))).
  intro. intros. apply top_boxes_nodup ; auto.
  assert (J03: incl (top_boxes l) (top_boxes (nodup eq_dec_form (XBoxed_list (top_boxes l))))).
  intros a H ; apply J01 ; apply J0 ; auto.
  pose (remove_list_incr_decr3 (subform_boxesS (nodupseq (XBoxed_list (top_boxes l), []%list))) _ _ J03).
  assert (J1: NoDup (subform_boxesS (nodupseq (XBoxed_list (top_boxes l), []%list)))). apply NoDup_subform_boxesS.
  assert (J2: NoDup (subform_boxesS (l, l0))). apply NoDup_subform_boxesS.
  assert (J3: incl (subform_boxesS (nodupseq (XBoxed_list (top_boxes l), []%list))) (subform_boxesS (l, l0))).
  intro ; intros. unfold subform_boxesS. simpl. unfold subform_boxesS in H. simpl in H.
  rewrite remove_list_of_nil in H. rewrite app_nil_r in H. apply in_or_app ; left.
  assert (J02: In a (subform_boxesLF (XBoxed_list (top_boxes l)))). apply subform_boxesLF_nodup ; auto.
  apply XBoxed_list_same_subform_boxes with (l:=(top_boxes l)) in J02.
  apply subform_boxesLF_top_boxes ; auto.
  pose (remove_list_incr_decr2 _ _ (top_boxes l) J1 J2 J3). lia.
  Qed.

  Lemma is_init_Canopy : forall s, is_init s -> (forall leaf, InT leaf (Canopy s) -> is_init leaf).
  Proof.
  intros s ; induction on s as IHs with measure (n_imp_subformS s).
  intros. apply fold_Canopy in H. destruct H ; subst ; auto.
  destruct s0 ; destruct p. unfold inv_prems in i. apply InT_flatten_list_InT_elem in i. destruct i.
  destruct p. destruct (finite_ImpRules_premises_of_S s). simpl in i1. subst.
  apply p in i1. destruct i1.
  - inversion i1 ; subst. inversion i ; subst. 2: inversion H0.
    assert (J0: n_imp_subformS (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) < n_imp_subformS (Γ0 ++ Γ1, Δ0 ++ A --> B :: Δ1)).
    unfold n_imp_subformS. simpl. repeat rewrite n_imp_subformLF_dist_app. simpl ; repeat rewrite n_imp_subformLF_dist_app.
    lia. apply IHs with (leaf:=leaf) in J0 ; auto.
    unfold is_init. destruct X. destruct s.
    left. left. inversion i2 ; subst. assert (InT (# P) (Γ0 ++ A :: Γ1)). apply InT_or_app.
    assert (InT (# P) (Γ0 ++ Γ1)). rewrite <- H. apply InT_or_app ; right ;apply InT_eq. apply InT_app_or in H0.
    destruct H0 ; auto. right ; apply InT_cons ; auto. apply InT_split in H0. destruct H0. destruct s. rewrite e.
    assert (InT (# P) (Δ0 ++ B :: Δ1)). apply InT_or_app.
    assert (InT (# P) (Δ0 ++ A --> B :: Δ1)). rewrite <- H1. apply InT_or_app ; right ;apply InT_eq. apply InT_app_or in H0.
    destruct H0 ; auto. inversion i3 ; subst. inversion H2. right ; apply InT_cons ; auto. apply InT_split in H0. destruct H0. destruct s.
    rewrite e0. apply IdPRule_I.
    left. right. inversion i2 ; subst. assert (InT (Box A0) (Γ0 ++ A :: Γ1)). apply InT_or_app.
    assert (InT (Box A0) (Γ0 ++ Γ1)). rewrite <- H. apply InT_or_app ; right ;apply InT_eq. apply InT_app_or in H0.
    destruct H0 ; auto. right ; apply InT_cons ; auto. apply InT_split in H0. destruct H0. destruct s. rewrite e.
    assert (InT (Box A0) (Δ0 ++ B :: Δ1)). apply InT_or_app.
    assert (InT (Box A0) (Δ0 ++ A --> B :: Δ1)). rewrite <- H1. apply InT_or_app ; right ;apply InT_eq. apply InT_app_or in H0.
    destruct H0 ; auto. inversion i3 ; subst. inversion H2. right ; apply InT_cons ; auto. apply InT_split in H0. destruct H0. destruct s.
    rewrite e0. apply IdBRule_I.
    right. inversion b ; subst. assert (InT (⊥) (Γ0 ++ A :: Γ1)). apply InT_or_app.
    assert (InT (⊥) (Γ0 ++ Γ1)). rewrite <- H. apply InT_or_app ; right ;apply InT_eq. apply InT_app_or in H0.
    destruct H0 ; auto. right ; apply InT_cons ; auto. apply InT_split in H0. destruct H0. destruct s. rewrite e. apply BotLRule_I.
  - inversion i1 ; subst. inversion i ; subst. 2: inversion H0. 3: inversion H1.
    assert (J0: n_imp_subformS (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) < n_imp_subformS (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)).
    unfold n_imp_subformS. simpl. repeat rewrite n_imp_subformLF_dist_app. simpl ; repeat rewrite n_imp_subformLF_dist_app.
    lia. apply IHs with (leaf:=leaf) in J0 ; auto.
    unfold is_init. destruct X. destruct s.
    left. left. inversion i2 ; subst. assert (InT (# P) (Γ0 ++ Γ1)). apply InT_or_app.
    assert (InT (# P) (Γ0 ++ A --> B :: Γ1)). rewrite <- H. apply InT_or_app ; right ;apply InT_eq. apply InT_app_or in H0.
    destruct H0 ; auto. inversion i3 ; subst. inversion H2. auto. apply InT_split in H0. destruct H0. destruct s. rewrite e.
    assert (InT (# P) (Δ0 ++ A :: Δ1)). apply InT_or_app.
    assert (InT (# P) (Δ0 ++ Δ1)). rewrite <- H1. apply InT_or_app ; right ;apply InT_eq. apply InT_app_or in H0.
    destruct H0 ; auto. right ; apply InT_cons ; auto. apply InT_split in H0. destruct H0. destruct s.
    rewrite e0. apply IdPRule_I.
    left. right. inversion i2 ; subst. assert (InT (Box A0) (Γ0 ++ Γ1)). apply InT_or_app.
    assert (InT (Box A0) (Γ0 ++ A --> B :: Γ1)). rewrite <- H. apply InT_or_app ; right ;apply InT_eq. apply InT_app_or in H0.
    destruct H0 ; auto. inversion i3 ; subst. inversion H2. auto. apply InT_split in H0. destruct H0. destruct s. rewrite e.
    assert (InT (Box A0) (Δ0 ++ A :: Δ1)). apply InT_or_app.
    assert (InT (Box A0) (Δ0 ++ Δ1)). rewrite <- H1. apply InT_or_app ; right ;apply InT_eq. apply InT_app_or in H0.
    destruct H0 ; auto. right ; apply InT_cons ; auto. apply InT_split in H0. destruct H0. destruct s.
    rewrite e0. apply IdBRule_I.
    right. inversion b ; subst. assert (InT (⊥) (Γ0 ++ Γ1)). apply InT_or_app.
    assert (InT (⊥) (Γ0 ++ A --> B :: Γ1)). rewrite <- H. apply InT_or_app ; right ;apply InT_eq. apply InT_app_or in H0.
    destruct H0 ; auto. inversion i2 ; subst. inversion H1. auto. apply InT_split in H0. destruct H0. destruct s. rewrite e. apply BotLRule_I.
    assert (J0: n_imp_subformS (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) < n_imp_subformS (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)).
    unfold n_imp_subformS. simpl. repeat rewrite n_imp_subformLF_dist_app. simpl ; repeat rewrite n_imp_subformLF_dist_app.
    lia. subst. apply IHs with (leaf:=leaf) in J0 ; auto.
    unfold is_init. destruct X. destruct s.
    left. left. inversion i2 ; subst. assert (InT (# P) (Γ0 ++ B :: Γ1)). apply InT_or_app.
    assert (InT (# P) (Γ0 ++ A --> B :: Γ1)). rewrite <- H. apply InT_or_app ; right ;apply InT_eq. apply InT_app_or in H1.
    destruct H1 ; auto. inversion i3 ; subst. inversion H3. right ; apply InT_cons ; auto. apply InT_split in H1. destruct H1. destruct s. rewrite e.
    apply IdPRule_I.
    left. right. inversion i2 ; subst. assert (InT (Box A0) (Γ0 ++ B :: Γ1)). apply InT_or_app.
    assert (InT (Box A0) (Γ0 ++ A --> B :: Γ1)). rewrite <- H. apply InT_or_app ; right ;apply InT_eq. apply InT_app_or in H1.
    destruct H1 ; auto. inversion i3 ; subst. inversion H3. right ; apply InT_cons ; auto. apply InT_split in H1. destruct H1. destruct s. rewrite e.
    apply IdBRule_I.
    right. inversion b ; subst. assert (InT (⊥) (Γ0 ++ B :: Γ1)). apply InT_or_app.
    assert (InT (⊥) (Γ0 ++ A --> B :: Γ1)). rewrite <- H. apply InT_or_app ; right ;apply InT_eq. apply InT_app_or in H1.
    destruct H1 ; auto. inversion i2 ; subst. inversion H2. right ; apply InT_cons ; auto. apply InT_split in H1. destruct H1. destruct s. rewrite e. apply BotLRule_I.
  Qed.

  Theorem is_init_UI_equiv_Top : forall s, is_init s -> forall p X Y0 Y1, GLS_prv (X, Y0 ++ Top --> (UI p s) :: Y1).
  Proof.
  intros. destruct (critical_Seq_dec s).
  - assert (J0: GUI p s (UI p s)). apply UI_GUI ; auto.
    pose (@GUI_inv_critic_init p s (UI p s) J0 c X). rewrite <- e.
    apply derI with (ps:=[([] ++ Top :: X0, Y0 ++ Top :: Y1)]).
    apply ImpR. assert ((X0, Y0 ++ Top --> Top :: Y1) = ([] ++ X0, Y0 ++ Top --> Top :: Y1)). auto. rewrite H.
    apply ImpRRule_I. apply dlCons. 2: apply dlNil. apply TopR.
  - assert (J0: GUI p s (UI p s)). apply UI_GUI ; auto.
    assert (J1: Gimap (GUI p) (Canopy (nodupseq s)) (map (UI p) (Canopy (nodupseq s)))). apply Gimap_map. intros.
    apply UI_GUI ; auto.
    pose (@GUI_inv_not_critic p s (UI p s) (map (UI p) (Canopy (nodupseq s))) J0 f J1). rewrite <- e.
    apply derI with (ps:=[([] ++ Top :: X0, Y0 ++ list_conj (map (UI p) (Canopy (nodupseq s))) :: Y1)]).
    apply ImpR. assert ((X0, Y0 ++ Top --> list_conj (map (UI p) (Canopy (nodupseq s))) :: Y1) = ([] ++ X0, Y0 ++ Top --> list_conj (map (UI p) (Canopy (nodupseq s))) :: Y1)). auto. rewrite H.
    apply ImpRRule_I. apply dlCons. 2: apply dlNil. simpl.
    apply GLS_adm_list_exch_R with (s:=(Top :: X0, list_conj (map (UI p) (Canopy (nodupseq s))) :: Y0 ++ Y1)).
    pose (list_conj_R (map (UI p) (Canopy (nodupseq s))) (Top :: X0, Y0 ++ Y1)). apply g. clear g.
    intros. simpl. apply InT_map_iff in H. destruct H. destruct p0. subst.
    assert (J2: GUI p x (UI p x)). apply UI_GUI ; auto.
    assert (J3: critical_Seq x). apply Canopy_critical in i ; auto.
    assert (J4: is_init x). apply is_init_Canopy in i ; auto.
    pose (is_init_nodupseq s). destruct p0. apply i0 ; auto.
    pose (@GUI_inv_critic_init p x (UI p x) J2 J3 J4). rewrite <- e0.
    assert ((Top :: X0, Top :: Y0 ++ Y1) = (Top :: X0, [] ++ Top :: Y0 ++ Y1)). auto. rewrite H. apply TopR.
    assert (list_conj (map (UI p) (Canopy (nodupseq s))) :: Y0 ++ Y1 = [] ++ [list_conj (map (UI p) (Canopy (nodupseq s)))] ++ Y0 ++ [] ++ Y1). auto. rewrite H.
    assert (Y0 ++ list_conj (map (UI p) (Canopy (nodupseq s))) :: Y1 = [] ++ [] ++ Y0 ++ [list_conj (map (UI p) (Canopy (nodupseq s)))] ++ Y1). auto. rewrite H0.
    apply list_exch_RI.
  Qed.

  Theorem is_init_UI : forall s, is_init s -> forall p X Y0 Y1, GLS_prv (X, Y0 ++ UI p s :: Y1).
  Proof.
  intros. eapply is_init_UI_equiv_Top in X. apply ImpR_inv with (prem:=([] ++ Top :: X0, Y0 ++ UI p s :: Y1)) in X.
  apply TopL_remove in X. simpl in X ; auto. assert ((X0, Y0 ++ Top --> UI p s :: Y1) = ([] ++ X0, Y0 ++ Top --> UI p s :: Y1)).
  auto. rewrite H. apply ImpRRule_I.
  Qed.

  End logic.


  Section top_boxes_facts.

  Theorem top_boxes_diam_jump : forall s, critical_Seq s -> (length (usable_boxes s) = length (usable_boxes (XBoxed_list (top_boxes (fst s)),[]))) ->
          (forall A, In A (top_boxes (fst s)) <-> In A (top_boxes (XBoxed_list (top_boxes (fst s))))).
  Proof.
  intros. split.
  - intro. apply top_boxes_XBoxed_list ; auto.
  - intro. pose (in_top_boxes _ _ H1). repeat destruct s0. destruct p. clear e0 ; subst.
    apply nolessub_In ; auto. lia.
  Qed.

  End top_boxes_facts.


  Section nodup_facts.

  Theorem list_prop_LF_In: forall l A B, In A l -> In B (list_prop_F A) -> In B (list_prop_LF l).
  Proof.
  induction l ; intuition. simpl. apply in_or_app. inversion H ; subst ; auto.
  right. apply IHl with (A:=A) ; auto.
  Qed.

  Theorem In_propvar_subform: forall l A p, In A l -> In # p (propvar_subform A) -> In # p (propvar_subform_list l).
  Proof.
  induction l ; intuition. simpl. apply in_or_app. inversion H ; subst ; auto.
  right. apply IHl with (A:=A) ; auto.
  Qed.

  Theorem restr_list_prop_nodup : forall l A p,
      (InT A (restr_list_prop p (nodup eq_dec_form l)) -> InT A (restr_list_prop p l)) *
      (InT A (restr_list_prop p l) -> InT A (restr_list_prop p (nodup eq_dec_form l))).
  Proof.
  induction l ; intros ; simpl ; intuition.
  - destruct (in_dec eq_dec_form a l) ; auto. apply IHl in H. unfold restr_list_prop. simpl.
    apply In_InT. apply InT_In in H. apply in_remove in H. destruct H.
    apply in_not_touched_remove ; auto. apply in_or_app ; right ; auto.
    unfold restr_list_prop. simpl.
    apply In_InT. apply InT_In in H. apply in_remove in H. destruct H.
    apply in_not_touched_remove ; auto. simpl in H. apply in_app_or in H.
    apply in_or_app ; destruct H ; auto. right.
    assert (InT A (restr_list_prop p (nodup eq_dec_form l))). apply In_InT.
    apply in_not_touched_remove ; auto. apply IHl in H1.
    apply InT_In in H1. apply in_remove in H1. destruct H1. auto.
  - destruct (in_dec eq_dec_form a l) ; auto. apply IHl. unfold restr_list_prop. simpl.
    apply In_InT. apply InT_In in H. apply in_remove in H. destruct H.
    apply in_not_touched_remove ; auto. simpl in H. apply in_app_or in H. destruct H ; auto.
    apply list_prop_LF_In with (A:=a) ; auto.
    unfold restr_list_prop. simpl. apply In_InT. apply InT_In in H. apply in_remove in H. destruct H.
    apply in_not_touched_remove ; auto. simpl in H. apply in_app_or in H. apply in_or_app ; destruct H ; auto.
    right.
    assert (InT A (restr_list_prop p l)). apply In_InT.
    apply in_not_touched_remove ; auto. apply IHl in H1.
    apply InT_In in H1. apply in_remove in H1. destruct H1. auto.
  Qed.

  Theorem propvar_subform_list_nodup: forall l q,
  In # q (propvar_subform_list (nodup eq_dec_form l)) <-> In # q (propvar_subform_list l).
  Proof.
  induction l ; intuition.
  - simpl. simpl in H. apply in_or_app. destruct (in_dec eq_dec_form a l).
    + right ; apply IHl ; auto.
    + simpl in H. apply in_app_or in H ; destruct H ; auto. right ; apply IHl ; auto.
  - simpl. simpl in H. apply in_app_or in H. destruct (in_dec eq_dec_form a l).
    + destruct H. apply In_propvar_subform with (A:=a) ; auto. apply nodup_In ; auto.
       apply IHl ; auto.
    + simpl. apply in_or_app. destruct H ; auto. right ; apply IHl ; auto.
  Qed.

  Lemma incl_hpadm_prv : forall s0 s1 (D0: GLS_prv s0), (incl (fst s0) (fst s1)) -> (incl (snd s0) (snd s1)) ->
    existsT2 (D1: GLS_prv s1), derrec_height D1 <= derrec_height D0.
  Proof.
  intros. pose (incl_idS _ _ H H0). destruct s. destruct p. destruct s. destruct s.
  pose (nodupseq_prv_hpadm_LR _ D0). destruct s.
  assert (derrec_height x2 = derrec_height x2). auto.
  apply PermutationTS_sym in p. pose (PermutationTS_prv_hpadm _ x2 _ p).
  destruct s. destruct x ; simpl in *.
  assert (derrec_height x3 = derrec_height x3). auto.
  pose (@GLS_list_wkn_L _ [] l1 _ x3 H2). simpl in s. destruct (s x0).
  assert (derrec_height x = derrec_height x). auto.
  pose (@GLS_list_wkn_R _ _ [] l2 x H3). simpl in s2. destruct (s2 x1).
  apply PermutationTS_sym in p0. pose (PermutationTS_prv_hpadm _ x4 _ p0).
  destruct s3. pose (nodupseq_prv_hpadm_RL _ x5). destruct s3.
  exists x6 ; lia.
  Qed.

  Lemma incl_prv : forall s0 s1, (incl (fst s0) (fst s1)) -> (incl (snd s0) (snd s1)) ->
    (GLS_prv s0) -> (GLS_prv s1).
  Proof.
  intros. pose (incl_idS _ _ H H0). destruct s. destruct p. destruct s. destruct s.
  pose (nodupseq_prv s0). destruct p1. apply g in X. apply PermutationTS_sym in p.
  pose (PermutationTS_prv _ _ p X). destruct x ; simpl in *.
  pose (GLS_prv_list_wkn_L [] l). simpl in g2. apply g2 with (l:=x0) in g1.
  epose (GLS_prv_list_wkn_R []). simpl in g3. apply g3 with (l:=x1) in g1.
  apply PermutationTS_sym in p0. pose (PermutationTS_prv _ _ p0 g1).
  apply nodupseq_prv in g4 ; auto.
  Qed.

  Lemma Canopy_nodupseq_equiprv_genR : forall s A,
    ((forall leaf, InT leaf (Canopy (nodupseq s)) -> GLS_prv (fst leaf, A :: snd leaf)) -> (GLS_prv (fst s, A :: snd s))) *
    ((GLS_prv (fst s, A :: snd s)) -> (forall leaf, InT leaf (Canopy (nodupseq s)) -> GLS_prv (fst leaf, A :: snd leaf))).
  Proof.
  intros. split ; intros.
  - apply Canopy_equiprv_genR in X. simpl in X.
    apply incl_prv with (s0:=(nodup eq_dec_form (fst s), A :: nodup eq_dec_form (snd s))) ; simpl ; auto.
    intros B HB. apply nodup_In in HB ; auto. intros B HB. inversion HB ; simpl ; auto. right. apply nodup_In in H ; auto.
  - pose (Canopy_equiprv_genR s A). simpl in p. destruct p. clear g. apply Canopy_nodupseq_perm in H.
    destruct H. destruct p ; subst. pose (g0 X _ i). 
    apply incl_prv with (s0:=((fst x), A :: (snd x))) ; simpl ; auto.
    intros B HB. apply (nodup_In eq_dec_form) ; apply (nodup_In eq_dec_form) in HB. destruct p.
    apply Permutation_in with (l:=(nodup eq_dec_form (fst x))) ; auto ; apply Permutation_PermutationT ; destruct x ; destruct leaf ; simpl in * ; auto.
    intros B HB. apply (nodup_In eq_dec_form) ; apply (nodup_In eq_dec_form) in HB. destruct p.
    simpl in *. destruct (in_dec eq_dec_form A (snd x)).
    + destruct (in_dec eq_dec_form A (snd leaf)).
       apply Permutation_in with (l:=(nodup eq_dec_form (snd x))) ; auto ; apply Permutation_PermutationT ; destruct x ; destruct leaf ; simpl in * ; auto.
       exfalso. apply n. apply Permutation_PermutationT in p0. apply (nodup_In eq_dec_form).
       apply Permutation_in with (l:=(nodup eq_dec_form (snd x))) ; auto. apply (nodup_In eq_dec_form) ; auto.
    + destruct (in_dec eq_dec_form A (snd leaf)).
       exfalso. apply n. apply Permutation_PermutationT in p0. apply (nodup_In eq_dec_form).
       apply Permutation_in with (l:=(nodup eq_dec_form (snd leaf))) ; auto. apply Permutation_sym ; auto. apply (nodup_In eq_dec_form) ; auto.
       simpl ; inversion HB ; auto. right.
       apply Permutation_in with (l:=(nodup eq_dec_form (snd x))) ; auto ; apply Permutation_PermutationT ; destruct x ; destruct leaf ; simpl in * ; auto.
  Qed.

  Lemma Canopy_nodupseq_equiprv_genL : forall s A,
    ((forall leaf, InT leaf (Canopy (nodupseq s)) -> GLS_prv (A :: fst leaf, snd leaf)) -> (GLS_prv (A :: fst s, snd s))) *
    ((GLS_prv (A :: fst s, snd s)) -> (forall leaf, InT leaf (Canopy (nodupseq s)) -> GLS_prv (A :: fst leaf, snd leaf))).
  Proof.
  intros. split ; intros.
  - apply Canopy_equiprv_genL in X. simpl in X.
    apply incl_prv with (s0:=(A :: nodup eq_dec_form (fst s), nodup eq_dec_form (snd s))) ; simpl ; auto.
    intros B HB. inversion HB ; simpl ; auto. right. apply nodup_In in H ; auto. intros B HB. apply nodup_In in HB ; auto.
  - pose (Canopy_equiprv_genL s A). simpl in p. destruct p. clear g. apply Canopy_nodupseq_perm in H.
    destruct H. destruct p ; subst. pose (g0 X _ i).
    apply incl_prv with (s0:=(A :: (fst x), (snd x))) ; simpl ; auto.
    intros B HB. apply (nodup_In eq_dec_form) ; apply (nodup_In eq_dec_form) in HB. destruct p.
    simpl in *. destruct (in_dec eq_dec_form A (fst x)).
    + destruct (in_dec eq_dec_form A (fst leaf)).
       apply Permutation_in with (l:=(nodup eq_dec_form (fst x))) ; auto ; apply Permutation_PermutationT ; destruct x ; destruct leaf ; simpl in * ; auto.
       exfalso. apply n. apply Permutation_PermutationT in p. apply (nodup_In eq_dec_form).
       apply Permutation_in with (l:=(nodup eq_dec_form (fst x))) ; auto. apply (nodup_In eq_dec_form) ; auto.
    + destruct (in_dec eq_dec_form A (fst leaf)).
       exfalso. apply n. apply Permutation_PermutationT in p. apply (nodup_In eq_dec_form).
       apply Permutation_in with (l:=(nodup eq_dec_form (fst leaf))) ; auto. apply Permutation_sym ; auto. apply (nodup_In eq_dec_form) ; auto.
       simpl ; inversion HB ; auto. right.
       apply Permutation_in with (l:=(nodup eq_dec_form (fst x))) ; auto ; apply Permutation_PermutationT ; destruct x ; destruct leaf ; simpl in * ; auto.
    + intros B HB. apply (nodup_In eq_dec_form) ; apply (nodup_In eq_dec_form) in HB. destruct p.
       apply Permutation_in with (l:=(nodup eq_dec_form (snd x))) ; auto ; apply Permutation_PermutationT ; destruct x ; destruct leaf ; simpl in * ; auto.
  Qed.

  End nodup_facts.



