Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import String.

Require Import general_export.

Require Import KS_export.

Require Import UIK_Def_measure.
Require Import UIK_Canopy.
Require Import UIK_irred_short.
Require Import UIK_basics.
Require Import UIK_braga.





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

  Lemma propvar_subform_list_unboxed_list : forall l A, In A (propvar_subform_list (unboxed_list l)) -> In A (propvar_subform_list l).
  Proof.
  induction l.
  - auto.
  - simpl. intros. apply in_app_or in H. destruct H. apply in_or_app ; left. destruct a ; auto.
    apply in_or_app ; auto.
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
  induction l ; simpl ; intros ; auto. repeat rewrite <- app_nil_end in H.
  apply in_app_or in H. apply in_or_app. destruct H ; auto.
  Qed.

  Lemma propvar_subform_list_disj : forall l A,
            In A (propvar_subform (list_disj l)) -> In A (propvar_subform_list l).
  Proof.
  induction l ; simpl ; intros ; auto. repeat rewrite <- app_nil_end in H.
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

  Lemma propvar_subform_list_restr_list_prop : forall l p q, In # q (propvar_subform_list (restr_list_prop p l)) ->
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

  Lemma In_unboxed_list : forall l A, In A (unboxed_list (top_boxes l)) -> (exists B, In B (top_boxes l) /\ B = Box A).
  Proof.
  induction l ; intros ; auto. simpl in H. exfalso ; auto. destruct a ; simpl ; simpl in H ; auto.
  destruct H ; subst. exists (Box A) ; auto.
  apply IHl in H. destruct H. firstorder.
  Qed.

  Lemma unboxed_list_In : forall l A, In (Box A) (top_boxes l) -> In A (unboxed_list (top_boxes l)).
  Proof.
  induction l ; simpl ; intros ; auto. destruct a ; simpl ; simpl in H ; auto. destruct H. inversion H ; subst. auto.
  apply IHl in H ; auto.
  Qed.

  Lemma unboxed_list_In_unfold : forall l A, (exists B, In B (top_boxes l) /\ B = Box A) -> In A (unboxed_list (top_boxes l)).
  Proof.
  induction l ; simpl ; intros ; auto. destruct H. destruct H ; auto.
  destruct a ; simpl ; simpl in H ; auto. destruct H. destruct H. subst. destruct H.
  inversion H ; subst ; auto. right. apply unboxed_list_In ; auto.
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

  End Diam_help.




  Section list_conj_disj_properties.

  Lemma AndL : forall s A B, KS_prv (A :: B :: fst s, snd s) -> KS_prv (And A B :: fst s, snd s).
  Proof.
  intros. unfold And. unfold Neg.
  apply derI with (ps:=[([] ++ fst s, [] ++ (A --> B --> Bot) :: snd s); ([] ++ Bot :: fst s, [] ++ snd s)]).
  apply ImpL. assert (((A --> B --> Bot) --> Bot :: fst s, snd s) = ([] ++ (A --> B --> Bot) --> Bot :: fst s, snd s)). auto.
  rewrite H. apply ImpLRule_I. apply dlCons. 2: apply dlCons. 3: apply dlNil.
  apply derI with (ps:=[([] ++ A :: fst s, [] ++ B --> Bot :: snd s)]). apply ImpR. apply ImpRRule_I.
  apply dlCons. 2: apply dlNil. apply derI with (ps:=[([A] ++ B :: fst s, [] ++ Bot :: snd s)]).
  assert (([] ++ A :: fst s, [] ++ B --> Bot :: snd s) = ([A] ++ fst s, [] ++ B --> Bot :: snd s)). auto. rewrite H.
  apply ImpR. apply ImpRRule_I. apply dlCons. 2: apply dlNil.
  assert (J0: derrec_height X = derrec_height X). auto.
  assert (J1: wkn_R Bot ([A] ++ B :: fst s, [] ++ snd s) ([A] ++ B :: fst s, [] ++ Bot :: snd s)). apply wkn_RI.
  pose (KS_wkn_R _ _ X J0 _ _ J1). destruct s0. auto. apply derI with (ps:=[]). apply BotL. apply BotLRule_I.
  apply dlNil.
  Qed.

  Lemma AndR : forall s A B,  KS_prv (fst s, A :: snd s) -> KS_prv (fst s, B :: snd s) -> KS_prv (fst s, And A B :: snd s).
  Proof.
  intros. unfold And. unfold Neg.
  apply derI with (ps:=[([] ++ A --> B --> Bot :: fst s, [] ++ Bot :: snd s)]).
  apply ImpR. assert ((fst s, (A --> B --> Bot) --> Bot :: snd s) = ([] ++ fst s, [] ++ (A --> B --> Bot) --> Bot :: snd s)). auto.
  rewrite H. apply ImpRRule_I. apply dlCons. 2: apply dlNil.
  apply derI with (ps:=[([] ++ fst s, [] ++ A :: Bot :: snd s);([] ++ B --> Bot :: fst s, [] ++ Bot :: snd s)]). apply ImpL.
  apply ImpLRule_I. apply dlCons. 2: apply dlCons. 3: apply dlNil.
  assert (J0: derrec_height X = derrec_height X). auto.
  assert (J1: wkn_R Bot ([] ++ fst s, [A] ++ snd s) ([] ++ fst s, [A] ++ Bot :: snd s)). apply wkn_RI.
  pose (KS_wkn_R _ _ X J0 _ _ J1). destruct s0. auto.
  apply derI with (ps:=[([] ++ fst s, [] ++ B :: Bot :: snd s);([] ++ Bot :: fst s, [] ++ Bot :: snd s)]). apply ImpL.
  apply ImpLRule_I. apply dlCons. 2: apply dlCons. 3: apply dlNil.
  assert (J0: derrec_height X0 = derrec_height X0). auto.
  assert (J1: wkn_R Bot ([] ++ fst s, [B] ++ snd s) ([] ++ fst s, [B] ++ Bot :: snd s)). apply wkn_RI.
  pose (KS_wkn_R _ _ X0 J0 _ _ J1). destruct s0. auto. apply derI with (ps:=[]). apply BotL. apply BotLRule_I.
  apply dlNil.
  Qed.

  Lemma list_conj_wkn_L : forall l s A, InT A l -> KS_prv (A :: fst s, snd s) -> KS_prv (list_conj l :: fst s, snd s).
  Proof.
  induction l.
  - intros. inversion H.
  - intros. inversion H ; subst.
    * simpl. apply AndL.
      assert (J0: derrec_height X = derrec_height X). auto.
      assert (J1: wkn_L (list_conj l) (A :: fst s, snd s) (A :: list_conj l :: fst s, snd s)).
      assert (A :: fst s = [A] ++ fst s). auto. rewrite H0.
      assert (A :: list_conj l :: fst s = [A] ++ list_conj l :: fst s). auto. rewrite H1. apply wkn_LI.
      pose (KS_wkn_L _ _ X J0 _ _ J1). destruct s0. auto.
    * simpl. apply IHl in X ; auto.
      assert (J0: derrec_height X = derrec_height X). auto.
      assert (J1: wkn_L a (list_conj l  :: fst s, snd s) (a :: list_conj l :: fst s, snd s)).
      assert (a :: list_conj l :: fst s = [] ++ a :: list_conj l :: fst s). auto. rewrite H0.
      assert ((list_conj l  :: fst s,snd s) = ([] ++ list_conj l :: fst s,snd s)). auto. rewrite H2. apply wkn_LI.
      pose (KS_wkn_L _ _ X J0 _ _ J1). destruct s0. apply AndL ; auto.
  Qed.

  Lemma list_conj_R : forall l s, (forall A, InT A l -> KS_prv (fst s, A :: snd s)) -> KS_prv (fst s, list_conj l :: snd s).
  Proof.
  induction l.
  - intros. simpl. unfold Top.
    apply derI with (ps:=[([] ++ Bot :: fst s, [] ++ Bot :: snd s)]).
    apply ImpR. assert ((fst s, Bot --> Bot :: snd s) = ([] ++ fst s, [] ++ Bot --> Bot :: snd s)). auto.
    rewrite H. apply ImpRRule_I. apply dlCons. 2: apply dlNil. apply derI with (ps:=[]). apply BotL.
    apply BotLRule_I. apply dlNil.
  - intros. simpl. apply AndR.
    * apply X. apply InT_eq.
    * simpl. apply IHl. intros. apply X. apply InT_cons ; auto.
  Qed.

  Lemma OrL : forall s A B,  KS_prv (A :: fst s, snd s) -> KS_prv (B :: fst s, snd s) -> KS_prv (Or A B :: fst s, snd s).
  Proof.
  intros. unfold Or. unfold Neg.
  apply derI with (ps:=[([] ++ fst s, [] ++ (A --> Bot) :: snd s); ([] ++ B :: fst s, [] ++ snd s)]).
  apply ImpL. assert (((A --> Bot) --> B :: fst s, snd s) = ([] ++ (A --> Bot) --> B :: fst s, snd s)). auto.
  rewrite H. apply ImpLRule_I. apply dlCons. 2: apply dlCons. 3: apply dlNil.
  apply derI with (ps:=[([] ++ A :: fst s, [] ++ Bot :: snd s)]). apply ImpR. apply ImpRRule_I.
  apply dlCons. 2: apply dlNil.
  assert (J0: derrec_height X = derrec_height X). auto.
  assert (J1: wkn_R Bot (A :: fst s, [] ++ snd s) (A :: fst s, [] ++ Bot :: snd s)). apply wkn_RI.
  pose (KS_wkn_R _ _ X J0 _ _ J1). destruct s0. auto. auto.
  Qed.

  Lemma OrR : forall s A B, KS_prv (fst s, A :: B :: snd s) -> KS_prv (fst s, Or A B :: snd s).
  Proof.
  intros. unfold Or. unfold Neg.
  apply derI with (ps:=[([] ++ (A --> Bot) :: fst s, [] ++ B :: snd s)]).
  apply ImpR. assert ((fst s, (A --> Bot) --> B :: snd s) = (fst s, [] ++ (A --> Bot) --> B :: snd s)). auto.
  rewrite H. apply ImpRRule_I. apply dlCons. 2: apply dlNil.
  apply derI with (ps:=[([] ++ fst s, [] ++ A :: B :: snd s);([] ++ Bot :: fst s, [] ++ B :: snd s)]).
  apply ImpL. apply ImpLRule_I.
  apply dlCons. 2: apply dlCons. 3: apply dlNil. simpl ; auto.
  apply derI with (ps:=[]). apply BotL. apply BotLRule_I. apply dlNil.
  Qed.

  Lemma list_disj_L : forall l s, (forall A, InT A l -> KS_prv (A :: fst s, snd s)) -> KS_prv (list_disj l :: fst s, snd s).
  Proof.
  induction l.
  - intros. simpl. apply derI with (ps:=[]). apply BotL. assert ((Bot :: fst s, snd s) = ([] ++ Bot :: fst s, snd s)). auto.
    rewrite H. apply BotLRule_I. apply dlNil.
  - intros. simpl. apply OrL.
    * apply X. apply InT_eq.
    * simpl. apply IHl. intros. apply X. apply InT_cons ; auto.
  Qed.

  Lemma list_disj_wkn_R : forall l s A, InT A l -> KS_prv (fst s, A :: snd s) -> KS_prv (fst s, list_disj l :: snd s).
  Proof.
  induction l.
  - intros. inversion H.
  - intros. inversion H ; subst.
    * simpl. apply OrR.
      assert (J0: derrec_height X = derrec_height X). auto.
      assert (J1: wkn_R (list_disj l) (fst s, A :: snd s) (fst s, A :: list_disj l :: snd s)).
      assert (A :: snd s = [A] ++ snd s). auto. rewrite H0.
      assert (A :: list_disj l :: snd s = [A] ++ list_disj l :: snd s). auto. rewrite H1. apply wkn_RI.
      pose (KS_wkn_R _ _ X J0 _ _ J1). destruct s0. auto.
    * simpl. apply IHl in X ; auto.
      assert (J0: derrec_height X = derrec_height X). auto.
      assert (J1: wkn_R a (fst s, list_disj l  :: snd s) (fst s, a :: list_disj l :: snd s)).
      assert (a :: list_disj l :: snd s = [] ++ a :: list_disj l :: snd s). auto. rewrite H0.
      assert ((fst s, list_disj l  :: snd s) = (fst s, [] ++ list_disj l :: snd s)). auto. rewrite H2. apply wkn_RI.
      pose (KS_wkn_R _ _ X J0 _ _ J1). destruct s0. apply OrR ; auto.
  Qed.

  Lemma DiamL_lim : forall A BΓ Γ0 Δ, (is_Boxed_list BΓ) ->
                                                                      (nobox_gen_ext BΓ Γ0) ->
                                                                      (KS_prv (A :: unboxed_list BΓ, [])) ->
                                                                      (KS_prv (Diam A :: Γ0, Δ)).
  Proof.
  intros. unfold Diam. unfold Neg.
  apply derI with (ps:=[([] ++ Γ0, [] ++ Box (A --> Bot) :: Δ);([] ++ Bot :: Γ0, [] ++ Δ)]).
  apply ImpL. assert ((Box (A --> Bot) --> Bot :: Γ0, Δ) = ([] ++ Box (A --> Bot) --> Bot :: Γ0, [] ++ Δ)). auto.
  rewrite H0. apply ImpLRule_I. apply dlCons. 2: apply dlCons. 3: apply dlNil.
  2: apply derI with (ps:=[]) ; try apply dlNil ; try apply BotL ; apply BotLRule_I.
  apply derI with (ps:=[(unboxed_list BΓ, [A --> Bot])]).
  apply KR. apply KRRule_I ; auto. apply dlCons. 2: apply dlNil.
  apply derI with (ps:=[([] ++ A :: unboxed_list BΓ, [] ++ Bot :: [])]).
  apply ImpR. assert ((unboxed_list BΓ, [A --> Bot]) = ([] ++ unboxed_list BΓ, [] ++ A --> Bot :: [])). auto.
  rewrite H0. apply ImpRRule_I. apply dlCons. 2: apply dlNil.
  assert (J0: derrec_height X0 = derrec_height X0) ; auto.
  assert (J3: wkn_R Bot (A :: unboxed_list BΓ, []%list) (A :: unboxed_list BΓ, [Bot])).
  assert ((A :: unboxed_list BΓ, @nil MPropF) =  (A :: unboxed_list BΓ, [] ++ [])).
  rewrite <- app_nil_end. auto. rewrite H0.
  assert ((A :: unboxed_list BΓ, [Bot]) =  (A :: unboxed_list BΓ, [] ++ Bot :: [])). auto. rewrite H1.
  apply wkn_RI. pose (KS_wkn_R _ _ X0 J0 _ _ J3). destruct s. simpl. auto.
  Qed.

  Lemma nobox_top_boxes : forall l, nobox_gen_ext (top_boxes l) l.
  Proof.
  induction l ; simpl ; auto. apply univ_gen_ext_nil. destruct a.
  1-3: apply univ_gen_ext_extra ; auto ; intro ; inversion X ; inversion H.
  apply univ_gen_ext_cons ; auto.
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
    unfold is_init. destruct X.
    left. inversion i2 ; subst. assert (InT (# P) (Γ0 ++ A :: Γ1)). apply InT_or_app.
    assert (InT (# P) (Γ0 ++ Γ1)). rewrite <- H. apply InT_or_app ; right ;apply InT_eq. apply InT_app_or in H0.
    destruct H0 ; auto. right ; apply InT_cons ; auto. apply InT_split in H0. destruct H0. destruct s. rewrite e.
    assert (InT (# P) (Δ0 ++ B :: Δ1)). apply InT_or_app.
    assert (InT (# P) (Δ0 ++ A --> B :: Δ1)). rewrite <- H1. apply InT_or_app ; right ;apply InT_eq. apply InT_app_or in H0.
    destruct H0 ; auto. inversion i3 ; subst. inversion H2. right ; apply InT_cons ; auto. apply InT_split in H0. destruct H0. destruct s.
    rewrite e0. apply IdPRule_I.
    right. inversion b ; subst. assert (InT (Bot) (Γ0 ++ A :: Γ1)). apply InT_or_app.
    assert (InT (Bot) (Γ0 ++ Γ1)). rewrite <- H. apply InT_or_app ; right ;apply InT_eq. apply InT_app_or in H0.
    destruct H0 ; auto. right ; apply InT_cons ; auto. apply InT_split in H0. destruct H0. destruct s. rewrite e. apply BotLRule_I.
  - inversion i1 ; subst. inversion i ; subst. 2: inversion H0. 3: inversion H1.
    assert (J0: n_imp_subformS (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) < n_imp_subformS (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)).
    unfold n_imp_subformS. simpl. repeat rewrite n_imp_subformLF_dist_app. simpl ; repeat rewrite n_imp_subformLF_dist_app.
    lia. apply IHs with (leaf:=leaf) in J0 ; auto.
    unfold is_init. destruct X.
    left. inversion i2 ; subst. assert (InT (# P) (Γ0 ++ Γ1)). apply InT_or_app.
    assert (InT (# P) (Γ0 ++ A --> B :: Γ1)). rewrite <- H. apply InT_or_app ; right ;apply InT_eq. apply InT_app_or in H0.
    destruct H0 ; auto. inversion i3 ; subst. inversion H2. auto. apply InT_split in H0. destruct H0. destruct s. rewrite e.
    assert (InT (# P) (Δ0 ++ A :: Δ1)). apply InT_or_app.
    assert (InT (# P) (Δ0 ++ Δ1)). rewrite <- H1. apply InT_or_app ; right ;apply InT_eq. apply InT_app_or in H0.
    destruct H0 ; auto. right ; apply InT_cons ; auto. apply InT_split in H0. destruct H0. destruct s.
    rewrite e0. apply IdPRule_I.
    right. inversion b ; subst. assert (InT (Bot) (Γ0 ++ Γ1)). apply InT_or_app.
    assert (InT (Bot) (Γ0 ++ A --> B :: Γ1)). rewrite <- H. apply InT_or_app ; right ;apply InT_eq. apply InT_app_or in H0.
    destruct H0 ; auto. inversion i2 ; subst. inversion H1. auto. apply InT_split in H0. destruct H0. destruct s. rewrite e. apply BotLRule_I.
    assert (J0: n_imp_subformS (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) < n_imp_subformS (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)).
    unfold n_imp_subformS. simpl. repeat rewrite n_imp_subformLF_dist_app. simpl ; repeat rewrite n_imp_subformLF_dist_app.
    lia. subst. apply IHs with (leaf:=leaf) in J0 ; auto.
    unfold is_init. destruct X.
    left. inversion i2 ; subst. assert (InT (# P) (Γ0 ++ B :: Γ1)). apply InT_or_app.
    assert (InT (# P) (Γ0 ++ A --> B :: Γ1)). rewrite <- H. apply InT_or_app ; right ;apply InT_eq. apply InT_app_or in H1.
    destruct H1 ; auto. inversion i3 ; subst. inversion H3. right ; apply InT_cons ; auto. apply InT_split in H1. destruct H1. destruct s. rewrite e.
    apply IdPRule_I.
    right. inversion b ; subst. assert (InT (Bot) (Γ0 ++ B :: Γ1)). apply InT_or_app.
    assert (InT (Bot) (Γ0 ++ A --> B :: Γ1)). rewrite <- H. apply InT_or_app ; right ;apply InT_eq. apply InT_app_or in H1.
    destruct H1 ; auto. inversion i2 ; subst. inversion H2. right ; apply InT_cons ; auto. apply InT_split in H1. destruct H1. destruct s. rewrite e. apply BotLRule_I.
  Qed.

  Lemma TopR : forall X Y0 Y1, KS_prv (X, Y0 ++ Top :: Y1).
  Proof.
  intros. unfold Top. apply derI with (ps:=[([] ++ Bot :: X, Y0 ++ Bot :: Y1)]).
  apply ImpR. assert ((X, Y0 ++ Bot --> Bot :: Y1) = ([] ++ X, Y0 ++ Bot --> Bot :: Y1)). auto.
  rewrite H. apply ImpRRule_I. apply dlCons. 2: apply dlNil. apply derI with (ps:=[]).
  apply BotL. apply BotLRule_I. apply dlNil.
  Qed.

  Lemma TopL_remove : forall Y X0 X1, KS_prv (X0 ++ Top :: X1, Y) -> KS_prv (X0 ++ X1, Y).
  Proof.
  intros. assert (Y= [] ++ Y). auto. rewrite H. rewrite H in X. apply KS_cut_adm with (A:=Top) ; auto.
  apply TopR.
  Qed.

  Theorem is_init_UI_equiv_Top : forall s, is_init s -> forall p X Y0 Y1, KS_prv (X, Y0 ++ Top --> (UI p s) :: Y1).
  Proof.
  intros. destruct (critical_Seq_dec s).
  - assert (J0: GUI p s (UI p s)). apply UI_GUI ; auto.
    pose (@GUI_inv_critic_init p s (UI p s) J0 c X). rewrite <- e.
    apply derI with (ps:=[([] ++ Top :: X0, Y0 ++ Top :: Y1)]).
    apply ImpR. epose (ImpRRule_I _ _ []). simpl in i ; apply i.
    apply dlCons. 2: apply dlNil. apply TopR.
  - assert (J0: GUI p s (UI p s)). apply UI_GUI ; auto.
    assert (J1: Gimap (GUI p) (Canopy s) (map (UI p) (Canopy s))). apply Gimap_map. intros.
    apply UI_GUI ; auto.
    pose (@GUI_inv_not_critic p s (UI p s) (map (UI p) (Canopy s)) J0 f J1). rewrite <- e.
    apply derI with (ps:=[([] ++ Top :: X0, Y0 ++ list_conj (map (UI p) (Canopy s)) :: Y1)]).
    apply ImpR. epose (ImpRRule_I _ _ []). simpl in i ; apply i. apply dlCons. 2: apply dlNil. simpl.
    apply KS_adm_list_exch_R with (s:=(Top :: X0, list_conj (map (UI p) (Canopy s)) :: Y0 ++ Y1)).
    pose (list_conj_R (map (UI p) (Canopy s)) (Top :: X0, Y0 ++ Y1)). apply k. clear k.
    intros. simpl. apply InT_map_iff in H. destruct H. destruct p0. subst.
    assert (J2: GUI p x (UI p x)). apply UI_GUI ; auto.
    assert (J3: critical_Seq x). apply Canopy_critical in i ; auto.
    assert (J4: is_init x). apply is_init_Canopy in i ; auto.
    pose (@GUI_inv_critic_init p x (UI p x) J2 J3 J4). rewrite <- e0. epose (TopR _ [] _). simpl in k ; apply k.
    epose (list_exch_RI _ [] [_] Y0 [] _). simpl in l. apply l.
  Qed.

  Theorem is_init_UI : forall s, is_init s -> forall p X Y0 Y1, KS_prv (X, Y0 ++ UI p s :: Y1).
  Proof.
  intros. eapply is_init_UI_equiv_Top in X. apply ImpR_inv with (prem:=([] ++ Top :: X0, Y0 ++ UI p s :: Y1)) in X.
  apply TopL_remove in X. simpl in X ; auto. assert ((X0, Y0 ++ Top --> UI p s :: Y1) = ([] ++ X0, Y0 ++ Top --> UI p s :: Y1)).
  auto. rewrite H. apply ImpRRule_I.
  Qed.

  End list_conj_disj_properties.






Section Canopy_lems.

  Lemma inv_prems_measure : forall s0 s1, InT s1 (inv_prems s0) ->  (measure s1 < measure s0).
  Proof.
  intros. unfold inv_prems in H. apply InT_flatten_list_InT_elem in H.
  destruct H. destruct p. destruct (finite_ImpRules_premises_of_S s0). simpl in i0.
  apply p in i0. destruct i0 ; inversion i0 ; subst. inversion i ; subst. unfold measure ; simpl.
  repeat rewrite size_LF_dist_app ; simpl ; lia. inversion H0. inversion i ; subst.
  unfold measure ; simpl ; repeat rewrite size_LF_dist_app ; simpl ; lia.
  inversion H0 ; subst. unfold measure ; simpl ; repeat rewrite size_LF_dist_app ; simpl ; lia.
  inversion H1.
  Qed.

  Lemma Canopy_measure: forall s0 s1, InT s1 (Canopy s0) -> ((s0 = s1) + (measure s1 < measure s0)).
  Proof.
  intros s ; induction on s as IHs with measure (measure s).
  intros. remember (finite_ImpRules_premises_of_S s) as H0. destruct H0. destruct x.
  - left. assert (Canopy s = [s]). apply irred_nil. unfold inv_prems ; rewrite <- HeqH0 ; auto.
    rewrite H0 in H. inversion H ; subst ; auto. inversion H2.
  - apply fold_Canopy in H. destruct H ; auto. right. destruct s0. destruct p0. apply IHs in i0.
    destruct i0 ; subst ; auto. apply inv_prems_measure in i ; auto. apply inv_prems_measure in i. lia.
    unfold inv_prems in i. apply InT_flatten_list_InT_elem in i.
    destruct i. destruct p0. rewrite <- HeqH0 in i1. simpl in i1. apply p in i1. destruct i1 ; inversion i1 ; subst.
    inversion i. subst. unfold measure ; simpl ; repeat rewrite size_LF_dist_app ; simpl ; lia.
    inversion H0. inversion i ; subst. unfold measure ; simpl ; repeat rewrite size_LF_dist_app ; simpl ; lia.
    inversion H0 ; subst. unfold measure ; simpl ; repeat rewrite size_LF_dist_app ; simpl ; lia.
    inversion H1.
  Qed.

End Canopy_lems.









