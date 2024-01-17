  (* Closure of sequents *)

  Require Import List.
  Export ListNotations.
  Require Import Lia.

  Require Import Coq.Init.Wf.

  Require Import GLS_export.
  Require Import UIGL_Def_measure.

  Require Import UIGL_irred_short UIGL_irred_high_level.

  Require Import general_export.

  (* Defining the premises of a sequent via Imp rules. *)

  Lemma finite_ImpRules_premises_of_S : forall (s : Seq), existsT2 listImpRulesprems,
                (forall prems, (((ImpRRule prems s) + (ImpLRule prems s)) -> (InT prems listImpRulesprems)) *
                               ((InT prems listImpRulesprems) -> ((ImpRRule prems s) + (ImpLRule prems s)))).
  Proof.
  intros.
  pose (finite_ImpR_premises_of_S s). destruct s0.
  pose (finite_ImpL_premises_of_S s). destruct s0.
  exists (x ++ x0). intros. split ; intro.
  - destruct H.
    + inversion i. subst. apply InT_or_app. left. apply p. apply ImpRRule_I.
    + inversion i. subst. apply InT_or_app. right. apply p0. apply ImpLRule_I.
  - apply InT_app_or in H. destruct H.
    + left. apply p ; auto.
    + right. apply p0 ; auto.
  Defined.

  Definition inv_prems (s : Seq) := flatten_list (proj1_sigT2 (finite_ImpRules_premises_of_S s)).

  (* The number of implication symbols in a sequent gives a measure
      which has a well-founded order.*)

  Definition less_imp (s0 s1 : Seq) := (n_imp_subformS s0) < (n_imp_subformS s1).

  Lemma Acc_less_imp : well_founded less_imp.
  Proof.
  intros s ; induction on s as IHm with measure (n_imp_subformS s).
  apply Acc_intro. auto.
  Defined.

  Definition invprem (s0 s1 : Seq) := In s0 (inv_prems s1).

  Lemma InT_In_inv_prems : forall s0 s1, (InT s0 (inv_prems s1) ->  In s0 (inv_prems s1)) *
                                                                   (In s0 (inv_prems s1) ->  InT s0 (inv_prems s1)).
  Proof.
  intros. split ; intros.
  - apply InT_In ; auto.
  - unfold inv_prems. unfold inv_prems in H. destruct (finite_ImpRules_premises_of_S s1).
    simpl. simpl in H. apply In_InT_seqs. auto.
Qed.

  Lemma Acc_invprem : well_founded invprem.
  Proof.
  intros s ; induction on s as IHs with measure (n_imp_subformS s).
  apply Acc_intro. intros. apply IHs. unfold invprem in H.
  apply InT_In_inv_prems in H. unfold inv_prems in H.
  destruct (finite_ImpRules_premises_of_S s) in H. simpl in H.
  apply InT_flatten_list_InT_elem in H. destruct H. destruct p0.
  apply p in i0. destruct i0.
  inversion i0. subst. inversion i. subst.
  unfold n_imp_subformS ; simpl. repeat rewrite n_imp_subformLF_dist_app.
  simpl. lia. subst. inversion H0.
  inversion i0. subst. inversion i. subst.
  unfold n_imp_subformS ; simpl. repeat rewrite n_imp_subformLF_dist_app.
  simpl. lia. subst.
  inversion H0. subst.
  unfold n_imp_subformS ; simpl. repeat rewrite n_imp_subformLF_dist_app.
  simpl. lia. subst. inversion H1.
  Defined.

  (* The closure of a sequent is the list of all sequents which can be
      reach via chains of backward applications of invertible rules. *)

  Definition Canopy := irred Acc_invprem.

  (* Critical sequents are sequents on which no invertible (Imp)
      rule is backward applicable. *)

  Definition critical_Seq (s : Seq) := is_Prime ((fst s) ++ (snd s)).

  Lemma is_Prime_dec : forall l, (is_Prime l) + (is_Prime l -> False).
  Proof.
  unfold is_Prime. induction l ; simpl ; auto.
  left. intros. inversion H. destruct IHl. destruct a.
  1,2,4: left ; intros ; destruct H ; auto. right. left ; exists n ; auto.
  left ; exists a ; auto. right. intro.
  assert (a1 --> a2 = a1 --> a2 \/ In (a1 --> a2) l). left ; auto. apply H in H0.
  destruct H0. destruct H0. inversion H0. destruct H0. destruct H0 ; inversion H0.
  inversion H0. right. intros. apply f. intros. apply H. auto.
  Qed.

  Lemma critical_Seq_dec (s : Seq) : (critical_Seq s) + (critical_Seq s -> False).
  Proof.
  unfold critical_Seq. destruct s ; simpl. apply is_Prime_dec.
  Qed.

  (* We show that all sequents in Canopy are critical. *)

  Lemma inv_prems_id_critical : forall s, inv_prems s = [] -> critical_Seq s.
  Proof.
  intros. destruct s. unfold critical_Seq. intros A H0. destruct A.
  right ; left ; exists n ; auto. right ; auto.
  2: left ; exists A ; auto. exfalso. simpl in H0.
  apply in_app_or in H0 ; destruct H0.
  apply in_split in H0. destruct H0. destruct H0. subst.
  assert (In (x ++ A2 :: x0, l0) (inv_prems (x ++ A1 --> A2 :: x0, l0))).
  unfold inv_prems. apply InT_In.
  apply InT_trans_flatten_list with (bs:=[(x ++ x0, [] ++ A1 :: l0);(x ++ A2 :: x0, [] ++ l0)]).
  apply InT_cons ; apply InT_eq.
  destruct (finite_ImpRules_premises_of_S (x ++ A1 --> A2 :: x0, l0)).
  apply p. right. assert ((x ++ A1 --> A2 :: x0, l0) = (x ++ A1 --> A2 :: x0, [] ++ l0)). auto.
  rewrite H0. apply ImpLRule_I.
  rewrite H in H0. inversion H0.
  apply in_split in H0. destruct H0. destruct H0. subst.
  assert (In (l ++ A1 :: [], x ++ A2 :: x0) (inv_prems (l ++ [] , x ++ A1 --> A2 :: x0))).
  unfold inv_prems. apply InT_In.
  apply InT_trans_flatten_list with (bs:=[(l ++ [A1], x ++ A2 :: x0)]). apply InT_eq.
  destruct (finite_ImpRules_premises_of_S (l ++ [], x ++ A1 --> A2 :: x0)).
  apply p. left. apply ImpRRule_I. rewrite <- app_nil_end in H0.
  rewrite H in H0. inversion H0.
  Qed.

  Lemma Canopy_critical : forall s leaf, InT leaf (Canopy s) -> (critical_Seq leaf).
  Proof.
  unfold Canopy.
  intros s ; induction on s as IHs with measure (n_imp_subformS s).
  intros. remember (inv_prems s) as prems. destruct prems.
  - symmetry in Heqprems ; pose (irred_nil _ _ Acc_invprem s Heqprems).
    rewrite e in H. pose (inv_prems_id_critical _ Heqprems). inversion H ; subst ; auto.
    inversion H1.
  - assert (J1: inv_prems s <> []%list). rewrite <- Heqprems. intro.
    inversion H0. pose (irred_not _ _ Acc_invprem s J1). rewrite e in H.
    pose (InT_In H). apply in_flat_map in i. destruct i. destruct H0.
    apply In_InT_seqs in H1. apply IHs with (y:=x) ; auto.
    apply InT_In_inv_prems in H0. unfold inv_prems in H0.
    destruct (finite_ImpRules_premises_of_S s) in H0. simpl in H0.
    apply InT_flatten_list_InT_elem in H0. destruct H0. destruct p0.
    apply p in i0. destruct i0.
    inversion i0. subst. inversion i. subst.
    unfold n_imp_subformS ; simpl. repeat rewrite n_imp_subformLF_dist_app.
    simpl. lia. subst. inversion H2.
    inversion i0. subst. inversion i. subst.
    unfold n_imp_subformS ; simpl. repeat rewrite n_imp_subformLF_dist_app.
    simpl. lia. subst.
    inversion H2. subst.
    unfold n_imp_subformS ; simpl. repeat rewrite n_imp_subformLF_dist_app.
    simpl. lia. subst. inversion H3.
  Qed.

  (* We show the equiprovability between a sequent and its Canopy. *)

  Lemma ImpRule_Canopy : forall s prems, ((ImpRRule prems s) + (ImpLRule prems s)) ->
                (forall prem, InT prem prems -> (forall leaf, InT leaf (Canopy prem) -> InT leaf (Canopy s))).
  Proof.
  intros. unfold Canopy. rewrite irred_not. apply In_InT_seqs.
  apply in_flat_map. exists prem ; split ; auto. 2: apply InT_In ; auto.
  unfold inv_prems. apply InT_In. apply InT_trans_flatten_list with (bs:=prems) ; auto.
  destruct (finite_ImpRules_premises_of_S s) ; simpl. apply p ; auto.
  intro. unfold inv_prems in H2. destruct (finite_ImpRules_premises_of_S s) ; simpl.
  simpl in H2. apply p in H. assert (InT prem (flatten_list x)).
  apply InT_trans_flatten_list with (bs:=prems) ; auto. rewrite H2 in H3. inversion H3.
  Qed.

  (* Move the lemma below to a more general location. *)

  Lemma InT_flat_map: forall (f : Seq -> list Seq) (l : list Seq) (y : Seq), (InT y (flat_map f l) -> (existsT2 x : Seq, InT x l * InT y (f x))) *
                                                                                                                ( (existsT2 x : Seq, InT x l * InT y (f x)) -> InT y (flat_map f l)).
  Proof.
  intros f. induction l.
  - intros ; split ; intros. simpl in H. inversion H. simpl. destruct H. destruct p. inversion i.
  - intros ; simpl ; split ; intros. apply InT_app_or in H. destruct H. exists a ; split ; auto. apply InT_eq.
    apply IHl in i. destruct i. destruct p. exists x ; split ; auto. apply InT_cons ; auto.
    apply InT_or_app. destruct H. destruct p. inversion i ; subst ; auto. right.
    apply IHl. exists x ; split ; auto.
  Qed.

  Lemma fold_Canopy : forall s leaf, InT leaf (Canopy s) ->
                  (leaf = s) + (existsT2 prem, InT prem (inv_prems s) * InT leaf (Canopy prem)).
  Proof.
  intros. remember (finite_ImpRules_premises_of_S s) as J.
  destruct J. destruct x.
  - assert (Canopy s = [s]). apply irred_nil. unfold inv_prems. rewrite <- HeqJ.
    simpl. auto. rewrite H0 in H. inversion H ; subst ; auto. inversion H2.
  - right. unfold Canopy in H. rewrite irred_not in H. apply InT_flat_map in H. destruct H.
    destruct p0. exists x0 ; split ; auto. intro. unfold inv_prems in H0. rewrite <- HeqJ in H0.
    assert (InT l (l :: x)). apply InT_eq. apply p in H1. destruct H1 ; inversion i ; subst ;
    simpl in H0 ; inversion H0.
  Qed.

  Lemma Canopy_equiprv : forall s,
    ((forall leaf, InT leaf (Canopy s) -> GLS_prv leaf) -> (GLS_prv s)) *
    ((GLS_prv s) -> (forall leaf, InT leaf (Canopy s) -> GLS_prv leaf)).
  Proof.
  intros s ; induction on s as IHs with measure (n_imp_subformS s).
  intros ; split ; intros.
  - remember (finite_ImpRules_premises_of_S s) as H.
    destruct H. destruct x.
    + assert (Canopy s = [s]). apply irred_nil. unfold inv_prems. rewrite <- HeqH.
       simpl. auto. rewrite H in X. apply X. apply InT_eq.
    + assert (J1: InT l (l :: x)). apply InT_eq. apply p in J1. destruct J1 ; unfold GLS_prv ; apply derI with (ps:=l).
       apply ImpR ; auto. 2: apply ImpL ; auto. all: inversion i ; subst ; apply dlCons. 4: apply dlCons. 2,5: apply dlNil.
       all: apply IHs. 1,3,5: unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
       all: intros ; apply X. apply ImpRule_Canopy with (prems:=[(Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)]) (prem:=(Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)) ; auto.
       apply InT_eq. apply ImpRule_Canopy with (prems:=[(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)])
       (prem:=(Γ0 ++ Γ1, Δ0 ++ A :: Δ1)) ; auto. apply InT_eq.
        apply ImpRule_Canopy with (prems:=[(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)])
       (prem:=(Γ0 ++ B :: Γ1, Δ0 ++ Δ1)) ; auto. apply InT_cons ; apply InT_eq.
  - apply fold_Canopy in H. destruct H ; subst ; auto. destruct s0. destruct p.
    unfold inv_prems in i ; apply InT_flatten_list_InT_elem in i ; destruct i ; destruct p ; destruct (finite_ImpRules_premises_of_S s) ;
    simpl in i1. apply p in i1. destruct i1 ; inversion i1 ; subst.
    + inversion i ; subst. 2: inversion H0. apply IHs with (y:=(Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)) ; auto.
       unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
       apply ImpR_inv with (concl:=(Γ0 ++ Γ1, Δ0 ++ A --> B :: Δ1)) ; auto.
    + inversion i ; subst. apply IHs with (y:=(Γ0 ++ Γ1, Δ0 ++ A :: Δ1)) ; auto.
       unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
       apply ImpL_inv with (concl:=(Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)) (prem2:= (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)) ; auto.
       inversion H0 ; subst. 2: inversion H1. apply IHs with (y:=(Γ0 ++ B :: Γ1, Δ0 ++ Δ1)) ; auto.
       unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
       apply ImpL_inv with (concl:=(Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)) (prem1:= (Γ0 ++ Γ1, Δ0 ++ A :: Δ1)) ; auto.
  Qed.

  Lemma Canopy_equiprv_genL : forall s A,
    ((forall leaf, InT leaf (Canopy s) -> GLS_prv (A :: fst leaf, snd leaf)) -> (GLS_prv (A :: fst s, snd s))) *
    ((GLS_prv (A :: fst s, snd s)) -> (forall leaf, InT leaf (Canopy s) -> GLS_prv (A :: fst leaf, snd leaf))).
  Proof.
  intros s ; induction on s as IHs with measure (n_imp_subformS s).
  intros ; split ; intros.
  - remember (finite_ImpRules_premises_of_S s) as H0.
    destruct H0. destruct x.
    + assert (Canopy s = [s]). apply irred_nil. unfold inv_prems. rewrite <- HeqH0.
       simpl. auto. rewrite H in X. apply X. apply InT_eq.
    + assert (J1: InT l (l :: x)). apply InT_eq. apply p in J1. destruct J1 ; unfold GLS_prv ; inversion i ; subst ; simpl.
       apply derI with (ps:=[(A :: Γ0 ++ A0 :: Γ1, Δ0 ++ B :: Δ1)]).
       apply ImpR ; auto. assert ((A :: Γ0 ++ A0 :: Γ1) = ((A :: Γ0) ++ A0 :: Γ1)). auto. rewrite H.
       assert (A :: Γ0 ++ Γ1 = (A :: Γ0) ++ Γ1). auto. rewrite H0. apply ImpRRule_I. apply dlCons. 2: apply dlNil.
       2: apply derI with (ps:=[(A :: Γ0 ++ Γ1, Δ0 ++ A0 :: Δ1);(A :: Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]).
       2: apply ImpL ; auto. 2: assert (A :: Γ0 ++ Γ1 = ((A :: Γ0) ++ Γ1)) ; auto ; rewrite H.
       2: assert (A :: Γ0 ++ B :: Γ1 = (A :: Γ0) ++ B :: Γ1) ; auto ; rewrite H0. 2: apply ImpLRule_I. 2: apply dlCons.
       3: apply dlCons. 4: apply dlNil.
       assert (J2: n_imp_subformS (Γ0 ++ A0 :: Γ1, Δ0 ++ B :: Δ1) < n_imp_subformS (Γ0 ++ Γ1, Δ0 ++ A0 --> B :: Δ1)).
       unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
       apply IHs with (A:=A) in J2. simpl in J2. destruct J2. apply g. intros. apply X.
       apply ImpRule_Canopy with (prems:=[(Γ0 ++ A0 :: Γ1, Δ0 ++ B :: Δ1)]) (prem:=(Γ0 ++ A0 :: Γ1, Δ0 ++ B :: Δ1)) ; auto.
       apply InT_eq.
       assert (J2: n_imp_subformS (Γ0 ++ Γ1, Δ0 ++ A0 :: Δ1) < n_imp_subformS (Γ0 ++ A0 --> B :: Γ1, Δ0 ++ Δ1)).
       unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
       apply IHs with (A:=A) in J2. simpl in J2. destruct J2. apply g. intros. apply X.
       apply ImpRule_Canopy with (prems:=[(Γ0 ++ Γ1, Δ0 ++ A0 :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)])
       (prem:=(Γ0 ++ Γ1, Δ0 ++ A0 :: Δ1)) ; auto. apply InT_eq.
       assert (J2: n_imp_subformS (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) < n_imp_subformS (Γ0 ++ A0 --> B :: Γ1, Δ0 ++ Δ1)).
       unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
       apply IHs with (A:=A) in J2. simpl in J2. destruct J2. apply g. intros. apply X.
       apply ImpRule_Canopy with (prems:=[(Γ0 ++ Γ1, Δ0 ++ A0 :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)])
       (prem:=(Γ0 ++ B :: Γ1, Δ0 ++ Δ1)) ; auto. apply InT_cons.  apply InT_eq.
  - apply fold_Canopy in H. destruct H ; subst ; auto. destruct s0. destruct p.
    unfold inv_prems in i ; apply InT_flatten_list_InT_elem in i ; destruct i ; destruct p ; destruct (finite_ImpRules_premises_of_S s) ;
    simpl in i1. apply p in i1. destruct i1 ; inversion i1 ; subst.
    + inversion i ; subst. 2: inversion H0. apply IHs with (y:=(Γ0 ++ A0 :: Γ1, Δ0 ++ B :: Δ1)) ; auto.
       unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
       apply ImpR_inv with (concl:=(A :: Γ0 ++ Γ1, Δ0 ++ A0 --> B :: Δ1)) ; auto. simpl.
       assert (A :: Γ0 ++ A0 :: Γ1 =  (A :: Γ0) ++ A0 :: Γ1). auto. rewrite H.
       assert (A :: Γ0 ++ Γ1 =  (A :: Γ0) ++ Γ1). auto. rewrite H0. apply ImpRRule_I.
    + inversion i ; subst. apply IHs with (y:=(Γ0 ++ Γ1, Δ0 ++ A0 :: Δ1)) ; auto.
       unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
       apply ImpL_inv with (concl:=(A :: Γ0 ++ A0 --> B :: Γ1, Δ0 ++ Δ1)) (prem2:= (A :: Γ0 ++ B :: Γ1, Δ0 ++ Δ1)) ; auto. simpl.
       assert (A :: Γ0 ++ B :: Γ1 =  (A :: Γ0) ++ B :: Γ1). auto. rewrite H.
       assert (A :: Γ0 ++ Γ1 =  (A :: Γ0) ++ Γ1). auto. rewrite H0. apply ImpLRule_I.
       inversion H0 ; subst. 2: inversion H1. apply IHs with (y:=(Γ0 ++ B :: Γ1, Δ0 ++ Δ1)) ; auto.
       unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
       apply ImpL_inv with (concl:=(A :: Γ0 ++ A0 --> B :: Γ1, Δ0 ++ Δ1)) (prem1:= (A :: Γ0 ++ Γ1, Δ0 ++ A0 :: Δ1)) ; auto. simpl.
       assert (A :: Γ0 ++ B :: Γ1 =  (A :: Γ0) ++ B :: Γ1). auto. rewrite H.
       assert (A :: Γ0 ++ Γ1 =  (A :: Γ0) ++ Γ1). auto. rewrite H1. apply ImpLRule_I.
  Qed.

  Lemma Canopy_equiprv_genR : forall s A,
    ((forall leaf, InT leaf (Canopy s) -> GLS_prv (fst leaf, A :: snd leaf)) -> (GLS_prv (fst s, A :: snd s))) *
    ((GLS_prv (fst s, A :: snd s)) -> (forall leaf, InT leaf (Canopy s) -> GLS_prv (fst leaf, A :: snd leaf))).
  Proof.
  intros s ; induction on s as IHs with measure (n_imp_subformS s).
  intros ; split ; intros.
  - remember (finite_ImpRules_premises_of_S s) as H0.
    destruct H0. destruct x.
    + assert (Canopy s = [s]). apply irred_nil. unfold inv_prems. rewrite <- HeqH0.
       simpl. auto. rewrite H in X. apply X. apply InT_eq.
    + assert (J1: InT l (l :: x)). apply InT_eq. apply p in J1. destruct J1 ; unfold GLS_prv ; inversion i ; subst ; simpl.
       apply derI with (ps:=[(Γ0 ++ A0 :: Γ1, A :: Δ0 ++ B :: Δ1)]).
       apply ImpR ; auto. assert ((A :: Δ0 ++ B :: Δ1) = ((A :: Δ0) ++ B :: Δ1)). auto. rewrite H.
       assert (A :: Δ0 ++ A0 --> B :: Δ1 = (A :: Δ0) ++ A0 --> B :: Δ1). auto. rewrite H0. apply ImpRRule_I. apply dlCons. 2: apply dlNil.
       2: apply derI with (ps:=[(Γ0 ++ Γ1, A :: Δ0 ++ A0 :: Δ1);(Γ0 ++ B :: Γ1, A :: Δ0 ++ Δ1)]).
       2: apply ImpL ; auto. 2: assert (A :: Δ0 ++ Δ1 = ((A :: Δ0) ++ Δ1)) ; auto ; rewrite H.
       2: assert (A :: Δ0 ++ A0 :: Δ1 = (A :: Δ0) ++ A0 :: Δ1) ; auto ; rewrite H0. 2: apply ImpLRule_I. 2: apply dlCons.
       3: apply dlCons. 4: apply dlNil.
       assert (J2: n_imp_subformS (Γ0 ++ A0 :: Γ1, Δ0 ++ B :: Δ1) < n_imp_subformS (Γ0 ++ Γ1, Δ0 ++ A0 --> B :: Δ1)).
       unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
       apply IHs with (A:=A) in J2. simpl in J2. destruct J2. apply g. intros. apply X.
       apply ImpRule_Canopy with (prems:=[(Γ0 ++ A0 :: Γ1, Δ0 ++ B :: Δ1)]) (prem:=(Γ0 ++ A0 :: Γ1, Δ0 ++ B :: Δ1)) ; auto.
       apply InT_eq.
       assert (J2: n_imp_subformS (Γ0 ++ Γ1, Δ0 ++ A0 :: Δ1) < n_imp_subformS (Γ0 ++ A0 --> B :: Γ1, Δ0 ++ Δ1)).
       unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
       apply IHs with (A:=A) in J2. simpl in J2. destruct J2. apply g. intros. apply X.
       apply ImpRule_Canopy with (prems:=[(Γ0 ++ Γ1, Δ0 ++ A0 :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)])
       (prem:=(Γ0 ++ Γ1, Δ0 ++ A0 :: Δ1)) ; auto. apply InT_eq.
       assert (J2: n_imp_subformS (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) < n_imp_subformS (Γ0 ++ A0 --> B :: Γ1, Δ0 ++ Δ1)).
       unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
       apply IHs with (A:=A) in J2. simpl in J2. destruct J2. apply g. intros. apply X.
       apply ImpRule_Canopy with (prems:=[(Γ0 ++ Γ1, Δ0 ++ A0 :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)])
       (prem:=(Γ0 ++ B :: Γ1, Δ0 ++ Δ1)) ; auto. apply InT_cons.  apply InT_eq.
  - apply fold_Canopy in H. destruct H ; subst ; auto. destruct s0. destruct p.
    unfold inv_prems in i ; apply InT_flatten_list_InT_elem in i ; destruct i ; destruct p ; destruct (finite_ImpRules_premises_of_S s) ;
    simpl in i1. apply p in i1. destruct i1 ; inversion i1 ; subst.
    + inversion i ; subst. 2: inversion H0. apply IHs with (y:=(Γ0 ++ A0 :: Γ1, Δ0 ++ B :: Δ1)) ; auto.
       unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
       apply ImpR_inv with (concl:=(Γ0 ++ Γ1, A :: Δ0 ++ A0 --> B :: Δ1)) ; auto. simpl.
       assert (A :: Δ0 ++ B :: Δ1 =  (A :: Δ0) ++ B :: Δ1). auto. rewrite H.
       assert (A :: Δ0 ++ A0 --> B :: Δ1 =  (A :: Δ0) ++ A0 --> B :: Δ1). auto. rewrite H0. apply ImpRRule_I.
    + inversion i ; subst. apply IHs with (y:=(Γ0 ++ Γ1, Δ0 ++ A0 :: Δ1)) ; auto.
       unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
       apply ImpL_inv with (concl:=(Γ0 ++ A0 --> B :: Γ1, A :: Δ0 ++ Δ1)) (prem2:= (Γ0 ++ B :: Γ1, A :: Δ0 ++ Δ1)) ; auto. simpl.
       assert (A :: Δ0 ++ A0 :: Δ1 =  (A :: Δ0) ++ A0 :: Δ1). auto. rewrite H.
       assert (A :: Δ0 ++ Δ1 =  (A :: Δ0) ++ Δ1). auto. rewrite H0. apply ImpLRule_I.
       inversion H0 ; subst. 2: inversion H1. apply IHs with (y:=(Γ0 ++ B :: Γ1, Δ0 ++ Δ1)) ; auto.
       unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
       apply ImpL_inv with (concl:=(Γ0 ++ A0 --> B :: Γ1, A :: Δ0 ++ Δ1)) (prem1:= (Γ0 ++ Γ1, A :: Δ0 ++ A0 :: Δ1)) ; auto. simpl.
       assert (A :: Δ0 ++ A0 :: Δ1 =  (A :: Δ0) ++ A0 :: Δ1). auto. rewrite H.
       assert (A :: Δ0 ++ Δ1 =  (A :: Δ0) ++ Δ1). auto. rewrite H1. apply ImpLRule_I.
  Qed.

  Lemma Canopy_hp_inv_ctx : forall s k scomp (D0 : GLS_prv scomp) X0 Y0,
        k = (derrec_height D0) ->
        scomp = (fst s ++ X0, snd s ++ Y0) ->
        (forall leaf, InT leaf (Canopy s) -> existsT2 (D1: GLS_prv (fst leaf ++ X0, snd leaf ++ Y0)),
                                                                                derrec_height D1 <= k).
  Proof.
  intros s ; induction on s as IHs with measure (n_imp_subformS s).
  intros. apply fold_Canopy in H1. destruct H1.
  - subst. exists D0 ; auto.
  - destruct s0 ; destruct p. unfold inv_prems in i. apply InT_flatten_list_InT_elem in i. destruct i.
    destruct p. destruct (finite_ImpRules_premises_of_S s). simpl in i1. subst.
    assert (J0: derrec_height D0 = derrec_height D0). auto.
    pose (ImpR_ImpL_hpinv D0 J0). destruct p0. apply p in i1. destruct i1.
    + inversion i1 ; subst. simpl in s0.
       assert (J1: ImpRRule [(Γ0 ++ A :: (Γ1 ++ X0), Δ0 ++ B :: (Δ1 ++ Y0))] ((Γ0 ++ Γ1) ++ X0, (Δ0 ++ A --> B :: Δ1) ++ Y0)).
       repeat rewrite <- app_assoc ; apply ImpRRule_I. apply s0 in J1. destruct J1. inversion i ; subst.
       assert (J2: n_imp_subformS (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) < n_imp_subformS (Γ0 ++ Γ1, Δ0 ++ A --> B :: Δ1)).
       unfold n_imp_subformS. simpl. repeat rewrite n_imp_subformLF_dist_app. simpl ; repeat rewrite n_imp_subformLF_dist_app.
       lia.
       assert (J3: derrec_height x0 = derrec_height x0). auto.
       assert (J4: (Γ0 ++ A :: Γ1 ++ X0, Δ0 ++ B :: Δ1 ++ Y0) = (fst (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) ++ X0, snd (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) ++ Y0)).
       simpl ; repeat rewrite <- app_assoc ; auto.
       pose (IHs _ J2 _ _ x0 X0 Y0 J3 J4 _ i0). destruct s. exists x. apply PeanoNat.Nat.le_trans with (m:=derrec_height x0) ; auto.
       inversion H0.
    + inversion i1 ; subst. simpl in s1. clear s0.
       assert (J1: ImpLRule [(Γ0 ++ Γ1 ++ X0, Δ0 ++ A :: Δ1 ++ Y0); (Γ0 ++ B :: Γ1 ++ X0, Δ0 ++ Δ1 ++ Y0)] ((Γ0 ++ A --> B :: Γ1) ++ X0, (Δ0 ++ Δ1) ++ Y0)).
       repeat rewrite <- app_assoc ; apply ImpLRule_I. apply s1 in J1. destruct J1. destruct s. destruct p0. inversion i ; subst.
       assert (J2: n_imp_subformS (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) < n_imp_subformS (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)).
       unfold n_imp_subformS. simpl. repeat rewrite n_imp_subformLF_dist_app. simpl ; repeat rewrite n_imp_subformLF_dist_app.
       lia.
       assert (J3: derrec_height x0 = derrec_height x0). auto.
       assert (J4: (Γ0 ++ Γ1 ++ X0, Δ0 ++ A :: Δ1 ++ Y0) = (fst (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) ++ X0, snd (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) ++ Y0)).
       simpl ; repeat rewrite <- app_assoc ; auto.
       pose (IHs _ J2 _ _ x0 X0 Y0 J3 J4 _ i0). destruct s. exists x. apply PeanoNat.Nat.le_trans with (m:=derrec_height x0) ; auto.
       inversion H0 ; subst.
       assert (J2: n_imp_subformS (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) < n_imp_subformS (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)).
       unfold n_imp_subformS. simpl. repeat rewrite n_imp_subformLF_dist_app. simpl ; repeat rewrite n_imp_subformLF_dist_app.
       lia.
       assert (J3: derrec_height x2 = derrec_height x2). auto.
       assert (J4: (Γ0 ++ B :: Γ1 ++ X0, Δ0 ++ Δ1 ++ Y0) = (fst (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) ++ X0, snd (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) ++ Y0)).
       simpl ; repeat rewrite <- app_assoc ; auto.
       pose (IHs _ J2 _ _ x2 X0 Y0 J3 J4 _ i0). destruct s. exists x. apply PeanoNat.Nat.le_trans with (m:=derrec_height x2) ; auto.
       inversion H1.
  Qed.

  Lemma Canopy_neg_var : forall s q, InT (# q) (fst s) -> (forall leaf, InT leaf (Canopy s) -> InT (# q) (fst leaf)).
  Proof.
  intros s ; induction on s as IHs with measure (n_imp_subformS s).
  intros. apply fold_Canopy in H0. destruct H0 ; subst ; auto.
  destruct s0 ; destruct p. unfold inv_prems in i. apply InT_flatten_list_InT_elem in i. destruct i.
  destruct p. destruct (finite_ImpRules_premises_of_S s). simpl in i1. subst.
  apply p in i1. destruct i1.
  - inversion i1 ; subst. inversion i ; subst. 2: inversion H1.
    assert (J0: n_imp_subformS (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) < n_imp_subformS (Γ0 ++ Γ1, Δ0 ++ A --> B :: Δ1)).
     unfold n_imp_subformS. simpl. repeat rewrite n_imp_subformLF_dist_app. simpl ; repeat rewrite n_imp_subformLF_dist_app.
     lia.
    apply IHs with (q:= q) (leaf:=leaf) in J0 ; auto. simpl. apply InT_or_app. simpl in H. apply InT_app_or in H ; destruct H ; auto.
    right ; apply InT_cons ; auto.
  - inversion i1 ; subst. inversion i ; subst. 2: inversion H1. 3: inversion H2.
    assert (J0: n_imp_subformS (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) < n_imp_subformS (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)).
     unfold n_imp_subformS. simpl. repeat rewrite n_imp_subformLF_dist_app. simpl ; repeat rewrite n_imp_subformLF_dist_app.
     lia.
    apply IHs with (q:= q) (leaf:=leaf) in J0 ; auto. simpl. apply InT_or_app. simpl in H. apply InT_app_or in H ; destruct H ; auto.
    inversion i2 ; subst. inversion H0. auto. subst.
    assert (J0: n_imp_subformS (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) < n_imp_subformS (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)).
     unfold n_imp_subformS. simpl. repeat rewrite n_imp_subformLF_dist_app. simpl ; repeat rewrite n_imp_subformLF_dist_app.
     lia.
    apply IHs with (q:= q) (leaf:=leaf) in J0 ; auto. simpl. apply InT_or_app. simpl in H. apply InT_app_or in H ; destruct H ; auto.
    inversion i2 ; subst. inversion H0. right ; apply InT_cons ; auto.
  Qed.

  Lemma Canopy_pos_var : forall s q, InT (# q) (snd s) -> (forall leaf, InT leaf (Canopy s) -> InT (# q) (snd leaf)).
  Proof.
  intros s ; induction on s as IHs with measure (n_imp_subformS s).
  intros. apply fold_Canopy in H0. destruct H0 ; subst ; auto.
  destruct s0 ; destruct p. unfold inv_prems in i. apply InT_flatten_list_InT_elem in i. destruct i.
  destruct p. destruct (finite_ImpRules_premises_of_S s). simpl in i1. subst.
  apply p in i1. destruct i1.
  - inversion i1 ; subst. inversion i ; subst. 2: inversion H1.
    assert (J0: n_imp_subformS (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) < n_imp_subformS (Γ0 ++ Γ1, Δ0 ++ A --> B :: Δ1)).
     unfold n_imp_subformS. simpl. repeat rewrite n_imp_subformLF_dist_app. simpl ; repeat rewrite n_imp_subformLF_dist_app.
     lia.
    apply IHs with (q:= q) (leaf:=leaf) in J0 ; auto. simpl. apply InT_or_app. simpl in H. apply InT_app_or in H ; destruct H ; auto.
    inversion i2 ; subst. inversion H0. right ; apply InT_cons ; auto.
  - inversion i1 ; subst. inversion i ; subst. 2: inversion H1. 3: inversion H2.
    assert (J0: n_imp_subformS (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) < n_imp_subformS (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)).
     unfold n_imp_subformS. simpl. repeat rewrite n_imp_subformLF_dist_app. simpl ; repeat rewrite n_imp_subformLF_dist_app.
     lia.
    apply IHs with (q:= q) (leaf:=leaf) in J0 ; auto. simpl. apply InT_or_app. simpl in H. apply InT_app_or in H ; destruct H ; auto.
    right ; apply InT_cons ; auto. subst.
    assert (J0: n_imp_subformS (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) < n_imp_subformS (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)).
     unfold n_imp_subformS. simpl. repeat rewrite n_imp_subformLF_dist_app. simpl ; repeat rewrite n_imp_subformLF_dist_app.
     lia.
    apply IHs with (q:= q) (leaf:=leaf) in J0 ; auto.
  Qed.

  Lemma Id_InT_Canopy : forall s, InT s (Canopy s) -> Canopy s = [s].
  Proof.
  intros. destruct (critical_Seq_dec s).
  - remember (finite_ImpRules_premises_of_S s) as J.
    destruct J. destruct x.
    + apply irred_nil. unfold inv_prems. rewrite <- HeqJ.
       simpl. auto.
    + exfalso. assert (J1: InT l (l :: x)). apply InT_eq. apply p in J1. unfold critical_Seq in c.
       destruct J1 ; inversion i ; subst ; simpl in c.
       assert (In (A --> B) ((Γ0 ++ Γ1) ++ Δ0 ++ A --> B :: Δ1)). apply in_or_app ; right ; apply in_or_app ; right ; apply in_eq.
       apply c in H0. destruct H0. destruct H0. inversion H0. destruct H0. destruct H0 ; inversion H0. inversion H0.
       assert (In (A --> B) ((Γ0 ++ A --> B :: Γ1) ++ Δ0 ++ Δ1)). apply in_or_app ; left ; apply in_or_app ; right ; apply in_eq.
       apply c in H0. destruct H0. destruct H0. inversion H0. destruct H0. destruct H0 ; inversion H0. inversion H0.
  - exfalso. apply Canopy_critical in H. auto.
  Qed.

  Lemma critical_Seq_InT_Canopy : forall s, critical_Seq s -> InT s (Canopy s).
  Proof.
  intros. remember (finite_ImpRules_premises_of_S s) as J.
  destruct J. destruct x.
  + pose irred_nil. unfold Canopy. rewrite e. apply InT_eq. unfold inv_prems. rewrite <- HeqJ.
     simpl. auto.
  + exfalso. assert (J1: InT l (l :: x)). apply InT_eq. apply p in J1. unfold critical_Seq in H.
     destruct J1 ; inversion i ; subst ; simpl in H.
     assert (In (A --> B) ((Γ0 ++ Γ1) ++ Δ0 ++ A --> B :: Δ1)). apply in_or_app ; right ; apply in_or_app ; right ; apply in_eq.
     apply H in H0. destruct H0. destruct H0. inversion H0. destruct H0. destruct H0 ; inversion H0. inversion H0.
     assert (In (A --> B) ((Γ0 ++ A --> B :: Γ1) ++ Δ0 ++ Δ1)). apply in_or_app ; left ; apply in_or_app ; right ; apply in_eq.
     apply H in H0. destruct H0. destruct H0. inversion H0. destruct H0. destruct H0 ; inversion H0. inversion H0.
  Qed.
