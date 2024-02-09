  Require Import List Extraction.
  Require Import Lia.

  Require Import KS_export.

Require Import UIK_Def_measure.
Require Import UIK_Canopy.
Require Import UIK_irred_short.

Section Arithmetic.

  Lemma lt_decT : forall m n, (m < n) + ((m < n) -> False).
  Proof.
  induction m ; destruct n. 1,3: right ; intro ; lia. left ; lia.
  destruct (IHm n). left ; lia. right ; intro ; lia.
  Qed.

  End Arithmetic.



  Section Logic_Abrv.



  (* Conjunction of a list of formulas. *)

  Fixpoint list_conj (l : list MPropF) : MPropF :=
  match l with
   | nil => Top
   | h :: t => And h (list_conj t)
  end.

  (* Disjunction of a list of formulas. *)

  Fixpoint list_disj (l : list MPropF) : MPropF :=
  match l with
   | nil => Bot
   | h :: t => Or h (list_disj t)
  end.

  (* List of propositional variables in a formula. *)

  Definition list_prop_F (A : MPropF) : list MPropF :=
  match A with
   | # P => [# P]
   | _ => []
  end.

  (* List of propositional variables in a list of formula. *)

  Fixpoint list_prop_LF (l : list MPropF) : list MPropF :=
  match l with
   | nil => []
   | h :: t => (list_prop_F h) ++ (list_prop_LF t)
  end.

  Lemma list_prop_LF_In : forall l A, In A l -> (existsT2 p, A = # p) -> In A (list_prop_LF l).
  Proof.
  induction l ; auto. intros. simpl. destruct H0 ; subst. simpl in H. destruct H ; subst.
  apply in_or_app ; left ; apply in_eq. apply in_or_app ; right. apply IHl ; auto. eexists ; auto.
  Qed.

  Lemma In_list_prop_LF : forall l A, In A (list_prop_LF l) -> In A l.
  Proof.
  induction l ; auto. intros. simpl. simpl in H. apply in_app_or in H ; destruct H.
  left. destruct a ; simpl in H ; subst. destruct H ; auto ; try inversion H.
  inversion H. 1,2: inversion H. right. apply IHl ; auto.
  Qed.

  Lemma In_list_prop_LF_bis : forall l A, In A (list_prop_LF l) -> ((In A l) * (existsT2 p, A = # p)).
  Proof.
  induction l ; auto ; intros. inversion H. simpl in H. split. apply In_list_prop_LF ; auto.
  apply In_InT in H. apply InT_app_or in H ; destruct H.
  destruct a ; simpl in i ; inversion i ; subst. eexists ; auto. inversion H0.
  apply InT_In in i ; apply IHl in i ; destruct i ; auto.
  Qed.

  (* Restricted list of propositional variables. *)

  Definition restr_list_prop p l : list MPropF := remove eq_dec_form (# p) (list_prop_LF l).

  (* List of all premises through the KR rule for a sequent s.
      Note that KR is not invertible. *)

  Definition KR_prems (s : Seq) := flatten_list (proj1_sigT2 (finite_KR_premises_of_S s)).

  (* Property of being an initial sequent. *)

  Definition is_init s : Type := (IdPRule [] s) + (BotLRule [] s).

  End Logic_Abrv.

  Section Random.

  Lemma InT_In_Seq: forall (s: Seq) l, (InT s l -> In s l) * (In s l -> InT s l).
  Proof.
  intros. split ; intros.
  - apply InT_In ; auto.
  - destruct s. apply In_InT_seqs ; auto.
  Qed.

  Lemma size_LF_nil_unbox_top_box : forall l, l <> nil ->
      size_LF (unboxed_list (top_boxes l)) < size_LF l.
  Proof.
  induction l ; simpl ; auto ; intros.
  - exfalso ; auto.
  - destruct l.
    + destruct a ; simpl ; lia.
    + assert (m :: l <> []). intro H0 ; inversion H0. apply IHl in H0.
       destruct a ; destruct m ; simpl in * ; try lia.
  Qed.

  End Random.



  Section LtSeq_ind.

  Definition LtSeq := fun s0 s1 => (lt (measure s0) (measure s1)).

  Lemma wf_LtSeq : well_founded LtSeq.
  Proof.
  unfold LtSeq. apply Inverse_Image.wf_inverse_image.
  apply Wf_nat.lt_wf.
  Qed.

  Variable (P : Seq -> Type).

  Theorem LtSeq_ind : (forall s0, (forall s1, LtSeq s1 s0 -> P s1) -> P s0) -> (forall s, P s).
  Proof.
  intros. induction s as [ s0 IHs0 ] using (well_founded_induction_type wf_LtSeq).
  apply X; intros; apply IHs0 ; auto.
  Qed.

  End LtSeq_ind.

  Section LtSeq_properties.

  Theorem LtSeq_trans : forall x y z, LtSeq x y -> LtSeq y z -> LtSeq x z.
  Proof.
  unfold LtSeq. intros. lia.
  Qed.

  Lemma inv_prems_LtSeq : forall s0 s1, InT s1 (inv_prems s0) -> LtSeq s1 s0.
  Proof.
  intros. unfold inv_prems in H. apply InT_flatten_list_InT_elem in H.
  destruct H. destruct p. destruct (finite_ImpRules_premises_of_S s0). simpl in i0.
  apply p in i0. destruct i0 ; inversion i0 ; subst. 
  - inversion i ; subst. unfold LtSeq. unfold measure. simpl. repeat rewrite size_LF_dist_app ; simpl ; lia.
    inversion H0.
  - inversion i ; subst. unfold LtSeq. unfold measure. simpl. repeat rewrite size_LF_dist_app ; simpl ; lia.
    inversion H0 ; subst. unfold LtSeq. unfold measure. simpl. repeat rewrite size_LF_dist_app ; simpl ; lia.
    inversion H1.
  Qed.

  Lemma KR_prems_LtSeq : forall s0 s1, InT s1 (KR_prems s0) -> LtSeq s1 s0.
  Proof.
  intros s0 s1 H. unfold KR_prems in H. apply InT_flatten_list_InT_elem in H.
  destruct H. destruct p. destruct (finite_KR_premises_of_S s0). simpl in i0.
  apply p in i0. inversion i0 ; subst. unfold LtSeq.
  unfold measure. inversion i ; subst. simpl. pose (nobox_gen_ext_top_boxes_identity X H).
  rewrite e in *. pose (size_unboxed (top_boxes Γ0)). pose (size_top_boxes Γ0).
  repeat rewrite size_LF_dist_app ; simpl. lia.
  inversion H1.
  Qed.

  Lemma Canopy_nil : forall s0, (inv_prems s0 = []) ->  (forall s1, InT s1 (Canopy s0) -> s1 = s0).
  Proof.
  intros. assert (Canopy s0 = [s0]). apply irred_nil. unfold inv_prems. unfold inv_prems in H. auto.
  rewrite H1 in H0. inversion H0. subst. auto. inversion H3.
  Qed.

  Lemma Canopy_LtSeq: forall s0 s1, InT s1 (Canopy s0) -> ((s0 = s1) + (LtSeq s1 s0)).
  Proof.
  intros s ; induction on s as IHs with measure (n_imp_subformS s).
  intros. remember (finite_ImpRules_premises_of_S s) as H0. destruct H0. destruct x.
  - left. assert (Canopy s = [s]). apply irred_nil. unfold inv_prems ; rewrite <- HeqH0 ; auto.
    rewrite H0 in H. inversion H ; subst ; auto. inversion H2.
  - apply fold_Canopy in H. destruct H ; auto. right. destruct s0. destruct p0. apply IHs in i0.
    destruct i0 ; subst ; auto. apply inv_prems_LtSeq in i ; auto. apply inv_prems_LtSeq in i.
    apply (LtSeq_trans _ _ _ l0 i). unfold inv_prems in i. apply InT_flatten_list_InT_elem in i.
    destruct i. destruct p0. rewrite <- HeqH0 in i1. simpl in i1. apply p in i1. destruct i1 ; inversion i1 ; subst.
    inversion i. subst. unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
    inversion H0. inversion i ; subst. unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
    inversion H0 ; subst. unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
    inversion H1.
  Qed.

  End LtSeq_properties.

  Section empty_seq.

  Lemma empty_seq_dec : forall (s: Seq), (s = ([],[])) + (s <> ([],[])).
  Proof.
  intros. destruct s. destruct l ; destruct l0 ; auto.
  all: right ; intro H ; inversion H.
  Qed.

  Lemma not_init_empty_set : is_init ([],[]) -> False.
  Proof.
  intro. destruct X. inversion i. destruct Γ0 ; inversion H.
  inversion b ; subst. destruct Γ0 ; inversion H.
  Qed.

  Lemma critical_empty_set : critical_Seq ([],[]).
  Proof.
  intros A HA ; simpl in *. inversion HA.
  Qed.

  End empty_seq.


