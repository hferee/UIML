  Require Import List Extraction.
  Require Import Lia.

  Require Import GLS_export.

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

  Definition restr_list_prop p  (l : list MPropF) := remove eq_dec_form (# p) (list_prop_LF l).

  End Logic_Abrv.

  Section Random.

  Lemma InT_In_Seq: forall (s: Seq) l, (InT s l -> In s l) * (In s l -> InT s l).
  Proof.
  intros. split ; intros.
  - apply InT_In ; auto.
  - destruct s. apply In_InT_seqs ; auto.
  Qed.

  End Random.



