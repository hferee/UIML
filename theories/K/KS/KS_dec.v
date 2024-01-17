Require Import List.
Export ListNotations.
Require Import Lia.
Require Import PeanoNat.

Require Import KS_calc.

(* In this file we show that the applicability of the rules in KS is decidable. *)

Lemma top_boxes_incl_list : forall l, incl (top_boxes l) l.
Proof.
induction l.
- simpl. unfold incl. intros. inversion H.
- unfold incl. intros. destruct a.
  * simpl in H. apply in_cons. apply IHl. assumption.
  * simpl in H. apply in_cons. apply IHl. assumption.
  * simpl in H. apply in_cons. apply IHl. assumption.
  * simpl in H. destruct H.
    + subst. apply in_eq.
    + apply in_cons. apply IHl. assumption.
Qed.

Lemma in_top_boxes : forall l A, (In A (top_boxes l)) -> (existsT2 B l1 l2, (A = Box B) * (l = l1 ++ A :: l2)).
Proof.
induction l.
- intros. simpl in H. inversion H.
- intros. destruct a.
  * simpl in H. apply IHl in H. destruct H. destruct s. destruct s. destruct p. subst.
    exists x. exists ([# n] ++ x0). exists x1. auto.
  * simpl in H. apply IHl in H. destruct H. destruct s. destruct s. destruct p. subst.
    exists x. exists ([Bot] ++ x0). exists x1. auto.
  * simpl in H. apply IHl in H. destruct H. destruct s. destruct s. destruct p. subst.
    exists x. exists ([a1 --> a2] ++ x0). exists x1. auto.
  * simpl (top_boxes (Box a :: l)) in H. destruct (eq_dec_form (Box a) A).
    + subst. exists a. exists []. exists l. auto.
    + subst. assert (H0 : In A (top_boxes l)). inversion H. exfalso. apply n. assumption.
      assumption. apply IHl in H0. destruct H0. destruct s. destruct s. destruct p.
      subst. exists x. exists ([Box a] ++ x0). exists x1. auto.
Qed.

Lemma dec_is_PropVar : forall (A : MPropF), (existsT2 P, A = # P) + ((existsT2 P, A = # P) -> False).
Proof.
induction A.
- left. exists n. reflexivity.
- right. intro. inversion H. inversion H0.
- right. intro. inversion H. inversion H0.
- right. intro. inversion H. inversion H0.
Qed.

Lemma dec_prop_var_in : forall s, (existsT2 P, (In (# P) (fst s)) /\ (In (# P) (snd s))) +
                                      ((existsT2 P, (In (# P) (fst s)) /\ (In (# P) (snd s))) -> False).
Proof.
intro. destruct s.
induction l.
- right. intro. destruct H. destruct a. simpl in H. inversion H.
- destruct IHl.
  * destruct s. simpl in a0. destruct a0. left. exists x. simpl. split. auto. assumption.
  * destruct (dec_is_PropVar a) ; simpl.
    + destruct (In_dec l0 a).
      { left. subst. destruct s. exists x. simpl. split. auto. subst. assumption. }
      { right. simpl. intro. destruct H. destruct a0. destruct H.
        - subst. apply f0. assumption.
        - apply f. simpl. exists x. firstorder. }
    + right. intro. simpl in H. destruct H. destruct a0. destruct H.
      { subst. apply f0. exists x. reflexivity. }
      { apply f. firstorder. }
Qed.

Lemma dec_is_boxedT : forall (A : MPropF), (is_boxedT A) + ((is_boxedT A) -> False).
Proof.
induction A.
- right. intro. inversion X. inversion H.
- right. intro. inversion X. inversion H.
- right. intro. inversion X. inversion H.
- left. exists A. reflexivity.
Qed.

Lemma dec_is_box : forall (A : MPropF), (existsT2 B, A = Box B) + ((existsT2 B, A = Box B ) -> False).
Proof.
destruct A.
- right. intro. destruct H. inversion e.
- right. intro. destruct H. inversion e.
- right. intro. destruct H. inversion e.
- left. exists A. reflexivity.
Qed.

Lemma dec_box_in : forall s, (existsT2 (A : MPropF), (In (Box A) (fst s)) /\ (In (Box A) (snd s))) +
                             ((existsT2 (A : MPropF), (In (Box A) (fst s)) /\ (In (Box A) (snd s))) -> False).
Proof.
intro. destruct s.
induction l.
- right. intro. destruct H. destruct a. simpl in H. inversion H.
- destruct IHl.
  * destruct s. simpl in a0. destruct a0. left. exists x. simpl. split. auto. assumption.
  * destruct (dec_is_box a).
    + destruct (In_dec l0 a).
      { left. destruct s. subst. simpl. exists x. split. auto. assumption. }
      { right. simpl. intro. destruct H. destruct a0. destruct H.
        - subst. apply f0. assumption.
        - apply f. simpl. exists x. firstorder. }
    + right. intro. simpl in H. destruct H. destruct a0. destruct H.
      { subst. apply f0. exists x. reflexivity. }
      { apply f. firstorder. }
Qed.

Lemma dec_KS_init_rules : forall (s :Seq) ,
          ((IdPRule [] s) + (BotLRule [] s)) +
          (((IdPRule [] s) + (BotLRule [] s)) -> False).
Proof.
intro s. destruct s. destruct (dec_prop_var_in (pair l l0)).
- destruct s. destruct a. left. left. simpl in H. simpl in H0.
  apply in_splitT in H. destruct H. destruct s. apply in_splitT in H0. destruct H0. destruct s.
  subst. apply IdPRule_I.
- destruct (In_dec l (Bot)).
  + left. apply in_splitT in i. destruct i. destruct s. subst. right. apply BotLRule_I.
  + right. intro. destruct H.
    * inversion i. subst. simpl in f. apply f. exists P. split ; apply in_or_app ; right ; apply in_eq.
    * inversion b. subst. apply f0. apply in_or_app. right. apply in_eq.
Qed.

Lemma dec_IdP_rule : forall (s :Seq) ,
          (IdPRule [] s) +
          ((IdPRule [] s) -> False).
Proof.
intro s. destruct s. destruct (dec_prop_var_in (pair l l0)).
- destruct s. destruct a. left. simpl in H. simpl in H0.
  apply in_splitT in H. destruct H. destruct s. apply in_splitT in H0. destruct H0. destruct s.
  subst. apply IdPRule_I.
- right. intro. destruct H. apply f. exists P. split ; apply in_or_app ; right ; apply in_eq.
Qed.

Lemma dec_BotL_rule : forall (s :Seq) ,
          (BotLRule [] s) +
          ((BotLRule [] s) -> False).
Proof.
intro s. destruct s. destruct (In_dec l (Bot)).
- left. apply in_splitT in i. destruct i. destruct s. subst. apply BotLRule_I.
- right. intro. inversion H. apply f. subst. apply in_or_app. right. apply in_eq.
Qed.

Lemma dec_is_imp : forall (A : MPropF), (existsT2 B C, A = Imp B C) + ((existsT2 B C, A = Imp B C) -> False).
Proof.
destruct A.
- right. intro. destruct H. destruct s. inversion e.
- right. intro. destruct H. destruct s. inversion e.
- left. exists A1. exists A2. reflexivity.
- right. intro. destruct H. destruct s. inversion e.
Qed.

Lemma dec_imp_in : forall (l : list MPropF), (existsT2 A B, In (Imp A B) l) + ((existsT2 A B, In (Imp A B) l) -> False).
Proof.
induction l.
- right. intro. destruct H. destruct s. inversion i.
- destruct IHl.
  * repeat destruct s. left. exists x. exists x0. apply in_cons. assumption.
  * destruct (dec_is_imp a).
    + repeat destruct s. subst. left. exists x. exists x0. apply in_eq.
    + right. intro. destruct H. destruct s. inversion i.
      { subst. apply f0. exists x. exists x0. reflexivity. }
      { apply f. exists x. exists x0. assumption. }
Qed.

Lemma dec_ImpR_rule : forall (concl :Seq),
          (existsT2 prem, ImpRRule [prem] concl) + ((existsT2 prem, ImpRRule [prem] concl) -> False).
Proof.
intros concl. destruct concl. destruct (dec_imp_in l0).
- left. repeat destruct s. apply in_splitT in i. destruct i. destruct s. subst.
  exists ([] ++ x :: l, x1 ++ x0 :: x2). assert ((l, x1 ++ x --> x0 :: x2) = ([] ++ l, x1 ++ x --> x0 :: x2)).
  reflexivity. apply ImpRRule_I.
- right. intro. destruct H. inversion i. subst. apply f. exists A. exists B. apply in_or_app.
  right. apply in_eq.
Qed.

Lemma dec_ImpL_rule : forall (concl :Seq),
          (existsT2 prem1 prem2, ImpLRule [prem1 ; prem2] concl) + ((existsT2 prem1 prem2, ImpLRule [prem1 ; prem2] concl) -> False).
Proof.
intro concl. destruct concl. destruct (dec_imp_in l).
- left. repeat destruct s. apply in_splitT in i. destruct i. destruct s. subst.
  exists (x1 ++ x2, [] ++ x :: l0). exists (x1 ++ x0 :: x2, [] ++ l0).
  assert ((x1 ++ x --> x0 :: x2, l0) = (x1 ++ x --> x0 :: x2, [] ++ l0)). reflexivity.
  rewrite H. apply ImpLRule_I.
- right. intro. destruct H. destruct s. inversion i. subst. apply f. exists A. exists B.
  apply in_or_app. right. apply in_eq.
Qed.

Lemma dec_box_in_list : forall l, (existsT2 (A : MPropF), In (Box A) l) +
                             ((existsT2 (A : MPropF), In (Box A) l) -> False).
Proof.
induction l.
- simpl. right. intro. destruct H. assumption.
- destruct (dec_is_box a).
  * destruct s. subst. left. exists x. apply in_eq.
  * destruct IHl.
    + left. destruct s. exists x. apply in_cons. assumption.
    + right. intro. destruct H. inversion i. subst. apply f. exists x. reflexivity. apply f0.
      exists x. assumption.
Qed.

Lemma dec_KR_rule : forall (concl :Seq),
          (existsT2 prem, KRRule [prem] concl) + ((existsT2 prem, KRRule [prem] concl) -> False).
Proof.
intro concl. destruct concl. destruct (dec_box_in_list l0).
- left. destruct s. exists ((unboxed_list (top_boxes l)), [x]).
  apply in_splitT in i. destruct i. destruct s. subst. apply KRRule_I.
  + unfold is_Boxed_list. intros. apply in_top_boxes in H. destruct H. destruct s. destruct s.
    destruct p. exists x2. assumption.
  + induction l.  simpl. apply univ_gen_ext_nil. destruct a.
    * simpl. apply univ_gen_ext_extra. intro. destruct X. inversion H. assumption.
    * simpl. apply univ_gen_ext_extra. intro. destruct X. inversion H. assumption.
    * simpl. apply univ_gen_ext_extra. intro. destruct X. inversion H. assumption.
    * simpl. apply univ_gen_ext_cons. apply IHl.
- right. intro. destruct X. inversion k. subst. apply f. exists A. apply in_or_app. right. apply in_eq.
Qed.

Lemma dec_KS_rules : forall (concl :Seq) ,
          ((existsT2 prems, KS_rules prems concl) -> False) + (existsT2 prems, KS_rules prems concl).
Proof.
intro concl. destruct (dec_KS_init_rules concl).
- right. repeat destruct s.
  * exists nil. apply IdP. assumption.
  * exists nil. apply BotL. assumption.
- destruct (dec_ImpR_rule concl).
  * right. destruct s. exists [x]. apply ImpR. assumption.
  * destruct (dec_ImpL_rule concl).
    + right. repeat destruct s. exists [x; x0]. apply ImpL. assumption.
    + destruct (dec_KR_rule concl).
      { right. repeat destruct s. exists [x]. apply KR. assumption. }
      { left. intro. destruct X. inversion k.
        - inversion H. subst. apply f. auto.
        - inversion H. subst. apply f. auto.
        - inversion H. subst. apply f0. exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1). assumption.
        - inversion H. subst. apply f1. exists (Γ0 ++ Γ1, Δ0 ++ A :: Δ1). exists (Γ0 ++ B :: Γ1, Δ0 ++ Δ1).
          assumption.
        - inversion X. subst. apply f2. exists (unboxed_list BΓ, [A]). assumption. }
Qed.



