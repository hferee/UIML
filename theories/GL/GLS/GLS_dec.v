Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import GLS_calcs.

Delimit Scope My_scope with M.
Open Scope My_scope.
Set Implicit Arguments.

(* In this file we show that the applicability of the rules in GLS is decidable. *)

Lemma in_top_boxes : forall l A, (In A (top_boxes l)) -> (existsT2 B l1 l2, (A = Box B) * (l = l1 ++ A :: l2)).
Proof.
induction l.
- intros. simpl in H. inversion H.
- intros. destruct a.
  * simpl in H. apply IHl in H. destruct H. destruct s. destruct s. destruct p. subst.
    exists x. exists ([# n] ++ x0). exists x1. auto.
  * simpl in H. apply IHl in H. destruct H. destruct s. destruct s. destruct p. subst.
    exists x. exists ([⊥] ++ x0). exists x1. auto.
  * simpl in H. apply IHl in H. destruct H. destruct s. destruct s. destruct p. subst.
    exists x. exists ([a1 --> a2] ++ x0). exists x1. auto.
  * simpl (top_boxes (Box a :: l)) in H. destruct (eq_dec_form (Box a) A).
    + subst. exists a. exists []. exists l. auto.
    + subst. assert (H0 : In A (top_boxes l)). inversion H. exfalso. apply n. assumption.
      assumption. apply IHl in H0. destruct H0. destruct s. destruct s. destruct p.
      subst. exists x. exists ([Box a] ++ x0). exists x1. auto.
Qed.

Lemma remove_add_rest_gen_ext : forall l (A : MPropF), rest_gen_ext [A] (remove eq_dec_form A l) l.
Proof.
induction l.
- intro A. simpl. apply univ_gen_ext_nil.
- intro A. pose (IHl A). simpl. destruct (eq_dec_form A a).
  * subst. apply univ_gen_ext_extra. apply InT_eq.
    assumption.
  * apply univ_gen_ext_cons. assumption.
Qed.

(* Lemma in_atom_gen_ext_atom_or_in_list : forall (l1 l2 : list MPropF), atom_gen_ext l1 l2 -> (forall A, In A l2 ->
                    ((existsT2 P, A = # P) + (A = Bot) + (In A l1))).
Proof.
intros l1 l2 X. induction X.
- intros. inversion H.
-  intros. destruct (eq_dec_form A x).
  * subst. right. apply in_eq.
  * assert (In A le). inversion H. exfalso. apply n. auto. assumption.
    apply IHX in H0. destruct H0.
    + destruct s. subst. left. left. assumption. left. right. assumption.
    + right. apply in_cons. assumption.
- intros. destruct (eq_dec_form A x).
  * subst. left. inversion p. left. assumption.
    right. assumption.
  * assert (In A le). inversion H. exfalso. apply n. auto. assumption.
    apply IHX in H0. destruct H0.
    + destruct s. subst. left. auto. auto.
    + right. assumption.
Qed.

Lemma dec_is_atomicT : forall (A : MPropF), (is_atomicT A) + ((is_atomicT A) -> False).
Proof.
induction A.
- left. left. exists v. reflexivity.
- left. right. reflexivity.
- right. intro. inversion X. inversion H. inversion H0. inversion H.
- right. intro. inversion X. inversion H. inversion H0. inversion H.
Qed. *)

Lemma dec_prop_var_in : forall s, (existsT2 P, (In (# P) (fst s)) /\ (In (# P) (snd s))) +
                                      ((existsT2 P, (In (# P) (fst s)) /\ (In (# P) (snd s))) -> False).
Proof.
intro. destruct s ; simpl.
induction l.
- right. intro. destruct H. destruct a. simpl in H. inversion H.
- destruct IHl.
  * destruct s. simpl in a0. destruct a0. left. exists x. simpl. split. auto. assumption.
  * simpl in *. destruct a.
    2-4: right ; intro H ; destruct H as (n, H0) ; destruct H0 as (H2 , H3) ; destruct H2 as [H4 | H5] ; 
    [ inversion H4 | apply f ; exists n ; auto].
    + destruct (In_dec l0 (# n)).
      { left. exists n ; split ; auto. }
      { right. intro. destruct H. destruct a. destruct H ; subst.
        - inversion H ; subst. apply f0. assumption.
        - apply f. simpl. exists x. firstorder. }
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

Lemma dec_GLS_init_rules : forall (s :Seq) ,
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

Lemma dec_IdB_rule : forall (s :Seq) ,
          (IdBRule [] s) +
          ((IdBRule [] s) -> False).
Proof.
intro s. destruct s. destruct (dec_box_in (l, l0)).
- destruct s. destruct a. left. simpl in H. simpl in H0.
  apply in_splitT in H. destruct H. destruct s. apply in_splitT in H0. destruct H0. destruct s.
  subst. apply IdBRule_I.
- right. intro. destruct H. apply f. exists A. split ; apply in_or_app ; right ; apply in_eq.
Qed.

Lemma dec_BotL_rule : forall (s :Seq) ,
          (BotLRule [] s) +
          ((BotLRule [] s) -> False).
Proof.
intro s. destruct s. destruct (In_dec l (Bot)).
- left. apply in_splitT in i. destruct i. destruct s. subst. apply BotLRule_I.
- right. intro. inversion H. apply f. subst. apply in_or_app. right. apply in_eq.
Qed.

Lemma dec_init_rules : forall (s :Seq) ,
          ((IdPRule [] s) + (IdBRule [] s) + (BotLRule [] s)) +
          (((IdPRule [] s) + (IdBRule [] s) + (BotLRule [] s)) -> False).
Proof.
intro s. destruct s. destruct (dec_prop_var_in (pair l l0)).
- destruct s. destruct a. left. left. left. simpl in H. simpl in H0.
  apply in_splitT in H. destruct H. destruct s. apply in_splitT in H0. destruct H0. destruct s.
  subst. apply IdPRule_I.
- destruct (In_dec l (Bot)).
  + left. right. apply in_splitT in i. destruct i. destruct s. subst. apply BotLRule_I.
  + destruct (dec_box_in (l, l0)).
    * left. left. right. destruct s. destruct a. apply in_splitT in H. destruct H. destruct s.
      simpl in e. apply in_splitT in H0. destruct H0. destruct s. simpl in e0. subst. apply IdBRule_I.
    * right. intro. destruct H.
      { destruct s.
        - inversion i. subst. simpl in f. apply f. exists P. split ; apply in_or_app ; right ; apply in_eq.
        - inversion i. subst. apply f1. exists A. split ; apply in_or_app ; right ; apply in_eq. }
      { inversion b. subst. apply f0. apply in_or_app. right. apply in_eq. }
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

Lemma dec_GLR_rule : forall (concl :Seq),
          (existsT2 prem, GLRRule [prem] concl) + ((existsT2 prem, GLRRule [prem] concl) -> False).
Proof.
intro concl. destruct concl. destruct (dec_box_in_list l0).
- left. destruct s. exists ((XBoxed_list (top_boxes l)) ++ [Box x], [x]).
  apply in_splitT in i. destruct i. destruct s. subst. apply GLRRule_I.
  + unfold is_Boxed_list. intros. apply in_top_boxes in H. destruct H. destruct s. destruct s.
    destruct p. exists x2. assumption.
  + induction l.  simpl. apply univ_gen_ext_nil. destruct a.
    * simpl. apply univ_gen_ext_extra. intro. destruct X. inversion H. assumption.
    * simpl. apply univ_gen_ext_extra. intro. destruct X. inversion H. assumption.
    * simpl. apply univ_gen_ext_extra. intro. destruct X. inversion H. assumption.
    * simpl. apply univ_gen_ext_cons. apply IHl.
- right. intro. destruct X. inversion g. subst. apply f. exists A. apply in_or_app. right. apply in_eq.
Qed.

Lemma dec_GLS_rules : forall (concl :Seq) ,
          ((existsT2 prems, GLS_rules prems concl) -> False) + (existsT2 prems, GLS_rules prems concl).
Proof.
intro concl. destruct (dec_GLS_init_rules concl).
- right. repeat destruct s.
  * exists nil. apply IdP. assumption.
  * exists nil. apply BotL. assumption.
- destruct (dec_ImpR_rule concl).
  * right. destruct s. exists [x]. apply ImpR. assumption.
  * destruct (dec_ImpL_rule concl).
    + right. repeat destruct s. exists [x; x0]. apply ImpL. assumption.
    + destruct (dec_GLR_rule concl).
      { right. repeat destruct s. exists [x]. apply GLR. assumption. }
      { left. intro. destruct X. inversion g.
        - inversion H. subst. apply f. auto.
        - inversion H. subst. apply f. auto.
        - inversion H. subst. apply f0. exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1). assumption.
        - inversion H. subst. apply f1. exists (Γ0 ++ Γ1, Δ0 ++ A :: Δ1). exists (Γ0 ++ B :: Γ1, Δ0 ++ Δ1).
          assumption.
        - inversion X. subst. apply f2. exists (XBoxed_list BΓ ++ [Box A], [A]). assumption. }
Qed.



