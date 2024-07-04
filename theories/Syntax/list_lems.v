Require Import List.
Export ListNotations.

Require Import genT.
Require Import gen_tacs.
Require Import List_lemmasT.
Require Import existsT.

Require Import CML_Syntax.

(* Some useful lemmas about lists. *)

Lemma in_exch_list : forall {A : Type} (l0 l1 l2 l3 l4 : list A) (a : A),
  In a (l0 ++ l1 ++ l2 ++ l3 ++ l4) -> In a (l0 ++ l3 ++ l2 ++ l1 ++ l4).
Proof.
intros A l0 l1 l2 l3 l4 a H.
apply in_app_or in H. destruct H. apply in_or_app. left. assumption.
apply in_app_or in H. destruct H. apply in_or_app. right. apply in_or_app. right.
apply in_or_app. right. apply in_or_app. left. assumption.
apply in_app_or in H. destruct H. apply in_or_app. right. apply in_or_app. right.
apply in_or_app. left. assumption.
apply in_app_or in H. destruct H. apply in_or_app. right. apply in_or_app. left. 
assumption.
apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
apply in_or_app. right. assumption.
Qed.

Lemma InT_exch_list : forall {A : Type} (l0 l1 l2 l3 l4 : list A) (a : A),
  InT a (l0 ++ l1 ++ l2 ++ l3 ++ l4) -> InT a (l0 ++ l3 ++ l2 ++ l1 ++ l4).
Proof.
intros A l0 l1 l2 l3 l4 a H.
apply InT_app_or in H. destruct H. apply InT_or_app. left. assumption.
apply InT_app_or in i. destruct i. apply InT_or_app. right. apply InT_or_app. right.
apply InT_or_app. right. apply InT_or_app. left. assumption.
apply InT_app_or in i. destruct i. apply InT_or_app. right. apply InT_or_app. right.
apply InT_or_app. left. assumption.
apply InT_app_or in i. destruct i. apply InT_or_app. right. apply InT_or_app. left. 
assumption.
apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. right.
apply InT_or_app. right. assumption.
Qed.

Lemma partition_1_element : forall {A : Type} (l1 l2 l3 l4 l5 l6 l7 : list A) a,
l1 ++ l2 ++ l3 ++ l4 ++ l5 = l6 ++ a :: l7 ->
  (existsT2 l8 l9, l1 = l8 ++ a :: l9) +
  ((existsT2 l8 l9, l2 = l8 ++ a :: l9) +
  ((existsT2 l8 l9, l3 = l8 ++ a :: l9) +
  ((existsT2 l8 l9, l4 = l8 ++ a :: l9) +
  ((existsT2 l8 l9, l5 = l8 ++ a :: l9))))).
Proof.
intros A l1. induction l1.
- simpl. induction l2.
  * simpl. induction l3.
    + simpl. induction l4.
      { simpl. intros. right. right. right. right. exists l6. exists l7.
        assumption. }
      { intros. destruct l6. simpl in H. right. right. right. left. exists []. simpl.
        inversion H. exists l4. reflexivity.
        inversion H. apply IHl4 in H2. destruct H2. destruct s. destruct s. exfalso.
        apply app_cons_not_nil in e. assumption.
        destruct s. destruct s. destruct s. exfalso.
        apply app_cons_not_nil in e. assumption.
        destruct s. destruct s. destruct s. exfalso.
        apply app_cons_not_nil in e. assumption.
        destruct s. destruct s. destruct s. right. right. right.
        left. exists (a1 :: x). exists x0. simpl. rewrite e. reflexivity.
        destruct s. destruct s. right. right. right. right. exists x. exists x0.
        assumption. }
    + intros l4 l5 l6 l7 a0 E. destruct l6.
      { inversion E. right. right. left. exists []. exists l3. simpl. reflexivity. }
      { inversion E. apply IHl3 in H1. destruct H1.
        destruct s. destruct s. exfalso.
        apply app_cons_not_nil in e. assumption.
        destruct s. destruct s. destruct s. exfalso.
        apply app_cons_not_nil in e. assumption.
        destruct s. destruct s. destruct s. right. right. left. exists (a1 :: x).
        exists x0. rewrite e. simpl. reflexivity.
        right. right. right. assumption. }
  * intros l3 l4 l5 l6 l7 a0 E. destruct l6. inversion E.
    { inversion E. right. left. exists []. exists l2. simpl. reflexivity. }
    { inversion E. apply IHl2 in H1. destruct H1.
      destruct s. destruct s. exfalso.
      apply app_cons_not_nil in e. assumption.
      destruct s. destruct s. destruct s. right. left. exists (a1 :: x). exists x0.
      rewrite e. simpl. reflexivity.
      right. right. assumption. }
- intros l2 l3 l4 l5 l6 l7 a0 E. destruct l6.
  { inversion E. left. exists []. exists l1. auto. }
  { inversion E. apply IHl1 in H1. destruct H1.
    destruct s. destruct s. left. exists (a1 :: x). exists x0. rewrite e. auto.
    right. assumption. }
Qed.

Lemma partition_1_element2 : forall {A : Type} (l1 l2 l3 l4 l5 l6 l7 : list A) a,
l1 ++ l2 ++ l3 ++ l4 ++ l5 = l6 ++ a :: l7 ->
  ((existsT2 l8 l9, (l1 = l8 ++ a :: l9) * (l9 ++ l2 ++ l3 ++ l4 ++ l5 = l7) * (l8 = l6)) +
  ((existsT2 l8 l9, (l2 = l8 ++ a :: l9) * (l9 ++ l3 ++ l4 ++ l5 = l7) * (l1 ++ l8 = l6)) +
  ((existsT2 l8 l9, (l3 = l8 ++ a :: l9) * (l9 ++ l4 ++ l5 = l7) * (l1 ++ l2 ++ l8 = l6)) +
  ((existsT2 l8 l9, (l4 = l8 ++ a :: l9) * (l9 ++ l5 = l7) * (l1 ++ l2 ++ l3 ++ l8 = l6)) +
  ((existsT2 l8 l9, (l5 = l8 ++ a :: l9) * (l9 = l7) * (l1 ++ l2 ++ l3 ++ l4 ++ l8 = l6))))))).
Proof.
intros A l1. induction l1.
- simpl. induction l2.
  * simpl. induction l3.
    + simpl. induction l4.
      { simpl. intros. right. right. right. right. exists l6. exists l7.
        split. split. assumption. reflexivity. reflexivity. }
      { intros. destruct l6. simpl in H. right. right. right. left. exists []. simpl.
        inversion H. exists l4.  split. split. reflexivity. reflexivity. reflexivity.
        inversion H. apply IHl4 in H2. destruct H2. destruct s. destruct s. exfalso.
        repeat destruct p. apply app_cons_not_nil in e0. assumption.
        destruct s. destruct s. destruct s. exfalso.
        repeat destruct p. apply app_cons_not_nil in e0. assumption.
        destruct s. destruct s. destruct s. exfalso.
        repeat destruct p. apply app_cons_not_nil in e0. assumption.
        destruct s. destruct s. destruct s. right. right. right.
        left. exists (a1 :: x). exists x0. simpl. repeat destruct p. rewrite e0.
        split. split. reflexivity. assumption. subst. reflexivity.
        destruct s. destruct s. right. right. right. right. exists x. exists x0.
        split. split. repeat destruct p. assumption. repeat destruct p. subst. reflexivity.
        repeat destruct p. subst. reflexivity. }
    + intros l4 l5 l6 l7 a0 E. destruct l6.
      { inversion E. right. right. left. exists []. exists l3. simpl. split. split. reflexivity. reflexivity. reflexivity. }
      { inversion E. apply IHl3 in H1. destruct H1.
        destruct s. destruct s. exfalso.
        repeat destruct p. apply app_cons_not_nil in e0. assumption.
        destruct s. destruct s. destruct s. exfalso.
        repeat destruct p. apply app_cons_not_nil in e0. assumption.
        destruct s. destruct s. destruct s. right. right. left. exists (a1 :: x).
        exists x0. repeat destruct p. rewrite e0. simpl. split. split. reflexivity. assumption. subst. reflexivity.
        right. right. right. destruct s. left. repeat destruct s. exists x. exists x0. repeat destruct p. 
        split. split. assumption. assumption. simpl. subst. reflexivity. 
        repeat destruct s. right. exists x. exists x0. repeat destruct p. split. split. assumption. assumption. subst. reflexivity. }
  * intros l3 l4 l5 l6 l7 a0 E. destruct l6. inversion E.
    { inversion E. right. left. exists []. exists l2. simpl. split. split. reflexivity. reflexivity. reflexivity. }
    { inversion E. apply IHl2 in H1. destruct H1.
      destruct s. destruct s. exfalso.
      repeat destruct p. apply app_cons_not_nil in e0. assumption.
      destruct s. destruct s. destruct s. right. left. exists (a1 :: x). exists x0.
      repeat destruct p. rewrite e. simpl. subst. split. split. reflexivity. reflexivity. reflexivity.
      right. right. destruct s. repeat destruct s. repeat destruct p. left. exists x. exists x0. subst. split. split. reflexivity.
      reflexivity. reflexivity.
      destruct s. repeat destruct s. repeat destruct p. subst. right. left. exists x. exists x0. subst. split. split. reflexivity.
      reflexivity. reflexivity.
      repeat destruct s. repeat destruct p. right. right. exists x. exists x0. subst. split. split. reflexivity.
      reflexivity. reflexivity. }
- intros l2 l3 l4 l5 l6 l7 a0 E. destruct l6.
  { inversion E. left. exists []. exists l1. auto. }
  { inversion E. apply IHl1 in H1. destruct H1.
    destruct s. destruct s. left. exists (a1 :: x). exists x0. repeat destruct p. rewrite e0. split.
    split. subst. reflexivity. subst. reflexivity. subst. reflexivity.
    destruct s.
    repeat destruct s. right. left. exists x. exists x0. repeat destruct p. subst. split. split. subst. reflexivity.
    reflexivity. reflexivity.
    destruct s.
    repeat destruct s. right. right. left. exists x. exists x0. repeat destruct p. subst. split. split. subst. reflexivity.
    reflexivity. reflexivity. 
    destruct s.
    repeat destruct s. right. right. right. left. exists x. exists x0. repeat destruct p. subst. split. split. subst. reflexivity.
    reflexivity. reflexivity.
    destruct s.
    repeat destruct s. right. right. right. right. exists x. exists x0. repeat destruct p. subst. split. split. subst. reflexivity.
    reflexivity. reflexivity. }
Qed.


Lemma add_1_element_split_lists : forall {A : Type} (l1 l2 l3 l4 : list A) a,
    l1 ++ l2 = l3 ++ l4 -> ((l1 = l3) * (l2 = l4)) +
    (existsT2 l5 l6, ((l5 ++ a :: l6 ++ l2 = l3 ++ a :: l4) * (l5 ++ l6 = l1) * (l6 ++ l2 = l4) * (l5 = l3)) +
                     ((l1 ++ l5 ++ a :: l6 = l3 ++ a :: l4) * (l5 ++ l6 = l2) * (l1 ++ l5 = l3) * (l6 = l4))).
Proof.
intros A l1. induction l1.
- intros. rewrite app_nil_l in H. destruct l3.
  + left. rewrite app_nil_l in H. split. reflexivity. assumption.
  + right. exists (a0 :: l3). exists l4. right. split. split. split.
    rewrite app_nil_l. reflexivity. symmetry. assumption. rewrite app_nil_l.
    reflexivity. reflexivity.
- destruct l3.
  + intros. right. exists []. exists (a :: l1). left. split. split. split.
    repeat rewrite app_nil_l. rewrite H. reflexivity. rewrite app_nil_l. reflexivity.
    rewrite app_nil_l in H. assumption. reflexivity.
  + intros. inversion H. apply IHl1 with (a:=a1) in H2. destruct H2.
    * destruct p. subst. left. split. reflexivity. reflexivity.
    * destruct s. destruct s. destruct s.
      { repeat destruct p. subst. right. exists (a0 :: l3). exists x0.
        left. split. split. split. reflexivity. reflexivity. reflexivity.
        reflexivity. }
      { repeat destruct p. subst. right. exists x. exists l4. right. split. split. split.
        repeat rewrite app_assoc. reflexivity. reflexivity. reflexivity. reflexivity. }
Qed.

Lemma app2_find_hole {A : Type} : forall (l1 l2 l3 l4 : list A),
              l1 ++ l2 = l3 ++ l4 ->
              (existsT2 l5,
                ((l3 = l1) * (l4 = l2)) +
                ((l3 = l1 ++ l5) * (l2 = l5 ++ l4)) +
                ((l1 = l3 ++ l5) * (l4 = l5 ++ l2))).
Proof.
induction l1.
- intros. exists l3. left. right. split. reflexivity. assumption.
- intros l2 l3 l4 E. destruct l3.
  * rewrite app_nil_l in E. exists (a :: l1). right. split. reflexivity.
    symmetry. assumption.
  * inversion E. apply IHl1 in H1. destruct H1. destruct s.
    + destruct s.
      { destruct p. subst. exists []. left. left. auto. }
      { destruct p. subst. exists x. left. right. auto. }
    + destruct p. subst. exists x. right. auto.
Qed.

Theorem in_splitT : forall x (l:list MPropF), In x l -> existsT2 l1 l2, l = l1++x::l2.
Proof.
intros x l. induction l.
- intro. inversion H.
- intro. destruct (eq_dec_form x a).
  * subst. exists nil. exists l. auto.
  * assert (In x l). inversion H. subst. exfalso. apply n. reflexivity. assumption.
    apply IHl in H0. destruct H0. destruct s. subst. exists ([a] ++ x0). exists x1.
    auto.
Defined.


Lemma InT_dec : forall l (a : MPropF) , (InT a l) + ((InT a l) -> False).
Proof.
induction l.
- intro. right. intro. inversion H.
- intro a0. pose (IHl a0). destruct s.
  * left. apply InT_cons. assumption.
  * destruct (eq_dec_form a a0).
    + subst. left. apply InT_eq.
    + right. intro. inversion H.
      { apply n. assumption. }
      { apply f. assumption. }
Qed.

Definition eq_dec_listsF : forall (l0 l1 : list MPropF), {l0 = l1} + {l0 <> l1}.
Proof.
apply list_eq_dec. apply eq_dec_form.
Defined.

Definition eq_dec_seqs : forall (s0 s1 : rel (list MPropF)), {s0 = s1} + {s0 <> s1}.
Proof.
intros. destruct s0. destruct s1. destruct (eq_dec_listsF l l1) ; destruct (eq_dec_listsF l0 l2).
- subst. left. reflexivity.
- subst. right. intro. inversion H. auto.
- subst. right. intro. inversion H. auto.
- subst. right. intro. inversion H. auto.
Defined.

Definition seqs_in_splitT : forall (x : rel (list MPropF)) l,
       In x l -> existsT2 l1 l2, l = l1 ++ x :: l2.
Proof.
intros x l. induction l.
- intro. inversion H.
- intro. destruct (eq_dec_seqs x a).
  * subst. exists nil. exists l. auto.
  * assert (In x l). inversion H. subst. exfalso. apply n. reflexivity. assumption.
    apply IHl in H0. destruct H0. destruct s. subst. exists ([a] ++ x0). exists x1.
    auto.
Defined.

Definition In_InT_seqs : forall (seq : rel (list MPropF)) seqs, In seq seqs -> InT seq seqs.
Proof.
intros seq seqs. induction seqs.
- intro. inversion H.
- intro. apply seqs_in_splitT in H. destruct H. destruct s. rewrite e. apply InT_or_app.
  right. apply InT_eq.
Defined.

Lemma list_split_form : forall (A B : MPropF) l0 l1 l2 l3, (l0 ++ A :: l1 = l2 ++ B :: l3) ->
                          ((A = B) * (l0 = l2) * (l1 = l3)) +
                          (existsT2 l4 l5, (l0 = l4 ++ l5) * (l5 ++ A :: l1 = l3) * (l2 ++ [B] = l4)) +
                          (existsT2 l4 l5, (l1 = l4 ++ l5) * (l0 ++ A :: l4 = l2) * (B :: l3 = l5)).
Proof.
intros A B l0. generalize dependent A. generalize dependent B. induction l0.
- intros. simpl in H. destruct l2.
  * simpl in H. left. left. inversion H. auto.
  * simpl. inversion H. subst. right. exists l2. exists (B :: l3). auto.
- simpl. simpl in IHl0. intros. destruct l2.
  * left. right. simpl. exists [B]. exists l0. simpl. inversion H. subst. auto.
  * inversion H. subst. pose (@IHl0 B A l1 l2 l3 H2). repeat destruct s.
    + repeat destruct p. subst. left. left. auto.
    + repeat destruct p. subst. left. right. exists ((m :: l2) ++ [B]). exists x0.
      auto.
    + repeat destruct p. subst. right. exists x. exists (B :: l3). auto.
Qed.
