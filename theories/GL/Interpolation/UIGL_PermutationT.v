Require Import List.
Export ListNotations.
Require Export Permutation.

Require Import GLS_export.

Section PermutationT.

    Inductive PermutationT : list MPropF -> list MPropF -> Type :=
      | permT_nil: PermutationT nil nil
      | permT_skip: forall (x: MPropF) (l l':list MPropF), PermutationT l l' -> PermutationT (cons x l) (cons x l')
      | permT_swap: forall (x y: MPropF) (l:list MPropF), PermutationT (cons y (cons x l)) (cons x (cons y l))
      | permT_trans: forall (l l' l'':list MPropF), PermutationT l l' -> PermutationT l' l'' -> PermutationT l l''.

Local Hint Constructors PermutationT : core.

Theorem PermutationT_refl : forall l, PermutationT l l.
Proof.
  induction l; constructor. exact IHl.
Qed.

Theorem PermutationT_sym : forall l l',
 PermutationT l l' -> PermutationT l' l.
Proof.
  intros l l' Hperm; induction Hperm; auto.
  apply permT_trans with (l':=l'); assumption.
Qed.

Lemma PermutationT_app_tail : forall l l' tl,
 PermutationT l l' -> PermutationT (l++tl) (l'++tl).
Proof.
  intros l l' tl Hperm; induction Hperm as [|x l l'|x y l|l l' l'']; simpl; auto.
  apply PermutationT_refl.
  eapply permT_trans with (l':=l'++tl); trivial.
Qed.

Lemma PermutationT_app_head : forall l tl tl',
 PermutationT tl tl' -> PermutationT (l++tl) (l++tl').
Proof.
  intros l tl tl' Hperm; induction l;
   [trivial | repeat rewrite <- app_comm_cons; constructor; assumption].
Qed.

Theorem PermutationT_app : forall l m l' m',
 PermutationT l l' -> PermutationT m m' -> PermutationT (l++m) (l'++m').
Proof.
  intros l m l' m' Hpermll' Hpermmm';
   induction Hpermll' as [|x l l'|x y l|l l' l''];
    repeat rewrite <- app_comm_cons; auto.
  - apply permT_trans with (l' := (x :: y :: l ++ m));
      [idtac | repeat rewrite app_comm_cons; apply PermutationT_app_head]; trivial.
  - apply permT_trans with (l' := (l' ++ m')); try assumption.
    apply PermutationT_app_tail; assumption.
Qed.

Lemma PermutationT_cons_append : forall l x,
  PermutationT (x :: l) (l ++ x :: nil).
Proof.
induction l; intros; auto. simpl. apply permT_skip ; apply permT_nil. simpl.
apply permT_trans with (l':=(a :: x :: l)). apply permT_swap. apply permT_skip ; auto.
Qed.

Theorem PermutationT_app_comm : forall l l',
  PermutationT (l ++ l') (l' ++ l).
Proof.
  induction l as [|x l]; simpl; intro l'.
  - rewrite app_nil_r; trivial. apply PermutationT_refl.
  - rewrite app_comm_cons. pose (IHl l').
    apply permT_trans with (l':= (l' ++ l ++ [x])).
    simpl. apply permT_trans with (l':= (x :: l' ++ l)).
    apply permT_skip ; auto. pose (PermutationT_cons_append (l' ++ l) x).
    rewrite <- app_assoc in p0 ; auto.
    apply (PermutationT_app l'). apply PermutationT_refl.
    apply PermutationT_sym , PermutationT_cons_append.
Qed.
Local Hint Resolve PermutationT_app_comm : core.

Theorem PermutationT_cons_app : forall l l1 l2 a,
  PermutationT l (l1 ++ l2) -> PermutationT (a :: l) (l1 ++ a :: l2).
Proof.
  intros l l1 l2 a H. apply permT_trans with (l':=(a :: (l1 ++ l2))).
  apply permT_skip ; auto.
  rewrite app_comm_cons. apply permT_trans with (l':=(a :: (l2 ++ l1))).
  simpl. apply permT_skip ; auto. pose (PermutationT_app_comm (a :: l2) l1).
  simpl in p ; auto.
Qed.

Lemma Permutation_vs_elt_invT : forall l l1 l2 (a : MPropF),
 Permutation l (l1 ++ a :: l2) -> existsT2 l' l'', l = l' ++ a :: l''.
Proof.
  intros l l1 l2 a HP. apply Permutation_sym in HP.
  assert (In a (l1 ++ a :: l2)). apply in_or_app ; right ; apply in_eq.
  epose (Permutation_in a HP H). apply In_InT in i. apply InT_split in i.
  auto.
Qed.

Lemma Permutation_vs_cons_invT : forall l l1 (a : MPropF),
  Permutation l (a :: l1) -> existsT2 l' l'', l = l' ++ a :: l''.
Proof.
  intros l l1 a HP.
  rewrite <- (app_nil_l (a :: l1)) in HP. apply Permutation_vs_elt_invT in HP. auto.
Qed.

    Theorem Permutation_PermutationT : forall l l', (Permutation l l' -> PermutationT l l') * (PermutationT l l' -> Permutation l l').
    Proof.
    intros l l'. split ; intros.
    - revert H. revert l'. induction l.
      + intros. destruct l'. apply permT_nil. apply Permutation_nil in H ; inversion H.
      + intros. pose (Permutation_sym H). apply Permutation_vs_cons_invT in p. destruct p. destruct s. subst.
         apply Permutation_cons_app_inv in H. apply IHl in H. apply PermutationT_cons_app ; auto.
    - induction H.
      + apply perm_nil.
      + apply perm_skip ; auto.
      + apply perm_swap ; auto.
      + apply perm_trans with (l':=l') ; auto.
    Qed.

Theorem PermutationT_ind_T :
 forall P : list MPropF -> list MPropF -> Type,
   P [] [] ->
   (forall x l l', PermutationT l l' -> P l l' -> P (x :: l) (x :: l')) ->
   (forall x y l l', PermutationT l l' -> P l l' -> P (y :: x :: l) (x :: y :: l')) ->
   (forall l l' l'', PermutationT l l' -> P l l' -> PermutationT l' l'' -> P l' l'' -> P l l'') ->
   forall l l', PermutationT l l' -> P l l'.
Proof.
  intros P Hnil Hskip Hswap Htrans.
  intros l l' ; induction 1 ; auto.
  - apply Htrans with (x::y::l); auto.
    + apply Hswap; auto. apply Permutation_PermutationT ; apply Permutation_refl.
      induction l; auto. apply Hskip ; auto. apply Permutation_PermutationT ; apply Permutation_refl.
    + apply Permutation_PermutationT ; apply Permutation_refl.
    + apply Hskip; auto. apply Permutation_PermutationT ; apply Permutation_refl.
      apply Hskip; auto. apply Permutation_PermutationT ; apply Permutation_refl.
      induction l; auto. apply Hskip ; auto. apply Permutation_PermutationT ; apply Permutation_refl.
  - eauto.
Qed.

  End PermutationT.