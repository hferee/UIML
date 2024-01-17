Require Import List.
Export ListNotations.
Require Import Lia.
Require Import PeanoNat.

Require Import KS_calc.
Require Import KS_dec.
Require Import KS_termination_measure.

Delimit Scope My_scope with M.
Open Scope My_scope.
Set Implicit Arguments.

(* In this file we prove that each sequent Γ |- Δ has a derivation (not proof) D in
   KS of maximal height: all derivations in KS of this sequent must have an
   inferior or equal height to that of D.

   This result can be understood as claiming that the proof search defined by KS
   terminates. *)

Definition proj1_sigT2 {A : Type} (P : A -> Type) (e:sigT P) := match e with
                                    | existT _ a b => a
                                    end.

Definition proj2_sigT2 {A : Type} (P : A -> Type) (e : sigT P) :=
  match e return (P (proj1_sigT2 e)) with
  | existT _ a b => b
  end.

Lemma In_InT : forall (A : MPropF) l, In A l -> InT A l.
Proof.
intros. apply in_splitT in H. destruct H. destruct s. subst. apply InT_or_app. right.
apply InT_eq.
Qed.

Lemma In_InT_pair : forall (A : MPropF) (n : nat) l, In (A, n) l -> InT (A, n) l.
Proof.
induction l.
- intro. inversion H.
- intro. assert ({(A, n) = a} + {(A, n) <> a}). destruct a.
  destruct (eq_dec_form A m). subst. destruct (Nat.eq_dec n n0). subst. auto.
  right. intro. apply n1. inversion H0. auto. right. intro. inversion H0.
  auto. destruct H0. subst. apply InT_eq. apply InT_cons. apply IHl.
  inversion H. exfalso. auto. assumption.
Qed.

Lemma dec_le : forall n m, (n <= m) + ((n <= m) -> False).
Proof.
induction n.
- intro m. left. apply le_0_n.
- intro m. pose (IHn m). destruct s.
  * destruct (Nat.eq_dec n m). subst. right. intro. lia. left. lia.
  * right. intro. apply f. lia.
Qed.

Lemma InT_map_iff : forall {A B : Type} (f : A -> B) (l : list A) (y : B),
       (InT y (map f l) -> (existsT2 x : A, (f x = y) * InT x l)) *
       ((existsT2 x : A, (f x = y) * InT x l) -> InT y (map f l)).
Proof.
induction l.
- intros. simpl. split. intro. inversion X. intro. destruct X. destruct p. inversion i.
- simpl. intros. split.
  * intro. inversion X.
    + subst. exists a. split ; [ reflexivity | apply InT_eq].
    + subst. pose (IHl y). destruct p. apply s in X0. destruct X0. destruct p. exists x.
      split. assumption. apply InT_cons. assumption.
  * intro. pose (IHl y). destruct p. clear s. pose (proj2_sigT2 X).
    destruct p. inversion i0. subst. rewrite <- e. rewrite <- H0. apply InT_eq.
    subst. assert (existsT2 x : A, (f x = y) * InT x l). exists (proj1_sigT2 X).
    split ; assumption. apply i in X1. apply InT_cons. assumption.
Qed.

Fixpoint top_imps (l : list MPropF) : list MPropF :=
match l with
  | nil => nil
  | h :: t => match h with
                | Imp A B => (Imp A B) :: top_imps t
                | _ => top_imps t
              end
end.

Fixpoint pos_top_imps (l : list MPropF) : (list ((MPropF) * nat)) :=
match l with
  | nil => nil
  | h :: t => match h with
                | Imp A B => (Imp A B, 1) :: (map (fun y => (fst y, S (snd y))) (pos_top_imps t))
                | _ => (map (fun y => (fst y, S  (snd y))) (pos_top_imps t))
              end
end.

Lemma le_False_lt : forall n m, ((n <= m) -> False) -> (m < n).
Proof.
induction n.
- intros. exfalso. apply H. apply le_0_n.
- induction m.
  * intros. lia.
  * intros. rewrite <- Nat.succ_lt_mono. apply IHn. intro. apply H.
    rewrite <- Nat.succ_le_mono. assumption.
Qed.

Lemma top_boxes_nobox_gen_ext : forall l, nobox_gen_ext (top_boxes l) l.
Proof.
induction l.
- simpl. apply univ_gen_ext_nil.
- destruct a ; simpl.
  * apply univ_gen_ext_extra. intro. inversion X. inversion H. assumption.
  * apply univ_gen_ext_extra. intro. inversion X. inversion H. assumption.
  * apply univ_gen_ext_extra. intro. inversion X. inversion H. assumption.
  * apply univ_gen_ext_cons. assumption.
Qed.

Lemma nobox_gen_ext_top_boxes_identity : forall l0 l1, nobox_gen_ext l0 l1 ->
                                                       is_Boxed_list l0 ->
                                                       (l0 = top_boxes l1).
Proof.
intros l0 l1 X. induction X.
- intros. reflexivity.
- intro. simpl. destruct x.
  * exfalso. pose (H (# n)). assert (In # n (# n :: l)). apply in_eq. apply e in H0.
    destruct H0. inversion H0.
  * exfalso. pose (H (Bot)). assert (In (Bot) (Bot :: l)). apply in_eq. apply e in H0.
    destruct H0. inversion H0.
  * exfalso. pose (H (x1 --> x2)). assert (In (x1 --> x2) (x1 --> x2 :: l)). apply in_eq. apply e in H0.
    destruct H0. inversion H0.
  * assert (l = top_boxes le). apply IHX. intro. intros. apply H. apply in_cons. assumption.
    rewrite H0. reflexivity.
- simpl. destruct x.
  * apply IHX.
  * apply IHX.
  * apply IHX.
  * exfalso. apply p. exists x. reflexivity.
Qed.

Fixpoint flatten_list {A : Type} (l : list (list A)) : list A :=
  match l with
  | [ ] => [ ]
  | h :: t => h ++ (flatten_list t)
  end
.

Lemma InT_flatten_list_InT_elem {A : Type} : forall (l : list (list A)) b,
        InT b (flatten_list l) -> (existsT2 bs, (InT b bs) * (InT bs l)).
Proof.
induction l.
- intros. simpl in X. inversion X.
- intros. simpl in X. apply InT_app_or in X. destruct X.
  * exists a. split ; [assumption | apply InT_eq].
  * pose (IHl b). apply s in i. destruct i. destruct p. exists x. split ; [assumption | apply InT_cons ; assumption].
Qed.

Lemma redundant_flatten_list : forall ls (s : Seq), map (fun z : list MPropF * list MPropF => [z;s]) ls =
flatten_list (map (fun y : list MPropF * list MPropF => [[y;s]]) ls).
Proof.
induction ls.
- intros. simpl. reflexivity.
- simpl. intros. rewrite IHls. reflexivity.
Qed.

Lemma InT_trans_flatten_list {A : Type} : forall (l : list (list A)) bs b,
        (InT b bs) -> (InT bs l) -> (InT b (flatten_list l)).
Proof.
induction l.
- intros. inversion X0.
- intros. inversion X0.
  * subst. simpl. apply InT_or_app. auto.
  * subst. simpl. apply InT_or_app. right. pose (IHl bs b X X1) ; assumption.
Qed.

(* The next lemma claims that for each sequent s there is a derivation of that sequent. *)

Lemma der_s_inhabited : forall s, inhabited (KS_drv s).
Proof.
intros s.
pose (@dpI Seq KS_rules (fun _ : Seq => True) s).
assert (H: (fun _ : Seq => True) s). apply I. apply d in H. apply inhabits. assumption.
Qed.

(* The next definition deals with the property of being a derivation D0 of maximal height
   for the sequent s. *)

Definition is_mhd (s: Seq) (D0 : KS_drv s): Prop :=
      forall (D1 : KS_drv s), derrec_height D1 <= derrec_height D0.


(* The next lemma says that given a list and an element, there are only finitely many
   ways to insert this element in a list. *)

Lemma list_of_splits : forall (l : list MPropF), existsT2 listSplits,
                            forall l1 l2, ((l1 ++ l2 = l) <-> In (l1, l2) listSplits).
Proof.
induction l.
- exists [([],[])]. intros. destruct l1. split ; intro. simpl in H. rewrite H. apply in_eq.
  simpl in H. destruct H. inversion H. reflexivity. inversion H. split ; intro.
  simpl in H. inversion H. simpl. inversion H. inversion H0. inversion H0.
- destruct IHl. exists ([([], a :: l)] ++ (map (fun y => (a :: (fst y), snd y)) x)).
  intros. split ; intro.
  * apply in_or_app. destruct l1. simpl. left. left. simpl in H. rewrite H.
    reflexivity. simpl in H. inversion H. subst. right. pose (i l1 l2). destruct i0.
    assert (l1 ++ l2 = l1 ++ l2). reflexivity. apply H0 in H2.
    pose (in_map (fun y : list MPropF * list MPropF => (a :: fst y, snd y)) x (l1, l2) H2).
    simpl in i. assumption.
  * simpl in H. destruct H. inversion H. simpl. reflexivity. rewrite in_map_iff in H.
    destruct H. destruct H. inversion H. subst. simpl. pose (i (fst x0) (snd x0)).
    destruct i0. assert ((fst x0, snd x0) = x0). destruct x0. simpl. reflexivity.
    rewrite H3 in H2. apply H2 in H0. rewrite H0. reflexivity.
Qed.

Definition listInserts l (A : MPropF) := map (fun y => (fst y) ++ A :: (snd y)) (proj1_sigT2 (list_of_splits l)).

(* The next two lemmas make sure that the definition listInserts indeed captures the intended
   list. *)

Lemma listInserts_In : forall l (A: MPropF) l1 l2, ((l1 ++ l2 = l) -> In (l1 ++ A :: l2) (listInserts l A)).
Proof.
intros. unfold listInserts. assert (In (l1, l2) (proj1_sigT2 (list_of_splits l))). destruct (list_of_splits l).
simpl. pose (i l1 l2). apply i0. assumption.
pose (in_map (fun y : list MPropF * list MPropF => fst y ++ A :: snd y) (proj1_sigT2 (list_of_splits l)) (l1, l2) H0).
simpl in i. assumption.
Qed.

Lemma In_listInserts : forall l (A: MPropF) l0, In l0 (listInserts l A) ->
                            (exists l1 l2, prod (l1 ++ l2 = l) (l1 ++ A :: l2 = l0)).
Proof.
intros. unfold listInserts in H. destruct (list_of_splits l). simpl in H. rewrite in_map_iff in H.
destruct H. destruct H. subst. exists (fst x0). exists (snd x0). split. apply i.
destruct x0. simpl. assumption. reflexivity.
Qed.

(* The definitions below allow you to create the list of all sequents given two lists and a
   formula to insert in one of them. *)

Definition listInsertsR_Seqs (Γ Δ : list MPropF) (A : MPropF) := map (fun y => (y, Δ)) (listInserts Γ A).

Definition listInsertsL_Seqs (Γ Δ : list MPropF) (A : MPropF) := map (fun y => (Γ, y)) (listInserts Δ A).

(* The next definition allows one to create all sequents *)

Definition listInsertsRL_Seqs (Γ Δ : list MPropF) (A B : MPropF) :=
                  flatten_list (map (fun z => (map (fun y => (z, y)) (listInserts Δ B))) (listInserts Γ A)).

(* Some useful functions *)

Fixpoint remove_nth (n: nat) (A : MPropF) l:=
    match n with
      | 0 => l
      | 1 => match l with
               | [] => []
               | B::tl => if (eq_dec_form A B) then tl else B:: tl
             end
      | S m => match l with
                 | [] => []
                 | B::tl => B::(remove_nth m A tl)
               end
      end.

Fixpoint nth_split (n : nat) (l : list MPropF) : (list MPropF * list MPropF) :=
    match n with
      | 0 => ([], l)
      | 1 => match l with
               | [] => ([], [])
               | B::tl => ([B] , tl)
             end
      | S m => match l with
                 | [] => ([], [])
                 | B::tl => (B :: (fst (nth_split m tl)), snd (nth_split m tl))
               end
      end.

Lemma nth_split_length : forall (l0 l1 : list MPropF), (nth_split (length l0) (l0 ++ l1)) = (l0, l1).
Proof.
induction l0.
- intros. simpl. reflexivity.
- intros. pose (IHl0 l1). simpl (length (a :: l0)). simpl ((a :: l0) ++ l1).
  simpl. destruct l0.
  * simpl. reflexivity.
  * assert (match length (m :: l0) with
| 0 => ([a], (m :: l0) ++ l1)
| S _ =>
    (a :: fst (nth_split (length (m :: l0)) ((m :: l0) ++ l1)),
    snd (nth_split (length (m :: l0)) ((m :: l0) ++ l1)))
end = (a :: fst (nth_split (length (m :: l0)) ((m :: l0) ++ l1)),
    snd (nth_split (length (m :: l0)) ((m :: l0) ++ l1)))). reflexivity. rewrite H.
clear H. rewrite e. simpl. reflexivity.
Qed.

Lemma nth_split_idL : forall (l0 l1 : list MPropF), l0 = fst (nth_split (length l0) (l0 ++ l1)).
Proof.
induction l0.
- intros. simpl. reflexivity.
- intros. simpl (length (a :: l0)). pose (IHl0 l1). assert (fst (nth_split (S (length l0)) ((a :: l0) ++ l1)) =
  a :: fst (nth_split (length l0) (l0 ++ l1))). simpl. destruct l0. simpl. reflexivity.
  simpl. reflexivity. rewrite H. rewrite <- e. reflexivity.
Qed.

Lemma nth_split_idR : forall (l0 l1 : list MPropF), l1 = snd (nth_split (length l0) (l0 ++ l1)).
Proof.
induction l0.
- intros. simpl. reflexivity.
- intros. simpl (length (a :: l0)). pose (IHl0 l1). rewrite e. destruct l0.
  * simpl. reflexivity.
  * simpl (length (m :: l0)). simpl (S (S (length l0))).
    simpl (length (m :: l0)) in e. rewrite <- e.
    assert ((S (S (length l0))) = (length (a :: m :: l0))). simpl. reflexivity.
    rewrite H. rewrite nth_split_length. simpl. reflexivity.
Qed.

Lemma nth_split_length_id : forall (l0 l1 : list MPropF) n, (length l0 = n) ->
                                (fst (nth_split n (l0 ++ l1)) = l0 /\
                                snd (nth_split n (l0 ++ l1)) = l1).
Proof.
induction l0.
- intros. simpl. split. simpl in H. subst. simpl. reflexivity. simpl in H. subst. simpl. reflexivity.
- intros. simpl in H. subst. split.
  * assert (J1:length l0 = length l0). reflexivity. pose (@IHl0 l1 (length l0) J1).
    destruct a0. simpl. destruct l0. simpl. reflexivity. simpl. rewrite <- H.
    simpl. reflexivity.
  * assert (J1:length l0 = length l0). reflexivity. pose (@IHl0 l1 (length l0) J1).
    destruct a0. rewrite <- H0. simpl ((a :: l0) ++ snd (nth_split (length l0) (l0 ++ l1))).
    assert ((nth_split (S (length l0)) (a :: l0 ++ snd (nth_split (length l0) (l0 ++ l1))) =
    (a :: l0 ,snd (nth_split (length l0) (l0 ++ l1))))).
    pose (nth_split_length (a :: l0) (snd (nth_split (length l0) (l0 ++ l1)))). apply e.
    rewrite H1. simpl. reflexivity.
Qed.

Lemma effective_remove_nth : forall A l0 l1, ((remove_nth (S (length l0)) A (l0 ++ A :: l1)) = l0 ++ l1).
Proof.
induction l0.
- intros. simpl. destruct (eq_dec_form A A). reflexivity. exfalso. auto.
- intros. simpl (S (length (a :: l0))). repeat rewrite <- app_assoc. simpl ((a :: l0) ++ A :: l1).
  pose (IHl0 l1). simpl ((a :: l0) ++ l1). rewrite <- e. simpl. reflexivity.
Qed.

