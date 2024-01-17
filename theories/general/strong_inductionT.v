Require Import PeanoNat.

(* Strong induction on Natural numbers with properties sending to Type. *)

Theorem strong_inductionT:
forall P : nat -> Type,
(forall n : nat, (forall k : nat, (k < n -> P k)) -> P n) ->
forall n : nat, P n.
Proof.
intros P H. assert (Lem : forall n, (forall m, m <= n -> P m)).
{ induction n. intros.
  - assert (E: m = 0). inversion H0.  reflexivity. rewrite E. apply H.
    intros. exfalso. inversion H1.
  - intros. apply H. intros. apply IHn. inversion H0.
    * rewrite H2 in H1. apply Nat.lt_succ_r. apply H1.
    * assert (E: k <= m). apply Nat.lt_le_incl. apply H1. 
      apply Nat.le_trans with (m:=m). apply E. apply H3. }
intro n. apply H. intros. apply Lem with (n:=n) (m:=k).
apply Nat.lt_le_incl. apply H0.
Qed.