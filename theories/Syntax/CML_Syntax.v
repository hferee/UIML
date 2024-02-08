Require Import List.
Export ListNotations.
Require Import PeanoNat.

Require Import general_export.

Set Implicit Arguments.

(* Definitions Language *)

(* First, let us define the propositional formulas we use here. *)

Inductive MPropF : Type :=
 | Var : nat -> MPropF
 | Bot : MPropF
 | Imp : MPropF -> MPropF -> MPropF
 | Box : MPropF -> MPropF
.

Notation "# p" := (Var p) (at level 1).
Notation "A --> B" := (Imp A B) (at level 16, right associativity).
Notation "⊥" := Bot (at level 0).
Notation "¬ A" := (A --> ⊥) (at level 42).

  Definition Top := (Bot --> Bot).
  Definition Neg (A : MPropF) := A --> Bot.
  Definition And (A B : MPropF) := Neg (A --> Neg B).
  Definition Or (A B : MPropF) := (Neg A) --> B.
  Definition Diam (A : MPropF) := Neg (Box (Neg A)).

Fixpoint subformlist (φ : MPropF) : list MPropF :=match φ with
| Var p => (Var p) :: nil | Bot => Bot :: nil
| Imp ψ χ => (Imp ψ χ) ::
(subformlist ψ) ++ (subformlist χ) | Box ψ => (Box ψ) :: (subformlist ψ)end.

Lemma eq_dec_form : forall x y : MPropF, {x = y} + {x <> y}.
Proof.
repeat decide equality.
Qed.

Fixpoint size (φ : MPropF) : nat :=
match φ with
| Var p => 1| Bot => 1
| Imp ψ χ => 1 + (size ψ) + (size χ) | Box ψ => 1 + (size ψ)
end.

Fixpoint size_LF (l : list MPropF) : nat :=
match l with
  | [] => 0
  | h :: t => (size h) + (size_LF t)
end.

Fixpoint subst (σ : nat -> MPropF) (φ : MPropF) : MPropF :=
match φ with
| Var p => (σ p)
| Bot => Bot
| Imp ψ χ => Imp (subst σ ψ) (subst σ χ)| Box ψ => Box (subst σ ψ)
end.

Definition is_atomicT A : Type :=
                  (exists p, A = # p) + (A = Bot).


(* Order all this *)

Definition is_boxedT (A : MPropF) : Type :=
                  exists (B : MPropF), A = Box B.

Definition is_Boxed_list (Γ : list (MPropF)) : Prop :=
    forall (A : MPropF), (In A Γ) -> (exists (B : MPropF), A = Box B).

Definition is_Prime (Γ : list MPropF) : Prop :=
    forall (A : MPropF), (In A Γ) ->
    (exists (B : MPropF), A = Box B) \/ (exists P, A = # P) \/ (A = Bot).


(* With these properties we can define restrictions of univ_gen_ext on
   formulae. *)

Definition nobox_gen_ext := univ_gen_ext (fun x => (is_boxedT x) -> False).

(* A lemmas about nobox_gen_ext. *)

Lemma nobox_gen_ext_injective : forall (l0 l1 l : list (MPropF)), (is_Boxed_list l0) -> (is_Boxed_list l1) ->
                                (nobox_gen_ext l0 l) -> (nobox_gen_ext l1 l) -> l1 = l0.
Proof.
intros l0 l1 l Hl0 Hl1 gen. generalize dependent l1.
induction gen.
- intros. inversion X. reflexivity.
- intros. inversion X.
  * subst. assert (l0 = l). apply IHgen. intro. intros. apply Hl0. apply in_cons. assumption.
    intro. intros. apply Hl1. apply in_cons. assumption. assumption. rewrite H. reflexivity.
  * subst. exfalso. apply H1. apply Hl0. apply in_eq.
- intros. apply IHgen. intro. intros. apply Hl0. assumption.
  intro. intros. apply Hl1. assumption. inversion X.
  subst. exfalso. apply p. apply Hl1. apply in_eq. subst. assumption.
Qed.

(* The next definitions help to define the combination of a list of boxed
   formulae and the unboxing of all the formulae in that list. *)

Definition unBox_formula (A : MPropF) : MPropF :=
  match A with
              | # P => # P
              | Bot => Bot
              | A --> B => A --> B
              | Box A => A
              end
.

Fixpoint unboxed_list (Γ : list (MPropF)) : list (MPropF):=
  match Γ with
  | [ ] => [ ]
  | h :: t => (unBox_formula h :: unboxed_list t)
  end
.

Fixpoint top_boxes (l : list (MPropF)) : list (MPropF) :=
match l with
  | nil => nil
  | h :: t => match h with
                | Box A => (Box A) :: top_boxes t
                | _ => top_boxes t
              end
end.

(* Now that we have defined these, we can prove some properties about them. *)

Lemma unbox_app_distrib :
  forall (l1 l2: list (MPropF)), unboxed_list (l1 ++ l2) = (unboxed_list l1) ++ (unboxed_list l2).
Proof.
induction l1.
- intro l2. rewrite app_nil_l with (l:=l2). simpl. reflexivity.
- intro l2. simpl. rewrite IHl1. reflexivity.
Qed.

Lemma subl_of_boxl_is_boxl {V : Set}:
  forall (l1 l2: list (MPropF)), (incl l1 l2) -> (is_Boxed_list l2) -> (is_Boxed_list l1).
Proof.
intros. unfold is_Boxed_list. intros. apply H in H1. apply H0 in H1.
destruct H1. exists x. assumption.
Qed.

Lemma tl_of_boxl_is_boxl {V : Set}:
  forall (h : MPropF) (t l : list (MPropF)) (H: l = h :: t),
         (is_Boxed_list l) -> (is_Boxed_list t).
Proof.
intros. unfold is_Boxed_list. intros. assert (Hyp: In A l).
rewrite H. simpl. right. apply H1. apply H0 in Hyp. destruct Hyp.
exists x. assumption.
Qed.

Lemma is_box_is_in_boxed_list : forall l (A : MPropF), In A l -> is_Boxed_list l -> (exists B, Box B = A).
Proof.
induction l.
- intros. inversion H.
- intros. inversion H.
  + subst. unfold is_Boxed_list in H0. pose (H0 A).
    apply e in H. destruct H. exists x. symmetry. assumption.
  + apply IHl. assumption. unfold is_Boxed_list. intros. unfold is_Boxed_list in H0.
    pose (H0 A0). apply e. apply in_cons. assumption.
Qed.

Lemma top_boxes_distr_app : forall (l1 l2 : list (MPropF)),
      top_boxes (l1 ++ l2) = (top_boxes l1) ++ (top_boxes l2).
Proof.
induction l1.
- intro l2. rewrite app_nil_l. simpl. reflexivity.
- intro l2. simpl. destruct a ; try apply IHl1.
  simpl. rewrite IHl1. reflexivity.
Qed.

Lemma box_in_top_boxes : forall l1 l2 A, existsT2 l3 l4, top_boxes (l1 ++ Box A :: l2) = l3 ++ Box A :: l4.
Proof.
intros. exists (top_boxes l1). exists (top_boxes l2). rewrite top_boxes_distr_app. auto.
Qed.

Lemma is_Boxed_list_top_boxes : forall l, is_Boxed_list (top_boxes l).
Proof.
intros. induction l.
- simpl. intro. intros. inversion H.
- intro. destruct a.
  + simpl. intros. apply IHl in H. assumption.
  + simpl. intros. apply IHl in H. assumption.
  + simpl. intros. apply IHl in H. assumption.
  + simpl. intros. destruct H.
    * exists a. auto.
    * apply IHl. assumption.
Qed.

Lemma nobox_gen_ext_top_boxes : forall l, nobox_gen_ext (top_boxes l) l.
Proof.
induction l.
- simpl. apply univ_gen_ext_refl.
- destruct a.
  * simpl. apply univ_gen_ext_extra. intros. inversion X. inversion H. assumption.
  * simpl. apply univ_gen_ext_extra. intros. inversion X. inversion H. assumption.
  * simpl. apply univ_gen_ext_extra. intros. inversion X. inversion H. assumption.
  * simpl. apply univ_gen_ext_cons. assumption.
Qed.


