(** * Formulas

This file defines propositional formulas, the proof that there are countably many, and the definition of the well-founded ordering on the set of formulas, via weight. *)


(** Theory of countability from Iris *)
From stdpp Require Import countable strings.
Require Import Coq.Program.Equality.

(** ** Definitions and notations. *)
Definition variable := string.

(* We declare simultaneously two kinds of formulas: normal and modal *)
Inductive Kind := Modal | Normal.


Existing Class Kind.

Inductive form : Kind -> Type :=
| Var {K} : variable -> form K
| Bot {K} : form K
| And {K} : form K -> form K -> form K
| Or {K} : form K -> form K -> form K
| Implies {K} : form K -> form K -> form K
| Box : form Modal -> form Modal.

Arguments form {_}.
Arguments Var {_} _, _ _.

Fixpoint occurs_in `{K : Kind} (x : variable) (φ : form) :=
match φ with
| Var y => x = y
| Bot => False
| And φ ψ => (occurs_in x φ) \/ (occurs_in x ψ)
| Or φ ψ => (occurs_in x φ) \/ (occurs_in x ψ)
| Implies φ ψ => (occurs_in x φ) \/ (occurs_in x ψ)
| Box φ => occurs_in x φ
end.

(** Pretty notations for formulas *)
Notation "¬ φ" := (Implies φ Bot) (at level 75, φ at level 75).
Notation " ⊥ " := Bot.
Notation " ⊤ " := (Implies Bot Bot).
Notation " A ∧ B" := (And A B) (at level 80, B at level 80).
Notation " A ∨ B" := (Or A B) (at level 85, B at level 85).
Notation " A → B" := (Implies A B) (at level 99, B at level 200).
Notation "□ φ" := (Box φ) (at level 75, φ at level 75).
Infix " φ ⇔ ψ " := (And (Implies φ ψ) (Implies ψ φ)) (at level 100).

Global Instance fomula_bottom {K : Kind} : base.Bottom form := Bot.

Global Coercion Var: variable >-> form.

Global Instance form_top {K : Kind} : base.Top form := ⊤.

Ltac solve_trivial_decision :=
  match goal with
  | |- Decision (?P) => apply _
  | |- sumbool ?P (¬?P) => change (Decision P); apply _
  end.
Ltac solve_decision :=
  unfold EqDecision; intros; first
    [ solve_trivial_decision
    | unfold Decision; decide equality; solve_trivial_decision ].

Global Instance variable_eq_dec : EqDecision variable.
solve_decision. Defined.
(** Formulas have decidable equality. *)
Global Instance form_eq_dec {K : Kind} : EqDecision form.
Proof.
(* solve decision does not support the modality parameter). *)
Local Ltac ctac Hn := right; let Heq := fresh "Heq" in intro Heq;
                contradict Hn; dependent destruction Heq; now subst.
Local Ltac dec := now subst; left.
intros φ. induction φ; intro ψ; dependent destruction ψ;
try solve[right; discriminate].
- case (decide (v = v0)) as [Heq|Hn]; [dec|ctac Hn].
- dec.
- destruct (IHφ1 ψ1) as [Heq|Hn]; [|ctac Hn].
  destruct (IHφ2 ψ2) as [Heq'|Hn]; [dec|ctac Hn].
- destruct (IHφ1 ψ1) as [Heq|Hn]; [|ctac Hn].
  destruct (IHφ2 ψ2) as [Heq'|Hn]; [dec|ctac Hn].
- destruct (IHφ1 ψ1) as [Heq|Hn]; [|ctac Hn].
  destruct (IHφ2 ψ2) as [Heq'|Hn]; [dec|ctac Hn].
- destruct (IHφ ψ) as [Heq|Hn]; [dec |ctac Hn].
Defined. (* solve decision *)

Section CountablyManyFormulas.

Context {K : Kind}.

(** ** Countability of the set of formulas *)
(** We prove that there are countably many formulas by exhibiting an injection
  into general trees over nat for countability. *)
Local Fixpoint form_to_gen_tree {K : Kind} (φ : form) : gen_tree (option string) :=
match φ with
| ⊥ => GenLeaf  None
| Var v => GenLeaf (Some v)
| φ ∧ ψ => GenNode 0 [form_to_gen_tree φ ; form_to_gen_tree ψ]
| φ ∨ ψ => GenNode 1 [form_to_gen_tree φ ; form_to_gen_tree ψ]
| φ →  ψ => GenNode 2 [form_to_gen_tree φ ; form_to_gen_tree ψ]
| □ φ => GenNode 3 [form_to_gen_tree φ]
end.

Local Fixpoint gen_tree_to_form {K : Kind} (t : gen_tree (option string)) : option form :=
match t with
| GenLeaf None => Some ⊥
| GenLeaf (Some v) => Some (Var v)
| GenNode 0 [t1 ; t2] =>
    gen_tree_to_form t1 ≫= fun φ => gen_tree_to_form t2 ≫= fun ψ =>
      Some (φ ∧ ψ)
| GenNode 1 [t1 ; t2] =>
    gen_tree_to_form t1 ≫= fun φ => gen_tree_to_form t2 ≫= fun ψ =>
      Some (φ ∨ ψ)
| GenNode 2 [t1 ; t2] =>
    gen_tree_to_form t1 ≫= fun φ => gen_tree_to_form t2 ≫= fun ψ =>
      Some (φ →  ψ)
| GenNode 3 [t] =>
    match K with
    | Modal => gen_tree_to_form t ≫= fun φ => Some (□φ)
    | Normal => None
    end
| _=> None
end.

Global Instance form_count : Countable form.
Proof.
  eapply inj_countable with (f := form_to_gen_tree) (g := gen_tree_to_form).
  intro φ; induction φ; simpl; trivial; now rewrite IHφ1, IHφ2 || rewrite  IHφ.
Defined.

End CountablyManyFormulas.

Inductive subform : forall (K : Kind), form -> form -> Prop :=
| SubEq : ∀ K φ, subform K φ φ
| SubAnd : ∀ K φ ψ1 ψ2, (subform K φ ψ1 + subform K φ ψ2) -> subform K φ (ψ1 ∧ ψ2)
| SubOr : ∀ K φ ψ1 ψ2, (subform K φ ψ1 + subform K φ ψ2) -> subform K φ (ψ1 ∨ ψ2)
| SubImpl : ∀ K φ ψ1 ψ2, (subform K φ ψ1 + subform K φ ψ2) -> subform K φ (ψ1→  ψ2)
| SubBox : ∀ φ ψ, @subform Modal φ ψ -> @subform Modal φ (□ ψ).
Local Hint Constructors subform : dyckhoff.

(** ** Weight

We define the weight function on formulas, following (Dyckhoff Negri 2000) *)
Fixpoint weight {K : Kind} (φ : form) : nat := match φ with
| ⊥ => 1
| Var _ => 1
| φ ∧ ψ => 2 + weight φ + weight ψ
| φ ∨ ψ => 1 + weight φ + weight ψ
| φ → ψ => 1 + weight φ + weight ψ
| □φ => 1 + weight φ
end.

Lemma weight_pos {K : Kind} φ : weight φ > 0.
Proof. induction φ; simpl; lia. Qed.

(** We obtain an induction principle based on weight. *)
Definition weight_ind {K : Kind} (P : form -> Type) :
 (forall ψ, (∀ φ, (weight φ < weight ψ) -> P φ) -> P ψ) ->
 (∀ φ, P φ).
Proof.
  intros Hc φ. remember (weight φ) as w.
  assert(Hw : weight φ ≤ w) by now subst. clear Heqw.
  revert φ Hw. induction w; intros φ Hw.
  - pose (Hw' := weight_pos φ). auto with *.
  - destruct φ; simpl in Hw; trivial;
    apply Hc; intros φ' Hw'; apply IHw; simpl in Hw'; lia.
Defined.

Definition form_order {K : Kind} φ ψ := weight φ > weight ψ.

Global Instance transitive_form_order {K : Kind} : Transitive form_order.
Proof. unfold form_order. auto with *. Qed.

Global Instance irreflexive_form_order {K : Kind} : Irreflexive form_order.
Proof. unfold form_order. intros x y. lia. Qed.

Notation "φ ≺f ψ" := (form_order ψ φ) (at level 149).
