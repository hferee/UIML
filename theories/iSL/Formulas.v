(** * Overview: formulas

This file defines propositional formulas, the proof that there are countably many, and the definition of the well-founded ordering on the set of formulas, via weight. *)


(** Theory of countability from Iris *)
From stdpp Require Import countable strings.


Local Open Scope string_scope.

(** * Definitions and notations. *)
Definition variable := string.

Inductive form : Type :=
| Var : variable -> form
| Bot : form
| And : form -> form -> form
| Or : form -> form -> form
| Implies : form -> form -> form
| Box : form -> form.

Fixpoint occurs_in (x : variable) (φ : form) := 
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
Global Instance fomula_bottom : base.Bottom form := Bot.

Global Coercion Var : variable >-> form.

Global Instance form_top : base.Top form := ⊤.

(** Formulas have decidable equality. *)
Global Instance string_dec : EqDecision string := string_dec.
Global Instance form_eq_dec : EqDecision form.
Proof. solve_decision . Defined.

Section CountablyManyFormulas.
(** * Countability of the set of formulas *)
(** We prove that there are countably many formulas by exhibiting an injection
  into general trees over nat for countability. *)
Local Fixpoint form_to_gen_tree (φ : form) : gen_tree (option string) :=
match φ with
| ⊥ => GenLeaf  None
| Var v => GenLeaf (Some v)
| φ ∧ ψ => GenNode 0 [form_to_gen_tree φ ; form_to_gen_tree ψ]
| φ ∨ ψ => GenNode 1 [form_to_gen_tree φ ; form_to_gen_tree ψ]
| φ →  ψ => GenNode 2 [form_to_gen_tree φ ; form_to_gen_tree ψ]
| □ φ => GenNode 3 [form_to_gen_tree φ]
end.

Local Fixpoint gen_tree_to_form (t : gen_tree (option string)) : option form :=
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
 | GenNode 3 [t] => gen_tree_to_form t ≫= fun φ => Some (□φ)
| _=> None
end.

Global Instance form_count : Countable form.
Proof.
  eapply inj_countable with (f := form_to_gen_tree) (g := gen_tree_to_form).
  intro φ; induction φ; simpl; trivial; now rewrite IHφ1, IHφ2 || rewrite  IHφ.
Defined.

End CountablyManyFormulas.

Inductive subform : form -> form -> Prop :=
| SubEq : ∀ φ, subform φ φ
| SubAnd : ∀ φ ψ1 ψ2, (subform φ ψ1 + subform φ ψ2) -> subform φ (ψ1 ∧ ψ2)
| SubOr : ∀ φ ψ1 ψ2, (subform φ ψ1 + subform φ ψ2) -> subform φ (ψ1 ∨ ψ2)
| SubImpl : ∀ φ ψ1 ψ2, (subform φ ψ1 + subform φ ψ2) -> subform φ (ψ1→  ψ2)
| SubBox : ∀ φ ψ, subform φ ψ -> subform φ (□ ψ).
Local Hint Constructors subform : dyckhoff.

(** * Weight

We define the weight function on formulas, following (Dyckhoff Negri 2000) *)
Fixpoint weight (φ : form) : nat := match φ with
| ⊥ => 1
| Var _ => 1
| φ ∧ ψ => 2 + weight φ + weight ψ
| φ ∨ ψ => 3 + weight φ + weight ψ
| φ → ψ => 1 + weight φ + weight ψ
| □φ => 1 + weight φ
end.

Lemma weight_pos φ : weight φ > 0.
Proof. induction φ; simpl; lia. Qed.

(** We obtain an induction principle based on weight. *)
Definition weight_ind (P : form -> Type) :
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

Definition form_order φ ψ := weight φ > weight ψ.

Global Instance transitive_form_order : Transitive form_order.
Proof. unfold form_order. auto with *. Qed.

Global Instance irreflexive_form_order : Irreflexive form_order.
Proof. unfold form_order. intros x y. lia. Qed.

Notation "φ ≺f ψ" := (form_order ψ φ) (at level 149).


Fixpoint form_size (φ : form) : nat := match φ with
| ⊥ => 1
| Var _ => 1
| φ ∧ ψ => 1 + form_size φ + form_size ψ
| φ ∨ ψ => 1 + form_size φ + form_size ψ
| φ → ψ => 1 + form_size φ + form_size ψ
| □φ => 1 + form_size φ
end.
