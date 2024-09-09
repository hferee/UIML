Require Import ISL.Sequents.
Require Import ISL.SequentProps ISL.Order ISL.Optimizations.
Require Import Coq.Program.Equality. (* for dependent induction *)

(** * Overview: Propositional Quantifiers

The main theorem proved in this file was first proved as Theorem 1 in:

(Pitts 1992). A. M. Pitts. On an interpretation of second order quantification in first order intuitionistic propositional logic. J. Symb. Log., 57(1):33–52.
It has been further extended to handle iSL

It consists of two parts: 

1) the inductive construction of the propositional quantifiers; 

2) a proof of its correctness. *)

Section UniformInterpolation.

(** Throughout the construction and proof, we fix a variable p, with respect to
  which the propositional quantifier will be computed. *)
Variable p : variable.


(** * Definition of propositional quantifiers. *)

Section PropQuantDefinition.

(** We define the formulas Eφ and Aφ associated to any formula φ. This
  is an implementation of Pitts' Table 5, together with a (mostly automatic)
  proof that the definition terminates*)

Local Notation "Δ '•' φ" := (cons φ Δ).

(* solves the obligations of the following programs *)
Obligation Tactic := intros; order_tac.

Notation "□⁻¹ Γ" := (map open_box Γ) (at level 75).

(** First, the implementation of the rules for calculating E. The names of the rules
  refer to the table in Pitts' paper. *)
(** note the use of  "lazy" conjunctions, disjunctions and implications *)
Program Definition e_rule {Δ : list form } {ϕ : form}
  (E : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
  (A : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
  (θ: form) (Hin : θ ∈ Δ) : form :=
let E Δ H := E (Δ, ϕ) H in
let Δ'  := rm θ Δ in
match θ with
| Bot => ⊥  (* E0 *)
| Var q =>
    if decide (p = q) then ⊤ (* default *)
    else q (* E1 modified *)
(* E2 *)
| δ₁ ∧ δ₂ => E ((Δ'•δ₁)•δ₂) _
(* E3 *)
| δ₁ ∨ δ₂ => E (Δ'•δ₁) _ ⊻ E (Δ' •δ₂) _
| Var q → δ =>
    if decide (Var q ∈ Δ) then E (Δ'•δ) _ (* E5 modified *)
    else if decide (p = q) then ⊤
    else q ⇢ E (Δ'•δ) _ (* E4 *)
(* E6 *)
| (δ₁ ∧ δ₂)→ δ₃ => E (Δ'•(δ₁ → (δ₂ → δ₃))) _
(* E7 *)
| (δ₁ ∨ δ₂)→ δ₃ => E (Δ'•(δ₁ → δ₃)•(δ₂ → δ₃)) _
(* E8 modified *)
| ((δ₁→ δ₂)→ δ₃) =>
  (E (Δ'•(δ₂ → δ₃) • δ₁) _⇢ A (Δ'•(δ₂ → δ₃) • δ₁, δ₂) _) ⇢ E (Δ'•δ₃) _
| Bot → _ => ⊤
| □ φ => □(E ((□⁻¹ Δ') • φ ) _) (* very redundant ; identical for each box *)
| (□δ1 → δ2) =>  (□(E((□⁻¹ Δ') • δ2 • □δ1) _ ⇢ A((□⁻¹ Δ') • δ2 • □δ1, δ1) _)) ⇢ E(Δ' • δ2) _
end.


(** The implementation of the rules for defining A is separated into two pieces.
    Referring to Table 5 in Pitts, the definition a_rule_env handles A1-8 and A10,
    and the definition a_rule_form handles A9 and A11-13. *)
Program Definition a_rule_env {Δ : list form} {ϕ : form}
  (E : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
  (A : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
  (θ: form) (Hin : θ ∈ Δ) : form :=
let E Δ H := E (Δ, ϕ) H in
let Δ'  := rm θ Δ in
match θ with
| Var q =>
    if decide (p = q)
    then
      if decide (Var p = ϕ) then ⊤ (* A10 *)
      else ⊥
    else ⊥ (* A1 modified : A (Δ', ϕ) can be removed *)
(* A2 *)
| δ₁ ∧ δ₂ => A ((Δ'•δ₁)•δ₂, ϕ) _
(* A3 *)
| δ₁ ∨ δ₂ =>
      (E (Δ'•δ₁) _ ⇢ A (Δ'•δ₁, ϕ) _)
  ⊼ (E (Δ'•δ₂) _ ⇢ A (Δ'•δ₂, ϕ) _)
| Var q → δ =>
    if decide (Var q ∈ Δ) then A (Δ'•δ, ϕ) _ (* A5 modified *)
    else if decide (p = q) then ⊥
    else q ⊼ A (Δ'•δ, ϕ) _ (* A4 *)
(* A6 *)
| (δ₁ ∧ δ₂)→ δ₃ =>
  A (Δ'•(δ₁ → (δ₂ → δ₃)), ϕ) _
(* A7 *)
| (δ₁ ∨ δ₂)→ δ₃ =>
  A ((Δ'•(δ₁ → δ₃))•(δ₂ → δ₃), ϕ) _
(* A8 modified*)
| ((δ₁→ δ₂)→ δ₃) =>
  (E (Δ'•(δ₂ → δ₃) • δ₁) _ ⇢ A (Δ'•(δ₂ → δ₃) • δ₁, δ₂) _)
  ⊼ A (Δ'•δ₃, ϕ) _
| Bot => ⊥
| Bot → _ => ⊥
| □δ => ⊥
| ((□δ1) → δ2) => (□(E((□⁻¹ Δ')• δ2 • □δ1) _  ⇢ A((□⁻¹ Δ')• δ2 • □δ1, δ1) _)) ∧ A(Δ' • δ2, ϕ) _
(* using ⊼ here breaks congruence *)
end.

Obligation Tactic := intros Δ ϕ _ _; intros; order_tac.
Program Definition a_rule_form {Δ : list form} {ϕ : form}
  (E : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
  (A : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form) :=
match ϕ with
| Var q =>
    if decide (p = q) (* TODO : change this to p∈Vars(ϕ) *)
    then ⊥
    else Var q (* A9 *)
(* A11 *)
| ϕ₁ ∧ ϕ₂ => A (Δ, ϕ₁) _ ⊼ A (Δ, ϕ₂) _
(* A12 *)
| ϕ₁ ∨ ϕ₂ => A (Δ, ϕ₁) _ ⊻ A (Δ, ϕ₂) _
(* A13 *)
| ϕ₁→ ϕ₂ => E (Δ•ϕ₁, ϕ₂) _ ⇢ A (Δ•ϕ₁, ϕ₂) _
    (* TODO would a general right-implication rule be useful efficient? *)
| Bot => ⊥
| □δ => □((E ((□⁻¹ Δ) • □δ, δ) _) ⇢ A((□⁻¹ Δ) • □δ, δ) _)
end.

Obligation Tactic := intros; order_tac.
Program Fixpoint EA (b : bool) (pe : list form * form) {wf pointed_env_order pe} : form :=
  let Δ := pe.1 in
  let E := EA true in
  let A := EA false in
  if b then⋀ (in_map Δ (e_rule E A))
  else ⋁ (in_map Δ (a_rule_env E A)) ⊻ a_rule_form E A.
Next Obligation. apply Wf.measure_wf, wf_pointed_order. Defined.

Definition E := EA true.
Definition A := EA false.

Definition Ef (ψ : form) := E ([ψ], ⊥).
Definition Af (ψ : form) := A ([], ψ).


(** Congruence lemmas: if we apply any of e_rule, a_rule_env, or a_rule_form
  to two equal environments, then they give the same results. *)
Lemma e_rule_cong Δ ϕ θ (Hin: θ ∈ Δ) E1 A1 E2 A2:
  (forall pe Hpe, E1 pe Hpe = E2 pe Hpe) ->
  (forall pe Hpe, A1 pe Hpe = A2 pe Hpe) ->
  @e_rule Δ ϕ E1 A1 θ Hin = @e_rule Δ ϕ E2 A2 θ Hin.
Proof.
  intros HeqE HeqA.
  destruct θ; simpl; try (destruct θ1); repeat (destruct decide);
  f_equal; repeat erewrite ?HeqE, ?HeqA; trivial.
Qed.

Lemma e_rule_cong_strong Δ ϕ θ (Hin1 Hin2: θ ∈ Δ) E1 A1 E2 A2:
  (forall pe Hpe1 Hpe2, E1 pe Hpe1 = E2 pe Hpe2) ->
  (forall pe Hpe1 Hpe2, A1 pe Hpe1 = A2 pe Hpe2) ->
  @e_rule Δ ϕ E1 A1 θ Hin1 = @e_rule Δ ϕ E2 A2 θ Hin2.
Proof.
  intros HeqE HeqA.
  destruct θ; simpl; try (destruct θ1); repeat (destruct decide);
  f_equal; repeat erewrite ?HeqE, ?HeqA; trivial.
Qed.

Lemma a_rule_env_cong Δ ϕ θ Hin  E1 A1 E2 A2:
  (forall pe Hpe, E1 pe Hpe = E2 pe Hpe) ->
  (forall pe Hpe, A1 pe Hpe = A2 pe Hpe) ->
  @a_rule_env Δ ϕ E1 A1 θ Hin = @a_rule_env Δ ϕ E2 A2 θ Hin.
Proof.
  intros HeqE HeqA.
  destruct θ; simpl; trivial; repeat (destruct decide);
  f_equal; repeat erewrite ?HeqE, ?HeqA; trivial;
  destruct θ1; try (destruct decide); trivial; simpl;
  repeat erewrite ?HeqE, ?HeqA; trivial; (destruct decide); trivial.
Qed.

Lemma a_rule_env_cong_strong Δ ϕ θ Hin1 Hin2  E1 A1 E2 A2:
  (forall pe Hpe1 Hpe2, E1 pe Hpe1 = E2 pe Hpe2) ->
  (forall pe Hpe1 Hpe2, A1 pe Hpe1 = A2 pe Hpe2) ->
  @a_rule_env Δ ϕ E1 A1 θ Hin1 = @a_rule_env Δ ϕ E2 A2 θ Hin2.
Proof.
  intros HeqE HeqA.
  destruct θ; simpl; trivial; repeat (destruct decide);
  f_equal; repeat erewrite ?HeqE, ?HeqA; trivial;
  destruct θ1; try (destruct decide); trivial; simpl;
  repeat erewrite ?HeqE, ?HeqA; trivial; (destruct decide); trivial.
Qed.


Lemma a_rule_form_cong Δ ϕ  E1 A1 E2 A2:
  (forall pe Hpe, E1 pe Hpe = E2 pe Hpe) ->
  (forall pe Hpe, A1 pe Hpe = A2 pe Hpe) ->
  @a_rule_form Δ ϕ E1 A1 = @a_rule_form Δ ϕ E2 A2.
Proof.
  intros HeqE HeqA.
  destruct ϕ; simpl; repeat (destruct decide); trivial;
  repeat (erewrite ?HeqE, ?HeqA; eauto); trivial.
Qed.


Lemma a_rule_form_cong_strong Δ ϕ  E1 A1 E2 A2:
  (forall pe Hpe1 Hpe2, E1 pe Hpe1 = E2 pe Hpe2) ->
  (forall pe Hpe1 Hpe2, A1 pe Hpe1 = A2 pe Hpe2) ->
  @a_rule_form Δ ϕ E1 A1 = @a_rule_form Δ ϕ E2 A2.
Proof.
  intros HeqE HeqA.
  destruct ϕ; simpl; repeat (destruct decide); trivial;
  repeat (erewrite ?HeqE, ?HeqA; eauto); trivial.
Qed.

Lemma EA_eq Δ ϕ:
  (E (Δ, ϕ) =  ⋀ (in_map Δ (@e_rule Δ ϕ (λ pe _, E pe) (λ pe _, A pe)))) /\
  (A (Δ, ϕ) = (⋁ (in_map Δ (@a_rule_env Δ ϕ (λ pe _, E pe) (λ pe _, A pe)))) ⊻
       @a_rule_form Δ ϕ (λ pe _, E pe) (λ pe _, A pe)).
Proof.
simpl. unfold E, A, EA. simpl.
unfold EA_func at 1.
rewrite -> Wf.Fix_eq; simpl.
-  split; trivial.
   unfold EA_func at 1. rewrite -> Wf.Fix_eq; simpl; trivial.
    intros [[|] Δ'] f g Heq; simpl; f_equal.
  + apply in_map_ext. intros. trivial. apply e_rule_cong; intros; now rewrite Heq.
  + f_equal. apply in_map_ext. intros. apply a_rule_env_cong; intros;
      now rewrite Heq.
  + apply a_rule_form_cong; intros; now rewrite Heq.
- intros [[|] Δ'] f g Heq; simpl; f_equal.
  + apply in_map_ext. intros. trivial. apply e_rule_cong; intros; now rewrite Heq.
  + f_equal. apply in_map_ext. intros. apply a_rule_env_cong; intros;
      now rewrite Heq.
  + apply a_rule_form_cong; intros; now rewrite Heq.
Qed.

Definition E_eq Δ ϕ := proj1 (EA_eq Δ ϕ).
Definition A_eq Δ ϕ := proj2 (EA_eq Δ ϕ).

End PropQuantDefinition.

(** * Correctness *)
Section Correctness.


(** This section contains the proof of Proposition 5, the main correctness result, stating that the E- and A-formulas defined above are indeed existential and universal propositional quantified versions of the original formula, respectively. *)

(** ** (i) Variables *)
Section VariablesCorrect.

(** In this subsection we prove (i), which states that the variable p no longer
  occurs in the E- and A-formulas, and that the E- and A-formulas contain no more variables than the original formula.
  *)

(* A general tactic for variable occurrences *)
Ltac vars_tac :=
intros; subst;
repeat match goal with
| HE : context [occurs_in ?x (?E _ _)], H : occurs_in ?x (?E _ _) |- _ =>
    apply HE in H
end;
intuition;
repeat match goal with | H : exists x, _ |- _ => destruct H end;
intuition;
simpl in *; in_tac; try (split; [tauto || auto with *|]); simpl in *;
try match goal with
| H : occurs_in _ (?a ⇢ (?b ⇢ ?c)) |- _ => apply occurs_in_make_impl2 in H
| H : occurs_in _ (?a ⇢ ?b) |- _ => apply occurs_in_make_impl in H
| H : occurs_in _ (?a ⊻ ?b) |- _ => apply occurs_in_make_disj in H
| H : occurs_in _ (?a ⊼ ?b) |- _ => apply occurs_in_make_conj in H
|H1 : ?x0 ∈ (⊗ ?Δ), H2 : occurs_in ?x ?x0 |- _ =>
      apply (occurs_in_open_boxes _ _ _ H2) in H1
|H1 : ?x0 ∈ (map open_box ?Δ), H2 : occurs_in ?x ?x0 |- _ =>
      apply (occurs_in_map_open_box _ _ _ H2) in H1
end; repeat rewrite elem_of_cons in * ; intuition; subst;
repeat match goal with | H : exists x, _ |- _ => destruct H end; intuition;
try multimatch goal with
| H : ?θ0 ∈ ?Δ0 |- context [exists θ, θ ∈ ?Δ /\ occurs_in ?x θ] =>
  solve[try right; exists θ0; split; [eauto using remove_include|simpl; tauto]; eauto] end.


(** *** (a)  *)

Lemma e_rule_vars Δ (θ : form) (Hin : θ ∈ Δ) (ϕ : form)
  (E0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
  (A0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
   x
  (HEA0 : ∀ pe Hpe, 
      (occurs_in x (E0 pe Hpe) -> x ≠ p ∧ ∃ θ, θ ∈ pe.1 /\ occurs_in x θ) /\
      (occurs_in x (A0 pe Hpe) -> x ≠ p ∧ (occurs_in x pe.2 \/ ∃ θ, θ ∈ pe.1 /\ occurs_in x θ))) :
occurs_in x (e_rule E0 A0 θ Hin) -> x ≠ p ∧ ∃ θ, θ ∈ Δ /\ occurs_in x θ.
Proof. 
destruct θ; unfold e_rule; simpl; try tauto; try solve [repeat case decide; repeat vars_tac].
destruct θ1; repeat case decide; repeat vars_tac.
Qed.


(** *** (b) *)

Lemma a_rule_env_vars Δ θ Hin ϕ
  (E0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
  (A0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
   x
  (HEA0 : ∀ pe Hpe, 
      (occurs_in x (E0 pe Hpe) -> x ≠ p ∧ ∃ θ, θ ∈ pe.1 /\ occurs_in x θ) /\
      (occurs_in x (A0 pe Hpe) -> x ≠ p ∧ (occurs_in x pe.2 \/ ∃ θ, θ ∈ pe.1 /\ occurs_in x θ))):
occurs_in x (a_rule_env E0 A0 θ Hin) -> x ≠ p ∧ (occurs_in x ϕ \/ ∃ θ, θ ∈ Δ /\ occurs_in x θ).
Proof. 
destruct θ; unfold a_rule_env; simpl; try tauto; try solve [repeat case decide; repeat vars_tac].
destruct θ1; repeat case decide; repeat vars_tac.
Qed.


Lemma a_rule_form_vars Δ ϕ
  (E0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
  (A0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
   x
  (HEA0 : ∀ pe Hpe, 
      (occurs_in x (E0 pe Hpe) -> x ≠ p ∧ ∃ θ, θ ∈ pe.1 /\ occurs_in x θ) /\
      (occurs_in x (A0 pe Hpe) -> x ≠ p ∧ (occurs_in x pe.2 \/ ∃ θ, θ ∈ pe.1 /\ occurs_in x θ))):
  occurs_in x (a_rule_form E0 A0) -> x ≠ p ∧ (occurs_in x ϕ \/ ∃ θ, θ ∈ Δ /\ occurs_in x θ).
Proof. 
destruct ϕ; unfold a_rule_form; simpl; try tauto; try solve [repeat case decide; repeat vars_tac].
Qed.

Proposition EA_vars Δ ϕ x:
  (occurs_in x (E (Δ, ϕ)) -> x <> p /\ ∃ θ, θ ∈ Δ /\ occurs_in x θ) /\
  (occurs_in x (A (Δ, ϕ)) -> x <> p /\ (occurs_in x ϕ \/ (∃ θ, θ ∈ Δ /\ occurs_in x θ))).
Proof. 
remember (Δ, ϕ) as pe.
replace Δ with pe.1 by now subst.
replace ϕ with pe.2 by now subst. clear Heqpe Δ ϕ. revert pe.
refine  (@well_founded_induction _ _ wf_pointed_order _ _).
intros [Δ ϕ] Hind. simpl.
rewrite E_eq, A_eq. simpl.
split.
(* E *)
- intros Hocc. apply variables_conjunction in Hocc as (φ&Hin&Hφ).
  apply in_in_map in Hin as (ψ&Hin&Heq). subst φ.
  apply e_rule_vars in Hφ.
  + trivial.
  + intros; now apply Hind.
(* A *)
- intro Hocc. apply occurs_in_make_disj in Hocc as [Hocc|Hocc].
  (* disjunction *)
  + apply variables_disjunction in Hocc as (φ&Hin&Hφ).
      apply in_in_map in Hin as (ψ&Hin&Heq). subst φ.
      apply a_rule_env_vars in Hφ; trivial.
  (* pointer rule *)
  + apply a_rule_form_vars in Hocc.
    * destruct Hocc as [Hneq [Hocc | Hocc]]; vars_tac.
    * vars_tac; apply Hind in H; trivial; tauto.
Qed.

End VariablesCorrect.

Ltac foldEA := repeat match goal with
| |- context C [(EA ?pe).1] => fold (E pe)
| |- context C [(EA ?pe).2] => fold (A pe)
end.

(** ** (ii) Entailment *)
Section EntailmentCorrect.

(** In this section we prove (ii), which states that the E- and A-formula are
  entailed by the original formula and entail the original formula,
  respectively. *)

Hint Extern 5 (?a ≺ ?b) => order_tac : proof.
Opaque make_disj.
Opaque make_conj.

Local Ltac l_tac := repeat rewrite list_to_set_disj_open_boxes;
    rewrite (proper_Provable _ _ (list_to_set_disj_env_add _ _) _ _ eq_refl)
|| rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (list_to_set_disj_env_add _ _)) _ _ eq_refl)
|| rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (equiv_disj_union_compat_r (list_to_set_disj_env_add _ _))) _ _ eq_refl)
|| rewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r (equiv_disj_union_compat_r (list_to_set_disj_env_add _ _)))) _ _ eq_refl).

Lemma a_rule_env_spec (Δ : list form) θ ϕ Hin
  (E0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
  (A0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
  (HEA : forall Δ ϕ Hpe, (list_to_set_disj Δ ⊢ E0 (Δ, ϕ) Hpe) * (list_to_set_disj  Δ• A0 (Δ, ϕ) Hpe ⊢ ϕ)) :
  (list_to_set_disj  Δ • a_rule_env E0 A0 θ Hin ⊢ ϕ).
Proof with (auto with proof).
assert (HE := λ Δ0 ϕ0 Hpe, fst (HEA Δ0 ϕ0 Hpe)).
assert (HA := λ Δ0 ϕ0 Hpe, snd (HEA Δ0 ϕ0 Hpe)).
clear HEA.
assert(Hi : θ ∈ list_to_set_disj  Δ) by now apply elem_of_list_to_set_disj.
destruct θ; exhibit Hi 1;
rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (equiv_disj_union_compat_r (list_to_set_disj_rm _ _))) _ _ eq_refl).
- simpl; case decide; intro Hp.
  + subst. case_decide; subst; auto with proof.
  + exch 0...
- constructor 2.
- simpl; exch 0. apply AndL. exch 1; exch 0. do 2 l_tac...
- apply make_conj_sound_L.
  exch 0. apply OrL; exch 0.
  + apply AndL. apply make_impl_sound_L. exch 0. apply make_impl_sound_L.
      l_tac. apply ImpL...
  + apply AndL. l_tac. apply make_impl_sound_L. exch 0. apply make_impl_sound_L...
- destruct θ1.
  + simpl; case decide; intro Hp.
    * assert (Hin'' : Var v ∈ (list_to_set_disj (rm (v → θ2) Δ) : env))
       by (rewrite <- list_to_set_disj_rm; apply in_difference; try easy; now apply elem_of_list_to_set_disj).
       exhibit Hin'' 2. exch 0; exch 1. apply ImpLVar. exch 0. backward.
       rewrite env_add_remove. exch 0. l_tac...
    * case decide; intro; subst.
     -- apply ExFalso.
     -- apply make_conj_sound_L. constructor 4. exch 0. exch 1. exch 0. apply ImpLVar.
         exch 0. exch 1. l_tac. apply weakening...
  + constructor 2.
  + simpl; exch 0. apply ImpLAnd. exch 0. l_tac...
  + simpl; exch 0. apply ImpLOr. exch 1. l_tac. exch 0. l_tac...
  + apply make_conj_sound_L. exch 0. apply ImpLImp; exch 0.
      * apply AndL. exch 0. apply make_impl_sound_L. l_tac.
         apply ImpR. exch 0.  exch 1. l_tac...
      * apply AndL. exch 0. l_tac. apply weakening, HA.
  + exch 0. exch 0. simpl. apply  AndL. exch 1; exch 0. apply ImpBox.
      * box_tac. box_tac. exch 0; exch 1; exch 0. apply weakening. exch 1; exch 0.
         apply make_impl_sound_L. do 2 l_tac. apply ImpL.
         -- auto with proof.
         -- apply HA.
      * exch 1; exch 0. apply weakening. exch 0. l_tac. auto with proof.
- auto with proof.
Qed.

Proposition entail_correct Δ ϕ : (list_to_set_disj Δ ⊢ E (Δ, ϕ)) * (list_to_set_disj Δ•A (Δ, ϕ) ⊢ ϕ).
Proof with (auto with proof).
remember (Δ, ϕ) as pe.
replace Δ with pe.1 by now subst.
replace ϕ with pe.2 by now subst. clear Heqpe Δ ϕ. revert pe.
refine  (@well_founded_induction _ _ wf_pointed_order _ _).
unfold pointed_env_order.
intros (Δ, ϕ) Hind. simpl.
rewrite E_eq, A_eq.
(* uncurry the induction hypothesis for convenience *)
assert (HE := fun d f x=> fst (Hind (d, f) x)).
assert (HA := fun d f x=> snd (Hind (d, f) x)).
unfold E, A in *; simpl in HE, HA.
simpl in *. clear Hind.
split. {
(* E *)
apply conjunction_R1. intros φ Hin. apply in_in_map in Hin.
destruct Hin as (ψ&Hin&Heq). subst.
assert(Hi : ψ ∈ list_to_set_disj  Δ) by now apply elem_of_list_to_set_disj.
destruct ψ; unfold e_rule; exhibit Hi 0; rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (list_to_set_disj_rm _ _)) _ _ eq_refl).
- case decide; intro; subst; simpl; auto using HE with proof.
- auto with proof.
- apply AndL. do 2 l_tac...
- apply make_disj_sound_R, OrL.
  + l_tac. apply OrR1, HE. order_tac.
  + l_tac. apply OrR2, HE. order_tac.
- destruct ψ1; auto 3 using HE with proof.
  + case decide; intro Hp.
    * assert(Hin'' : Var v ∈ (list_to_set_disj (rm (v → ψ2) Δ) : env))
          by (rewrite <- list_to_set_disj_rm; apply in_difference; try easy; now apply elem_of_list_to_set_disj).
          exhibit Hin'' 1. apply ImpLVar. exch 0. backward. rewrite env_add_remove.
          l_tac. apply HE...
    * case decide; intro; subst.
      -- apply ImpR, ExFalso.
      -- apply make_impl_sound_R, ImpR. exch 0. apply ImpLVar. exch 0.
          l_tac. apply weakening, HE. order_tac.
  + apply ImpLAnd. l_tac...
  + apply ImpLOr. do 2 l_tac...
  + apply make_impl_sound_R, ImpR, make_impl_sound_L. exch 0. apply ImpLImp.
      * exch 0. l_tac. apply ImpR. exch 0. l_tac. auto with proof.
      * exch 0. l_tac. auto with proof.
  + foldEA. apply make_impl_sound_R, ImpR. exch 0. apply ImpBox.
         --  box_tac. exch 0; exch 1; exch 0. apply make_impl_sound_L, ImpL.
            ++ do 2 l_tac. apply weakening, HE. order_tac.
            ++ do 2 l_tac. apply HA. order_tac.
         -- exch 0. l_tac. apply weakening, HE. order_tac.
-  apply BoxR. apply weakening. box_tac. l_tac. apply HE. order_tac.
}
(* A *)
apply make_disj_sound_L, OrL.
- apply disjunction_L. intros φ Hin.
  apply in_in_map in Hin as (φ' & Heq & Hφ'). subst φ.
  apply a_rule_env_spec; intros; split ; apply HE || apply HA; order_tac.
- destruct ϕ; simpl; auto using HE with proof.
  + case decide; intro; subst; [constructor 2|constructor 1].
  + apply make_conj_sound_L, AndR; apply AndL; auto using HE with proof.
  + apply ImpR. exch 0. l_tac. apply make_impl_sound_L, ImpL; auto using HE, HA with proof.
  + foldEA. apply BoxR. box_tac. exch 0. l_tac. apply make_impl_sound_L, ImpL.
      * apply weakening, HE. order_tac.
      * apply HA. order_tac.
Qed.

End EntailmentCorrect.

(** ** Uniformity *)
Section PropQuantCorrect.

Hint Extern 5 (?a ≺· ?b) => order_tac : proof.

(** The proof in this section, which is the most complex part of the argument,
  shows that the E- and A-formulas constructed above are indeed their propositionally quantified versions, that is, *any* formula entailed by the original formula and
  using only variables from that formula except p is already a consequence of
  the E-quantified version, and similarly on the other side for the A-quantifier.
*)

(** E's second argument is mostly irrelevant and is only there for uniform treatment with A *)
Lemma E_irr ϕ' Δ ϕ : E (Δ, ϕ) = E (Δ, ϕ').
Proof. 
remember ((Δ, ϕ) : pointed_env) as pe.
replace Δ with pe.1 by now subst.
replace ϕ with pe.2 by now subst. clear Heqpe Δ ϕ.
  induction pe as [[Γ φ] Hind0] using (well_founded_induction_type wf_pointed_order).
assert(Hind : ∀ Γ0 φ0, ((Γ0, φ0) ≺· (Γ, φ)) → E (Γ0, φ0) = E (Γ0, ϕ'))
  by exact (fun Γ0 φ0 => (Hind0 (Γ0, φ0))).
unfold E in Hind. simpl in Hind.
do 2 rewrite E_eq. f_equal. apply in_map_ext.
intros φ' Hin. unfold e_rule.
destruct φ'; repeat rewrite (Hind _ φ) by (trivial; order_tac); trivial.
destruct φ'1; repeat rewrite (Hind _ φ) by (trivial; order_tac); trivial.
Qed.

Lemma E_left {Γ} {θ} {Δ} {φ φ'} (Hin : φ ∈ Δ) :
(Γ • e_rule (λ pe (_ : pe ≺· (Δ, φ')),  E pe) (λ pe (_ : pe ≺· (Δ, φ')),  A pe)  φ Hin) ⊢ θ ->
Γ • E (Δ, φ') ⊢ θ.
Proof. 
intro Hp. rewrite E_eq.
destruct (@in_map_in _ _ _  (e_rule (λ pe (_ : pe ≺· (Δ, φ')), E pe) (λ pe (_ : pe ≺· (Δ, φ')), A pe) ) _ Hin) as [Hin' Hrule].
eapply conjunction_L.
- apply Hrule.
- exact Hp.
Qed.

Lemma A_right {Γ} {Δ} {φ φ'} (Hin : φ ∈ Δ) :
Γ ⊢ a_rule_env  (λ pe (_ : pe ≺· (Δ, φ')), E pe) (λ pe (_ : pe ≺· (Δ, φ')), A pe) φ Hin ->
Γ ⊢ A (Δ, φ').
Proof.  intro Hp. rewrite A_eq.
destruct (@in_map_in _ _ _  (a_rule_env  (λ pe (_ : pe ≺· (Δ, φ')), E pe) (λ pe (_ : pe ≺· (Δ, φ')), A pe)) _ Hin) as [Hin' Hrule].
eapply make_disj_sound_R, OrR1, disjunction_R.
- exact Hrule.
- exact Hp.
Qed.

Proposition pq_correct Γ Δ ϕ:
  (∀ φ0, φ0 ∈ Γ -> ¬ occurs_in p φ0) ->
  (Γ ⊎ list_to_set_disj Δ ⊢ ϕ) ->
  (¬ occurs_in p ϕ -> Γ•E (Δ, ϕ) ⊢ ϕ) * (Γ•E (Δ, ϕ) ⊢ A (Δ, ϕ)).
Proof.
(* This proof goes by induction on the ordering w.r.t (Γ ⊎Δ, ϕ)
  instead of on the structure of Γ ⊎Δ ⊢ ϕ, to allow better rules *)
(* we want to use an E rule *)
Local Ltac Etac := foldEA; intros; match goal with
| Hin : ?a ∈ list_to_set_disj ?Δ |- _•E (?Δ, _) ⊢ _=>
    apply (E_left (proj1 (elem_of_list_to_set_disj _ _) Hin)); unfold e_rule end.

(* we want to use an A rule defined in a_rule_env *)
Local Ltac Atac := foldEA; match goal with | Hin : ?a ∈ list_to_set_disj ?Δ |- _  ⊢ A (?Δ, _) => 
  apply (A_right (proj1 (elem_of_list_to_set_disj _ _) Hin)); unfold a_rule_env end.

(* we want to use an A rule defined in a_rule_form *)
Local Ltac Atac' := foldEA; rewrite A_eq; apply make_disj_sound_R, OrR2; simpl.

Local Ltac occ := simpl; tauto ||
match goal with
| Hnin : ∀ φ0 : form, φ0 ∈ ?Γ → ¬ occurs_in p φ0  |- _ =>

  let Hin := fresh "Hin" in
  try (match goal with |Hocc : ?a ∈ ?Γ |- _ =>   let Hocc' := fresh "Hocc" in assert (Hocc' := Hnin _ Hocc); simpl in Hocc';
  let Hin' := fresh "Hinx" in assert(Hin' := In_open_boxes _ _ Hocc); simpl in *;
  try rewrite open_boxes_remove in * by trivial  end);
  intro; repeat rewrite env_in_add; repeat rewrite difference_include; simpl;
  intro Hin; try tauto;
  try (destruct Hin as [Hin|[Hin|Hin]] ||destruct Hin as [Hin|Hin]);
  subst; simpl; try tauto;
  repeat (apply difference_include in Hin; [|assumption]);
  try (now apply Hnin)
end.

Local Ltac equiv_tac :=
multimatch goal with
| Heq' : _•_ ≡ _ |- _ => fail
| Heq' : _ ≡ _ |- _ ≡ _ =>
  try (rewrite <- difference_singleton; trivial);
  try rewrite Heq';
  repeat rewrite <- list_to_set_disj_env_add;
  try rewrite <- list_to_set_disj_rm;
  try (rewrite union_difference_L by trivial);
  try (rewrite union_difference_R by trivial);
  try ms
end.

Local Ltac peapply' th := (erewrite proper_Provable;  [| |reflexivity]);  [eapply th|equiv_tac].

remember (elements Γ++ Δ, ϕ) as pe.
revert pe Γ Δ ϕ Heqpe.
refine  (@well_founded_induction _ _ wf_pointed_order _ _).
intros (ΓΔ, ϕ0) Hind Γ Δ ϕ Heq Hnin Hp.
inversion Heq; subst; clear Heq.
assert(Hind' := λ Γ0 Δ0 ψ Ho, Hind (elements Γ0 ++ Δ0, ψ) Ho _ _ _ eq_refl).
clear Hind. rename Hind' into Hind.
dependent destruction Hp;
(* try and solve the easy case where the main formula is on the left *)
 try match goal with
| H : (?Γ0•?a•?b) = Γ ⊎ list_to_set_disj Δ |- _ => rename H into Heq;
      pose(Heq' := env_equiv_eq _ _ Heq); apply env_add_inv' in Heq'
| H : ((?Γ0 • ?a) = Γ ⊎ list_to_set_disj Δ) |- _ => rename H into Heq;
  assert(Hin : a ∈ (Γ ⊎ list_to_set_disj Δ)) by (rewrite <- Heq; ms);
  pose(Heq' := env_equiv_eq _ _ Heq); apply env_add_inv' in Heq';
  try (case (decide (a ∈ Γ)); intro Hin0;
  [split; intros; exhibit Hin0 1|
   case (decide (a ∈ (list_to_set_disj Δ : env))); intro Hin0';
  [|apply gmultiset_elem_of_disj_union in Hin; exfalso; tauto]])
end; simpl.

(* Atom *)
- auto 2 with proof.
- Atac'. case decide; intro; subst; [exfalso; now apply (Hnin _ Hin0)|]; auto with proof.
- split.
  + intro Hneq. Etac. rewrite decide_False. auto with proof. trivial.
  + case (decide (p = p0)).
    * intro Heqp0. Atac. do 2 rewrite decide_True by (f_equal; trivial). auto with proof.
    * intro Hneq. Etac. Atac'. do 2 rewrite decide_False by trivial. apply Atom.
(* ExFalso *)
- auto 2 with proof.
- auto 2 with proof.
-  split; Etac; auto with proof.
(* AndR *)
- split.
  + intro Hocc. apply AndR; erewrite E_irr; apply Hind; auto with proof.
  + Atac'. foldEA. apply make_conj_sound_R, AndR; erewrite E_irr;
      (eapply Hind; [order_tac | occ | trivial]).
(* AndL *)
- exch 0. apply AndL. exch 1; exch 0. peapply Hind; auto with proof. occ. peapply' Hp.
- exch 0. apply AndL. exch 1; exch 0. peapply Hind; auto with proof. occ. peapply' Hp.
-  split.
   + Etac. foldEA. apply Hind; auto with proof. peapply' Hp.
   + Atac. Etac. apply Hind; auto; auto with proof. peapply' Hp.
(* OrR1 & OrR2 *)
- split.
  + intro Hocc. apply OrR1. erewrite E_irr; apply Hind; auto with proof.
  + rewrite A_eq. apply make_disj_sound_R, OrR2.
      apply make_disj_sound_R, OrR1; erewrite E_irr.
      apply Hind; auto with proof.
- simpl. split.
  + intro Hocc. apply OrR2. erewrite E_irr; apply Hind; auto with proof.
  + rewrite A_eq. apply make_disj_sound_R, OrR2.
       apply make_disj_sound_R, OrR2; erewrite E_irr.
       apply Hind; auto with proof.
(* OrL *)
- exch 0. apply OrL; exch 0.
 + apply Hind; auto with proof. occ. peapply' Hp1.
 + apply Hind; auto with proof. occ. peapply' Hp2.
- exch 0. apply OrL; exch 0.
  + apply Hind; auto with proof. occ. peapply' Hp1.
  + apply Hind; auto with proof. occ. peapply' Hp2.
- split.
  + Etac. apply make_disj_sound_L, OrL; apply Hind; auto with proof.
      * peapply' Hp1.
      * peapply' Hp2.
  + Atac. apply weakening. apply make_conj_sound_R,AndR, make_impl_sound_R.
    * apply make_impl_sound_R, ImpR. apply Hind; auto with proof. peapply' Hp1.
    * apply ImpR. apply Hind; auto with proof. peapply' Hp2.
(* ImpR *)
- split.
  + intro Hocc. apply ImpR. exch 0.
    erewrite E_irr. apply Hind; auto with proof. occ. peapply Hp.
  + Atac'. apply weakening, make_impl_sound_R, ImpR, Hind; auto with proof. order_tac.
      * rewrite <- Permutation_middle. order_tac.
      * peapply Hp.
(* ImpLVar *)
- pose(Heq'' := Heq'); apply env_add_inv' in Heq''.
  case (decide ((Var p0 → φ) ∈ Γ)).
  + intro Hin0.
    assert (Hocc' := Hnin _ Hin0). simpl in Hocc'.
    case (decide (Var p0 ∈ Γ)); intro Hin1.
    * (* subcase 1: p0, (p0 → φ) ∈ Γ *)
      assert (Hin2 : Var p0 ∈ Γ ∖ {[Var p0 → φ]}) by (apply in_difference; trivial; discriminate).
      clear Hin1. 
      split; [intro Hocc|]; exhibit Hin0 1; exhibit Hin2 2; exch 0; exch 1; apply ImpLVar; exch 1; exch 0;
      (apply Hind; auto with proof; [occ | peapply' Hp]).
    * assert(Hin0' : Var p0 ∈ (Γ0•Var p0•(p0 → φ))) by ms. rewrite Heq in Hin0'.
      case (decide (Var p0 ∈ (list_to_set_disj Δ: env))); intro Hp0;
      [|apply gmultiset_elem_of_disj_union in Hin0'; exfalso; tauto].
      (* subcase 3: p0 ∈ Δ ; (p0 → φ) ∈ Γ *)
      clear Heq''.
      split; try case decide; intros; subst.
      -- apply contraction. Etac. rewrite decide_False by tauto.
          exhibit Hin0 2. exch 1. exch 0. apply ImpLVar. exch 0. apply weakening. exch 0.
         apply Hind; auto with proof. occ. peapply' Hp.
      -- apply contraction. Etac. rewrite decide_False by tauto.
          exhibit Hin0 2. exch 1; exch 0. apply ImpLVar. exch 0. apply weakening.
          exch 0. foldEA. apply Hind; auto with proof. occ. peapply' Hp.
  + intro.
    assert(Hin : (Var p0 → φ) ∈ (Γ0•Var p0•(p0 → φ))) by ms.
    rewrite Heq in Hin.
    case (decide ((Var p0 → φ) ∈ (list_to_set_disj Δ : env))); intro Hin0;
    [|apply gmultiset_elem_of_disj_union in Hin; exfalso; tauto].
    case (decide (Var p0 ∈ Γ)); intro Hin1.
    * (* subcase 2: p0 ∈ Γ ; (p0 → φ) ∈ Δ *)
      do 2 exhibit Hin1 1.
      split; [intro Hocc|].
      -- Etac. case decide; intro Hp0;[|case decide; intro; subst; [auto with *|]].
         ++ foldEA. apply Hind; auto with proof; [order_tac; order_tac|occ | peapply' Hp]. 
         ++  apply make_impl_sound_L, ImpLVar. exch 0. backward. rewrite env_add_remove.
         apply Hind; auto with proof. peapply' Hp.
      -- Etac. Atac. case decide; intro Hp0;[|case decide; intro; subst; [auto with *|]].
        ++ foldEA. apply Hind; auto with proof; [order_tac; order_tac|occ | peapply' Hp].
        ++ apply make_impl_sound_L, ImpLVar.
               apply make_conj_sound_R, AndR; auto 2 with proof.
               exch 0. backward. rewrite env_add_remove.
               apply Hind; auto with proof. peapply' Hp.
    * assert(Hin': Var p0 ∈ Γ ⊎ list_to_set_disj Δ) by (rewrite <- Heq; ms).
       apply gmultiset_elem_of_disj_union in Hin'.
       case (decide (Var p0 ∈ (list_to_set_disj Δ: env))); intro Hin1'; [|exfalso; tauto].
      (* subcase 4: p0,(p0 → φ) ∈ Δ *)
      case (decide (p = p0)); intro.
      -- (* subsubcase p = p0 *)
        apply elem_of_list_to_set_disj in Hin1'.
        subst. split; Etac; repeat rewrite decide_True by trivial.
        ++ clear Heq. apply Hind; auto with proof. peapply' Hp.
        ++ Atac. repeat rewrite decide_True by trivial. clear Heq.
                apply Hind; auto with proof. peapply' Hp.
      -- (* subsubcase p ≠ p0 *)
         split; [intro Hocc|].
         ++ apply contraction. Etac. rewrite decide_False by trivial. exch 0.
                 assert((p0 → φ) ∈ list_to_set_disj Δ) by ms. Etac.
                 rewrite decide_True by now apply elem_of_list_to_set_disj.
                 exch 0. apply weakening. apply Hind; auto with proof. peapply' Hp.
         ++ apply contraction. Etac. exch 0. assert((p0 → φ) ∈ list_to_set_disj Δ) by ms. 
                 Etac; Atac. rewrite decide_False by trivial.
                 do 2 rewrite decide_True by now apply elem_of_list_to_set_disj.
                 exch 0. apply weakening.
                 apply Hind; auto with proof. peapply' Hp.
(* ImpLAnd *)
- exch 0. apply ImpLAnd. exch 0. apply Hind; auto with proof; [occ|peapply' Hp].
- exch 0. apply ImpLAnd. exch 0. apply Hind; auto with proof; [occ|peapply' Hp].
- split; Etac.
  + apply Hind; auto with proof. peapply' Hp.
  + Atac. simpl. apply Hind; auto with proof. peapply' Hp.
(* ImpLOr *)
- exch 0; apply ImpLOr. exch 1; exch 0. apply Hind; auto with proof. occ. peapply' Hp.
- exch 0; apply ImpLOr. exch 1; exch 0. apply Hind; [order_tac | occ|peapply' Hp].
- split; Etac.
  +  apply Hind; auto with proof. peapply' Hp.
  +  Atac. apply Hind; auto with proof. peapply' Hp.
(* ImpLImp *)
- (* subcase 1: ((φ1 → φ2) → φ3) ∈ Γ *)
  assert(ψ ≠ Var p) by (intro; subst; simpl in *; tauto).
  exch 0; apply ImpLImp; exch 0.
  + erewrite E_irr. apply Hind; auto with proof. occ. peapply' Hp1.
      simpl. apply Hnin in Hin0. simpl in *. tauto.
  + erewrite E_irr. apply Hind; auto with proof. occ. peapply' Hp2.
- exch 0; apply ImpLImp; exch 0.
  + erewrite E_irr. apply Hind; auto with proof. occ. peapply' Hp1.
       simpl. apply Hnin in Hin0. simpl in Hin0. tauto.
  +  apply Hind; auto with proof. occ. peapply' Hp2.
- (* subcase 2: ((φ1 → φ2) → φ3) ∈ Δ *)
  split.
  + Etac. apply make_impl_sound_L2'. apply ImpLImp.
    * apply weakening. apply ImpR. foldEA.
       rewrite (E_irr φ2).
       apply Hind; auto with proof.
       -- order_tac. repeat rewrite Permutation_middle. order_tac.
       -- repeat setoid_rewrite gmultiset_disj_union_assoc.
           setoid_rewrite gmultiset_disj_union_comm.
           repeat setoid_rewrite gmultiset_disj_union_assoc.  exch 0. apply ImpR_rev.
           peapply' Hp1.
    * apply Hind; auto with proof. peapply' Hp2.
  + Atac. apply make_conj_sound_R, AndR.
    * apply weakening. apply make_impl_sound_R, ImpR. foldEA.
       rewrite (E_irr φ2). apply Hind; auto with proof.
       -- order_tac. repeat rewrite Permutation_middle. order_tac.
       -- repeat setoid_rewrite gmultiset_disj_union_assoc.
           setoid_rewrite gmultiset_disj_union_comm.
           repeat setoid_rewrite gmultiset_disj_union_assoc.  exch 0. apply ImpR_rev.
           peapply' Hp1.
    * Etac. simpl. apply make_impl_sound_L2', ImpLImp.
      -- apply weakening. apply ImpR. foldEA.
       rewrite (E_irr φ2). apply Hind; auto with proof.
       ++ order_tac. repeat rewrite Permutation_middle. order_tac.
       ++ repeat setoid_rewrite gmultiset_disj_union_assoc.
               setoid_rewrite gmultiset_disj_union_comm.
               repeat setoid_rewrite gmultiset_disj_union_assoc.  exch 0. apply ImpR_rev.
               peapply' Hp1.
      -- apply Hind; auto with proof. peapply' Hp2.
- (* ImpBox, external *)
   destruct (open_boxes_case (list_to_set_disj Δ)) as [[θ Hθ] | Hequiv].
    + apply contraction. Etac. exch 1; exch 0; apply ImpBox.
        * box_tac. box_tac. exch 2; exch 1; exch 0. apply weakening. foldEA.
           erewrite E_irr with (ϕ' := φ1).
           exch 1; exch 0. apply Hind.
           --  order_tac. (* cannot handle it. manual proof *)
               rewrite  elements_open_boxes.
               do 2 apply env_order_cancel_right. apply env_order_4; simpl; try lia. left. 
               apply env_order_disj_union_compat_strong_left; order_tac.
           -- occ. intro HF. destruct (occurs_in_open_boxes _ _ _ HF Hin1) as (θ0 & Hθ0 & Hinθ).
               apply (Hnin θ0); ms.
           -- assert(Hθ' := In_open_boxes _ _ Hθ).
               assert(Heq'' : Γ0 ≡ (Γ  ∖ {[□ φ1 → φ2]} ⊎ list_to_set_disj ((□θ) :: rm (□ θ) Δ))). {
               rewrite Heq'. simpl. rewrite union_difference_L by trivial.
               rewrite (difference_singleton _ _ Hθ).
               rewrite list_to_set_disj_rm. ms.
               }
               clear Heq'. clear Hθ.
              (erewrite proper_Provable;  [| |reflexivity]);  [eapply Hp1|].
              rewrite Heq''. rewrite open_boxes_disj_union.
              repeat rewrite  <- ?list_to_set_disj_open_boxes,  <- list_to_set_disj_env_add.
              rewrite open_boxes_add. simpl. ms.
          -- intro HF. apply (Hnin _ Hin0). simpl. tauto.
        * exch 0. apply weakening. exch 0. apply Hind; [order_tac | occ|peapply' Hp2| trivial].
  + assert(Heq'' : (⊗ Γ0) ≡ ((⊗Γ  ∖ {[□ φ1 → φ2]}) ⊎ ⊗ (list_to_set_disj Δ))). {
       rewrite Heq'. rewrite union_difference_L by trivial.
       rewrite <- Hequiv, open_boxes_disj_union.
       rewrite open_boxes_remove by trivial. ms. }
       exch 0. apply ImpBox.
      * box_tac. exch 1; exch 0. apply open_box_L.
         erewrite E_irr with (ϕ' := φ1).
         apply Hind.
         -- order_tac. rewrite elements_open_boxes. repeat rewrite Permutation_middle. order_tac.
         -- occ. intro HF. destruct (occurs_in_open_boxes _ _ _ HF Hin1) as (θ0 & Hθ0 & Hinθ).
             apply (Hnin θ0); ms.
         -- peapply' Hp1.
         -- intro HF. apply (Hnin _ Hin0). simpl. tauto.
     * exch 0. apply Hind; [order_tac|occ |  | trivial].
        (erewrite proper_Provable;  [| |reflexivity]);  [eapply Hp2|].
        rewrite Heq'. rewrite union_difference_L by trivial. ms.
- destruct (open_boxes_case (list_to_set_disj Δ)) as [[θ Hθ] | Hequiv].
    + apply contraction. Etac. exch 1; exch 0; apply ImpBox.
        * box_tac. box_tac. exch 2; exch 1; exch 0. apply weakening. foldEA.
           erewrite E_irr with (ϕ' := φ1).
           exch 1; exch 0. apply Hind.
         -- order_tac.
             rewrite  elements_open_boxes.
               do 2 apply env_order_cancel_right. apply env_order_4; simpl; try lia. left. 
               apply env_order_disj_union_compat_strong_left; order_tac.
         -- occ. intro HF. destruct (occurs_in_open_boxes _ _ _ HF Hin1) as (θ0 & Hθ0 & Hinθ).
             apply (Hnin θ0); ms.
           -- assert(Hθ' := In_open_boxes _ _ Hθ).
               assert(Heq'' : Γ0 ≡ (Γ  ∖ {[□ φ1 → φ2]} ⊎ list_to_set_disj ((□θ) :: rm (□ θ) Δ))). {
               rewrite Heq'. simpl. rewrite union_difference_L by trivial.
               rewrite (difference_singleton _ _ Hθ).
               rewrite list_to_set_disj_rm. ms.
               }
               clear Heq'. clear Hθ.
              (erewrite proper_Provable;  [| |reflexivity]);  [eapply Hp1|].
              rewrite Heq''. rewrite open_boxes_disj_union.
              repeat rewrite  <- ?list_to_set_disj_open_boxes,  <- list_to_set_disj_env_add.
              rewrite open_boxes_add. simpl. ms.
         -- intro HF. apply (Hnin _ Hin0). simpl. tauto.
        * exch 0. apply weakening. exch 0. apply Hind ; [order_tac|occ|peapply' Hp2].
  + erewrite E_irr with (ϕ' := φ1).
      exch 0. apply ImpBox. 
      * box_tac. exch 1; exch 0. apply open_box_L. apply Hind.
         --  order_tac. rewrite  elements_open_boxes.  order_tac.
         -- occ. intro HF. destruct (occurs_in_open_boxes _ _ _ HF Hin1) as (θ0 & Hθ0 & Hinθ).
             apply (Hnin θ0); ms.
         -- assert(Heq'' : (⊗ Γ0) ≡ ((⊗Γ  ∖ {[□ φ1 → φ2]}) ⊎ ⊗ (list_to_set_disj Δ))). {
                 rewrite Heq'. rewrite union_difference_L by trivial.
                 rewrite <- Hequiv, open_boxes_disj_union.
                 rewrite open_boxes_remove by trivial. ms. }
                 peapply Hp1.
         -- intro HF. apply (Hnin _ Hin0). simpl. tauto.
      * erewrite E_irr with (ϕ' := ψ).
          exch 0. apply Hind. order_tac. occ. clear Hequiv. peapply' Hp2.
- split; Etac.
  + foldEA. apply make_impl_sound_L, ImpBox.
        -- do 2 apply weakening. apply make_impl_sound_R, ImpR.
            erewrite E_irr with (ϕ' := φ1) by ms.
            apply Hind.
             ++ order_tac. rewrite elements_open_boxes. 
                     do 2 apply env_order_cancel_right.
                     repeat rewrite Permutation_middle.
                     apply env_order_disj_union_compat_strong_left; order_tac.
            ++ intros φ0 Hin1 HF. destruct (occurs_in_open_boxes _ _ _ HF Hin1) as (θ0 & Hθ0 & Hinθ).
                    apply (Hnin θ0); ms.
            ++ assert(Heq'' : (⊗ Γ0) ≡ ((⊗Γ) ⊎ list_to_set_disj (map open_box (rm (□ φ1 → φ2) Δ)))). {
                    rewrite Heq'.
                    repeat rewrite open_boxes_remove by ms. simpl.
                    rewrite <- list_to_set_disj_open_boxes, <- list_to_set_disj_rm, open_boxes_disj_union. trivial.
                    simpl. rewrite union_difference_R by auto with proof. rewrite open_boxes_remove by ms. ms.
                    }
                    peapply Hp1.
        -- apply Hind. order_tac. occ. peapply' Hp2. trivial.
  + assert(Heq'' : (⊗ Γ0) ≡ ((⊗Γ) ⊎ list_to_set_disj (map open_box (rm (□ φ1 → φ2) Δ)))). {
          rewrite Heq'.
          repeat rewrite open_boxes_remove by ms. simpl.
          rewrite <- list_to_set_disj_open_boxes, <- list_to_set_disj_rm, open_boxes_disj_union. trivial.
          simpl. rewrite union_difference_R by auto with proof. rewrite open_boxes_remove by ms. ms.
        }
  foldEA. Atac.  apply AndR.
     * apply make_impl_sound_L, ImpBox.
        -- do 2 apply weakening. apply make_impl_sound_R, ImpR.
            erewrite E_irr with (ϕ' := φ1).
            apply Hind.
             ++ order_tac. rewrite elements_open_boxes. 
                     do 2 apply env_order_cancel_right.
                     repeat rewrite Permutation_middle.
                     apply env_order_disj_union_compat_strong_left; order_tac.
            ++ intros φ0 Hin1 HF. destruct (occurs_in_open_boxes _ _ _ HF Hin1) as (θ0 & Hθ0 & Hinθ).
                    apply (Hnin θ0); ms.
            ++ peapply Hp1.
       -- apply BoxR. box_tac. do 2 apply weakening. apply make_impl_sound_R, ImpR. foldEA. 
           erewrite E_irr with (ϕ' := φ1) by ms.
           apply Hind.
             ++ order_tac. rewrite elements_open_boxes. 
                     do 2 apply env_order_cancel_right.
                     repeat rewrite Permutation_middle.
                     apply env_order_disj_union_compat_strong_left; order_tac.
            ++ intros φ0 Hin1 HF. destruct (occurs_in_open_boxes _ _ _ HF Hin1) as (θ0 & Hθ0 & Hinθ).
                    apply (Hnin θ0); ms.
            ++ peapply Hp1.
     * foldEA. apply make_impl_sound_L, ImpBox.
        -- do 2 apply weakening. apply make_impl_sound_R, ImpR.
               erewrite E_irr with (ϕ' := φ1).
               apply Hind.
             ++ order_tac. rewrite elements_open_boxes. 
                     do 2 apply env_order_cancel_right.
                     repeat rewrite Permutation_middle.
                     apply env_order_disj_union_compat_strong_left; order_tac.
               ++ intros φ0 Hφ0 HF. destruct (occurs_in_open_boxes _ _ _ HF Hφ0) as (θ0 & Hθ0 & Hinθ).
                     apply (Hnin θ0); ms.
               ++ peapply Hp1.
        -- clear Heq''. apply Hind; [order_tac|occ|peapply' Hp2].
- split.
  + intro Hocc. destruct (open_boxes_case (list_to_set_disj Δ)) as [[θ Hθ] | Hequiv].
      * Etac. foldEA. apply BoxR. box_tac. exch 0.
        erewrite E_irr with (ϕ' := φ); apply Hind.
        -- order_tac. 
            rewrite elements_open_boxes.
            repeat rewrite Permutation_middle.
            apply env_order_disj_union_compat_strong_left. order_tac.
            apply env_order_2. simpl; lia. simpl; lia.
            apply env_order_eq_add. left. order_tac.
        -- intros φ0 Hφ0 HF. apply gmultiset_elem_of_disj_union in Hφ0.
            destruct Hφ0 as [Hφ0|]; [|ms].
            destruct (occurs_in_open_boxes _ _ _ HF Hφ0) as (θ0 & Hθ0 & Hinθ). apply (Hnin θ0); ms.
        -- (erewrite proper_Provable;  [| |reflexivity]);  [eapply Hp|].
            rewrite open_boxes_disj_union.
            rewrite <- list_to_set_disj_env_add.
            rewrite <- list_to_set_disj_open_boxes, <- list_to_set_disj_rm.
            rewrite open_boxes_remove by ms.
            rewrite <- difference_singleton by auto with proof. ms.
        -- trivial.
      * apply BoxR. box_tac. exch 0. apply open_box_L.
         erewrite E_irr with (ϕ' := φ).
         apply Hind.
         -- order_tac.
             rewrite elements_open_boxes.
            repeat rewrite Permutation_middle.
            apply env_order_disj_union_compat_strong_left. order_tac.
            apply env_order_2. simpl; lia. simpl; lia. now right.
         -- intros φ0 Hφ0 HF. apply gmultiset_elem_of_disj_union in Hφ0.
            destruct Hφ0 as [Hφ0|]; [|ms].
            destruct (occurs_in_open_boxes _ _ _ HF Hφ0) as (θ0 & Hθ0 & Hinθ). apply (Hnin θ0); ms.
         -- (erewrite proper_Provable;  [| |reflexivity]);  [eapply Hp|].
              rewrite open_boxes_disj_union, <- Hequiv. ms.
         --  trivial.
  + Atac'. foldEA. apply BoxR. box_tac. apply weakening. erewrite E_irr with (ϕ' := φ).
       apply weakening. apply make_impl_sound_R, ImpR.
       apply Hind.
       * order_tac.
          rewrite elements_open_boxes.
          repeat rewrite Permutation_middle.
          order_tac.
       * intros φ0 Hφ0 HF. destruct (occurs_in_open_boxes _ _ _ HF Hφ0) as (θ0 & Hθ0 & Hinθ).
          apply (Hnin θ0); ms.
       * (erewrite proper_Provable;  [| |reflexivity]);  [eapply Hp|].
            rewrite open_boxes_disj_union.
            rewrite <- list_to_set_disj_env_add.
            rewrite <- list_to_set_disj_open_boxes. ms.
Qed.

End PropQuantCorrect.

End Correctness.


End UniformInterpolation.

(** * Main uniform interpolation Theorem *)

Open Scope type_scope.


Lemma E_of_empty p φ : E p ([], φ) = (Implies Bot Bot).
Proof. 
  rewrite E_eq. rewrite in_map_empty. now unfold conjunction, nodup, foldl.
Qed.

Definition vars_incl φ l := forall x, occurs_in x φ -> In x l.

(**  The overall correctness result is summarized here. *)

Theorem iSL_uniform_interpolation p V: p ∉ V ->
  ∀ φ, vars_incl φ (p :: V) ->
    (vars_incl (Ef p φ) V)
  * ({[φ]} ⊢ (Ef p φ))
  * (∀ ψ, vars_incl ψ V -> {[φ]} ⊢ ψ -> {[Ef p φ]} ⊢ ψ)
  * (vars_incl (Af p φ) V)
  * ({[Af p φ]} ⊢ φ)
  * (∀ θ, vars_incl θ V -> {[θ]} ⊢ φ -> {[θ]} ⊢ Af p φ).
Proof. 
intros Hp φ Hvarsφ; repeat split.
  + intros x Hx. apply (EA_vars p _ ⊥ x) in Hx.
      destruct Hx as [Hneq [θ [Hθ Hocc]]]. apply elem_of_list_singleton in Hθ. subst.
      apply Hvarsφ in Hocc. destruct Hocc; subst; tauto.
  + replace {[φ]} with (list_to_set_disj [φ] : env). apply entail_correct. simpl. ms.
  + intros ψ Hψ Hyp. rewrite elem_of_list_In in Hp. unfold Ef. rewrite E_irr with (ϕ' := ψ).
      * peapply (pq_correct p ∅ [φ] ψ).
         -- intros θ Hin. inversion Hin.
         -- peapply Hyp.
         -- intro HF. apply Hψ in HF. tauto.
  + intros x Hx. apply (EA_vars p ∅ φ x) in Hx.
      destruct Hx as [Hneq [Hin | [θ [Hθ Hocc]]]].
      * apply Hvarsφ in Hin. destruct Hin; subst; tauto.
      * inversion Hθ.
  + peapply (entail_correct p []).
  + intros ψ Hψ Hyp. rewrite elem_of_list_In in Hp.
      apply (TopL_rev _ ⊥). peapply (pq_correct p {[ψ]} [] φ).
      * intros φ0 Hφ0. apply gmultiset_elem_of_singleton in Hφ0. subst. auto with *.
      * peapply Hyp.
      * now rewrite E_of_empty.
Qed.