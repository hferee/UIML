Require Import ISL.Sequents.
Require Import ISL.SequentProps ISL.Order.
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


(* solves the obligations of the following programs *)
Obligation Tactic := intros; order_tac.

(** First, the implementation of the rules for calculating E. The names of the rules
  refer to the table in Pitts' paper. *)
(** note the use of  "lazy" conjunctions, disjunctions and implications *)
Program Definition e_rule {Δ : env} {ϕ : form}
  (EA0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form * form)
  (θ: form) (Hin : θ ∈ Δ) : form :=
let E Δ H := fst (EA0 (Δ, ϕ) H) in
let A pe0 H := snd (EA0 pe0 H) in
let Δ'  := Δ ∖ {[θ]} in
match θ with
| Bot => ⊥  (* E0 *)
| Var q =>
    if decide (p = q) then ⊤ (* default *)
    else E Δ' _ ⊼ q (* E1 *)
(* E2 *)
| δ₁ ∧ δ₂ => E ((Δ'•δ₁)•δ₂) _
(* E3 *)
| δ₁ ∨ δ₂ => E (Δ'•δ₁) _ ⊻ E (Δ' •δ₂) _
| Var q → δ =>
    if decide (p = q)
    then
      if decide (Var p ∈ Δ) then E (Δ'•δ) _ (* E5 *)
      else ⊤
    else q ⇢ E (Δ'•δ) _ (* E4 *)
(* E6 *)
| (δ₁ ∧ δ₂)→ δ₃ => E (Δ'•(δ₁ → (δ₂ → δ₃))) _
(* E7 *)
| (δ₁ ∨ δ₂)→ δ₃ => E (Δ'•(δ₁ → δ₃)•(δ₂ → δ₃)) _
(* E8 *)
| ((δ₁→ δ₂)→ δ₃) =>
  (E (Δ'•(δ₂ → δ₃)) _⇢ A (Δ'•(δ₂ → δ₃), δ₁ → δ₂) _) ⇢ E (Δ'•δ₃) _
| Bot → _ => ⊤
| □ φ => □(E ((⊗Δ') • φ ) _) (* very redundant ; identical for each box *)
| (□δ1 → δ2) =>  (□(E((⊗Δ') • δ2 • □δ1) _ → A((⊗Δ') • δ2 • □δ1, δ1) _) → E(Δ' • δ2) _)
end. (* TODO: E((⊗Δ') • δ2 • □δ1) _) →  ? *)
(* TODO lemma : E(Δ) |- θ -> E(⊗Δ) ⊢ θ *)

(** The implementation of the rules for defining A is separated into two pieces.
    Referring to Table 5 in Pitts, the definition a_rule_env handles A1-8 and A10,
    and the definition a_rule_form handles A9 and A11-13. *)
Program Definition a_rule_env {Δ : env} {ϕ : form}
  (EA0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form * form)
  (θ: form) (Hin : θ ∈ Δ) : form :=
let E Δ H := fst (EA0 (Δ, ϕ) H) in
let A pe0 H := snd (EA0 pe0 H) in
let Δ'  := Δ ∖ {[θ]} in
match θ with
| Var q =>
    if decide (p = q)
    then
      if decide (Var p = ϕ) then ⊤ (* A10 *)
      else ⊥
    else A (Δ', ϕ) _ (* A1 *)
(* A2 *)
| δ₁ ∧ δ₂ => A ((Δ'•δ₁)•δ₂, ϕ) _
(* A3 *)
| δ₁ ∨ δ₂ =>
      (E (Δ'•δ₁) _ ⇢ A (Δ'•δ₁, ϕ) _)
  ⊼ (E (Δ'•δ₂) _ ⇢ A (Δ'•δ₂, ϕ) _)
| Var q → δ =>
    if decide (p = q)
    then
      if decide (Var p ∈ Δ) then A (Δ'•δ, ϕ) _ (* A5 *)
      else ⊥
    else q ⊼ A (Δ'•δ, ϕ) _ (* A4 *)
(* A6 *)
| (δ₁ ∧ δ₂)→ δ₃ =>
  A (Δ'•(δ₁ → (δ₂ → δ₃)), ϕ) _
(* A7 *)
| (δ₁ ∨ δ₂)→ δ₃ =>
  A ((Δ'•(δ₁ → δ₃))•(δ₂ → δ₃), ϕ) _
(* A8 *)
| ((δ₁→ δ₂)→ δ₃) =>
  (E (Δ'•(δ₂ → δ₃)) _ ⇢ A (Δ'•(δ₂ → δ₃), (δ₁ → δ₂)) _)
  ⊼ A (Δ'•δ₃, ϕ) _
| Bot => ⊥
| Bot → _ => ⊥
| □δ => ⊥
| ((□δ1) → δ2) => □(E((⊗Δ')• δ2 • □δ1) _  → A((⊗Δ')• δ2 • □δ1, δ1) _) ∧ A(Δ' • δ2, ϕ) _
(* TODO: (E((⊗Δ') • δ2 • □δ1)  _ → ? *)
end.

(* make sure that the proof obligations do not depend on EA0 *)
Obligation Tactic := intros Δ ϕ _ _ _; intros; order_tac.
Program Definition a_rule_form {Δ : env} {ϕ : form}
  (EA0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form * form) : form :=
let E pe0 H := fst (EA0 pe0 H) in
let A pe0 H := snd (EA0 pe0 H) in 
match ϕ with
| Var q =>
    if decide (p = q)
    then ⊥
    else Var q (* A9 *)
(* A11 *)
| ϕ₁ ∧ ϕ₂ => A (Δ, ϕ₁) _ ⊼ A (Δ, ϕ₂) _
(* A12 *)
| ϕ₁ ∨ ϕ₂ => A (Δ, ϕ₁) _ ⊻ A (Δ, ϕ₂) _
(* A13 *)
| ϕ₁→ ϕ₂ => E (Δ•ϕ₁, ϕ₂) _ ⇢ A (Δ•ϕ₁, ϕ₂) _
| Bot => ⊥
| □δ => □((E ((⊗Δ) • □δ, δ) _) ⇢ A((⊗Δ) • □δ, δ) _)
end.

Obligation Tactic := intros; order_tac.
Program Fixpoint EA (pe : env * form) {wf pointed_env_order pe} :=
  let Δ := fst pe in
  (⋀ (in_map Δ (e_rule EA)),
   ⋁ (in_map Δ (a_rule_env EA)) ⊻ a_rule_form EA).
Next Obligation. apply wf_pointed_order. Defined.

Definition E (pe : env * form) := (EA pe).1.
Definition A (pe : env * form) := (EA pe).2.

Definition Ef (ψ : form) := E ({[ψ]}, ⊥).
Definition Af (ψ : form) := A (∅, ψ).


(** Congruence lemmas: if we apply any of e_rule, a_rule_env, or a_rule_form
  to two equal environments, then they give the same results. *)
Lemma e_rule_cong Δ ϕ θ (Hin : θ ∈ Δ) EA1 EA2:
  (forall pe Hpe, EA1 pe Hpe = EA2 pe Hpe) ->
  @e_rule Δ ϕ EA1 θ Hin = @e_rule Δ ϕ EA2 θ Hin.
Proof.
  intro Heq.
  destruct θ; simpl; try (destruct θ1); repeat (destruct decide);
  f_equal; repeat erewrite Heq; trivial.
Qed.

Lemma a_rule_env_cong Δ ϕ θ Hin EA1 EA2:
  (forall pe Hpe, EA1 pe Hpe = EA2 pe Hpe) ->
  @a_rule_env Δ ϕ EA1 θ Hin = @a_rule_env Δ ϕ EA2 θ Hin.
Proof.
  intro Heq.
  destruct θ; simpl; trivial; repeat (destruct decide);
  f_equal; repeat erewrite Heq; trivial;
  destruct θ1; try (destruct decide); trivial;
  repeat erewrite Heq; trivial.
Qed.

Lemma a_rule_form_cong Δ ϕ EA1 EA2:
  (forall pe Hpe, EA1 pe Hpe = EA2 pe Hpe) ->
  @a_rule_form Δ ϕ EA1 = @a_rule_form Δ ϕ EA2.
Proof.
  intro Heq.
  destruct ϕ; simpl; repeat (destruct decide); trivial;
  repeat (erewrite Heq; eauto); trivial.
Qed.

(** The following lemma requires proof irrelevance due to in_map. *)
Lemma EA_eq Δ ϕ:
  (E (Δ, ϕ) =  ⋀ (in_map Δ (@e_rule Δ ϕ (λ pe _, EA pe)))) /\
  (A (Δ, ϕ) = (⋁ (in_map Δ (@a_rule_env Δ ϕ (λ pe _, EA pe)))) ⊻
       @a_rule_form Δ ϕ (λ pe _, EA pe)).
Proof.
simpl. unfold E, A, EA. simpl.
rewrite -> Wf.Fix_eq.
- simpl. split; trivial.
- intros Δ' f g Heq. f_equal; f_equal.
  + apply in_map_ext. intros. apply e_rule_cong; intros; f_equal.
      now rewrite Heq.
  + f_equal. apply in_map_ext. intros. apply a_rule_env_cong; intros.
      now rewrite Heq.
  + apply a_rule_form_cong; intros. now rewrite Heq.
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

(** *** (a)  *)

Lemma e_rule_vars (Δ : env) (θ : form) (Hin : θ ∈ Δ) (ϕ : form)
  (EA0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form * form) x
  (HEA0 : ∀ pe Hpe, 
      (occurs_in x (fst (EA0 pe Hpe)) -> x ≠ p ∧ ∃ θ, θ ∈ pe.1 /\ occurs_in x θ) /\
      (occurs_in x (snd (EA0 pe Hpe)) -> x ≠ p ∧ (occurs_in x pe.2 \/ ∃ θ, θ ∈ pe.1 /\ occurs_in x θ))) :
occurs_in x (e_rule EA0 θ Hin) -> x ≠ p ∧ ∃ θ, θ ∈ Δ /\ occurs_in x θ.
Proof.
destruct θ; unfold e_rule.
- case decide.
  + simpl. intros Heq HF; subst. tauto.
  + simpl. intros Hneq Hocc. apply occurs_in_make_conj in Hocc.
      destruct Hocc as [Hocc|Heq]; vars_tac. subst; tauto.
- simpl. tauto.
- vars_tac.
- intro Hocc. apply occurs_in_make_disj in Hocc as [Hocc|Hocc]; vars_tac.
- destruct θ1; try solve[vars_tac].
  + case decide.
    * intro; subst. case decide.
      -- vars_tac.
      -- simpl; tauto.
    * intros Hneq Hocc. apply occurs_in_make_impl in Hocc as [Heq | Hocc]; vars_tac.
      subst. tauto.
  + intros Hocc. apply occurs_in_make_impl in Hocc.
      destruct Hocc as [Hocc|Hocc]; [apply occurs_in_make_impl in Hocc as [Hocc|Hocc]|]; vars_tac; subst; tauto.
  + intros Hocc; repeat destruct Hocc as [Hocc|Hocc]; simpl in Hocc; vars_tac.
- intuition; simpl in *; vars_tac.
Qed.
(** *** (b) *)

Lemma a_rule_env_vars Δ θ Hin ϕ
  (EA0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form * form) x
  (HEA0 : ∀ pe Hpe, 
      (occurs_in x (fst (EA0 pe Hpe)) -> x ≠ p ∧ ∃ θ, θ ∈ pe.1 /\ occurs_in x θ) /\
      (occurs_in x (snd (EA0 pe Hpe)) -> x ≠ p ∧ (occurs_in x pe.2 \/ ∃ θ, θ ∈ pe.1 /\ occurs_in x θ))):
occurs_in x (a_rule_env EA0 θ Hin) -> x ≠ p ∧ (occurs_in x ϕ \/ ∃ θ, θ ∈ Δ /\ occurs_in x θ).
Proof.
destruct θ; unfold a_rule_env.
- case decide.
  + intro; subst. case decide; simpl; tauto.
  + intros Hneq Hocc. vars_tac.
- simpl. tauto.
- intro Hocc. vars_tac.
- intros Hocc. apply occurs_in_make_conj in Hocc.
  destruct Hocc as [Hocc|Hocc];
  apply occurs_in_make_impl in Hocc; vars_tac; vars_tac.
- destruct θ1; try solve[vars_tac].
  + case decide.
    * intro; subst. case decide.
      -- intros Hp Hocc. vars_tac.
      -- simpl; tauto.
    * intros Hneq Hocc. apply occurs_in_make_conj in Hocc.
       destruct Hocc as [Heq | Hocc]; vars_tac. subst; tauto.
  + intros Hocc. apply occurs_in_make_conj in Hocc.
      destruct Hocc as [Hocc|Hocc].
      * apply occurs_in_make_impl in Hocc; vars_tac; vars_tac.
      * vars_tac.
  + intros Hocc.  try apply occurs_in_make_impl in Hocc.
      destruct Hocc as [Hocc|Hocc].
      * try apply occurs_in_make_conj in Hocc; vars_tac; vars_tac.
      * vars_tac.
- simpl; tauto.
Qed.


Lemma a_rule_form_vars Δ ϕ
  (EA0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form * form) x
  (HEA0 : ∀ pe Hpe, 
      (occurs_in x (fst (EA0 pe Hpe)) -> x ≠ p ∧ ∃ θ, θ ∈ pe.1 /\ occurs_in x θ) /\
      (occurs_in x (snd (EA0 pe Hpe)) -> x ≠ p ∧ (occurs_in x pe.2 \/ ∃ θ, θ ∈ pe.1 /\ occurs_in x θ))):
  occurs_in x (a_rule_form EA0) -> x ≠ p ∧ (occurs_in x ϕ \/ ∃ θ, θ ∈ Δ /\ occurs_in x θ).
Proof.
destruct ϕ.
- simpl. case decide; simpl; intros; subst; intuition; auto.
- tauto.
- simpl. intros Hocc; apply occurs_in_make_conj in Hocc as [Hocc|Hocc]; vars_tac.
- simpl. intros Hocc; apply occurs_in_make_disj in Hocc as  [Hocc|Hocc]; vars_tac.
- simpl. intro Hocc. apply occurs_in_make_impl in Hocc. destruct Hocc; vars_tac; vars_tac.
- intro Hocc. replace (occurs_in x (□ ϕ)) with (occurs_in x ϕ) by trivial.
  unfold a_rule_form in Hocc. (* apply occurs_in_make_impl in Hocc. *)
  repeat vars_tac; eauto using occurs_in_open_boxes.
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

Lemma a_rule_env_spec Δ θ ϕ Hin (EA0 : ∀ pe, (pe ≺· (Δ, ϕ)) → form * form)
  (HEA : forall Δ ϕ Hpe, (Δ ⊢ fst (EA0 (Δ, ϕ) Hpe)) * (Δ• snd(EA0 (Δ, ϕ) Hpe) ⊢ ϕ)) :
  (Δ•a_rule_env EA0 θ Hin ⊢ ϕ).
Proof with (auto with proof).
assert (HE := λ Δ0 ϕ0 Hpe, fst (HEA Δ0 ϕ0 Hpe)).
assert (HA := λ Δ0 ϕ0 Hpe, snd (HEA Δ0 ϕ0 Hpe)).
clear HEA.
destruct θ; exhibit Hin 1.
- simpl; case decide; intro Hp.
  + subst. case_decide; subst; auto with proof.
  + exch 0...
- constructor 2.
- simpl; exch 0. apply AndL. exch 1; exch 0...
- apply make_conj_sound_L.
  exch 0. apply OrL; exch 0.
  + apply AndL. apply make_impl_sound_L. exch 0. apply make_impl_sound_L... (* uses imp_cut *)
  + apply AndL. apply make_impl_sound_L. exch 0. apply make_impl_sound_L. auto with proof.
- destruct θ1.
  + simpl; case decide; intro Hp.
    * subst. case decide.
      -- intros Hp.
         assert(Hin' : (p → θ2) ∈ Δ ∖ {[Var p]})
         by (rewrite (gmultiset_disj_union_difference' _ _ Hp) in Hin; ms).
         assert (Hin'' : Var p ∈ Δ ∖ {[p → θ2]}) by now apply in_difference.
         exhibit Hin'' 2. exch 0; exch 1. apply ImpLVar.
         exch 1. exch 0. peapply HA. rewrite <- difference_singleton by trivial. reflexivity.
      -- intro; constructor 2.
    * apply make_conj_sound_L. constructor 4. exch 0. exch 1. exch 0. apply ImpLVar.
      exch 0. apply weakening. exch 0...
  + constructor 2.
  + simpl; exch 0. apply ImpLAnd. apply make_impl_complete_L2. exch 0...
  + simpl; exch 0. apply ImpLOr. exch 1. exch 0...
  + apply make_conj_sound_L. exch 0. apply ImpLImp; exch 0.
      * apply AndL...
      * apply AndL. exch 0. apply weakening, HA.
  + exch 0. simpl. exch 0. apply AndL. exch 1; exch 0. apply ImpBox.
      * box_tac. box_tac. exch 0; exch 1; exch 0. apply weakening. exch 1; exch 0. apply ImpL.
         -- auto with proof.
         -- apply HA.
      * exch 1; exch 0. apply weakening. exch 0. auto with proof.
- auto with proof.
Qed.

Proposition entail_correct Δ ϕ : (Δ ⊢ E (Δ, ϕ)) * (Δ•A (Δ, ϕ) ⊢ ϕ).
Proof.
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
destruct ψ; unfold e_rule; exhibit Hin 0.
- case decide; intro; subst; simpl; auto using HE with proof.
- auto with proof.
- auto 3 with proof.
- apply make_disj_sound_R, OrL.
  + apply OrR1, HE. order_tac.
  + apply OrR2, HE. order_tac.
- destruct ψ1; auto 3 using HE with proof.
  + case decide; intro Hp.
    * subst. case decide; intro Hp.
      -- assert(Hin'' : Var p ∈ Δ ∖ {[p → ψ2]}) by (apply in_difference; trivial; discriminate).
         exhibit Hin'' 1. apply ImpLVar.
         peapply (HE (Δ ∖ {[p → ψ2]}•ψ2) ϕ). auto with proof.
         rewrite <- difference_singleton; trivial.
      -- apply ImpR, ExFalso.
    * apply make_impl_sound_R, ImpR. exch 0. apply ImpLVar. exch 0. apply weakening, HE. order_tac.
  + remember (Δ ∖ {[(ψ1_1 → ψ1_2) → ψ2]}) as Δ'.
      apply make_impl_sound_R, ImpR. apply make_impl_sound_L. exch 0. apply ImpLImp.
      * exch 0. auto with proof.
      * exch 0. auto with proof.
  + foldEA. apply ImpR. exch 0. apply ImpBox.
         --  box_tac. exch 0; exch 1; exch 0. apply ImpL. 
            ++ apply weakening, HE. order_tac.
            ++ apply HA. order_tac.
         -- exch 0; apply weakening, HE. order_tac.
-  apply BoxR. apply weakening. box_tac. simpl. apply HE. order_tac.
}
(* A *)
apply make_disj_sound_L, OrL.
- apply disjunction_L. intros φ Hin.
  apply in_in_map in Hin as (φ' & Heq & Hφ'). subst φ.
  apply a_rule_env_spec; intros; split ; apply HE || apply HA; order_tac.
- destruct ϕ; simpl; auto using HE with proof.
  + case decide; intro; subst; [constructor 2|constructor 1].
  + apply make_conj_sound_L, AndR; apply AndL; auto using HE with proof.
  + apply ImpR. exch 0. apply make_impl_sound_L, ImpL; auto using HE, HA with proof.
  + foldEA. apply BoxR. box_tac. exch 0. apply make_impl_sound_L, ImpL.
      * apply weakening, HE. order_tac.
      * apply HA. order_tac.
Qed.

End EntailmentCorrect.

(** ** Uniformity *)
Section PropQuantCorrect.

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
(Γ•e_rule (λ pe (_ : pe ≺· (Δ, φ')),  EA pe)  φ Hin) ⊢ θ ->
Γ•E (Δ, φ') ⊢ θ.
Proof.
intro Hp. rewrite E_eq.
destruct (@in_map_in _ _ _  (e_rule (λ pe (_ : pe ≺· (Δ, φ')), EA pe)) _ Hin) as [Hin' Hrule].
eapply conjunction_L.
- apply Hrule.
- exact Hp.
Qed.

Lemma A_right {Γ} {Δ} {φ φ'} (Hin : φ ∈ Δ) :
Γ ⊢ a_rule_env (λ pe (_ : pe ≺· (Δ, φ')), EA pe) φ Hin ->
Γ ⊢ A (Δ, φ').
Proof. intro Hp. rewrite A_eq.
destruct (@in_map_in _ _ _  (a_rule_env (λ pe (_ : pe ≺· (Δ, φ')), EA pe)) _ Hin) as [Hin' Hrule].
eapply make_disj_sound_R, OrR1, disjunction_R.
- exact Hrule.
- exact Hp.
Qed.

(* TODO: move *)
Lemma open_boxes_case Δ : {φ | (□ φ) ∈ Δ} + {Δ ≡ ⊗Δ}.
Proof.
unfold open_boxes.
induction Δ as [|ψ Δ IH] using gmultiset_rec.
- right. ms.
- case_eq(is_box ψ); intro Hbox.
  + left. exists (⊙ψ).
      destruct ψ; try discriminate Hbox. ms.
  + destruct IH as [[φ Hφ]| Heq].
     * left. exists φ. ms.
     * right. symmetry. etransitivity.
        -- apply env_equiv_eq, list_to_set_disj_perm, Permutation_map.
            apply gmultiset_elements_disj_union.
        -- rewrite map_app, list_to_set_disj_app. rewrite <- Heq. apply env_equiv_eq.
            f_equal.
            unfold elements. apply is_not_box_open_box in Hbox.  rewrite <- Hbox at 2.
            transitivity (list_to_set_disj (map open_box (id [ψ])) : env).
            ++ apply list_to_set_disj_perm, Permutation_map.
                    apply Permutation_refl', gmultiset_elements_singleton.
            ++ simpl. ms.
Qed.


Proposition pq_correct Γ Δ ϕ: (∀ φ0, φ0 ∈ Γ -> ¬ occurs_in p φ0) -> (Γ ⊎ Δ ⊢ ϕ) ->
  (¬ occurs_in p ϕ -> Γ•E (Δ, ϕ) ⊢ ϕ) *
  (Γ•E (Δ, ϕ) ⊢ A (Δ, ϕ)).
Proof.
(* we want to use an E rule *)
Ltac Etac := foldEA; intros; match goal with | Hin : ?a ∈ ?Δ |- _•E (?Δ, _) ⊢ _=> apply (E_left Hin); unfold e_rule end.

(* we want to use an A rule defined in a_rule_env *)
Ltac Atac := foldEA; match goal with | Hin : ?a ∈ ?Δ |- _  ⊢ A (?Δ, _) => apply (A_right Hin); unfold a_rule_env end.

(* we want to use an A rule defined in a_rule_form *)
Ltac Atac' := foldEA; rewrite A_eq; apply make_disj_sound_R, OrR2; simpl.

Ltac occ := simpl; tauto ||
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

Ltac equiv_tac :=
multimatch goal with
| Heq' : _•_ ≡ _ |- _ => fail
| Heq' : _ ≡ _ |- _ ≡ _ =>
  try (rewrite <- difference_singleton; trivial);
  rewrite Heq';
  try (rewrite union_difference_L by trivial);
  try (rewrite union_difference_R by trivial);
  try ms
end.

intros Hnin Hp.
remember (Γ ⊎ Δ) as Γ' eqn:HH.
assert (Heq: Γ' ≡ Γ ⊎ Δ) by ms. clear HH.
revert Heq.
dependent induction Hp generalizing Γ Δ Hnin; intro Heq;
try (apply env_add_inv in Heq; [|discriminate]);

(* try and solve the easy case where the main formula is on the left *)
try match goal with
| H : (?Γ0•?a•?b) ≡ Γ ⊎ Δ |- _ => idtac
| H : (?Γ0•?a) ≡ Γ ⊎ Δ |- _ => rename H into Heq;
  assert(Hin : a ∈ (Γ0•a)) by ms; rewrite Heq in Hin;
  pose(Heq' := Heq); apply env_add_inv' in Heq';
  try (case (decide (a ∈ Γ)); intro Hin0;
  [split; intros; exhibit Hin0 1|
   case (decide (a ∈ Δ)); intro Hin0';
  [|apply gmultiset_elem_of_disj_union in Hin; exfalso; tauto]])
end; simpl.

(* Atom *)
- auto 2 with proof.
- Atac'. case decide; intro; subst; [exfalso; now apply (Hnin _ Hin0)|]; auto with proof.
- split; Etac; case decide; intro; subst; try tauto; auto with proof.
  + Atac. repeat rewrite decide_True by trivial. auto with proof.
  + fold E. apply make_conj_sound_L, AndL. Atac. repeat rewrite decide_False by trivial.
    Atac'. rewrite decide_False by trivial. apply Atom.
(* ExFalso *)
- auto 2 with proof.
- auto 2 with proof.
-  split; Etac; auto with proof.
(* AndR *)
- destruct (IHHp1 _ _ Hnin Heq) as (PE & PEA).
  destruct (IHHp2 _ _ Hnin Heq) as (PE' & PEA').
  split.
  + intro Hocc. simpl in Hocc.
    apply AndR; erewrite E_irr; apply IHHp2 || apply IHHp1; tauto.
  + Atac'. apply make_conj_sound_R, AndR; erewrite E_irr; eassumption.
(* AndL *)
- exch 0. apply AndL. exch 1; exch 0. apply IHHp; trivial. occ. equiv_tac.
- exch 0. apply AndL. exch 1; exch 0. apply IHHp; trivial. occ. equiv_tac.
-  split.
   + Etac. apply IHHp; auto. equiv_tac.
   + Atac. Etac. apply IHHp; auto. equiv_tac.
(* OrR1 & OrR2 *)
- split.
  + intro Hocc. apply OrR1. erewrite E_irr; apply IHHp; tauto.
  + rewrite A_eq. apply make_disj_sound_R, OrR2.
      apply make_disj_sound_R, OrR1; erewrite E_irr.
      apply IHHp; auto.
- simpl. split.
  + intro Hocc. apply OrR2. erewrite E_irr; apply IHHp; tauto.
  + rewrite A_eq. apply make_disj_sound_R, OrR2.
       apply make_disj_sound_R, OrR2; erewrite E_irr.
       apply IHHp; auto.
(* OrL *)
- exch 0. apply OrL; exch 0.
 + apply IHHp1; trivial. occ. equiv_tac.
 + apply IHHp2; trivial. occ. equiv_tac.
- exch 0. apply OrL; exch 0.
  + apply IHHp1. occ. equiv_tac.
  + apply IHHp2. occ. equiv_tac.
- split.
  + Etac. apply make_disj_sound_L, OrL; [apply IHHp1| apply IHHp2]; trivial;
      rewrite Heq', union_difference_R by trivial; ms.
  + Atac. apply weakening. apply make_conj_sound_R,AndR, make_impl_sound_R.
    * apply make_impl_sound_R, ImpR. apply IHHp1; [tauto|equiv_tac].
    * apply ImpR. apply IHHp2; [tauto|equiv_tac].
(* ImpR *)
- destruct (IHHp Γ (Δ•φ)) as [IHa IHb]; [auto|ms|].
  split.
  + intro Hocc. apply ImpR. exch 0.
    erewrite E_irr. apply IHHp; auto. ms. equiv_tac.
  + Atac'. auto with proof.
(* ImpLVar *)
- pose(Heq' := Heq); apply env_add_inv' in Heq'.
  pose(Heq'' := Heq'); apply env_add_inv' in Heq''.
  case (decide ((Var p0 → φ) ∈ Γ)).
  + intro Hin0.
    assert (Hocc' := Hnin _ Hin0). simpl in Hocc'.
    case (decide (Var p0 ∈ Γ)); intro Hin1.
    * (* subcase 1: p0, (p0 → φ) ∈ Γ *)
      assert (Hin2 : Var p0 ∈ Γ ∖ {[Var p0 → φ]}) by (apply in_difference; trivial; discriminate).
      split; [intro Hocc|];
      exhibit Hin0 1; exhibit Hin2 2; exch 0; exch 1; apply ImpLVar; exch 1; exch 0;
      (peapply IHHp; trivial; [occ|equiv_tac]).
    * assert(Hin0' : Var p0 ∈ (Γ0•Var p0•(p0 → φ))) by ms. rewrite Heq in Hin0'.
      case (decide (Var p0 ∈ Δ)); intro Hp0;
      [|apply gmultiset_elem_of_disj_union in Hin0'; exfalso; tauto].
      (* subcase 3: p0 ∈ Δ ; (p0 → φ) ∈ Γ *)
      split; [Etac|Atac]; case decide; intro; subst.
      -- tauto.
      -- exhibit Hin0 1. apply make_conj_sound_L, AndL. exch 1; exch 0. apply ImpLVar. exch 1. exch 0.
         apply IHHp; [occ|equiv_tac|trivial].
      -- tauto.
      -- exhibit Hin0 1. Etac. rewrite decide_False by trivial.
         apply make_conj_sound_L, AndL. exch 1; exch 0. apply ImpLVar.
         exch 1; exch 0. apply IHHp. occ. equiv_tac.
  + intro.
    assert(Hin : (Var p0 → φ) ∈ (Γ0•Var p0•(p0 → φ))) by ms.
    rewrite Heq in Hin.
    case (decide ((Var p0 → φ) ∈ Δ)); intro Hin0;
    [|apply gmultiset_elem_of_disj_union in Hin; exfalso; tauto].
    case (decide (Var p0 ∈ Γ)); intro Hin1.
    * (* subcase 2: p0 ∈ Γ ; (p0 → φ) ∈ Δ *)
      do 2 exhibit Hin1 1.
      split; [intro Hocc|].
      -- Etac. case_decide; [auto with *|].
         apply make_impl_sound_L, ImpLVar. apply IHHp; trivial. occ.
         rewrite Heq', union_difference_R, <- union_difference_L by trivial; ms.
      -- Etac. case_decide; [auto with *|].
         apply make_impl_sound_L, ImpLVar. Atac. repeat case_decide; auto 2 with proof; [tauto| tauto|].
         apply make_conj_sound_R, AndR; auto 2 with proof. apply IHHp; [occ|].
         rewrite Heq', union_difference_R, <- union_difference_L by trivial; ms.
    * assert(Hin': Var p0 ∈ Γ ⊎ Δ) by (rewrite <- Heq; ms).
      apply gmultiset_elem_of_disj_union in Hin'.
      case (decide (Var p0 ∈ Δ)); intro Hin1'; [|exfalso; tauto].
      (* subcase 4: p0,(p0 → φ) ∈ Δ *)
      case (decide (p = p0)); intro.
      -- (* subsubcase p = p0 *)
        subst. split; Etac; repeat rewrite decide_True by trivial.
        ++ apply IHHp; [tauto|equiv_tac|trivial].
        ++ Atac. repeat rewrite decide_True by trivial.
           apply IHHp; [tauto|equiv_tac].
      -- (* subsubcase p ≠ p0 *)
         assert ((p0 → φ) ∈ (Δ ∖ {[Var p0]})) by (apply in_difference; trivial; discriminate).
         assert((Γ0•Var p0•φ) ≡ (Γ•Var p0) ⊎ (Δ ∖ {[Var p0]} ∖ {[p0 → φ]}•φ)). {
          rewrite (assoc disj_union).
          apply equiv_disj_union_compat_r.
          rewrite (comm disj_union Γ {[Var p0]}).
          rewrite <- (assoc disj_union).
          rewrite (comm disj_union {[Var p0]}).
          apply equiv_disj_union_compat_r.
          rewrite Heq''.
          rewrite union_difference_R by trivial.
          rewrite union_difference_R. ms.
          apply in_difference. discriminate. trivial.
         } (* not pretty *)
         split; Etac; rewrite decide_False by trivial;
         apply make_conj_sound_L, AndL; exch 0; Etac; case decide; intro; try tauto.
         ++ apply make_impl_sound_L, ImpLVar. apply IHHp; trivial. occ.
         ++ Atac. case decide; intro; try tauto.
            apply make_impl_sound_L, ImpLVar. Atac; case decide; intro; try tauto.
            apply make_conj_sound_R, AndR; auto 2 with proof.
            apply IHHp; trivial. occ.
(* ImpLAnd *)
- exch 0. apply ImpLAnd. exch 0. apply IHHp; trivial; [occ|equiv_tac].
- exch 0. apply ImpLAnd. exch 0. apply IHHp; trivial; [occ|equiv_tac].
- split; Etac.
  + apply IHHp; trivial. equiv_tac.
  + Atac. simpl. apply IHHp; trivial. equiv_tac.
(* ImpLOr *)
- exch 0; apply ImpLOr. exch 1; exch 0. apply IHHp; [occ|equiv_tac|trivial].
- exch 0; apply ImpLOr. exch 1; exch 0. apply IHHp; [occ|equiv_tac].
- split; Etac.
  +  apply IHHp; trivial. equiv_tac.
  +  Atac. apply IHHp; [occ|equiv_tac].
(* ImpLImp *)
- (* subcase 1: ((φ1 → φ2) → φ3) ∈ Γ *)
  assert(ψ ≠ Var p) by (intro; subst; simpl in *; tauto).
  exch 0; apply ImpLImp; exch 0.
  + erewrite E_irr. apply IHHp1; [occ|equiv_tac|].
      simpl. apply Hnin in Hin0. simpl in *. tauto.
  + erewrite E_irr. apply IHHp2; [occ|equiv_tac|trivial].
- exch 0; apply ImpLImp; exch 0.
  + assert(IH: (Γ0•(φ2 → φ3)) ≡ (Γ ∖ {[(φ1 → φ2) → φ3]}•(φ2 → φ3)) ⊎ Δ) by equiv_tac.
    erewrite E_irr. apply IHHp1; [occ|equiv_tac| trivial].
    simpl. apply Hnin in Hin0. simpl in Hin0. tauto.
  +  apply IHHp2; [occ|equiv_tac].
- (* subcase 2: ((φ1 → φ2) → φ3) ∈ Δ *)
  split.
  + Etac. apply make_impl_sound_L2'. apply ImpLImp.
    * apply weakening. apply ImpR. foldEA.
       rewrite (E_irr (φ1 → φ2)). apply IHHp1; [occ|equiv_tac].
    * apply IHHp2; [occ|equiv_tac| trivial].
  + Atac. apply make_conj_sound_R, AndR.
    * apply weakening. apply make_impl_sound_R, ImpR. foldEA.
      rewrite (E_irr (φ1 → φ2)). apply IHHp1; [occ|equiv_tac].
    * Etac. simpl. apply make_impl_sound_L2', ImpLImp.
      -- apply weakening. apply ImpR. foldEA.
          rewrite (E_irr (φ1 → φ2)). apply IHHp1; [occ|equiv_tac].
      -- apply IHHp2. occ. equiv_tac.
- (* ImpBox, external *)
   destruct (open_boxes_case Δ) as [[θ Hθ] | Hequiv].
    + apply contraction. Etac. exch 1; exch 0; apply ImpBox.
        * box_tac. box_tac. exch 2; exch 1; exch 0. apply weakening. foldEA.
           erewrite E_irr with (ϕ' := φ1).
           exch 1; exch 0.
           apply IHHp1.
           -- occ.  intro HF. destruct (occurs_in_open_boxes _ _ _ HF Hin1) as (θ0 & Hθ0 & Hinθ).
               apply (Hnin θ0); ms.
           -- rewrite Heq'. assert(Hθ' := In_open_boxes _ _ Hθ).
              simpl in *. repeat rewrite open_boxes_remove by ms. rewrite open_boxes_disj_union.
              simpl. rewrite <- difference_singleton by trivial.
              assert((□ φ1 → φ2) ∈ ⊗Γ) by auto with proof. rewrite union_difference_L by trivial. ms.
          -- intro HF. apply (Hnin _ Hin0). simpl. tauto.
        * exch 0. apply weakening. exch 0. apply IHHp2; [occ|equiv_tac| trivial].
  + exch 0. apply ImpBox.
      * box_tac. exch 1; exch 0. apply open_box_L.
         erewrite E_irr with (ϕ' := φ1).
         apply IHHp1.
         -- occ. intro HF. destruct (occurs_in_open_boxes _ _ _ HF Hin1) as (θ0 & Hθ0 & Hinθ).
             apply (Hnin θ0); ms.
         -- rewrite Hequiv, Heq'. assert(Hθ' := In_open_boxes _ _ Hin0).
             repeat rewrite open_boxes_remove by ms. rewrite open_boxes_disj_union.
              simpl. rewrite union_difference_L by trivial. ms.
         -- intro HF. apply (Hnin _ Hin0). simpl. tauto.
     * exch 0. apply IHHp2; [occ | rewrite Heq'; equiv_tac | trivial].
- destruct (open_boxes_case Δ) as [[θ Hθ] | Hequiv].
    + apply contraction. Etac. exch 1; exch 0; apply ImpBox.
        * box_tac. box_tac. exch 2; exch 1; exch 0. apply weakening. foldEA.
           erewrite E_irr with (ϕ' := φ1).
           exch 1; exch 0.
           apply IHHp1.
         -- occ. intro HF. destruct (occurs_in_open_boxes _ _ _ HF Hin1) as (θ0 & Hθ0 & Hinθ).
             apply (Hnin θ0); ms.
         -- rewrite Heq'. assert(Hθ' := In_open_boxes _ _ Hin0).
             repeat rewrite open_boxes_remove by ms. rewrite open_boxes_disj_union.
              simpl. rewrite union_difference_L by trivial.
              rewrite <- difference_singleton by auto with proof. ms.
         -- intro HF. apply (Hnin _ Hin0). simpl. tauto.
        * exch 0. apply weakening. exch 0. apply IHHp2 ; [occ|equiv_tac].
  + erewrite E_irr with (ϕ' := φ1).
      exch 0. apply ImpBox. 
      * box_tac. exch 1; exch 0. apply open_box_L. apply IHHp1.
         -- occ. intro HF. destruct (occurs_in_open_boxes _ _ _ HF Hin1) as (θ0 & Hθ0 & Hinθ).
             apply (Hnin θ0); ms.
         -- rewrite Heq'. assert(Hθ' := In_open_boxes _ _ Hin0).
             repeat rewrite open_boxes_remove by ms. rewrite open_boxes_disj_union.
              simpl. rewrite union_difference_L by trivial. ms.
         -- intro HF. apply (Hnin _ Hin0). simpl. tauto.
      * erewrite E_irr with (ϕ' := ψ).
          exch 0. apply IHHp2. occ. rewrite Heq'. (* TODO: equiv_tac should do that *) equiv_tac.
- split; Etac.
  + foldEA. apply ImpBox.
        -- do 2 apply weakening. apply ImpR.
            erewrite E_irr with (ϕ' := φ1) by ms.
            apply IHHp1.
            ++ intros φ0 Hin1 HF. destruct (occurs_in_open_boxes _ _ _ HF Hin1) as (θ0 & Hθ0 & Hinθ).
                    apply (Hnin θ0); ms.
            ++ rewrite Heq'.
                    repeat rewrite open_boxes_remove by ms. rewrite open_boxes_disj_union.
                    simpl. rewrite union_difference_R by auto with proof. ms.
        -- apply IHHp2. occ. equiv_tac. trivial.
  + foldEA. Atac.  apply AndR.
     * apply ImpBox.
        -- do 2 apply weakening. apply ImpR.
            erewrite E_irr with (ϕ' := φ1).
            apply IHHp1.
            ++ intros φ0 Hin1 HF. destruct (occurs_in_open_boxes _ _ _ HF Hin1) as (θ0 & Hθ0 & Hinθ).
                    apply (Hnin θ0); ms.
            ++ rewrite Heq', union_difference_R, open_boxes_disj_union, open_boxes_remove by trivial. ms.
       -- apply BoxR. box_tac. do 2 apply weakening. apply ImpR. foldEA. 
           erewrite E_irr with (ϕ' := φ1) by ms.
           apply IHHp1.
            ++ intros φ0 Hin1 HF. destruct (occurs_in_open_boxes _ _ _ HF Hin1) as (θ0 & Hθ0 & Hinθ).
                    apply (Hnin θ0); ms.
            ++ rewrite Heq', union_difference_R, open_boxes_disj_union, open_boxes_remove by trivial. ms.
     * foldEA. apply ImpBox.
        ++ do 2 apply weakening. apply ImpR.
               erewrite E_irr with (ϕ' := φ1).
               apply IHHp1.
               ** intros φ0 Hφ0 HF. destruct (occurs_in_open_boxes _ _ _ HF Hφ0) as (θ0 & Hθ0 & Hinθ).
                     apply (Hnin θ0); ms.
               **  rewrite Heq'.
                     repeat rewrite open_boxes_remove by ms. rewrite open_boxes_disj_union.
                     simpl. rewrite union_difference_R. ms. auto with proof.
        ++ apply IHHp2; [occ|equiv_tac].
- split.
  + intro Hocc. destruct (open_boxes_case Δ) as [[θ Hθ] | Hequiv].
      * Etac. foldEA. apply BoxR. box_tac. exch 0.
        erewrite E_irr with (ϕ' := φ); apply IHHp.
        -- intros φ0 Hφ0 HF. apply gmultiset_elem_of_disj_union in Hφ0.
            destruct Hφ0 as [Hφ0|]; [|ms].
            destruct (occurs_in_open_boxes _ _ _ HF Hφ0) as (θ0 & Hθ0 & Hinθ). apply (Hnin θ0); ms.
        -- rewrite Heq.
            repeat rewrite open_boxes_remove by ms. rewrite open_boxes_disj_union.
            simpl. auto with proof. rewrite <- difference_singleton by auto with proof. ms.
        -- trivial.
      * apply BoxR. box_tac. exch 0. apply open_box_L.
         erewrite E_irr with (ϕ' := φ).
         apply IHHp.
         -- intros φ0 Hφ0 HF. apply gmultiset_elem_of_disj_union in Hφ0.
            destruct Hφ0 as [Hφ0|]; [|ms].
            destruct (occurs_in_open_boxes _ _ _ HF Hφ0) as (θ0 & Hθ0 & Hinθ). apply (Hnin θ0); ms.
         -- rewrite Hequiv, Heq. rewrite open_boxes_disj_union. ms.
         --  trivial.
  + Atac'. foldEA. apply BoxR. box_tac. apply weakening. erewrite E_irr with (ϕ' := φ).
       apply weakening. apply make_impl_sound_R, ImpR.
       apply IHHp.
       * intros φ0 Hφ0 HF. destruct (occurs_in_open_boxes _ _ _ HF Hφ0) as (θ0 & Hθ0 & Hinθ).
          apply (Hnin θ0); ms.
       * rewrite Heq, open_boxes_disj_union. ms.
Qed.

End PropQuantCorrect.

End Correctness.

End UniformInterpolation.

(** * Main uniform interpolation Theorem *)

Open Scope type_scope.


Lemma E_of_empty p φ : E p (∅, φ) = (Implies Bot Bot).
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
      destruct Hx as [Hneq [θ [Hθ Hocc]]]. apply gmultiset_elem_of_singleton in Hθ. subst.
      apply Hvarsφ in Hocc. destruct Hocc; subst; tauto.
  + apply entail_correct.
  + intros ψ Hψ Hyp. rewrite elem_of_list_In in Hp. unfold Ef. rewrite E_irr with (ϕ' := ψ).
      * peapply (pq_correct p ∅ {[φ]} ψ).
         -- intros θ Hin. inversion Hin.
         -- peapply Hyp.
         -- intro HF. apply Hψ in HF. tauto.
  + intros x Hx. apply (EA_vars p ∅ φ x) in Hx.
      destruct Hx as [Hneq [Hin | [θ [Hθ Hocc]]]].
      * apply Hvarsφ in Hin. destruct Hin; subst; tauto.
      * inversion Hθ.
  + peapply (entail_correct p ∅).
  + intros ψ Hψ Hyp. rewrite elem_of_list_In in Hp.
      apply (TopL_rev _ ⊥). peapply (pq_correct p {[ψ]} ∅ φ).
      * intros φ0 Hφ0. apply gmultiset_elem_of_singleton in Hφ0. subst. auto with *.
      * peapply Hyp.
      * now rewrite E_of_empty.
Qed.

