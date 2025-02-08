(** * Simplifications for formulas and contexts 

This file defines the main simplifications for formulas and contexts,
maintaining intuitionistic equivalence.

*)

Require Import Coq.Program.Equality.
Require Import Coq.Classes.RelationClasses.
Require Import ISL.Sequents ISL.SequentProps.
Require Import ISL.Order ISL.DecisionProcedure.
Require Import ISL.Cut.
Require Import ISL.Optimizations. (* NB This import must come last. *)
Require Import ISL.Simplifications.
From Equations Require Import Equations.


Module S <: SimpT.

(** ** Applicability of rules

  This section provides definitions for checking the applicability of various
  logical rules within a given context (list of formulas).
  The definitions use decidable existence checks to determine if specific
  patterns of formulas are present in the context.
*)


Definition applicable_AndL {K : Kind} (Γ : list form):
  {ψ1 & {ψ2 | (And ψ1 ψ2) ∈ Γ}} + (∀ ψ1 ψ2, (And ψ1 ψ2) ∈ Γ -> False).
Proof.
  pose (fA := (fun θ => match θ with |And _ _ => true | _ => false end)).
  destruct (exists_dec fA Γ) as [(θ & Hin & Hθ) | Hf].
  - left. subst fA. destruct θ. 3: { eexists. eexists. apply elem_of_list_In. eauto. }
    all:  auto with *.
  - right. intros ψ1 ψ2 Hψ. rewrite elem_of_list_In in Hψ. apply Hf in Hψ. subst fA. simpl in Hψ. tauto.
Defined.

Definition applicable_ImpLVar {K : Kind} (Γ : list form):
  {q & {ψ | Var q ∈ Γ /\ (Implies (Var q) ψ) ∈ Γ}} +
  (∀ q ψ, Var q ∈ Γ -> (Implies (Var q) ψ) ∈ Γ -> False).
Proof.
  pose (fIp :=λ p θ, match θ with | Implies (Var q) _ =>
    if decide (p = q) then true else false | _ => false end).
  pose (fp:= (fun θ => match θ with |Var p =>
    if (exists_dec (fIp p) Γ) then true else false | _ => false end)).
  destruct (exists_dec fp Γ) as [(θ & Hin & Hθ) | Hf].
  - left. subst fp. destruct θ. 2-6: auto with *.
    case exists_dec as [(ψ &Hinψ & Hψ)|] in Hθ; [|auto with *]. 
    unfold fIp in Hψ. destruct ψ.  1-4, 6: auto with *.
    destruct ψ1. 2-6: auto with *. case decide in Hψ; [|auto with *].
    subst. apply elem_of_list_In in Hinψ, Hin.
    do 2 eexists. split; eauto.
  - right. intros q ψ Hp Hψ. rewrite elem_of_list_In in Hp, Hψ.
    apply Hf in Hp. subst fp fIp.
    simpl in Hp. case exists_dec as [|Hf'] in Hp. auto with *.
    apply (Hf' _ Hψ). rewrite decide_True; trivial. auto with *.
Defined.

Definition applicable_ImpLAnd {K : Kind} (Γ : list form):
    {φ1 & {φ2 & {φ3 | (Implies (And φ1 φ2) φ3) ∈ Γ}}} +
    (∀ φ1 φ2 φ3, (Implies (And φ1 φ2) φ3) ∈ Γ -> False).
Proof.
    pose (fII := (fun θ => match θ with |Implies (And _ _) _ => true
                                        | _ => false end)).
   destruct (exists_dec fII Γ) as [(θ & Hin & Hθ) | Hf].
    - left. subst fII. destruct θ. 1-4, 6: auto with *.
      destruct θ1. 1-2,4-6: auto with *.
      do 3 eexists; apply elem_of_list_In; eauto.
    - right. intros ψ1 ψ2 ψ3 Hψ. rewrite elem_of_list_In in Hψ.
      apply Hf in Hψ. subst fII. simpl in Hψ. tauto.
Defined.

Definition applicable_ImpLOr {K : Kind} (Γ : list form):
    {φ1 & {φ2 & {φ3 |  (Implies (Or φ1 φ2) φ3) ∈ Γ}}} +
    (∀ φ1 φ2 φ3, (Implies (Or φ1 φ2) φ3) ∈ Γ -> False).
Proof.
    pose (fII := (fun θ => match θ with |Implies (Or _ _) _ => true | _ => false end)).
   destruct (exists_dec fII Γ) as [(θ & Hin & Hθ) | Hf].
    - left. subst fII. destruct θ. 1-4, 6: auto with *.
      destruct θ1. 1-3, 5-6: auto with *. do 3 eexists; apply elem_of_list_In; eauto.
    - right. intros ψ1 ψ2 ψ3 Hψ. rewrite elem_of_list_In in Hψ.
      apply Hf in Hψ. subst fII. simpl in Hψ. tauto.
Defined.


(* Probably very costly *)
Definition applicable_strong_weakening {K : Kind} (Γ : list form):
  {φ : form | φ ∈ Γ /\ exists (_ : list_to_set_disj (rm φ Γ) ⊢ φ), True}
  + (∀ φ, φ ∈ Γ -> forall (_ : list_to_set_disj (rm φ Γ) ⊢ φ), False).
Proof.
destruct (exists_dec (λ φ, if Provable_dec (rm φ Γ) φ then true else false) Γ) as [[φ [Hin Hφ]]| Hf].
- left. exists φ; split.
  + now apply elem_of_list_In.
  + destruct ((rm φ Γ) ⊢? φ). trivial. contradict Hφ.
- right. intros φ Hin Hφ. apply (Hf φ). now apply elem_of_list_In.
   destruct ((rm φ Γ) ⊢? φ). auto with *. tauto.
Defined.

(** ** Ternary if notation
  This section defines a set of functions and notations for handling ternary
  conditional logic. The functions [sumor_bind0], [sumor_bind1], [sumor_bind2], and
  [sumor_bind3] provide a way to handle different levels of nested dependent sums and
  propositions. Each function takes a sum type and applies a function to the left component 
  if it exists, or returns a default value otherwise. The notations
  `cond '?' A '⋮₀' B`, `cond '?' A '⋮₁' B`, `cond '?' A '⋮₂' B`, and `cond '?' A '⋮₃' B`
  are provided to simplify the usage of these functions.
  This notation is used in the definition of [simp_env].
*)
Definition sumor_bind0 {A} {B : Prop} {C}:
  A + B -> (A -> C) -> C -> C :=
λ qH f c,
match qH with
| inl a => f a
| inr _ => c
end.

Definition sumor_bind1 {A A'} {B : Prop} {C}:
  {q : A | A' q} + B -> (forall x (_ : A' x), C) -> C -> C :=
λ qH f c,
match qH with
| inl (exist _ q Hq) => f q Hq
| inr _ => c
end.

Definition sumor_bind2 {A A' A''} {B : Prop} {C}:
  {q : A & {r : A' | A'' q r}} + B -> (forall x y (_ : A'' x y), C) -> C -> C :=
λ qH f c,
match qH with
| inl (existT q (exist _ r Hq)) => f q r Hq
| inr _ => c
end.

Definition sumor_bind3 {A A' A'' A'''} {B : Prop} {C}:
  {q : A & {r : A' & { s : A'' | A''' q r s}}} + B -> 
  (forall x y z (_ : A''' x y z), C) -> C -> C :=
λ qH f c,
match qH with
| inl (existT q (existT r (exist _ s Hq))) => f q r s Hq
| inr _ => c
end.

Notation "cond '?' A '⋮₀' B" := (sumor_bind0 cond A B) (at level 150, right associativity).
Notation "cond '?' A '⋮₁' B" := (sumor_bind1 cond A B) (at level 150, right associativity).
Notation "cond '?' A '⋮₂' B" := (sumor_bind2 cond A B) (at level 150, right associativity).
Notation "cond '?' A '⋮₃' B" := (sumor_bind3 cond A B) (at level 150, right associativity).

Local Notation "Δ '•' φ" := (cons φ Δ) : list_scope.

(** ** Definition of contextual simplification *)

(** The [contextual_simp_form] function performs contextual simplification on a
  given formula [φ] within a context [Δ].
  It recursively simplifies conjunctions, disjunctions, and implications by
  considering the context in which each subformula appears.
*)

Equations contextual_simp_form {K : Kind} : list form -> form -> form :=
| Δ, φ1 ∧ φ2 := let φ2' := (contextual_simp_form (φ1 :: Δ) φ2) in
    choose_conj (contextual_simp_form (φ2' :: Δ) φ1) φ2';
| Δ, φ1 ∨ φ2 := choose_disj (contextual_simp_form Δ φ1) (contextual_simp_form Δ φ2);
| Δ, φ1 → φ2 := choose_impl (contextual_simp_form Δ φ1) (contextual_simp_form (φ1 :: Δ) φ2)
| Δ, φ => if (Δ ⊢? φ) then ⊤ else φ (* TODO: simplify under box *)
.

(** ** Weight lemmas
  This section contains several lemmas related to the properties of logical formulas
  and their weights in the context of the Lindenbaum-Tarski preorder. The lemmas
  are used to reason about the relationship between the weights of formulas and 
  their simplified forms.
*)

Lemma contextual_simp_form_weight {K : Kind} Δ (φ : @form K):
  contextual_simp_form Δ φ = ⊤ /\
       (φ = Bot 
    \/ (exists Heq : K = Modal, eq_rect K (fun K => @form K) φ Modal Heq = □ ⊥)
    \/ exists (v : variable), 
        (φ = v \/
         exists Heq : K = Modal, eq_rect K (fun K => @form K) φ Modal Heq = □ v)
    ) \/
  (weight (contextual_simp_form Δ φ) ≤ weight φ).
Proof.
induction φ; simp contextual_simp_form; simpl.
1, 2: (case Provable_dec; simpl; [left; intuition; eauto| right; lia]).
1-3:right; try pose (weight_pos φ1); try pose (weight_pos φ2).
- pose (contextual_simp_form (Δ • φ1) φ2) as φ2'.
  destruct (IHφ1 (φ2' :: Δ)) as [[Heq1 _]| Hle1];
  destruct (IHφ2 (φ1 :: Δ)) as [[Heq2 _]| Hle2];
   repeat rewrite ?Heq1, ?Heq2; subst φ2'.
  + setoid_rewrite choose_conj_topL. rewrite Heq2 in Heq1. rewrite Heq1. simpl. lia.
  + unfold choose_conj. rewrite Heq1.
    case_eq (obviously_smaller ⊤ (contextual_simp_form (φ1 :: Δ) φ2)).
      * intro Hf. contradict Hf. apply obviously_smaller_top_not_Eq.
      * intro. simpl; lia.
      * intro. destruct (IHφ2 (φ1 :: Δ)); lia.
  + setoid_rewrite choose_conj_topL. pose (weight_pos φ1); pose (weight_pos φ2).
    simpl. destruct (IHφ1 (⊤ :: Δ)) as [[e _]|]. rewrite e. simpl. lia. lia.
  + unfold choose_conj. destruct obviously_smaller; simpl; lia.
- destruct (IHφ1 Δ) as [[Heq1 _] | Hle1]; destruct (IHφ2 Δ) as [[Heq2 _] | Hle2];
   repeat rewrite ?Heq1, ?Heq2; unfold choose_disj.
  + rewrite (obviously_smaller_compatible_LT _ _).2. simpl; lia. apply generalised_axiom.
  + case_eq (obviously_smaller ⊤ (contextual_simp_form Δ φ2)).
      * intro Hf. contradict Hf. apply obviously_smaller_top_not_Eq.
      * intro. right. lia.
      * intro. simpl; lia.
  + rewrite (obviously_smaller_compatible_LT _ _).2. simpl; lia.
    auto with proof.
  + destruct obviously_smaller; simpl; lia.
- pose (weight_pos φ1). pose (weight_pos φ2).
  destruct (IHφ1 Δ) as [[Heq1 _] | Hle1];
  destruct (IHφ2 (φ1 :: Δ)) as [[Heq2 _] | Hle2];
   repeat rewrite ?Heq1, ?Heq2.
  + etransitivity. apply choose_impl_top_weight. simpl. lia.
  + etransitivity. apply choose_impl_top_weight. simpl. lia.
  + unfold choose_impl.
    rewrite (obviously_smaller_compatible_LT _ ⊤).2; simpl. lia.
      auto with proof.
  + etransitivity. apply choose_impl_weight. simpl. lia.
- dependent destruction φ.
  3-5:right; try pose (weight_pos φ1); try pose (weight_pos φ2);
      case Provable_dec; simpl; lia.
  + case Provable_dec; simpl; [| right; now lia].
    left; intuition; right; right; eexists; right. exists eq_refl. eauto.
  + case Provable_dec; simpl; [| right; now lia].
    left; intuition. right. left. exists eq_refl. eauto.
  + case Provable_dec; simpl; [| right; now lia]. pose (weight_pos φ). lia.
Qed.


(** ** Simplifying environments

This section contains the function [simp_env], which simplifies an environment (context) Δ.
If none of the left rules are applicable anymore to Δ, then the function calls 
[applicable_contextual_simp_form] to find a simplification for one of the formulas in Δ, given
the fact that it appears in context Δ. 
We also define [simp_form], which tries to simplify a formula in the empty context.
*)

Definition applicable_contextual_simp_form {K : Kind} Δ:
  {φ & {φ' | φ ∈ Δ /\ φ' = contextual_simp_form (rm φ Δ) φ /\ weight φ' < weight φ}} +
  (forall φ, φ ∈ Δ -> weight(contextual_simp_form (rm φ Δ) φ) ≥ weight φ).
Proof.
(* try not to do the simplification twice. *)
assert(Hs: forall φ, {φ' | φ' = contextual_simp_form (rm φ Δ) φ /\ weight φ' < weight φ} +
                     (weight(contextual_simp_form (rm φ Δ) φ) ≥ weight φ)).
{ intros φ. remember (contextual_simp_form (rm φ Δ) φ) as φ'.
case (decide (weight φ' < weight φ)).
- intro Hlt. left. exists φ'. tauto.
- right. lia.
}
destruct (exists_dec (λ φ, if Hs φ then true else false) Δ) as [[φ [Hin HH]]| Hf].
- destruct (Hs φ) as [[φ' [Heq Hw]]| Hf].
  + left. exists φ. exists φ'. repeat split; trivial. now apply elem_of_list_In. 
  + contradict HH.
- right. intros φ Hin. apply elem_of_list_In in Hin. apply Hf in Hin.
  destruct (Hs φ) as [|Hf']. auto with *. apply Hf'.
Defined.

Local Obligation Tactic := (simpl; intuition order_tac).

Section SimpEnv.
Context {K : Kind} .


Program Fixpoint simp_env (Δ : list form) {wf env_order Δ} : list form :=
    (* invertible left rules *)
    if Δ ⊢? ⊥ then [⊥] else
    applicable_AndL Δ ? λ δ₁ δ₂  _, simp_env ((rm (δ₁ ∧ δ₂) Δ•δ₁)•δ₂) ⋮₂
    applicable_ImpLVar Δ ? λ q ψ  _, simp_env ((rm (Var q → ψ) Δ • ψ)) ⋮₂
    applicable_ImpLAnd Δ ? λ δ₁ δ₂ δ₃  _, simp_env ((rm ((δ₁ ∧ δ₂)→ δ₃) Δ • (δ₁ → (δ₂ → δ₃)))) ⋮₃
    applicable_ImpLOr Δ ? λ δ₁ δ₂ δ₃  _, simp_env (rm ((δ₁ ∨ δ₂)→ δ₃) Δ • (δ₁ → δ₃) • (δ₂ → δ₃)) ⋮₃
    (* remove redundant assumptions *)
    applicable_strong_weakening Δ ? λ φ _, simp_env (rm φ Δ) ⋮₁
    (* simplify individual formulas in their context. should be done earlier ?
         this is probably quite costly *)
    applicable_contextual_simp_form Δ? λ φ φ' _, simp_env(rm φ Δ • φ') ⋮₂
    Δ
.
Next Obligation. apply Wf.measure_wf, wf_env_order. Qed.


Global Lemma simp_env_eq (Δ : list form): simp_env Δ =
    (* invertible left rules *)
    if Δ ⊢? ⊥ then [⊥] else
    applicable_AndL Δ ? λ δ₁ δ₂  _, simp_env ((rm (δ₁ ∧ δ₂) Δ•δ₁)•δ₂) ⋮₂
    applicable_ImpLVar Δ ? λ q ψ  _, simp_env ((rm (Var q → ψ) Δ • ψ)) ⋮₂
    applicable_ImpLAnd Δ ? λ δ₁ δ₂ δ₃  _, simp_env ((rm ((δ₁ ∧ δ₂)→ δ₃) Δ • (δ₁ → (δ₂ → δ₃)))) ⋮₃
    applicable_ImpLOr Δ ? λ δ₁ δ₂ δ₃  _, simp_env (rm ((δ₁ ∨ δ₂)→ δ₃) Δ • (δ₁ → δ₃) • (δ₂ → δ₃)) ⋮₃
    (* remove redundant assumptions *)
    (applicable_strong_weakening Δ ? λ φ _, simp_env (rm φ Δ) ⋮₁
    applicable_contextual_simp_form Δ? λ φ φ' _, simp_env(rm φ Δ • φ') ⋮₂
    Δ).
Proof.
simpl. unfold simp_env. simpl.
repeat rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl. split; trivial.
Qed.

End SimpEnv.

Definition simp_form {K : Kind} φ:= contextual_simp_form [] φ.

(* Simplification of formulas always decreases the weight.
  This is due to the fact that the only formulas with lower weight than ⊤
  are ⊥, v, □⊥, □v, which are not tautologies *)
Lemma simp_form_weight {K : Kind} φ : weight(simp_form φ) <= weight φ.
Proof.
unfold simp_form.
destruct (contextual_simp_form_weight [] φ) as [(_ & [Hbot|[[HK Hbox]|[v [Ht | [HK Hb]]]]] )|Hw];
subst; simp contextual_simp_form; simpl.
- case Provable_dec; [|simpl; lia]. intros (Hf&_).
  exfalso; apply bot_not_tautology. auto with proof.
- rewrite <- Eqdep.EqdepTheory.eq_rect_eq in Hbox. subst. simp contextual_simp_form.
  destruct Provable_dec as [(Hf&_)|]; [|simpl; lia].
  exfalso; apply box_bot_not_tautology. auto with proof.
- destruct Provable_dec as [(Hf&_)|]; [|simpl; lia].
  exfalso; apply (var_not_tautology v). auto with proof.
- rewrite <- Eqdep.EqdepTheory.eq_rect_eq in Hb. subst. simp contextual_simp_form.
  destruct Provable_dec as [(Hf&_)|]; [|simpl; lia].
  exfalso; apply (box_var_not_tautology v). auto with proof.
Qed.


(** ** Simplification and the weight ordering

In [simp_env_order], we show that the simplification [simp_env] always
decreases the weight of a context. We introduce a tactic [simp_env_tac]
for this, which is also used later.
*)

Ltac simp_env_tac :=
let Hf := fresh "Hf" in
match goal with
| |- context[sumor_bind2 ?cond ?A ?B] =>
    let φ1 := fresh "φ1" in let φ2 := fresh "φ2" in let Hc := fresh "Hc" in
    destruct cond as [(φ1 & φ2 & Hc) | Hf]
| |- context[sumor_bind3 ?cond ?A ?B] =>
    let φ1 := fresh "φ1" in let φ2 := fresh "φ2" in let φ3 := fresh "φ3" in let Hc := fresh "Hc" in
    destruct cond as [(φ1 & φ2 & φ3 & Hc) | Hf]
| |- context[sumor_bind1 ?cond ?A ?B] =>
    let φ1 := fresh "φ1" in let Hc := fresh "Hc" in
    destruct cond as [(φ1 & Hc) | Hf]
end; simpl.

Lemma simp_env_order {K : Kind} Δ : env_order_refl (simp_env Δ) Δ.
Proof.
revert Δ. apply (well_founded_induction_type wf_env_order). intros Δ Hind.
rewrite simp_env_eq.
case (Δ ⊢? ⊥).
{ intros [Hf _]. destruct Δ as [|φ Δ].
  + now apply bot_not_tautology in Hf.
  + unfold env_order_refl. do 2 rewrite env_weight_add. simpl. pose (weight_pos φ).
      replace 5 with (0 + 5^1) at 1 by trivial. apply Nat.add_le_mono.  lia.
      apply Nat.pow_le_mono_r; lia.
}
intro Hbot.
repeat simp_env_tac.
all: try (apply env_order_env_order_refl; eapply env_order_le_lt_trans; [apply Hind|]; intuition; order_tac).
apply env_order_self.
Qed.

Lemma simp_env_nil {K : Kind} : simp_env [] = [].
Proof.
assert(Ho := simp_env_order []). destruct (simp_env []) as [|φ Δ].
trivial.
contradict Ho. unfold env_order_refl. rewrite env_weight_add.
apply Nat.lt_nge.
unfold env_weight. simpl. pose(Order.pow5_gt_0 (weight φ)). lia.
Qed.
End S.


(** ** Simplification is provably equivalent

The goal in this section is to prove that the simplification of a formula
(in context) is equivalent to the original.
We prove in [contextual_simp_form_spec] that the function [contextual_simp_form]
creates equivalent formulas (in context).
This lets us then prove in [equiv_env_simp_env] that [simp_env] also creates
equivalent contexts.

*)

Module SoundS.
Import S.

Section Equivalence.

Local Ltac peapply' th := (erewrite proper_Provable;  [| |reflexivity]);  [eapply th|equiv_tac].

Ltac l_tac' := repeat rewrite list_to_set_disj_open_boxes;
    rewrite (proper_Provable _ _ (symmetry (list_to_set_disj_env_add _ _)) _ _ eq_refl)
|| rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (symmetry (list_to_set_disj_env_add _ _))) _ _ eq_refl)
|| rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (equiv_disj_union_compat_r (symmetry (list_to_set_disj_env_add _ _)))) _ _ eq_refl)
|| rewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r (equiv_disj_union_compat_r (symmetry (list_to_set_disj_env_add _ _))))) _ _ eq_refl).

Lemma contextual_simp_form_spec {K : Kind} Δ φ: φ ∈ Δ ->
  equiv_env (rm φ Δ • contextual_simp_form (rm φ Δ) φ) Δ.
Proof.
revert Δ. induction φ; intros Δ Hin; simp contextual_simp_form; simpl;
apply elem_of_list_to_set_disj in Hin.
- case Provable_dec; intro Hdec.
  + apply Provable_dec_of_Prop in Hdec.
       split.
      * intros φ Hp. exhibit Hin 0. apply weakening. apply additive_cut with ⊤.
      -- apply top_provable.
      -- peapply' Hp.
    * intros φ Hφ. simpl. peapply (weakening ⊤). apply additive_cut with v. exact Hdec.
       -- peapply' Hφ.
       -- equiv_tac.
  + split; intros φ Hp; peapply' Hp; equiv_tac.
- case Provable_dec; intro Hdec.
  + apply Provable_dec_of_Prop in Hdec.
       split.
    * intros φ Hp. exhibit Hin 0. apply weakening. apply additive_cut with ⊤.
      -- apply top_provable.
      -- peapply' Hp.
    * intros φ Hφ. peapply (weakening ⊤). apply additive_cut with ⊥. exact Hdec.
       -- peapply' Hφ.
       -- equiv_tac.
  + split; intros φ Hp; peapply' Hp; equiv_tac.
- simpl.
  pose (φ2' := contextual_simp_form (rm (φ1 ∧ φ2) Δ • φ1) φ2).
  assert(Hin2 : φ2 ∈ (φ2 :: φ1 :: rm (φ1 ∧ φ2) Δ)) by (left; trivial).
  assert(Hin1 : φ1 ∈ (φ1 :: φ2' :: rm (φ1 ∧ φ2) Δ)) by (left; trivial).
  split; intros φ Hp.
  + exhibit Hin 0. apply AndL.
    assert(HH := (IHφ2 _ Hin2).1). simpl rm in HH; destruct form_eq_dec; [|tauto ].
    peapply' HH. clear HH. do 2 l_tac'. exch 0.
    assert(HH := (IHφ1 _ Hin1).1). simpl rm in HH; destruct form_eq_dec; [|tauto ].
    peapply' HH. clear HH. do 2 l_tac'.
    eapply additive_cut. apply choose_conj_sound_L; [|apply weakening]; apply generalised_axiom.
    exch 0. apply weakening. exch 0. apply weakening. subst φ2'. peapply' Hp.
  + l_tac'.
      apply additive_cut with ((contextual_simp_form (φ2' :: rm (φ1 ∧ φ2) Δ) φ1) ∧ (contextual_simp_form (φ1 :: rm (φ1 ∧ φ2) Δ) φ2)).
    * apply generalised_weakeningL. peapply choose_conj_equiv_R.
      -- apply generalised_axiom.
      -- apply generalised_axiom.
      -- ms.
    * exch 0. apply weakening, AndL. exch 0.
      assert(Hin2' : φ2' ∈ (φ2' :: contextual_simp_form (rm (φ1 ∧ φ2) Δ • φ2') φ1 :: rm (φ1 ∧ φ2) Δ)) by (left; trivial).
      assert (HH := (IHφ1 _ Hin1).2).
      simpl rm in HH; case form_eq_dec in HH; [|tauto ].
      peapply' HH. clear HH. do 2 l_tac'. exch 0.
      assert (HH := (IHφ2 _ Hin2).2).
      simpl rm in HH; case form_eq_dec in HH; [|tauto ].
      peapply' HH. clear HH. do 2 l_tac'. apply AndL_rev. peapply' Hp.
- assert(Hin1 : φ1 ∈ (φ1 :: rm (φ1 ∨ φ2) Δ)) by (left; trivial).
  assert(Hin2 : φ2 ∈ (φ2 :: rm (φ1 ∨ φ2) Δ)) by (left; trivial).
  split; intros φ Hp.
  + exhibit Hin 0. apply OrL.
    * peapply' (IHφ1 _ Hin1).1.
       simpl rm. destruct form_eq_dec; [|tauto ]. l_tac'.
       eapply additive_cut.
       -- apply choose_disj_sound_L1, generalised_axiom.
       -- exch 0. apply weakening. peapply' Hp.
    * peapply' (IHφ2 _ Hin2).1.
       simpl rm. destruct form_eq_dec; [|tauto ]. l_tac'.
       eapply additive_cut.
       -- apply choose_disj_sound_L2, generalised_axiom.
       -- exch 0. apply weakening. peapply' Hp.
  + l_tac'.
      apply additive_cut with ((contextual_simp_form (rm (φ1 ∨ φ2) Δ) φ1) ∨ (contextual_simp_form (rm (φ1 ∨ φ2) Δ) φ2)).
    * apply generalised_weakeningL. peapply choose_disj_equiv_R.
      -- apply generalised_axiom.
      -- apply generalised_axiom.
      -- ms.
    * exch 0. apply weakening.
       destruct (OrL_rev (list_to_set_disj (rm (φ1 ∨ φ2) Δ)) φ1 φ2 φ) as [Hp1 Hp2].
      -- peapply' Hp.
      -- apply OrL.
        ++ peapply (IHφ1 _ Hin1);
                [| simpl rm; destruct form_eq_dec; [|tauto ]; ms]. peapply Hp1.
        ++ peapply (IHφ2 _ Hin2);
                [| simpl rm; destruct form_eq_dec; [|tauto ]; ms]. peapply Hp2.
- assert(Hin1 : φ1 ∈ (φ1 :: rm (φ1 → φ2) Δ)) by (left; trivial).
  assert(Hin2 : φ2 ∈ (φ2 :: φ1 :: rm (φ1 → φ2) Δ)) by (left; trivial).
  split; intros φ Hp.
  + exhibit Hin 0.
       apply additive_cut with ( choose_impl (contextual_simp_form (rm (φ1 → φ2) Δ) φ1)
            (contextual_simp_form (rm (φ1 → φ2) Δ • φ1) φ2)).
       * apply choose_impl_sound_R, ImpR. exch 0.
          assert (Hp1:=(IHφ1 _ Hin1).2).
          simpl rm in Hp1. destruct form_eq_dec in Hp1; [|tauto ].
            apply ImpR_rev. peapply' Hp1. l_tac'.
            apply ImpR, ImpL. exch 0. apply generalised_axiom.
            peapply' (IHφ2 _ Hin2).1.
            simpl rm. destruct form_eq_dec; [|tauto ]. l_tac'. apply generalised_axiom.
       * exch 0. apply weakening. peapply' Hp.
  + l_tac'. apply choose_impl_sound_L. apply additive_cut with (φ1 → φ2).
    * apply ImpR. exch 0. apply ImpL.
      -- apply weakening. peapply (IHφ1 _ Hin1).1.
          l_tac'. simpl rm. destruct form_eq_dec; [|tauto ]. apply generalised_axiom.
      -- l_tac. peapply' (IHφ2 _ Hin2).2.
        ++ l_tac'. apply generalised_axiom.
        ++ simpl rm. destruct form_eq_dec; [|tauto ]. equiv_tac.
    * exch 0. apply weakening. peapply' Hp.
- destruct Provable_dec as [Hdec|Hdec].
  + apply Provable_dec_of_Prop in Hdec.
       split.
    * intros φ0 Hp. exhibit Hin 0. apply weakening. apply additive_cut with ⊤.
      -- apply top_provable.
      -- peapply' Hp.
    * intros φ0 Hφ. l_tac'.  apply weakening. apply additive_cut with (□ φ). exact Hdec.
       peapply' Hφ.
  + split; intros φ0 Hp; peapply' Hp; equiv_tac.
Qed.

(* TODO: move *)
Hint Resolve elem_of_list_to_set_disj : proof.

Lemma equiv_env_simp_env {K : Kind} Δ: equiv_env (simp_env Δ) Δ.
Proof.
revert Δ. apply (well_founded_induction_type wf_env_order). intros Δ Hind.
rewrite simp_env_eq.
case (Δ ⊢? ⊥).
{ intro Hf. apply Provable_dec_of_Prop in Hf.
  split; intros φ Hp.
  + apply exfalso. assumption.
  + simpl. peapply (ExFalso ∅).
}
intro Hbot.
repeat simp_env_tac; (try (eapply equiv_env_trans; [apply Hind; intuition; order_tac|])).
- apply elem_of_list_to_set_disj in Hc. 
  split; intros φ Hp.
  + exhibit Hc 0. apply AndL. peapply' Hp.
  + do 2 l_tac'. apply AndL_rev. peapply' Hp.
- destruct Hc as [Hc1 Hc2]. apply elem_of_list_to_set_disj in Hc1, Hc2.
   assert(Hc3: Var φ1 ∈ (list_to_set_disj Δ ∖ {[φ1 → φ2]} : env)).
      { apply in_difference. intro HF. discriminate HF. assumption. }
  split; intros φ Hp.
  + exhibit Hc2 0. exhibit Hc3 1. peapply ImpLVar. peapply' Hp.
  + l_tac'. peapply' (ImpLVar_rev (list_to_set_disj (rm φ1 (rm (φ1 → φ2) Δ))) φ1 φ2).
      peapply' Hp.
- apply elem_of_list_to_set_disj in Hc0. 
  split; intros φ Hp.
  + exhibit Hc0 0. apply ImpLAnd. peapply' Hp.
  + l_tac'. apply ImpLAnd_rev. peapply' Hp.
-  apply elem_of_list_to_set_disj in Hc0. 
  split; intros φ Hp.
  + exhibit Hc0 0. apply ImpLOr. peapply' Hp.
  + do 2 l_tac'. apply ImpLOr_rev. peapply' Hp.
- destruct Hc0 as [Hc0 Hφ1]. apply elem_of_list_to_set_disj in Hc0.
  split; intros φ Hp.
  + exhibit Hc0 0. apply weakening. peapply' Hp.
  + apply Provable_dec_of_Prop in Hφ1.
      apply additive_cut with φ0. trivial. peapply' Hp.
- destruct Hc as [Hc [Heq Hw]]. apply elem_of_list_to_set_disj in Hc.
  subst. apply contextual_simp_form_spec. now apply elem_of_list_to_set_disj.
- apply elem_of_list_to_set_disj in Hc. 
  split; intros φ Hp.
  + exhibit Hc 0. apply ImpLAnd. peapply' Hp.
  + l_tac'. apply ImpLAnd_rev. peapply' Hp.
-  apply elem_of_list_to_set_disj in Hc. 
  split; intros φ Hp.
  + exhibit Hc 0. apply ImpLOr. peapply' Hp.
  + do 2 l_tac'. apply ImpLOr_rev. peapply' Hp.
- destruct Hc as [Hc Hφ1]. apply elem_of_list_to_set_disj in Hc.
  split; intros φ Hp.
  + exhibit Hc 0. apply weakening. peapply' Hp.
  + apply Provable_dec_of_Prop in Hφ1.
      apply additive_cut with φ1. trivial. peapply' Hp.
- apply equiv_env_refl.
Qed.

Lemma equiv_form_simp_form {K : Kind} φ : equiv_form (simp_form φ) φ.
Proof.
assert (Hφ := contextual_simp_form_spec [φ] φ).
simpl in Hφ. destruct form_eq_dec in Hφ; [|tauto].
apply equiv_env_equiv_form. apply Hφ. auto with *.
Qed.

End Equivalence.

Section Variables.

(** ** Simplification does not introduce new variables

We show that simplifying a context or formula does not introduce any new variables.
This is important for the application to Pitts' algorithm, where one of the correctness properties
is an upper bound on the variables that may be used in the constructed formula.
*)

Local Ltac occ p := simpl; tauto ||
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

Lemma  occurs_in_contextual_simp_form {K : Kind} x Δ φ:
  occurs_in x (contextual_simp_form Δ φ) -> occurs_in x φ.
Proof.
revert Δ. induction φ; intro Δ; simp contextual_simp_form; try destruct Provable_dec;
intros; simpl in *; try tauto.
- apply occurs_in_choose_conj in H. pose (φ2' := contextual_simp_form (Δ • φ1) φ2).
  specialize (IHφ1 (φ2' :: Δ)); specialize (IHφ2 (φ1 :: Δ)). tauto.
- apply occurs_in_choose_disj in H.  specialize (IHφ1 Δ); specialize (IHφ2 Δ). tauto.
- apply occurs_in_choose_impl in H. specialize (IHφ1 Δ); specialize (IHφ2 (φ1 :: Δ)). tauto.
Qed.

Lemma equiv_env_vars {K : Kind} Δ x:
  (∃ θ : form, ((θ ∈ simp_env Δ) /\ occurs_in x θ)) ->
  ∃ θ : form, ((θ ∈ Δ) /\ occurs_in x θ).
Proof.
revert Δ. refine (well_founded_induction_type wf_env_order _ _). intros Δ Hind.
rewrite (simp_env_eq Δ).
case (Δ ⊢? ⊥).
{ intros _ [θ [Hin Hocc]]. apply elem_of_list_singleton in Hin.  subst. contradict Hocc. }
intro Hbot.
repeat simp_env_tac; trivial.

all:(decompose record Hc; try decompose record Hc0;
  intro Hocc; apply Hind in Hocc; [|order_tac]; destruct Hocc as [θ [Hin Hocc]];
  apply elem_of_list_to_set_disj in Hin;
  repeat rewrite <- ?list_to_set_disj_env_add, gmultiset_elem_of_disj_union in Hin;
  repeat ((try apply elem_of_list_to_set_disj, elem_of_list_In, in_rm, elem_of_list_In in Hin;
      try apply gmultiset_elem_of_singleton in Hin;
      try apply occurs_in_contextual_simp_form in Hocc;
      subst; try solve[eexists; split; simpl in *; eauto; simpl in *; eauto || tauto]) ||
  destruct Hin as [Hin | Hin] ||
  match goal with | Hin : ?a ∈ _ |- _ => exists a; split; trivial; simpl in *; tauto end)).
Qed.

Lemma occurs_in_simp_form {K : Kind} x φ: occurs_in x (simp_form φ) → occurs_in x φ.
Proof. apply occurs_in_contextual_simp_form. Qed.

End Variables.


(** The simp_env function is idempotent. *)
Lemma simp_env_idempotent {K : Kind} Δ: simp_env (simp_env Δ) = simp_env Δ.
Proof.
revert Δ. apply (well_founded_induction_type wf_env_order). intros Δ Hind.
rewrite (simp_env_eq Δ).
case (Δ ⊢? ⊥).
{ intro e. rewrite simp_env_eq. case ([⊥] ⊢? ⊥). trivial. intro Hf. contradict Hf.
  simpl. peapply (ExFalso ∅). }
intro Hbot.
repeat simp_env_tac; (try (intuition; apply Hind; order_tac)).
rewrite simp_env_eq.
case (Δ ⊢? ⊥); [intros [He _]; tauto| intros _].
repeat simp_env_tac; try (try (apply Provable_dec_of_Prop in Hc); contradict Hc; intuition; eauto); trivial.
- eapply Nat.le_ngt. eapply Hf1. eauto. subst; trivial.
- eapply Nat.le_ngt. eapply Hf1. eauto. subst; trivial.
- eapply Hf4. eauto. now apply Provable_dec_of_Prop.
Qed.
(* TODO clean ?
  Definition equiv_env_simp_env := equiv_env_simp_env.
  Definition equiv_form_simp_form:= equiv_form_simp_form.
  Definition equiv_env_vars := equiv_env_vars.
  Definition occurs_in_simp_form := occurs_in_simp_form.
  Definition simp_env_idempotent := simp_env_idempotent.
  Definition simp_env_nil := simp_env_nil.
  *)
End SoundS.

