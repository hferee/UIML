Require Import ISL.Sequents ISL.SequentProps ISL.Order ISL.Optimizations ISL.Cut.

(* Definitions and properties about equivalent formulas and environments *)
Section Equivalence.

Context {K : Kind}.

Definition equiv_form (φ ψ : form) : Type := (φ ≼ ψ) * (ψ ≼ φ).

Lemma symmetric_equiv_form {φ ψ} : equiv_form φ ψ -> equiv_form ψ φ.
Proof. intros [H H']. now split. Qed.

Lemma equiv_form_R {φ ψ} : (equiv_form φ ψ) ->
  forall Γ, Provable Γ φ -> Provable Γ ψ.
Proof.
intros Heq g Hp. apply additive_cut with φ. (* cut is only required here in this file*)
- auto with proof.
- apply generalised_weakeningL. peapply Heq.
Qed.

Lemma equiv_form_L {φ ψ} : (equiv_form φ ψ) ->
  forall Γ θ, Γ • φ ⊢ θ -> Γ • ψ ⊢ θ.
Proof.
intros Heq Γ θ Hp. apply additive_cut with φ. (* cut is only required here in this file*)
- apply generalised_weakeningL. peapply Heq.
- auto with proof.
Qed.

Definition equiv_env Δ Δ': Set :=
 (∀ φ, list_to_set_disj Δ ⊢ φ ->  list_to_set_disj Δ' ⊢ φ) *
 (∀ φ, list_to_set_disj Δ' ⊢ φ ->  list_to_set_disj Δ ⊢ φ).


Lemma symmetric_equiv_env Δ Γ: equiv_env Δ Γ -> equiv_env Γ Δ .
Proof. intros [H1 H2]. split; trivial. Qed.

Lemma equiv_env_refl Δ : equiv_env Δ Δ.
Proof. split; trivial. Qed.

Lemma equiv_env_trans Δ Δ' Δ'' : equiv_env Δ Δ' -> equiv_env Δ' Δ'' -> equiv_env Δ Δ''.
Proof.
intros [H11 H12] [H21 H22]. split; intros; auto.
Qed.

Lemma equiv_env_L1 Γ Δ Δ' φ: (equiv_env Δ Δ') ->
  Γ ⊎ list_to_set_disj Δ ⊢ φ ->  Γ ⊎ list_to_set_disj Δ' ⊢ φ.
Proof.
intros [H1 _] Hp.
revert φ Hp.
induction Γ as [|x Γ] using gmultiset_rec; intros φ Hp.
- peapply H1. peapply Hp.
- peapply (ImpR_rev (Γ ⊎ list_to_set_disj Δ') x).
  apply IHΓ, ImpR. peapply Hp.
Qed.

Lemma equiv_env_equiv_form φ φ': equiv_env [φ] [φ'] -> equiv_form φ φ'.
Proof.
intros [He1 He2]; split; unfold Lindenbaum_Tarski_preorder.
- peapply (He2 φ'). simpl. peapply (generalised_axiom ∅).
- peapply (He1 φ). simpl. peapply (generalised_axiom ∅).
Qed.

Lemma equiv_form_equiv_env φ φ': equiv_form φ φ' -> equiv_env [φ] [φ'].
Proof.
intros [He1 He2]; split; unfold Lindenbaum_Tarski_preorder.
- intros f Hp. simpl. apply additive_cut with φ.
  + apply He2.
  + apply generalised_weakeningL. peapply Hp.
- intros f Hp. simpl. apply additive_cut with φ'.
  + apply He1.
  + apply generalised_weakeningL. peapply Hp.
Qed.

End Equivalence.

Global Infix "≡f" := equiv_form (at level 120).

Global Infix "≡e" := equiv_env (at level 120).


(* The module type of weight-decreasing simplification functions over
  environments and formulas is the minimum to define uniform interpolants *)

Module Type SimpT.
  (* The simplification functions *)
  Parameter simp_env : forall {K : Kind}, list (@form K) -> list (@form K).
  Parameter simp_form : forall {K : Kind}, (@form K) -> (@form K).
    (* Orders are preserved *)
  Parameter simp_env_order : forall {K : Kind}, forall Δ, env_order_refl (simp_env Δ) Δ.
  Parameter simp_form_weight: forall {K : Kind}, forall φ, weight(simp_form φ) <= weight φ.
  Global Hint Resolve simp_env_order : order.
  Global Hint Resolve simp_env_order : order.
  Global Hint Resolve simp_form_weight : order.
End SimpT.

Module Type SimpProps (Import S : SimpT).
  Parameter simp_env_pointed_env_order_L : forall {K : Kind},
    forall pe Δ φ, (pe ≺· (simp_env Δ, φ)) -> pe ≺· (Δ, φ).
  Parameter simp_env_env_order_L: forall {K : Kind}, forall Δ Δ0, (Δ0 ≺ simp_env Δ) -> Δ0 ≺ Δ.
  Parameter simp_env_nil: forall {K : Kind}, simp_env [] = [].
  Global Hint Resolve simp_env_pointed_env_order_L : order.
  Global Hint Resolve simp_env_env_order_L : order.
End SimpProps.

Module MakeSimpProps (Import S : SimpT) : SimpProps S.
  Definition simp_env_pointed_env_order_L {K : Kind} pe Δ φ:
    (pe ≺· (simp_env Δ, φ)) -> pe ≺· (Δ, φ).
  Proof. intro Hl. eapply env_order_lt_le_trans; eauto. simpl. auto with order. Qed.

  Definition simp_env_env_order_L {K : Kind} Δ Δ0: (Δ0 ≺ simp_env Δ) -> Δ0 ≺ Δ.
  Proof.
  intro Hl. eapply env_order_lt_le_trans; eauto. auto with order.
  Qed.

  Definition simp_env_nil {K : Kind} : simp_env [] = [].
  Proof.
  assert (Ho := (simp_env_order [])). unfold env_order_refl in Ho.
  destruct (simp_env []) as [|a l]. trivial.
  contradict Ho.
  unfold env_weight, list_sum. simpl.
  enough (0 < 5 ^ weight a) by lia.
  pose(weight_pos a).
  pose (Nat.pow_gt_1 5 (weight a)). lia.
  Qed.
End MakeSimpProps.

(* Soundness properties *)
Module Type SoundSimpT (Export S : SimpT).
  (* Simplifications are sound *)
  Parameter equiv_env_simp_env: forall {K : Kind} Δ, equiv_env (simp_env Δ) Δ.
  Parameter equiv_form_simp_form: forall {K : Kind} φ, equiv_form (simp_form φ) φ.

  (* The variable are preserved *)
  Parameter equiv_env_vars: forall {K : Kind} Δ x,
  (∃ θ : form, ((θ ∈ simp_env Δ) /\ occurs_in x θ)) ->
  ∃ θ : form, ((θ ∈ Δ) /\ occurs_in x θ).

  Parameter occurs_in_simp_form:
    forall {K : Kind} x φ, occurs_in x (simp_form φ) → occurs_in x φ.

  (* To be removed in the future *)
  Parameter simp_env_idempotent: forall {K : Kind} Δ, simp_env (simp_env Δ) = simp_env Δ.
End SoundSimpT.
