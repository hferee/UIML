Require Import Coq.Program.Equality.
Require Import ISL.Sequents ISL.SequentProps.
Require Import ISL.Order ISL.DecisionProcedure.
Require Import Coq.Classes.RelationClasses.

Definition applicable_AndL (Γ : list form): {ψ1 & {ψ2 | (And ψ1 ψ2) ∈ Γ}} + (∀ ψ1 ψ2, (And ψ1 ψ2) ∈ Γ -> False).
Proof.
  pose (fA := (fun θ => match θ with |And _ _ => true | _ => false end)).
  destruct (exists_dec fA Γ) as [(θ & Hin & Hθ) | Hf].
  - left. subst fA. destruct θ. 3: { eexists. eexists. apply elem_of_list_In. eauto. }
    all:  auto with *.
  - right. intros ψ1 ψ2 Hψ. rewrite elem_of_list_In in Hψ. apply Hf in Hψ. subst fA. simpl in Hψ. tauto.
Defined.

Definition applicable_ImpLVar (Γ : list form):
  {q & {ψ | Var q ∈ Γ /\ (Implies (Var q) ψ) ∈ Γ}} +
  (∀ q ψ, Var q ∈ Γ -> (Implies (Var q) ψ) ∈ Γ -> False).
Proof.
  pose (fIp :=λ p θ, match θ with | Implies (Var q) _ => if decide (p = q) then true else false | _ => false end).
  pose (fp:= (fun θ => match θ with |Var p => if (exists_dec (fIp p) Γ) then true else false | _ => false end)).
  destruct (exists_dec fp Γ) as [(θ & Hin & Hθ) | Hf].
  - left. subst fp. destruct θ. 2-6: auto with *.
    case exists_dec as [(ψ &Hinψ & Hψ)|] in Hθ; [|auto with *]. 
    unfold fIp in Hψ. destruct ψ.  1-4, 6: auto with *.
    destruct ψ1. 2-6: auto with *. case decide in Hψ; [|auto with *].
    subst. apply elem_of_list_In in Hinψ, Hin.
    do 2 eexists. split; eauto.
  - right. intros q ψ Hp Hψ. rewrite elem_of_list_In in Hp, Hψ. apply Hf in Hp. subst fp fIp.
    simpl in Hp. case exists_dec as [|Hf'] in Hp. auto with *.
    apply (Hf' _ Hψ). rewrite decide_True; trivial. auto with *.
Defined.

Definition applicable_ImpLAnd (Γ : list form):
    {φ1 & {φ2 & {φ3 | (Implies (And φ1 φ2) φ3) ∈ Γ}}} +
    (∀ φ1 φ2 φ3, (Implies (And φ1 φ2) φ3) ∈ Γ -> False).
Proof.
    pose (fII := (fun θ => match θ with |Implies (And _ _) _ => true | _ => false end)).
   destruct (exists_dec fII Γ) as [(θ & Hin & Hθ) | Hf].
    - left. subst fII. destruct θ. 1-4, 6: auto with *.
      destruct θ1. 1-2,4-6: auto with *. do 3 eexists; apply elem_of_list_In; eauto.
    - right. intros ψ1 ψ2 ψ3 Hψ. rewrite elem_of_list_In in Hψ. apply Hf in Hψ. subst fII. simpl in Hψ. tauto.
Defined.

Definition applicable_ImpLOr (Γ : list form):
    {φ1 & {φ2 & {φ3 |  (Implies (Or φ1 φ2) φ3) ∈ Γ}}} +
    (∀ φ1 φ2 φ3, (Implies (Or φ1 φ2) φ3) ∈ Γ -> False).
Proof.
    pose (fII := (fun θ => match θ with |Implies (Or _ _) _ => true | _ => false end)).
   destruct (exists_dec fII Γ) as [(θ & Hin & Hθ) | Hf].
    - left. subst fII. destruct θ. 1-4, 6: auto with *.
      destruct θ1. 1-3, 5-6: auto with *. do 3 eexists; apply elem_of_list_In; eauto.
    - right. intros ψ1 ψ2 ψ3 Hψ. rewrite elem_of_list_In in Hψ. apply Hf in Hψ. subst fII. simpl in Hψ. tauto.
Defined.

Definition sumor_bind0 {A} {B : Prop} {C}: A + B -> (A -> C) -> C -> C :=
λ qH f c,
match qH with
| inl a => f a
| inr _ => c
end.

Definition sumor_bind1 {A A'} {B : Prop} {C}: {q : A | A' q} + B -> (forall x (_ : A' x), C) -> C -> C :=
λ qH f c,
match qH with
| inl (exist _ q Hq) => f q Hq
| inr _ => c
end.

Definition sumor_bind2 {A A' A''} {B : Prop} {C}: {q : A & {r : A' | A'' q r}} + B -> (forall x y (_ : A'' x y), C) -> C -> C :=
λ qH f c,
match qH with
| inl (existT q (exist _ r Hq)) => f q r Hq
| inr _ => c
end.

Definition sumor_bind3 {A A' A'' A'''} {B : Prop} {C}:
  {q : A & {r : A' & { s : A'' | A''' q r s}}} + B -> (forall x y z (_ : A''' x y z), C) -> C -> C :=
λ qH f c,
match qH with
| inl (existT q (existT r (exist _ s Hq))) => f q r s Hq
| inr _ => c
end.

Notation "cond '?' A ':0' B" := (sumor_bind0 cond A B) (at level 150, right associativity).
Notation "cond '?' A ':1' B" := (sumor_bind1 cond A B) (at level 150, right associativity).
Notation "cond '?' A ':2' B" := (sumor_bind2 cond A B) (at level 150, right associativity).
Notation "cond '?' A ':3' B" := (sumor_bind3 cond A B) (at level 150, right associativity).

Local Notation "Δ '•' φ" := (cons φ Δ).

Infix "⊢?" := Provable_dec (at level 80).

(* Probably very costly *)
Definition applicable_strong_weakening (Γ : list form):
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

Local Obligation Tactic := (simpl; intuition order_tac).
Program Fixpoint simp_env (Δ : list form) {wf env_order Δ} : list form :=
    (* invertible left rules *)
    if Δ ⊢? ⊥ then [⊥] else
    applicable_AndL Δ ? λ δ₁ δ₂  _, simp_env ((rm (δ₁ ∧ δ₂) Δ•δ₁)•δ₂) :2
    applicable_ImpLVar Δ ? λ q ψ  _, simp_env ((rm (Var q → ψ) Δ • ψ)) :2
    applicable_ImpLAnd Δ ? λ δ₁ δ₂ δ₃  _, simp_env ((rm ((δ₁ ∧ δ₂)→ δ₃) Δ • (δ₁ → (δ₂ → δ₃)))) :3
    applicable_ImpLOr Δ ? λ δ₁ δ₂ δ₃  _, simp_env (rm ((δ₁ ∨ δ₂)→ δ₃) Δ • (δ₁ → δ₃) • (δ₂ → δ₃)) :3
    (* remove redundant assumptions *)
    applicable_strong_weakening Δ ? λ φ _, simp_env (rm φ Δ) :1
    Δ
.
Next Obligation. apply Wf.measure_wf, wf_env_order. Qed.

Lemma simp_env_eq (Δ : list form): simp_env Δ =
    (* invertible left rules *)
    if Δ ⊢? ⊥ then [⊥] else
    applicable_AndL Δ ? λ δ₁ δ₂  _, simp_env ((rm (δ₁ ∧ δ₂) Δ•δ₁)•δ₂) :2
    applicable_ImpLVar Δ ? λ q ψ  _, simp_env ((rm (Var q → ψ) Δ • ψ)) :2
    applicable_ImpLAnd Δ ? λ δ₁ δ₂ δ₃  _, simp_env ((rm ((δ₁ ∧ δ₂)→ δ₃) Δ • (δ₁ → (δ₂ → δ₃)))) :3
    applicable_ImpLOr Δ ? λ δ₁ δ₂ δ₃  _, simp_env (rm ((δ₁ ∨ δ₂)→ δ₃) Δ • (δ₁ → δ₃) • (δ₂ → δ₃)) :3
    (* remove redundant assumptions *)
    applicable_strong_weakening Δ ? λ φ _, simp_env (rm φ Δ) :1
    Δ.
Proof.
simpl. unfold simp_env. simpl.
repeat rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl. split; trivial.
Qed.

Definition simp_form φ:= ⋀ (simp_env [φ]).

Definition pointed_env_order_refl pe1 pe2 := env_order_refl (pe1.2 :: pe1.2 :: pe1.1) (pe2.2 :: pe2.2 :: pe2.1).

(* TODO: move *)

Lemma empty_entails_not_bot : (∅ ⊢ ⊥) -> False.
Proof.
intro Hf. dependent destruction Hf; simpl in *;
match goal with x : _ ⊎ {[+?φ+]} = _ |- _ =>
exfalso; eapply (gmultiset_elem_of_empty φ); setoid_rewrite <- x; ms end. 
Qed.

Lemma simp_env_order Δ : env_order_refl (simp_env Δ) Δ.
Proof.
revert Δ. apply (well_founded_induction_type wf_env_order). intros Δ Hind.
rewrite simp_env_eq.
case (Δ ⊢? ⊥).
{ intros [Hf _]. destruct Δ as [|φ Δ].
  + now apply empty_entails_not_bot in Hf.
  + rewrite env_weight_add.
  unfold env_order_refl. destruct φ.
    * admit.
    * destruct Δ as [|φ Δ].
      -- now right.
      -- left. unfold env_order, ltof, env_weight. simpl. pose (Order.pow5_gt_0 (weight φ)). lia.
    * left. unfold env_order, ltof, env_weight. simpl.
       replace 5 with (5 ^ 1) at 1 by trivial. lia.
       apply Nat.lt_le_trans with (5 ^ weight φ); [|lia].
       apply Nat.pow_lt_mono_r. lia. destruct φ. simpl. lia.
    nia.
     pose (Order.pow5_gt_0 (weight φ)). lia.
 intro. simpl. auto with proof.

Admitted.

Global Hint Resolve simp_env_order : order.

Lemma simp_env_pointed_env_order_L pe Δ φ: (pe ≺· (simp_env Δ, φ)) -> pe ≺· (Δ, φ).
Proof.
intro Hl. eapply env_order_lt_le_trans; eauto. simpl. auto with order.
Qed.

Lemma simp_env_env_order_L Δ Δ0: (Δ0 ≺ simp_env Δ) -> Δ0 ≺ Δ.
Proof.
intro Hl. eapply env_order_lt_le_trans; eauto. auto with order.
Qed.

Global Hint Resolve simp_env_pointed_env_order_L : order.
Global Hint Resolve simp_env_env_order_L : order.

Section Equivalence.

Definition equiv_form φ ψ : Type := (φ ≼ ψ) * (ψ ≼ φ).

Definition equiv_env Δ Γ: Set := (list_to_set_disj Δ ⊢ ⋀ Γ) * (list_to_set_disj Γ ⊢ ⋀ Δ).

Lemma symmetric_equiv_env Δ Γ: equiv_env Δ Γ -> equiv_env Γ Δ .
Proof. intros [H1 H2]. split; trivial. Qed.

Lemma equiv_env_L0 Δ Δ' φ: (equiv_env Δ Δ') ->
  list_to_set_disj Δ ⊢ φ ->  list_to_set_disj Δ' ⊢ φ.
Proof.
intros [H1 H2].
Admitted.


Lemma equiv_env_L1 Γ Δ Δ' φ: (equiv_env Δ Δ') ->
  Γ ⊎ list_to_set_disj Δ ⊢ φ ->  Γ ⊎ list_to_set_disj Δ' ⊢ φ.
Proof.
intros [H1 H2].
Admitted.

Lemma equiv_env_L2 Γ Δ Δ' φ: (equiv_env Δ Δ') ->
  list_to_set_disj Δ  ⊎ Γ ⊢ φ ->  list_to_set_disj Δ' ⊎ Γ ⊢ φ.
Proof.
Admitted.

Lemma simp_env_equiv_env Δ: equiv_env (simp_env Δ) Δ.
Proof.
Admitted.

Lemma simp_env_L1 Γ Δ φ:
  Γ ⊎ list_to_set_disj (simp_env Δ) ⊢ φ ->  Γ ⊎ list_to_set_disj Δ ⊢ φ.
Proof.
apply equiv_env_L1, simp_env_equiv_env.
Qed.

End Equivalence.

Global Hint Resolve simp_env_L1 : proof.

Infix "≡f" := equiv_form (at level 120).

Global Infix "≡e" := equiv_env (at level 120).

Section Variables.
Lemma equiv_env_vars Δ x:
  (∃ θ : form, ((θ ∈ simp_env Δ) /\ occurs_in x θ)) ->
  ∃ θ : form, ((θ ∈ Δ) /\ occurs_in x θ).
Proof.
intros [θ [Hin Hocc]].
Admitted.

End Variables.

Lemma simp_env_idempotent Δ: simp_env (simp_env Δ) = simp_env Δ.
Proof.
Admitted.