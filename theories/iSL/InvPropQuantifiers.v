Require Import Coq.Program.Equality. (* for dependent induction *)
Require Import ISL.PropQuantifiers ISL.Sequents ISL.SequentProps.
Require Import ISL.Order ISL.DecisionProcedure.

Section UniformInterpolation.

Definition applicable_AndR φ: {φ1 & {φ2 | φ = (And φ1 φ2)}} + (∀ φ1 φ2, φ ≠ (And φ1 φ2)).
Proof. (destruct φ; eauto). Defined.
(*
Definition applicable_other_var (Γ : list form): {q | p ≠ q /\ Var q ∈ Γ} + (∀ q, p ≠ q -> Var q ∈ Γ -> False).
Proof.
  pose (fA := (fun θ => match θ with |Var q => if decide (p = q)  then false else true | _ => false end)).
  destruct (exists_dec fA Γ) as [(θ & Hin & Hθ) | Hf].
  - left. subst fA. destruct θ.
    1: { case decide in Hθ. auto with *. eexists; split; eauto. apply elem_of_list_In. assumption. }
    all:  auto with *.
  - right. intros ψ1 ψ2 Hψ. rewrite elem_of_list_In in Hψ. apply Hf in Hψ. subst fA. simpl in Hψ.
     case decide in Hψ; auto with *.
Defined.
*)

Definition applicable_AndL (Γ : list form): {ψ1 & {ψ2 | (And ψ1 ψ2) ∈ Γ}} + (∀ ψ1 ψ2, (And ψ1 ψ2) ∈ Γ -> False).
Proof.
  pose (fA := (fun θ => match θ with |And _ _ => true | _ => false end)).
  destruct (exists_dec fA Γ) as [(θ & Hin & Hθ) | Hf].
  - left. subst fA. destruct θ. 3: { eexists. eexists. apply elem_of_list_In. eauto. }
    all:  auto with *.
  - right. intros ψ1 ψ2 Hψ. rewrite elem_of_list_In in Hψ. apply Hf in Hψ. subst fA. simpl in Hψ. tauto.
Defined.

Definition applicable_ImpR φ: {φ1 & {φ2 | φ = (Implies φ1 φ2)}} + (∀ φ1 φ2, φ ≠ (Implies φ1 φ2)).
Proof. destruct φ; eauto. Defined.


Definition applicable_OrL (Γ : list form): {ψ1 & {ψ2 | (Or ψ1 ψ2) ∈ Γ}} + (∀ ψ1 ψ2, (Or ψ1 ψ2) ∈ Γ -> False).
Proof.
  pose (fA := (fun θ => match θ with |Or _ _ => true | _ => false end)).
  destruct (exists_dec fA Γ) as [(θ & Hin & Hθ) | Hf].
  - left. subst fA. destruct θ. 4: { eexists. eexists. apply elem_of_list_In. eauto. }
    all:  auto with *.
  - right. intros ψ1 ψ2 Hψ. rewrite elem_of_list_In in Hψ. apply Hf in Hψ. subst fA. simpl in Hψ. tauto.
Defined.

(*
Definition applicable_ImpL_other_Var (Γ : list form):
  {q & {ψ | q ≠ p /\ (Implies (Var q) ψ) ∈ Γ}} +
  (∀ q ψ, q ≠ p -> (Implies (Var q) ψ) ∈ Γ -> False).
Proof.
  pose (fIp :=λ θ, match θ with | Implies (Var q) _ => if decide (p = q) then false else true | _ => false end).
  destruct (exists_dec fIp Γ) as [(θ & Hin & Hθ) | Hf].
  - left. subst fIp. destruct θ; auto with *.
    destruct θ1; auto with *.
    case decide in Hθ; auto with *.
    apply elem_of_list_In in Hin.
    do 2 eexists; split; eauto.
  - right. intros q ψ Hp Hψ. rewrite elem_of_list_In in Hψ. apply Hf in Hψ. subst fIp.
    simpl in Hψ. rewrite decide_False in Hψ; trivial; auto with *.
Defined.
*)

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

Definition applicable_ImpLVar_spec (Γ : list form) q:
  {ψ | Var q ∈ Γ /\ (Implies (Var q) ψ) ∈ Γ} +
  (∀ ψ, Var q ∈ Γ -> (Implies (Var q) ψ) ∈ Γ -> False).
Proof.
  pose (fIp :=λ θ, match θ with | Implies (Var p) _ => if decide (p = q) then true else false | _ => false end).
  pose (fp:= (fun θ => match θ with |Var p => if decide (p = q) then if (exists_dec fIp Γ) then true else false  else false| _ => false end)).
  destruct (exists_dec fp Γ) as [(θ & Hin & Hθ) | Hf].
  - left. subst fp. destruct θ. 2-6: auto with *.
    case decide in Hθ; [|auto with *]. subst.
    case exists_dec as [(ψ &Hinψ & Hψ)|] in Hθ; [|auto with *]. 
    unfold fIp in Hψ. destruct ψ.  1-4, 6: auto with *.
    destruct ψ1. 2-6: auto with *. case decide in Hψ; [|auto with *].
    subst. apply elem_of_list_In in Hinψ, Hin.
    eexists. split; eauto.
  - right. intros ψ Hp Hψ. rewrite elem_of_list_In in Hp, Hψ. apply Hf in Hp. subst fp fIp.
    simpl in Hp. rewrite decide_True in Hp by trivial.
    case exists_dec as [|Hf'] in Hp. auto with *.
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

Definition applicable_OrR φ:
    {φ1 & {φ2 | φ = (Or φ1 φ2)}} + (∀ φ1 φ2, φ = (Or φ1 φ2) -> False).
Proof. destruct φ; eauto with *. Defined.

Definition applicable_BoxR φ: {φ' | φ = (□ φ')} + (∀ φ', φ = (□ φ') -> False).
Proof. destruct φ; eauto with *. Defined.

(*
Definition applicable_ImpLImp (Γ : list form):
  {φ1 & {φ2 & {φ3 | ((φ1 → φ2) → φ3) ∈ Γ}}} +(forall φ1 φ2 φ3, ((φ1 → φ2) → φ3) ∈ Γ -> False).
Proof.
    pose (fII := (fun θ => match θ with |Implies (Implies _ _) _ => true | _ => false end)).
   destruct (exists_dec fII Γ) as [(θ & Hin & Hθ) | Hf].
    - left. subst fII. destruct θ. 1-4, 6: auto with *.
      destruct θ1. 1-4, 6: auto with *. do 3 eexists; apply elem_of_list_In; eauto.
    - right. intros ψ1 ψ2 ψ3 Hψ. rewrite elem_of_list_In in Hψ. apply Hf in Hψ. subst fII. simpl in Hψ. tauto.
Defined.
*)

(* can this be replaced with generalised axiom?*)
Definition applicable_Atom q (Δ : list form) ϕ :
  (ϕ = Var q /\ Var q ∈ Δ) + (ϕ ≠ Var q \/ (Var q ∈ Δ -> False)).
Proof.
case (decide (ϕ = Var q)).
case (decide (Var q ∈ Δ)).
all: auto with *.
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

(* TODO: plan:
  - reuse propquantifiers (esp, don't redefine erule); 
  - define propquant' as the same fixpoint as propquant, but with a simplification step
  - the simplification shold look like the monadic simplifications done here, but more general
  - to ensure that' it's still correct, prove that simplified sequents are "equivalent" to the original ones
  -  show (by induction on the definition of EA and EA') that EA equiv EA'
  *)
  
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

Obligation Tactic := (simpl; intuition order_tac).
Program Fixpoint simp_env (Δ : list form) {wf env_order Δ} : list form :=
    (* invertible left rules *)
    applicable_AndL Δ ? λ δ₁ δ₂  _, simp_env ((rm (δ₁ ∧ δ₂) Δ•δ₁)•δ₂) :2
    applicable_ImpLVar Δ ? λ q ψ  _, simp_env ((rm (Var q → ψ) Δ • ψ)) :2
    applicable_ImpLAnd Δ ? λ δ₁ δ₂ δ₃  _, simp_env ((rm ((δ₁ ∧ δ₂)→ δ₃) Δ • (δ₁ → (δ₂ → δ₃)))) :3
    applicable_ImpLOr Δ ? λ δ₁ δ₂ δ₃  _, simp_env (rm ((δ₁ ∨ δ₂)→ δ₃) Δ • (δ₁ → δ₃) • (δ₂ → δ₃)) :3
    (* remove redundant assumptions *)
    applicable_strong_weakening Δ ? λ φ _, simp_env (rm φ Δ) :1
    Δ
.
Next Obligation. apply Wf.measure_wf, wf_env_order. Qed.

Definition simp_form φ:= ⋀ (simp_env [φ]).

Definition pointed_env_order_refl pe1 pe2 := env_order_refl (pe1.2 :: pe1.2 :: pe1.1) (pe2.2 :: pe2.2 :: pe2.1).

Lemma simp_env_order pe : env_order_refl (simp_env pe) pe.
Proof.
Admitted.

Variable p : variable.

Obligation Tactic := solve[simpl; intros; simpl in *; intuition;  order_tac] || (try (apply Wf.measure_wf, wf_pointed_order)).
Program Fixpoint EA (b : bool) (pe : pointed_env) {wf pointed_env_order pe} : form :=
  let Δ := simp_env pe.1 in (* because pattern matchin in lets is not broken *)
  let ϕ := pe.2 in
  let E pe H := EA true pe in
  let A pe H := EA false pe in
  (* E *)
  if b then
    ⋀ (in_map Δ (@e_rule p Δ ϕ E A))
  (* A *)
  else
    ⋁ (in_map Δ (@a_rule_env p  Δ ϕ E A)) ⊻ @a_rule_form p  Δ ϕ E A.
Next Obligation. intros. subst Δ ϕ. eapply env_order_lt_le_trans; [exact H|].
order_tac. do 2 apply env_order_eq_add. apply simp_env_order. Qed.
Next Obligation. intros. subst Δ ϕ. eapply env_order_lt_le_trans; [exact H|].
order_tac. do 2 apply env_order_eq_add. apply simp_env_order. Qed.


Definition E := EA true.
Definition A := EA false.

Definition Ef (ψ : form) := E ([ψ], ⊥).
Definition Af (ψ : form) := A ([], ψ).

End UniformInterpolation.
