Require Import ISL.Sequents ISL.SequentProps ISL.Order ISL.Optimizations ISL.DecisionProcedure.
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

Notation "□⁻¹ Γ" := (map open_box Γ) (at level 75).

Definition applicable_AndR φ: {φ1 & {φ2 | φ = (And φ1 φ2)}} + (∀ φ1 φ2, φ ≠ (And φ1 φ2)).
Proof. (destruct φ; eauto). Defined.

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

Definition applicable_ImpLImp (Γ : list form):
  {φ1 & {φ2 & {φ3 | ((φ1 → φ2) → φ3) ∈ Γ}}} +(forall φ1 φ2 φ3, ((φ1 → φ2) → φ3) ∈ Γ -> False).
Proof.
    pose (fII := (fun θ => match θ with |Implies (Implies _ _) _ => true | _ => false end)).
   destruct (exists_dec fII Γ) as [(θ & Hin & Hθ) | Hf].
    - left. subst fII. destruct θ. 1-4, 6: auto with *.
      destruct θ1. 1-4, 6: auto with *. do 3 eexists; apply elem_of_list_In; eauto.
    - right. intros ψ1 ψ2 ψ3 Hψ. rewrite elem_of_list_In in Hψ. apply Hf in Hψ. subst fII. simpl in Hψ. tauto.
Defined.

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

(* solves the obligations of the following programs *)
Obligation Tactic := simpl; intros; order_tac.
Program Definition e_rule {Δ : list form } {ϕ : form}
  (EA0 : ∀ bool pe (Hpe : pe ≺· (Δ, ϕ)), form)
  (θ: form) (Hin : θ ∈ Δ) : form :=
let E Δ H := EA0 true (Δ, ϕ) H in
let A pe0 H := EA0 false pe0 H in
let Δ'  := rm θ Δ in
match θ with
| Var q → δ => if decide (p = q) then ⊤ else q → E (Δ'•δ) _ (* E5 modified *)
(* E8 modified *)
| ((δ₁→ δ₂)→ δ₃) =>
  (E (Δ'•(δ₂ → δ₃) • δ₁) _⇢ A (Δ'•(δ₂ → δ₃) • δ₁, δ₂) _) ⇢ E (Δ'•δ₃) _
| □ φ => □(E ((□⁻¹ Δ') • φ ) _) (* very redundant ; identical for each box *)
| (□δ1 → δ2) =>  (□(E((□⁻¹ Δ') • δ2 • □δ1) _ ⇢ A((□⁻¹ Δ') • δ2 • □δ1, δ1) _)) ⇢ E(Δ' • δ2) _
| _ => ⊤
end.

(** The implementation of the rules for defining A is separated into two pieces.
    Referring to Table 5 in Pitts, the definition a_rule_env handles A1-8 and A10,
    and the definition a_rule_form handles A9 and A11-13. *)
Program Definition a_rule_env {Δ : list form} {ϕ : form}
  (EA0 : ∀ bool pe (Hpe : pe ≺· (Δ, ϕ)), form)
  (θ: form) (Hin : θ ∈ Δ) : form :=
let E Δ H := EA0 true (Δ, ϕ) H in
let A pe0 H := EA0 false pe0 H in
let Δ'  := rm θ Δ in
match θ with
| Var q → δ => if decide (p = q) then ⊥ else q ⊼ A (Δ'•δ, ϕ) _ (* A4 *)
(* A6 *)
(* A8 modified*)
| ((δ₁→ δ₂)→ δ₃) =>
  (E (Δ'•(δ₂ → δ₃) • δ₁) _ ⇢ A (Δ'•(δ₂ → δ₃) • δ₁, δ₂) _)
  ⊼ A (Δ'•δ₃, ϕ) _
| ((□δ1) → δ2) => (□(E((□⁻¹ Δ')• δ2 • □δ1) _  ⇢ A((□⁻¹ Δ')• δ2 • □δ1, δ1) _)) ∧ A(Δ' • δ2, ϕ) _
(* using ⊼ here breaks congruence *)
| _ => ⊥
end.

Program Definition a_rule_form {Δ : list form} {ϕ : form}
  (EA0 : ∀ bool pe (Hpe : pe ≺· (Δ, ϕ)), form) :=
let E pe0:= EA0 true pe0 in
let A pe0 H := EA0 false pe0 H in
match ϕ with
| Var q =>
    if decide (p = q)
    then ⊥
    else Var q (* A9 *)
(* A12 *)
| ϕ₁ ∨ ϕ₂ => A (Δ, ϕ₁) _ ⊻ A (Δ, ϕ₂) _
| □δ => □((E ((□⁻¹ Δ) • □δ, δ) _) ⇢ A((□⁻¹ Δ) • □δ, δ) _)
| _ => ⊥
end.

Obligation Tactic := solve[simpl; intros; simpl in *; intuition;  order_tac] || (try (apply Wf.measure_wf, wf_pointed_order)).
Program Fixpoint EA (b : bool) (pe : list form * form) {wf pointed_env_order pe} :=
  let Δ := fst pe in
  let ϕ := snd pe in
  let E := EA true in
  let A := EA false in
  (* E *)
  if b then
    if decide (⊥ ∈ Δ) then ⊥ else
    applicable_other_var Δ ? λ q _, q ⊼ E (rm (Var q) Δ, ϕ) _ :1
    applicable_AndL Δ ? λ δ₁ δ₂  _, E ((rm (δ₁ ∧ δ₂) Δ•δ₁)•δ₂, ϕ) _ :2
    applicable_OrL Δ ? λ δ₁ δ₂  _, E ((rm (δ₁ ∨ δ₂) Δ•δ₁, ϕ)) _ ⊻E ((rm (δ₁ ∨ δ₂) Δ•δ₂, ϕ)) _ :2
    applicable_ImpLVar Δ ? λ q ψ  _, E ((rm (Var q → ψ) Δ • ψ, ϕ)) _ :2
    applicable_ImpLAnd Δ ? λ δ₁ δ₂ δ₃  _, E ((rm ((δ₁ ∧ δ₂)→ δ₃) Δ • (δ₁ → (δ₂ → δ₃)), ϕ)) _ :3
    applicable_ImpLOr Δ ? λ δ₁ δ₂ δ₃  _, E (rm ((δ₁ ∨ δ₂)→ δ₃) Δ • (δ₁ → δ₃) • (δ₂ → δ₃), ϕ) _ :3
    ⋀ (in_map Δ (e_rule EA)) (* the non-invertible rules *)

  (* A *)
  else
    applicable_other_var Δ ? λ q _, A (rm (Var q) Δ, ϕ) _ :1
    applicable_AndL Δ ? λ δ₁ δ₂  _, A ((rm (δ₁ ∧ δ₂) Δ•δ₁)•δ₂, ϕ) _ :2
    applicable_OrL Δ ? λ δ₁ δ₂  _, (E ((rm (δ₁ ∨ δ₂) Δ•δ₁, ϕ)) _ ⇢ A ((rm (δ₁ ∨ δ₂) Δ•δ₁, ϕ)) _) ⊼
                                                          (E ((rm (δ₁ ∨ δ₂) Δ•δ₂, ϕ)) _ ⇢ A ((rm (δ₁ ∨ δ₂) Δ•δ₂, ϕ)) _) :2
    applicable_ImpLVar Δ ? λ q ψ _, A (rm (Var q → ψ) Δ • ψ, ϕ) _ :2
    applicable_ImpLAnd Δ ? λ δ₁ δ₂ δ₃  _, A ((rm ((δ₁ ∧ δ₂)→ δ₃) Δ • (δ₁ → (δ₂ → δ₃)), ϕ)) _ :3
    applicable_ImpLOr Δ ? λ δ₁ δ₂ δ₃  _, A (rm ((δ₁ ∨ δ₂)→ δ₃) Δ • (δ₁ → δ₃) • (δ₂ → δ₃), ϕ) _ :3
    applicable_Atom p Δ ϕ ? λ _, ⊤ :0
    applicable_AndR ϕ ? λ ϕ₁ ϕ₂ _, A (Δ, ϕ₁) _ ⊼ A (Δ, ϕ₂) _ :2
    applicable_ImpR ϕ ? λ ϕ₁ ϕ₂ _, E (Δ • ϕ₁, ϕ₂) _ ⇢ A (Δ • ϕ₁, ϕ₂) _ :2
    (⋁ (in_map Δ (a_rule_env EA)) ⊻ a_rule_form EA) (* the non-invertible rules *)
.


Definition E pe := EA true pe.
Definition A pe := EA false pe.

Definition Ef (ψ : form) := E ([ψ], ⊥).
Definition Af (ψ : form) := A ([], ψ).

End PropQuantDefinition.

End UniformInterpolation.

