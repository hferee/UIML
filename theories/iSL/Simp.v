Require Import ISL.SequentProps.
Require Import ISL.Sequents.
Require Import ISL.Environments.


Fixpoint simp φ := match φ with
| φ ∧ ψ => if decide (φ = ⊥) 
           then ⊥ 
          else
            if decide (ψ = ⊥) 
            then ⊥ 
            else (simp φ) ∧ (simp ψ)
| φ ∨ ψ => if decide (φ = ⊥) 
           then ψ 
          else
            if decide (ψ = ⊥) 
            then φ  
            else (simp φ) ∨ (simp ψ)
| _ => φ
end.

Lemma simpl_equiv_and_L Γ φ ψ : 
  Γ • φ ⊢ simp φ ->
  Γ • ψ ⊢ simp ψ  ->
  Γ • (φ ∧ ψ) ⊢ simp (φ ∧ ψ).
Proof.
  intros IHφ IHψ.
  simpl. 
  apply AndL.
  destruct decide.
  - rewrite e.
    exch 0. apply ExFalso.
  - destruct decide.
    -- rewrite e.
        apply ExFalso.
    -- apply AndR.
       ---  apply weakening.
            apply IHφ.
       ---  exch 0. apply weakening. 
            apply IHψ.
Qed.

Lemma simpl_equiv_or_L Γ φ ψ : 
  Γ • φ ⊢ simp φ ->
  Γ • ψ ⊢ simp ψ  ->
  Γ • (φ ∨ ψ) ⊢ simp (φ ∨ ψ).
Proof.
  intros IHφ IHψ.
  simpl.
  destruct decide.
  apply OrL.
  - rewrite e. apply ExFalso.
  - apply generalised_axiom.
  - destruct decide.
    -- apply OrL.
       --- apply generalised_axiom.
       --- rewrite e.
           apply ExFalso.
    -- apply OrL.
        --- apply OrR1.
            apply IHφ.
        --- apply OrR2.
            apply IHψ.
Qed.


Theorem simp_equiv_L Γ φ : Γ • φ ⊢ simp φ.
Proof.
  induction φ.
- apply generalised_axiom.
- apply generalised_axiom.
- apply (simpl_equiv_and_L Γ φ1  φ2 IHφ1 IHφ2).
- apply (simpl_equiv_or_L Γ φ1  φ2 IHφ1 IHφ2).
- apply generalised_axiom.
- apply generalised_axiom.
Qed.


Lemma simpl_equiv_and_R Γ φ ψ : 
  Γ • (simp φ) ⊢ φ ->
  Γ • (simp ψ) ⊢ ψ  ->
  Γ • (simp (φ ∧ ψ)) ⊢ φ ∧ ψ.
Proof.
  intros IHφ IHψ.
  simpl. 
  destruct decide.
  - apply ExFalso.
  - destruct decide.
    -- apply ExFalso.
    -- apply AndL.
       apply AndR.
       ---  apply weakening.
            apply IHφ.
       ---  exch 0. apply weakening. 
            apply IHψ.
Qed.


Lemma simpl_equiv_or_R Γ φ ψ : 
  Γ • (simp φ) ⊢ φ ->
  Γ • (simp ψ) ⊢ ψ  ->
  Γ • (simp (φ ∨ ψ)) ⊢ φ ∨ ψ.
Proof.
  intros IHφ IHψ.
  simpl.
  destruct decide.
  - apply OrR2.
    apply generalised_axiom.
  - destruct decide.
    -- apply OrR1.
       apply generalised_axiom.
    -- apply OrL.
        --- apply OrR1.
            apply IHφ.
        --- apply OrR2.
            apply IHψ.
Qed.


Theorem simp_equiv_R Γ φ : Γ • (simp φ) ⊢ φ.
Proof.
  induction φ.
- apply generalised_axiom.
- apply generalised_axiom.
- apply (simpl_equiv_and_R Γ φ1  φ2 IHφ1 IHφ2).
- apply (simpl_equiv_or_R Γ φ1  φ2 IHφ1 IHφ2).
- apply generalised_axiom.
- apply generalised_axiom.
Qed.

