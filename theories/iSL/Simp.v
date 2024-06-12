Require Import ISL.SequentProps.
Require Import ISL.Sequents.
Require Import ISL.Environments.


Definition simp_or φ ψ := match φ,ψ  with
| ⊥ , ψ => ψ 
| φ , ψ => φ ∨ ψ 
end.


Definition simp_and φ ψ := match φ,ψ  with
| ⊥ , _ => ⊥  
| φ , ψ => φ ∧ ψ 
end.

Fixpoint simp φ := match φ with
(*
| φ1 ∧ (φ2 ∧ φ3) => if decide (φ1  = φ2)
then (simp φ1) ∧ (simp φ3)
                          else (simp  φ1) ∧ (simp φ2) ∧ (simp φ3)
*)
| φ ∨ ψ => simp_or (simp φ) (simp ψ) 
| ⊥ ∧ _ | _ ∧ ⊥   =>  ⊥
| φ ∧ ψ => (simp φ) ∧ (simp ψ)
| _ => φ
end.




Lemma simp_shrink φ :
  weight (simp φ) <= weight φ.
Proof.
Admitted.


Lemma leq_to_le a b :
  a < b ->
  a <= b.
Proof.
  lia.
Qed.


 Lemma simp_or_no_bot φ ψ :
   φ ≠ ⊥ -> simp_or φ ψ = (φ ∨ ψ).
 Admitted.


 Lemma simp_and_no_bot φ ψ :
   φ ≠ ⊥ -> simp_or φ ψ = (φ ∧ ψ).
 Admitted.

Lemma simp_equiv_or_L Γ φ ψ : 
  (forall f, weight f < weight (φ ∨ ψ) -> Γ • f ⊢ simp f) ->
  Γ • (φ ∨ ψ) ⊢ simp (φ ∨ ψ).
Proof.
intros IH.

assert (Hφ : Γ • φ  ⊢ simp φ ) by (apply (IH φ); simpl; lia).
assert (Hψ : Γ • ψ  ⊢ simp ψ ) by (apply (IH ψ); simpl; lia).

destruct φ.
- simpl. auto 3 with proof.
- simpl. auto 2 with proof.
- assert (H: (Γ • φ1 ∧ φ2 ∨ ψ) ⊢ simp_or (simp (φ1 ∧ φ2)) (simp ψ)).
  destruct (decide (simp (φ1 ∧ φ2) = ⊥)).
  + rewrite e. simpl. apply OrL.
    * rewrite e in Hφ. apply exfalso. trivial.
    * apply Hψ.
  + rewrite simp_or_no_bot.
    * auto with proof.
    * apply n.
  +  apply H.
- assert (H: (Γ • (φ1 ∨ φ2) ∨ ψ) ⊢ simp_or (simp (φ1 ∨ φ2)) (simp ψ)).
  destruct (decide (simp (φ1 ∨ φ2) = ⊥)).
  + rewrite e. simpl. apply OrL. 
    * rewrite e in Hφ. apply exfalso. trivial.
    * apply Hψ.
  + rewrite simp_or_no_bot.
    * auto with proof.
    * apply n.
  +  apply H.
- simpl. auto 3 with proof.
- simpl. auto 3 with proof.
Qed.


Lemma simp_equiv_and_L Γ φ ψ : 
  (forall f, weight f < weight (φ ∧ ψ) -> Γ • f ⊢ simp f) ->
  Γ • (φ ∧ ψ) ⊢ simp (φ ∧ ψ).
Proof.
intros IH.

remember (weight φ) as wφ.
assert (Hφ : Γ • φ ⊢ simp φ) by (apply (IH φ); simpl; lia).

remember (weight ψ) as wψ.
assert (Hψ : Γ • ψ ⊢ simp ψ) by (apply (IH ψ); simpl; lia).

destruct φ; destruct ψ; simpl; apply AndL; auto 2 with proof; apply AndR;
simpl; auto 2 with proof; exch 0; apply weakening; try apply Hψ.
Qed.


Theorem simp_equiv_L Γ φ : Γ • φ ⊢ simp φ.
Proof.
remember (weight φ) as w.
assert(Hle : weight φ  ≤ w) by lia.
clear Heqw. revert φ Hle.
induction w; intros φ Hle; [destruct φ ; simpl in Hle; lia|].
destruct φ;  try apply generalised_axiom;
[eapply (simp_equiv_and_L Γ φ1  φ2)| eapply (simp_equiv_or_L Γ φ1  φ2)];
intros f H; apply IHw; lia.
Qed.

(* TODO
Lemma simp_equiv_and_R Γ φ ψ : 
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


Lemma simp_equiv_or_R Γ φ ψ : 
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
- apply (simp_equiv_and_R Γ φ1  φ2 IHφ1 IHφ2).
- apply (simp_equiv_or_R Γ φ1  φ2 IHφ1 IHφ2).
- apply generalised_axiom.
- apply generalised_axiom.
Qed.
 *)

