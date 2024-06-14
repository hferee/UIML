Require Import ISL.SequentProps.
Require Import ISL.Sequents.
Require Import ISL.Environments.


Definition simp_or φ ψ := 
  if decide (φ =⊥) then ψ
  else if decide (ψ = ⊥) then φ
  else if decide (φ = ⊤) then ⊤
  else if decide (ψ = ⊤) then ⊤
  else φ ∨ ψ.


Definition simp_and φ ψ :=
  if decide (φ =⊥) then ⊥
  else if decide (ψ = ⊥) then ⊥
  else if decide (φ = ⊤) then ψ 
  else if decide (ψ = ⊤) then φ 
  else φ ∨ ψ.

Fixpoint simp φ := match φ with
| φ ∨ ψ => simp_or (simp φ) (simp ψ) 
| φ ∧ ψ => simp_and (simp φ) (simp ψ) 
| _ => φ
end.


Lemma top_provable Γ:
 Γ ⊢ ⊤.
Proof.
  apply ImpR.
  apply ExFalso.
Qed.


Lemma simp_equiv_or_L Γ φ ψ : 
  (forall f, weight f < weight (φ ∨ ψ) -> Γ • f ⊢ simp f) ->
  Γ • (φ ∨ ψ) ⊢ simp (φ ∨ ψ).
Proof.
intros IH.
assert (Hφ : Γ • φ  ⊢ simp φ ) by (apply (IH φ); simpl; lia).
assert (Hψ : Γ • ψ  ⊢ simp ψ ) by (apply (IH ψ); simpl; lia).
simpl. unfold simp_or. 
case decide.
- intro Hbot.
  apply OrL.
  + rewrite Hbot in Hφ.
    apply exfalso. trivial.
  + apply Hψ.
- intro.
  case decide.
  + intro Hbot.
  apply OrL.
    * apply Hφ.
    * rewrite Hbot in Hψ.
      apply exfalso. trivial.
  + intro.
    case decide.
    * intro Htop.
      apply top_provable.
    * intro.  
      case decide.
      -- intro Htop.
         apply top_provable.
      -- intro.
         apply OrL.
         ++ apply OrR1.
            apply Hφ.
         ++ apply OrR2.
            apply Hψ.
Qed.


Lemma simp_equiv_and_L Γ φ ψ : 
  (forall f, weight f < weight (φ ∧ ψ) -> Γ • f ⊢ simp f) ->
  Γ • (φ ∧ ψ) ⊢ simp (φ ∧ ψ).
Proof.
intros IH.
assert (Hφ : Γ • φ  ⊢ simp φ ) by (apply (IH φ); simpl; lia).
assert (Hψ : Γ • ψ  ⊢ simp ψ ) by (apply (IH ψ); simpl; lia).
simpl. unfold simp_and. 
case decide.
- intro Hbot.
  rewrite Hbot in Hφ.
  apply AndL. apply weakening.
  apply exfalso. trivial.
- intro.
  case decide.
  + intro Hbot.
    rewrite Hbot in Hψ.
    apply AndL. exch 0. apply weakening.
    apply exfalso. trivial.
  + intro.
    case decide.
    * intro.
      apply AndL.
      exch 0. apply weakening.
      apply Hψ.
    * intro.
      case decide.
      -- intro.
         apply AndL.
         apply weakening.
         apply Hφ.
      -- intro.
         apply OrR1.
         apply AndL.
         apply weakening.
         apply Hφ.
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

Theorem simp_equiv_R Γ φ : Γ • (simp φ) ⊢ φ.
Admitted.

