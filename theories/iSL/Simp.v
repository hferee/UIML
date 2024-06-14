Require Import ISL.SequentProps.
Require Import ISL.Sequents.
Require Import ISL.Environments.
Require Import Coq.Program.Equality.


Definition simp_or φ ψ := 
  if decide (φ = ⊥) then ψ
  else if decide (ψ = ⊥) then φ
  else if decide (φ = ⊤) then ⊤
  else if decide (ψ = ⊤) then ⊤
  else if decide (φ = ψ) then φ
  else φ ∨ ψ.


Definition simp_and φ ψ :=
  if decide (φ =⊥) then ⊥
  else if decide (ψ = ⊥) then ⊥
  else if decide (φ = ⊤) then ψ
  else if decide (ψ = ⊤) then φ
  else if decide (φ = ψ) then φ
  else φ ∧ ψ.


Definition simp_imp φ ψ :=
  φ → ψ.

Fixpoint simp φ := match φ with
| φ ∨ ψ => simp_or (simp φ) (simp ψ)
| φ ∧ ψ => simp_and (simp φ) (simp ψ)
| φ → ψ => simp_imp φ ψ
| _ => φ
end.


Lemma top_provable Γ :
 Γ ⊢ ⊤.
Proof.
  apply ImpR.
  apply ExFalso.
Qed.

Lemma ImpR_idemp Γ φ :
 Γ ⊢ (φ → φ).
Proof.
  apply ImpR.
  apply generalised_axiom.
Qed.

Lemma simp_equiv_or_L Γ φ ψ : 
  (forall f, weight f < weight (φ ∨ ψ) -> Γ • f ⊢ simp f) ->
  Γ • (φ ∨ ψ) ⊢ simp (φ ∨ ψ).
Proof.
intros IH.
assert (Hφ : Γ • φ  ⊢ simp φ ) by (apply (IH φ); simpl; lia).
assert (Hψ : Γ • ψ  ⊢ simp ψ ) by (apply (IH ψ); simpl; lia).
simpl. unfold simp_or. 
case decide as [Hbot |].
- apply OrL.
  + rewrite Hbot in Hφ.
    apply exfalso. trivial.
  + apply Hψ.
- case decide as [Hbot |].
  + apply OrL.
    * apply Hφ.
    * rewrite Hbot in Hψ.
      apply exfalso. trivial.
  + case decide as [Htop |].
    * apply top_provable.
    * case decide as [Htop |].
      -- apply top_provable.
      -- case decide; [intro Heq | intro ]; apply OrL.
            ** apply Hφ.
            ** rewrite Heq.
               apply Hψ.
            ** apply OrR1.
               apply Hφ.
            ** apply OrR2.
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
case decide as [Hbot |].
- rewrite Hbot in Hφ.
  apply AndL. apply weakening.
  apply exfalso. trivial.
- case decide as [Hbot |].
  + rewrite Hbot in Hψ.
    apply AndL. exch 0. apply weakening.
    apply exfalso. trivial.
  + case decide as [].
    * apply AndL.
      exch 0. apply weakening.
      apply Hψ.
    * case decide as [].
      -- apply AndL.
         apply weakening.
         apply Hφ.
      -- apply AndL.
         case decide as [].
         ++ apply weakening.
            apply Hφ.
         ++ apply AndR.
            ** apply weakening.
               apply Hφ.
            ** exch 0. apply weakening.
               apply Hψ.
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


Lemma simp_equiv_or_R Γ φ ψ : 
  (forall f, weight f < weight (φ ∨ ψ) -> Γ • simp f ⊢ f) ->
  Γ •simp (φ ∨ ψ) ⊢  (φ ∨ ψ).
Proof.
intros IH.
assert (Hφ : Γ • simp φ ⊢ φ ) by (apply (IH φ); simpl; lia).
assert (Hψ : Γ • simp ψ ⊢ ψ ) by (apply (IH ψ); simpl; lia).
simpl. unfold simp_or. 
case decide as [].
- apply OrR2.
  apply Hψ.
- case decide as [].
  + apply OrR1.
    apply Hφ.
  + case decide as [Htop |].
    * apply OrR1.
      rewrite <- Htop.
      apply Hφ.
    * case decide as [Htop |].
      -- apply OrR2.
         rewrite <- Htop.
         apply Hψ.
      -- case decide as [].
         ++ apply OrR1.
            apply Hφ.
         ++ apply OrL.
            ** apply OrR1.
               apply Hφ.
            ** apply OrR2.
               apply Hψ.
Qed.

Lemma simp_equiv_and_R Γ φ ψ : 
  (forall f, weight f < weight (φ ∧ ψ) -> Γ • simp f ⊢ f) ->
  Γ • simp (φ ∧ ψ) ⊢  φ ∧ ψ.
Proof.
  intros IH.
  assert (Hφ : Γ • simp φ ⊢ φ ) by (apply (IH φ); simpl; lia).
  assert (Hψ : Γ • simp ψ ⊢ ψ ) by (apply (IH ψ); simpl; lia).
  simpl. unfold simp_and. 
  case decide as [].
  - apply exfalso. apply ExFalso.
  - case decide as [].
    + apply exfalso. apply ExFalso.
    + case decide as [Htop |].
      * apply AndR.
        -- rewrite Htop in Hφ.
           apply weakening.
           eapply TopL_rev.
           apply Hφ.
        -- apply Hψ.
      * case decide as [Htop |].
        -- apply AndR. 
           ++ apply Hφ.
           ++ rewrite Htop in Hψ.
              apply weakening.
              eapply TopL_rev.
              apply Hψ.
        -- case decide as [ Heq | Hneq].
           ++ apply AndR; [ apply Hφ| rewrite Heq ;apply Hψ].
           ++ apply AndL.
              apply AndR; [|exch 0]; apply weakening; [apply Hφ| apply Hψ].
Qed.

Theorem simp_equiv_R Γ φ : Γ • (simp φ) ⊢ φ.
Proof.
remember (weight φ) as w.
assert(Hle : weight φ  ≤ w) by lia.
clear Heqw. revert φ Hle.
induction w; intros φ Hle; [destruct φ ; simpl in Hle; lia|].
destruct φ;  try apply generalised_axiom;
[eapply (simp_equiv_and_R Γ φ1  φ2) | eapply (simp_equiv_or_R Γ φ1  φ2)];
intros f H; apply IHw; lia.
Qed.


