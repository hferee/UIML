Require Import ISL.SequentProps.
Require Import ISL.Sequents.
Require Import ISL.Environments.

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
  if decide (φ = ⊤) then ψ
  else if decide (φ = ⊥) then ⊤
  else φ → ψ.

Fixpoint simp φ := match φ with
| φ ∨ ψ => simp_or (simp φ) (simp ψ)
| φ ∧ ψ => simp_and (simp φ) (simp ψ)
| φ → ψ => simp_imp (simp φ) (simp ψ)
| _ => φ
end.


Lemma top_provable Γ :
 Γ ⊢ ⊤.
Proof.
  apply ImpR. apply ExFalso.
Qed.

Lemma simp_equiv_or_L Γ φ ψ : 
  (forall f, weight f < weight (φ ∨ ψ) -> (Γ • f ⊢ simp f) * (Γ • simp f ⊢ f)) ->
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


Lemma simp_equiv_or_R Γ φ ψ : 
  (forall f, weight f < weight (φ ∨ ψ) -> (Γ • f ⊢ simp f) * (Γ • simp f ⊢ f)) ->
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


Lemma simp_equiv_or Γ φ ψ: 
  (forall f, weight f < weight (φ ∨ ψ) -> (Γ • f ⊢ simp f) * (Γ • simp f ⊢ f)) ->
  (Γ • (φ ∨ ψ) ⊢ simp (φ ∨ ψ)) * (Γ •  simp (φ ∨ ψ) ⊢(φ ∨ ψ)).
Proof.
intros IH.
split; [ apply simp_equiv_or_L | apply simp_equiv_or_R] ; apply IH.
Qed.

Lemma simp_equiv_and_L Γ φ ψ : 
  (forall f, weight f < weight (φ ∧ ψ) -> (Γ • f ⊢ simp f) * (Γ • simp f ⊢ f)) ->
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
    apply Hψ.
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


Lemma simp_equiv_and_R Γ φ ψ : 
  (forall f, weight f < weight (φ ∧ ψ) -> (Γ • f ⊢ simp f) * (Γ • simp f ⊢ f)) ->
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


Lemma simp_equiv_and Γ φ ψ: 
  (forall f, weight f < weight (φ ∧ ψ) -> (Γ • f ⊢ simp f) * (Γ • simp f ⊢ f)) ->
  (Γ • (φ ∧ ψ) ⊢ simp (φ ∧ ψ)) * (Γ •  simp (φ ∧ ψ) ⊢(φ ∧ ψ)).
Proof.
intros IH.
split; [ apply simp_equiv_and_L | apply simp_equiv_and_R] ; apply IH.
Qed.


Lemma simp_equiv_imp_L Γ φ ψ : 
  (forall f, weight f < weight (φ → ψ) -> (Γ • f ⊢ simp f) * (Γ • simp f ⊢ f)) ->
  Γ • (φ → ψ) ⊢ simp (φ → ψ).
Proof.
intros IH.
assert (HφR : Γ • simp φ ⊢ φ) by (apply (IH φ); simpl; lia).
assert (HφL : Γ • φ ⊢ simp φ) by (apply (IH φ); simpl; lia).
assert (HψL: Γ • ψ  ⊢ simp ψ) by (apply (IH ψ); simpl; lia).
simpl. unfold simp_imp. 
case decide as [Htop |].
-  rewrite Htop in HφR.
  apply weak_ImpL.
  + eapply TopL_rev. 
    apply HφR.
  + apply HψL.
- case decide as [].
  + apply weakening.
    apply top_provable.
  + apply ImpR.
    exch 0.
    apply ImpL.
    * apply weakening. apply HφR.
    * exch 0. apply weakening.
      apply HψL.
Qed.

Lemma simp_equiv_imp_R Γ φ ψ : 
  (forall f, weight f < weight (φ → ψ) -> (Γ • f ⊢ simp f) * (Γ • simp f ⊢ f)) ->
  Γ • simp (φ → ψ) ⊢ (φ → ψ).
Proof.
intros IH.
assert (HφL : Γ • φ ⊢ simp φ) by (apply (IH φ); simpl; lia).
assert (HψR : Γ • simp ψ ⊢ ψ) by (apply (IH ψ); simpl; lia).
simpl. unfold simp_imp.
case decide as [Htop |].
- apply ImpR. 
  apply weakening.
  apply HψR.
- case decide as [Htop |].
  + rewrite Htop in HφL.
    auto with proof.
  + apply ImpR.
    exch 0.
    apply ImpL.
    * apply weakening. apply HφL.
    * exch 0. apply weakening.
      apply HψR.
Qed.


Lemma simp_equiv_imp Γ φ ψ: 
  (forall f, weight f < weight (φ → ψ) -> (Γ • f ⊢ simp f) * (Γ • simp f ⊢ f)) ->
  (Γ • (φ → ψ) ⊢ simp (φ → ψ)) * (Γ •  simp (φ → ψ) ⊢(φ → ψ)).
Proof.
intros IH.
split; [ apply simp_equiv_imp_L | apply simp_equiv_imp_R] ; apply IH.
Qed.


Theorem simp_equiv Γ φ : (Γ • φ ⊢ simp φ) * (Γ • (simp φ) ⊢ φ).
Proof.
remember (weight φ) as w.
assert(Hle : weight φ  ≤ w) by lia.
clear Heqw. revert φ Hle.
induction w; intros φ Hle; [destruct φ ; simpl in Hle; lia|].
destruct φ;  simpl; try (split ; apply generalised_axiom);
[eapply (simp_equiv_and Γ φ1  φ2)|
 eapply (simp_equiv_or Γ φ1  φ2)|
 eapply (simp_equiv_imp Γ φ1  φ2)];
intros f H; apply IHw; lia.
Qed.
