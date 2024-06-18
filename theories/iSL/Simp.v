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

Definition Lindenbaum_Tarski_preorder φ ψ :=
  ∅ • φ  ⊢ ψ.

Notation "φ ≼ ψ" := (form_order φ ψ) (at level 149).

Lemma order_to_proof φ ψ:
  ∅ • φ  ⊢ ψ ->
  (φ ≼ ψ).
Admitted.

Lemma proof_to_order φ ψ:
  (φ ≼ ψ) ->
  ∅ • φ  ⊢ ψ.
Admitted.

Ltac oeapply th :=
  apply proof_to_order; apply th.

Lemma top_provable Γ :
 Γ ⊢ ⊤.
Proof.
  apply ImpR. apply ExFalso.
Qed.

Lemma simp_equiv_or_L φ ψ : 
  (forall f, weight f < weight (φ ∨ ψ) -> (f ≼ simp f) * (simp f ≼ f)) ->
  (φ ∨ ψ) ≼ simp (φ ∨ ψ).
Proof.
intros IH.
apply order_to_proof.
assert (Hφ :  φ  ≼ simp φ ) by (apply (IH φ); simpl; lia).
assert (Hψ :  ψ  ≼ simp ψ ) by (apply (IH ψ); simpl; lia).
simpl. unfold simp_or. 
case decide as [Hbot |].
- apply OrL.
  + rewrite Hbot in Hφ.
    apply exfalso. oeapply Hφ.
  + oeapply Hψ.
- case decide as [Hbot |].
  + apply OrL.
    * oeapply Hφ.
    * rewrite Hbot in Hψ.
      apply exfalso. oeapply Hψ.
  + case decide as [Htop |].
    * apply top_provable.
    * case decide as [Htop |].
      -- apply top_provable.
      -- case decide; [intro Heq | intro ]; apply OrL.
            ** oeapply Hφ.
            ** rewrite Heq.
               oeapply Hψ.
            ** apply OrR1.
               oeapply Hφ.
            ** apply OrR2.
               oeapply Hψ.
Qed.


Lemma simp_equiv_or_R φ ψ : 
  (forall f, weight f < weight (φ ∨ ψ) -> (f ≼ simp f) * (simp f ≼ f)) ->
  simp (φ ∨ ψ) ≼ (φ ∨ ψ).
Proof.
intros IH.
apply order_to_proof.
assert (Hφ : simp φ ≼ φ ) by (apply (IH φ); simpl; lia).
assert (Hψ :  simp ψ ≼ ψ ) by (apply (IH ψ); simpl; lia).
simpl. unfold simp_or. 
case decide as [].
- apply OrR2.
  oeapply Hψ.
- case decide as [].
  + apply OrR1.
    oeapply Hφ.
  + case decide as [Htop |].
    * apply OrR1.
      rewrite <- Htop.
      oeapply Hφ.
    * case decide as [Htop |].
      -- apply OrR2.
         rewrite <- Htop.
         oeapply Hψ.
      -- case decide as [].
         ++ apply OrR1.
            oeapply Hφ.
         ++ apply OrL.
            ** apply OrR1.
               oeapply Hφ.
            ** apply OrR2.
               oeapply Hψ.
Qed.

Lemma simp_equiv_or φ ψ: 
  (forall f, weight f < weight (φ ∨ ψ) -> (f ≼ simp f) * (simp f ≼ f)) ->
  ((φ ∨ ψ) ≼ simp (φ ∨ ψ)) * (simp (φ ∨ ψ) ≼ (φ ∨ ψ)).
Proof.
intros IH.
split; [ apply simp_equiv_or_L | apply simp_equiv_or_R] ; apply IH.
Qed.

Lemma simp_equiv_and_L φ ψ : 
  (forall f, weight f < weight (φ ∧ ψ) -> (f ≼ simp f) * (simp f ≼ f)) ->
  (φ ∧ ψ) ≼ simp (φ ∧ ψ).
Proof.
intros IH.
apply order_to_proof.
assert (Hφ :  φ  ≼ simp φ ) by (apply (IH φ); simpl; lia).
assert (Hψ :  ψ  ≼ simp ψ ) by (apply (IH ψ); simpl; lia).
simpl. unfold simp_and. 
case decide as [Hbot |].
- rewrite Hbot in Hφ.
  apply AndL. apply weakening.
  apply exfalso. oeapply Hφ.
- case decide as [Hbot |].
  + rewrite Hbot in Hψ.
    apply AndL. exch 0. apply weakening.
    oeapply Hψ.
  + case decide as [].
    * apply AndL.
      exch 0. apply weakening.
      oeapply Hψ.
    * case decide as [].
      -- apply AndL.
         apply weakening.
         oeapply Hφ.
      -- apply AndL.
         case decide as [].
         ++ apply weakening.
            oeapply Hφ.
         ++ apply AndR.
            ** apply weakening.
               oeapply Hφ.
            ** exch 0. apply weakening.
               oeapply Hψ.
Qed.


Lemma simp_equiv_and_R φ ψ : 
  (forall f, weight f < weight (φ ∧ ψ) -> (f ≼ simp f) * (simp f ≼ f)) ->
  simp (φ ∧ ψ) ≼  φ ∧ ψ.
Proof.
  intros IH.
apply order_to_proof.
  assert (Hφ :  simp φ ≼ φ ) by (apply (IH φ); simpl; lia).
  assert (Hψ :  simp ψ ≼ ψ ) by (apply (IH ψ); simpl; lia).
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
           oeapply Hφ.
        -- oeapply Hψ.
      * case decide as [Htop |].
        -- apply AndR. 
           ++ oeapply Hφ.
           ++ rewrite Htop in Hψ.
              apply weakening.
              eapply TopL_rev.
              oeapply Hψ.
        -- case decide as [ Heq | Hneq].
           ++ apply AndR; [ oeapply Hφ| rewrite Heq ; oeapply Hψ].
           ++ apply AndL.
              apply AndR; [|exch 0]; apply weakening; [oeapply Hφ | oeapply Hψ].
Qed.


Lemma simp_equiv_and φ ψ: 
  (forall f, weight f < weight (φ ∧ ψ) -> (f ≼ simp f) * (simp f ≼ f)) ->
  ((φ ∧ ψ) ≼ simp (φ ∧ ψ)) * (simp (φ ∧ ψ) ≼ (φ ∧ ψ)).
Proof.
intros IH.
split; [ apply simp_equiv_and_L | apply simp_equiv_and_R] ; apply IH.
Qed.


Lemma simp_equiv_imp_L φ ψ : 
  (forall f, weight f < weight (φ → ψ) -> (f ≼ simp f) * (simp f ≼ f)) ->
  (φ → ψ) ≼ simp (φ → ψ).
Proof.
intros IH.
apply order_to_proof.
assert (HφR : simp φ ≼ φ) by (apply (IH φ); simpl; lia).
assert (HφL :  φ ≼ simp φ) by (apply (IH φ); simpl; lia).
assert (HψL:  ψ  ≼ simp ψ) by (apply (IH ψ); simpl; lia).
simpl. unfold simp_imp. 
case decide as [Htop |].
-  rewrite Htop in HφR.
  apply weak_ImpL.
  + eapply TopL_rev. 
    oeapply HφR.
  + oeapply HψL.
- case decide as [].
  + apply weakening.
    apply top_provable.
  + apply ImpR.
    exch 0.
    apply ImpL.
    * apply weakening. oeapply HφR.
    * exch 0. apply weakening.
      oeapply HψL.
Qed.

Lemma simp_equiv_imp_R φ ψ : 
  (forall f, weight f < weight (φ → ψ) -> (f ≼ simp f) * ( simp f ≼ f)) ->
  simp (φ → ψ) ≼ (φ → ψ).
Proof.
intros IH.
apply order_to_proof.
assert (HφL : φ ≼ simp φ) by (apply (IH φ); simpl; lia).
assert (HψR : simp ψ ≼ ψ) by (apply (IH ψ); simpl; lia).
simpl. unfold simp_imp.
case decide as [Htop |].
- apply ImpR. 
  apply weakening.
  oeapply HψR.
- case decide as [Htop |].
  + rewrite Htop in HφL.
    apply ImpR.
    apply exfalso.
    exch 0. apply weakening.
    oeapply HφL.
  + apply ImpR.
    exch 0.
    apply ImpL.
    * apply weakening. oeapply HφL.
    * exch 0. apply weakening.
      oeapply HψR.
Qed.


Lemma simp_equiv_imp φ ψ: 
  (forall f, weight f < weight (φ → ψ) -> (f ≼ simp f) * (simp f ≼ f)) ->
  ((φ → ψ) ≼ simp (φ → ψ)) * (simp (φ → ψ) ≼ (φ → ψ)).
Proof.
intros IH.
split; [ apply simp_equiv_imp_L | apply simp_equiv_imp_R] ; apply IH.
Qed.


Theorem simp_equiv φ : 
  (φ ≼ (simp φ)) * ((simp φ) ≼ φ).
Proof.
remember (weight φ) as w.
assert(Hle : weight φ  ≤ w) by lia.
clear Heqw. revert φ Hle.
induction w; intros φ Hle; [destruct φ ; simpl in Hle; lia|].
destruct φ;  simpl; try (split ; apply order_to_proof; apply generalised_axiom);
[eapply (simp_equiv_and φ1  φ2)|
 eapply (simp_equiv_or φ1  φ2)|
 eapply (simp_equiv_imp φ1  φ2)];
intros f H; apply IHw; lia.
Qed.
