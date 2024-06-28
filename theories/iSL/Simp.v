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
  else if decide (φ = ψ) then ⊤
  else φ → ψ.

Fixpoint simp φ := match φ with
| φ ∨ ψ => simp_or (simp φ) (simp ψ)
| φ ∧ ψ => simp_and (simp φ) (simp ψ)
| φ → ψ => simp_imp (simp φ) (simp ψ)
| _ => φ
end.

Definition Lindenbaum_Tarski_preorder φ ψ :=
  ∅ • φ  ⊢ ψ.

Notation "φ ≼ ψ" := (Lindenbaum_Tarski_preorder φ ψ) (at level 149).

Lemma top_provable Γ :
 Γ ⊢ ⊤.
Proof.
  apply ImpR. apply ExFalso.
Qed.

Theorem cut Γ Γ' φ ψ :
  Γ ⊢ φ  -> Γ' • φ ⊢ ψ ->
  Γ ⊎ Γ' ⊢ ψ.
Admitted.

Lemma preorder_singleton  φ ψ:
  {[φ]} ⊢ ψ -> (φ ≼ ψ).
Proof.
intro H.
assert (H3: (φ ≼ ψ) = ({[φ]} ⊢ ψ)) by (apply proper_Provable; ms).
rewrite H3.
apply H.
Qed.

Corollary cut2 φ ψ θ:
  (φ ≼ ψ) -> (ψ ≼ θ) ->
  φ ≼ θ.
Proof.
  intros H1 H2.
  assert ({[φ]} ⊎ ∅ ⊢ θ). {
  peapply (cut  {[φ]} ∅ ψ θ).
  - peapply H1.
  - apply H2.
  }
  apply H.
Qed.

Lemma simp_equiv_or_L φ ψ : 
  (φ  ≼ simp φ) -> (ψ  ≼ simp ψ) ->
  (φ ∨ ψ) ≼ simp (φ ∨ ψ).
Proof.
intros Hφ Hψ.
simpl. unfold simp_or. 
case decide as [Hbot |].
- apply OrL.
  + rewrite Hbot in Hφ.
    apply exfalso. apply Hφ.
  + apply Hψ.
- case decide as [Hbot |].
  + apply OrL.
    * apply Hφ.
    * rewrite Hbot in Hψ.
      apply exfalso. apply Hψ.
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

Lemma simp_equiv_or_R φ ψ : 
  (simp φ ≼ φ) -> (simp ψ ≼ ψ) ->
  simp (φ ∨ ψ) ≼ (φ ∨ ψ).
Proof.
intros Hφ Hψ.
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

Lemma simp_equiv_or φ ψ: 
  (φ ≼ simp φ) * (simp φ ≼ φ) ->
  (ψ ≼ simp ψ) * (simp ψ ≼ ψ) ->
  ((φ ∨ ψ) ≼ simp (φ ∨ ψ)) * (simp (φ ∨ ψ) ≼ (φ ∨ ψ)).
Proof.
intros IHφ IHψ.
split; [ apply simp_equiv_or_L | apply simp_equiv_or_R]; try apply IHφ ; try apply IHψ.
Qed.

Lemma simp_equiv_and_L φ ψ : 
  (φ  ≼ simp φ) -> (ψ  ≼ simp ψ) ->
  (φ ∧ ψ) ≼ simp (φ ∧ ψ).
Proof.
intros Hφ Hψ.
simpl. unfold simp_and. 
case decide as [Hbot |].
- rewrite Hbot in Hφ.
  apply AndL. apply weakening.
  apply exfalso. apply Hφ.
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


Lemma simp_equiv_and_R φ ψ : 
  (simp φ ≼ φ) -> (simp ψ ≼ ψ) ->
  simp (φ ∧ ψ) ≼  φ ∧ ψ.
Proof.
intros Hφ Hψ.
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
         ++ apply AndR; [ apply Hφ| rewrite Heq ; apply Hψ].
         ++ apply AndL.
            apply AndR; [|exch 0]; apply weakening; [apply Hφ | apply Hψ].
Qed.


Lemma simp_equiv_and φ ψ: 
  (φ ≼ simp φ) * (simp φ ≼ φ) ->
  (ψ ≼ simp ψ) * (simp ψ ≼ ψ) ->
  ((φ ∧ ψ) ≼ simp (φ ∧ ψ)) * (simp (φ ∧ ψ) ≼ (φ ∧ ψ)).
Proof.
intros IHφ IHψ.
split; [ apply simp_equiv_and_L | apply simp_equiv_and_R]; try apply IHφ ; try apply IHψ.
Qed.


Lemma simp_equiv_imp_L φ ψ : 
  (simp φ ≼ φ) ->
  (ψ ≼ simp ψ) ->
  (φ → ψ) ≼ simp (φ → ψ).
Proof.
intros HφR HψL.
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
  + case decide as [].
    * apply ImpR.
      apply ExFalso.
    * apply ImpR.
      exch 0.
      apply ImpL.
      -- apply weakening. apply HφR.
      -- exch 0. apply weakening.
         apply HψL.
Qed.

Lemma simp_equiv_imp_R φ ψ : 
  (φ ≼ simp φ) ->
  (simp ψ ≼ ψ) ->
  simp (φ → ψ) ≼ (φ → ψ).
Proof.
intros HφL HψR.
simpl. unfold simp_imp.
case decide as [Htop |].
- apply ImpR. 
  apply weakening.
  apply HψR.
- case decide as [Htop |].
  + rewrite Htop in HφL.
    apply ImpR.
    apply exfalso.
    exch 0. apply weakening.
    apply HφL.
  + case decide as [Heq |].
    * apply ImpR.
      exch 0. apply weakening.
      rewrite <- Heq in HψR.
      eapply cut2.
      -- apply HφL.
      -- apply HψR.
    * apply ImpR.
      exch 0.
      apply ImpL.
      -- apply weakening. apply HφL.
      -- exch 0. apply weakening.
         apply HψR.
Qed.

Lemma simp_equiv_imp φ ψ: 
  (φ ≼ simp φ) * (simp φ ≼ φ) ->
  (ψ ≼ simp ψ) * (simp ψ ≼ ψ) ->
  ((φ → ψ) ≼ simp (φ → ψ)) * (simp (φ → ψ) ≼ (φ → ψ)).
Proof.
intros IHφ IHψ.
split; [ apply simp_equiv_imp_L | apply simp_equiv_imp_R]; try apply IHφ ; try apply IHψ.
Qed.

Theorem simp_equiv φ : 
  (φ ≼ (simp φ)) * ((simp φ) ≼ φ).
Proof.
remember (weight φ) as w.
assert(Hle : weight φ  ≤ w) by lia.
clear Heqw. revert φ Hle.
induction w; intros φ Hle; [destruct φ ; simpl in Hle; lia|].
destruct φ; simpl; try (split ; apply generalised_axiom); 
[eapply (simp_equiv_and φ1  φ2)|
 eapply (simp_equiv_or φ1  φ2)|
eapply (simp_equiv_imp φ1  φ2)]; apply IHw;
[assert (Hφ1w: weight φ1 < weight (φ1 ∧ φ2))|
assert (Hφ1w: weight φ2 < weight (φ1 ∧ φ2))|
assert (Hφ1w: weight φ1 < weight (φ1 ∨ φ2))|
assert (Hφ1w: weight φ2 < weight (φ1 ∨ φ2))|
assert (Hφ1w: weight φ1 < weight (φ1 → φ2))|
assert (Hφ1w: weight φ2 < weight (φ1 → φ2))]; simpl; lia.
Qed.

Require Import ISL.PropQuantifiers.

Definition E_simplified (p: variable) (ψ: form) := simp (Ef p ψ).
Definition A_simplified (p: variable) (ψ: form) := simp (Af p ψ).

Lemma bot_vars_incl V:
vars_incl ⊥ V.
Proof.
  intros x H.
  unfold In.
  induction V; auto.
Qed.


Lemma top_vars_incl V:
vars_incl ⊤ V.
Proof.
  intros x H.
  unfold In.
  induction V. 
  - unfold occurs_in in H.
    lia.
  - auto.
Qed.

Lemma and_vars_incl_L φ ψ V:
  vars_incl (And φ ψ) V ->
  vars_incl φ V * vars_incl ψ V.
Proof.
  intros H.
  split; intros x H1; apply H; simpl; auto.
Qed.


Lemma and_vars_incl_R φ ψ V:
  vars_incl φ V ->
  vars_incl ψ V ->
  vars_incl (And φ ψ) V.
Proof.
  unfold vars_incl.
  simpl.
  intuition.
Qed.

Lemma vars_incl_simp φ V :
  vars_incl φ V -> vars_incl (simp φ) V.
Proof.
intro H.
induction φ; auto.
- simpl. unfold simp_and. 
  case decide as [].
  + apply bot_vars_incl.
  + case decide as [].
    * apply bot_vars_incl.
    * case decide as [].
      --  apply IHφ2.
          eapply and_vars_incl_L.
          apply H.
      -- case decide as [].
         ++ apply IHφ1.
            apply (and_vars_incl_L _  φ2).
            apply H.
         ++ case decide as [].
            ** apply IHφ1.
               apply (and_vars_incl_L _  φ2).
               apply H.
            ** apply and_vars_incl_R; 
               [ apply IHφ1; apply (and_vars_incl_L _  φ2)|
                  apply IHφ2; eapply and_vars_incl_L];
               apply H.
- simpl. unfold simp_or. 
  case decide as [].
  + apply IHφ2.
    eapply and_vars_incl_L.
    apply H.
  + case decide as [].
    * apply IHφ1.
      apply (and_vars_incl_L _  φ2).
      apply H.
    * case decide as [].
      -- apply top_vars_incl.
      -- case decide as [].
         ++ apply top_vars_incl.
         ++ case decide as [].
            ** apply IHφ1.
               apply (and_vars_incl_L _  φ2).
               apply H.
            ** apply and_vars_incl_R; 
               [ apply IHφ1; apply (and_vars_incl_L _  φ2)|
                  apply IHφ2; eapply and_vars_incl_L];
               apply H.

- simpl. unfold simp_imp. 
  case decide as [].
  + apply IHφ2.
    eapply and_vars_incl_L.
    apply H.
  + case decide as [].
    * apply top_vars_incl.
    * case decide as [].
      -- apply top_vars_incl.
      -- apply and_vars_incl_R;
        [ apply IHφ1; apply (and_vars_incl_L _  φ2)|
          apply IHφ2; eapply and_vars_incl_L];
          apply H.
Qed.

Theorem iSL_uniform_interpolation_simp p V: p ∉ V ->
  ∀ φ, vars_incl φ (p :: V) ->
    (vars_incl (E_simplified p φ) V)
  * (φ ≼ E_simplified p φ)
  * (∀ ψ, vars_incl ψ V -> (φ ≼ ψ) -> E_simplified p φ ≼ ψ)
  * (vars_incl (A_simplified p φ) V)
  * (A_simplified p φ ≼ φ)
  * (∀ θ, vars_incl θ V -> (θ ≼ φ) -> (θ ≼ A_simplified p φ)).
Proof.

intros Hp φ Hvarsφ.
assert (Hislφ : 
    (vars_incl (Ef p φ) V)
  * ({[φ]} ⊢ (Ef p φ))
  * (∀ ψ, vars_incl ψ V -> {[φ]} ⊢ ψ -> {[Ef p φ]} ⊢ ψ)
  * (vars_incl (Af p φ) V)
  * ({[Af p φ]} ⊢ φ)
  * (∀ θ, vars_incl θ V -> {[θ]} ⊢ φ -> {[θ]} ⊢ Af p φ)) by 
    (apply iSL_uniform_interpolation; [apply Hp | apply Hvarsφ]).
repeat split.
  + intros Hx.
    eapply vars_incl_simp.
    apply Hislφ.
  + eapply cut2.
    * assert (Hef: ({[φ]} ⊢ Ef p φ)) by apply Hislφ.
      apply preorder_singleton.
      apply Hef.
    * apply (simp_equiv  (Ef p φ)).
  + intros ψ Hψ Hyp.
    eapply cut2.
    * apply (simp_equiv  (Ef p φ)).
    * assert (Hef: ({[Ef p φ]} ⊢ ψ)) by (apply Hislφ; [apply Hψ | peapply Hyp]).
      apply preorder_singleton.
      apply Hef.
  + intros Hx.
    eapply vars_incl_simp.
    apply Hislφ.
  + eapply cut2.
    * apply (simp_equiv  (Af p φ)).
    * apply preorder_singleton.
      apply Hislφ.
  + intros ψ Hψ Hyp.
    eapply cut2.
    * assert (Hef: ({[ψ]} ⊢ Af p φ)) by (apply Hislφ; [apply Hψ | peapply Hyp]).
      apply preorder_singleton.
      apply Hef.
    * apply (simp_equiv  (Af p φ)).
Qed.

Require Import String.

Local Open Scope string_scope.

Example ex1: simp (Implies (Var "a")  (And (Var "b") (Var "b" ))) = Implies (Var "a")  (Var "b").
Proof. reflexivity. Qed.


Example ex2: simp (Implies (Var "a")  (Or (Var "b") (Var "b" ))) = Implies (Var "a")  (Var "b").
Proof. reflexivity. Qed.


Example ex3: simp (Implies (Var "a")  (Var "a")) = Implies Bot Bot.
Proof. reflexivity. Qed.


Example ex4: simp (Or (Implies (Var "a")  (Var "a")) (Implies (Var "a")  (Var "a"))) = Implies Bot Bot.
Proof. reflexivity. Qed.

Example ex5: simp (And (Implies (Var "a")  (Var "a")) (Implies (Var "a")  (Var "a"))) = Implies Bot Bot.
Proof. reflexivity. Qed.
