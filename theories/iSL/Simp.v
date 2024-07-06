Require Import ISL.Environments ISL.Sequents ISL.SequentProps ISL.Cut.


Definition obviously_smaller φ ψ :=
  if decide (φ = ⊥) then Lt
  else if decide (ψ = ⊥) then Gt
  else if decide (φ = ⊤) then Gt
  else if decide (ψ = ⊤) then Lt
  else if decide (φ = ψ) then Lt
  else Eq.


Definition choose_or φ ψ :=
match obviously_smaller φ ψ with
  | Lt => ψ
  | Gt => φ
  | Eq => φ ∨ ψ
 end.

Definition simp_or φ ψ := 
match (φ, ψ) with
  | (φ, ψ1 ∨ ψ2) => 
      match obviously_smaller φ ψ1 with
      | Lt => ψ1 ∨ ψ2
      | Gt => φ ∨ ψ2
      | Eq => φ ∨ (ψ1 ∨ ψ2)
      end
  |(φ,ψ) => choose_or φ ψ
end.

Infix "⊻" := simp_or (at level 65).

Fixpoint simp_ors φ ψ :=
match (φ,ψ) with
  |(φ1 ∨ φ2, ψ1 ∨ ψ2) => φ1 ⊻ (ψ1 ⊻ (simp_ors φ2 ψ2))
  |(φ1 ∨ φ2, ψ) => ψ ⊻ (φ1 ∨ φ2)
  |(φ, ψ1 ∨ ψ2) => φ ⊻ (ψ1 ∨ ψ2)
  |(φ, ψ) => φ ⊻ ψ
end.

Definition choose_and φ ψ :=
match obviously_smaller φ ψ with
  | Lt => φ
  | Gt => ψ
  | Eq => φ ∧ ψ
 end.

Definition simp_and φ ψ := 
match (φ, ψ) with
  | (φ, ψ1 ∧ ψ2) => 
      match obviously_smaller φ ψ1 with
      | Lt => φ ∧ ψ2
      | Gt => ψ1 ∧ ψ2
      | Eq => φ ∧ (ψ1 ∧ ψ2)
      end
  |(φ,ψ) => choose_and φ ψ
end.


Infix "⊼" := simp_and (at level 60).


Fixpoint simp_ands φ ψ :=
match (φ,ψ) with
  |(φ1 ∧ φ2, ψ1 ∧ ψ2) => φ1 ⊼ (ψ1 ⊼ (simp_ands φ2 ψ2))
  |(φ1 ∧ φ2, ψ) => ψ ⊼ (φ1 ∧ φ2)
  |(φ, ψ1 ∧ ψ2) => φ ⊼ (ψ1 ∧ ψ2)
  |(φ, ψ) => φ ⊼ ψ
end.

Definition simp_imp φ ψ :=
  if decide (φ = ⊤) then ψ
  else if decide (φ = ⊥) then ⊤
  else if decide (φ = ψ) then ⊤
  else φ → ψ.

Fixpoint simp φ :=
match φ with
  | φ ∨ ψ => simp_ors (simp φ) (simp ψ)
  | φ ∧ ψ => simp_ands (simp φ) (simp ψ)
  | φ → ψ => simp_imp (simp φ) (simp ψ)
  | _ => φ
end.


Definition Lindenbaum_Tarski_preorder φ ψ :=
  ∅ • φ ⊢ ψ.

Notation "φ ≼ ψ" := (Lindenbaum_Tarski_preorder φ ψ) (at level 149).

Lemma top_provable Γ :
 Γ ⊢ ⊤.
Proof.
  apply ImpR. apply ExFalso.
Qed.

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

Lemma obviously_smaller_compatible_LT φ ψ :
  obviously_smaller φ ψ = Lt -> φ ≼ ψ.
Proof.
intro H.
unfold obviously_smaller in H.
case decide in H.
- rewrite e. apply ExFalso.
- case decide in H.
  + contradict H; auto.
  + case decide in H.
    * contradict H; auto.
    * case decide in H.
      -- rewrite e. apply top_provable.
      -- case decide in H.
         ++ rewrite e; apply generalised_axiom.
         ++ contradict H; auto.
Qed.


Lemma obviously_smaller_compatible_GT φ ψ :
  obviously_smaller φ ψ = Gt -> ψ ≼ φ .
Proof.
intro H.
unfold obviously_smaller in H.
case decide in H.
- contradict H; auto.
- case decide in H.
  + rewrite e. apply ExFalso.
  + case decide in H.
    * rewrite e. apply top_provable.
    * case decide in H.
      -- contradict H; auto.
      -- case decide in H; contradict H; auto.
Qed.

Lemma or_congruence φ ψ φ' ψ':
  (φ ≼ φ') -> (ψ ≼ ψ') ->
  (φ ∨ ψ) ≼ φ' ∨ ψ'.
Proof.
intros Hφ Hψ.
apply OrL.
- apply OrR1; apply Hφ. 
- apply OrR2; apply Hψ. 
Qed.


Lemma or_comm φ ψ:
  φ ∨ ψ ≼  ψ ∨ φ.
Proof.
apply OrL; [apply OrR2 | apply OrR1]; apply generalised_axiom.
Qed.


Lemma or_comm_ctx_L φ ψ ϴ:
  (φ ∨ ψ ≼ ϴ) -> ψ ∨ φ ≼ ϴ.
Proof.
intro H.
eapply cut2.
apply or_comm.
assumption.
Qed.

Lemma or_comm_ctx_R φ ψ ϴ:
  (ϴ ≼ φ ∨ ψ ) -> ϴ ≼ ψ ∨ φ.
Proof.
intro H.
eapply cut2.
apply H.
apply or_comm.
Qed.

Lemma or_assoc_R φ ψ ϴ :
  ((φ ∨ ψ) ∨ ϴ  ≼ φ ∨ (ψ ∨ ϴ)).
Proof.
  apply OrL.
  - apply OrL.
    + apply OrR1; apply generalised_axiom.
    + apply OrR2; apply OrR1; apply generalised_axiom.
  - apply OrR2; apply OrR2; apply generalised_axiom.
Qed.

Lemma or_assoc_L φ ψ ϴ :
  (φ ∨ (ψ ∨ ϴ)  ≼ (φ ∨ ψ) ∨ ϴ).
Proof.
  apply OrL.
  - apply OrR1; apply OrR1; apply generalised_axiom.
  - apply OrL.
    + apply OrR1; apply OrR2; apply generalised_axiom.
    + apply OrR2; apply generalised_axiom.
Qed.


Lemma or_assoc_ctx_L_R φ ψ ϴ a:
  (φ ∨ (ψ ∨ ϴ)  ≼ a) -> ((φ ∨ ψ) ∨ ϴ) ≼ a.
Proof.
intro H.
eapply cut2.
apply or_assoc_R.
assumption.
Qed.


Lemma or_assoc_ctx_R_L φ ψ ϴ a:
  (a ≼ (φ ∨ ψ) ∨ ϴ)  ->a ≼ φ ∨ (ψ ∨ ϴ).
Proof.
intro H.
eapply cut2.
apply H.
apply or_assoc_R.
Qed.



Lemma or_assoc_ctx_R_R φ ψ ϴ a:
  (a ≼ φ ∨ (ψ ∨ ϴ))  ->a ≼ (φ ∨ ψ) ∨ ϴ.
Proof.
intro H.
eapply cut2.
apply H.
apply or_assoc_L.
Qed.

Lemma choose_or_equiv_L φ ψ φ' ψ':
  (φ ≼ φ') -> (ψ ≼ ψ') ->
  (φ ∨ ψ) ≼ choose_or φ' ψ'.
Proof.
intros Hφ Hψ.
unfold choose_or.
case (decide (obviously_smaller φ' ψ' = Lt)); [intro HLt | intro Hneq1].
-rewrite HLt. apply OrL.
  + eapply cut2. 
    * apply Hφ.
    * apply obviously_smaller_compatible_LT; assumption.
  + assumption.
- case (decide (obviously_smaller φ' ψ' = Gt)); [intro HGt| intro Hneq2].
  + rewrite HGt. apply OrL.
    * assumption.
    * eapply cut2.
      -- eapply cut2.
         ++ apply Hψ.
         ++ apply obviously_smaller_compatible_GT. apply HGt.
      -- apply generalised_axiom.
  + case (decide (obviously_smaller φ' ψ' = Eq)); [intro HEq| intro Hneq3].
    * rewrite HEq. apply or_congruence; [apply Hφ | apply Hψ].
    * destruct (obviously_smaller φ' ψ'); [contradict Hneq3 | contradict Hneq1 |contradict Hneq2]; trivial.
Qed.

Lemma simp_or_equiv_L φ ψ φ' ψ' : 
  (φ ≼ φ') -> (ψ ≼ ψ') ->
  (φ ∨ ψ) ≼ simp_or φ' ψ'.
Proof.
intros Hφ Hψ.
unfold simp_or.
destruct ψ'; try (apply choose_or_equiv_L; assumption).
case (decide (obviously_smaller φ' ψ'1 = Lt)); [intro HLt | intro Hneq1].
- rewrite HLt. apply OrL.
  + eapply cut2. 
    * apply Hφ.
    * apply OrR1. apply obviously_smaller_compatible_LT; assumption.
  + assumption.
- case (decide (obviously_smaller φ' ψ'1 = Gt)); [intro HGt| intro Hneq2].
  + rewrite HGt. apply OrL.
    * apply OrR1; assumption.
    * eapply cut2.
      -- apply Hψ. 
      -- apply or_congruence; [apply obviously_smaller_compatible_GT; assumption| apply generalised_axiom].
  + case (decide (obviously_smaller φ' ψ'1 = Eq)); [intro HEq| intro Hneq3].
    * rewrite HEq. apply or_congruence; [apply Hφ | apply Hψ].
    * destruct (obviously_smaller φ' ψ'1); [contradict Hneq3 | contradict Hneq1 |contradict Hneq2]; trivial.
Qed.

Lemma choose_or_equiv_R φ ψ φ' ψ' : 
  (φ' ≼ φ) -> (ψ' ≼ ψ) ->
  choose_or φ' ψ' ≼  φ ∨ ψ.
Proof.
intros Hφ Hψ.
unfold choose_or.
case (decide (obviously_smaller φ' ψ' = Lt)); [intro HLt | intro Hneq1].
- rewrite HLt. apply OrR2; assumption.
- case (decide (obviously_smaller φ' ψ' = Gt)); [intro HGt| intro Hneq2].
  + rewrite HGt. apply OrR1; assumption.
  + case (decide (obviously_smaller φ' ψ' = Eq)); [intro HEq| intro Hneq3].
    * rewrite HEq. apply or_congruence; [apply Hφ | apply Hψ].
    * destruct (obviously_smaller φ' ψ'); [contradict Hneq3 | contradict Hneq1 |contradict Hneq2]; trivial.
Qed.


Lemma simp_or_equiv_R φ ψ φ' ψ' : 
  (φ' ≼ φ) -> (ψ' ≼ ψ) ->
  simp_or φ' ψ' ≼  φ ∨ ψ.
Proof.
intros Hφ Hψ.
unfold simp_or.
destruct ψ'; try (apply choose_or_equiv_R; assumption).
case (decide (obviously_smaller φ' ψ'1 = Lt)); [intro HLt | intro Hneq1].
- rewrite HLt. apply OrR2; assumption.
- case (decide (obviously_smaller φ' ψ'1 = Gt)); [intro HGt| intro Hneq2].
  + rewrite HGt. apply OrL.
    * apply OrR1; assumption.
    * apply OrL_rev in Hψ.
      apply OrR2.
      apply Hψ.
  + case (decide (obviously_smaller φ' ψ'1 = Eq)); [intro HEq| intro Hneq3].
    * rewrite HEq. apply or_congruence; [apply Hφ | apply Hψ].
    * destruct (obviously_smaller φ' ψ'1); [contradict Hneq3 | contradict Hneq1 |contradict Hneq2]; trivial.
Qed.

Lemma simp_or_comm φ ψ :
  (φ ⊻ ψ) ≼ (ψ ⊻  φ).
Proof.
  apply (cut2 _ (φ ∨ ψ) _).
  - apply simp_or_equiv_R; apply generalised_axiom.
  - apply (cut2 _ (ψ ∨ φ) _).
    + apply or_comm.
    + apply simp_or_equiv_L; apply generalised_axiom.
Qed.

Lemma simp_or_comm_ctx_R  a φ ψ :
  (a ≼ φ ⊻ ψ)  -> a ≼ ψ ⊻ φ.
Proof.
  intro H.
  eapply cut2.
  apply H.
  apply simp_or_comm.
Qed.

Lemma simp_or_comm_ctx_L  a φ ψ :
  (φ ⊻ ψ ≼ a)  ->  ψ ⊻ φ ≼ a.
Proof.
  intro H.
  eapply cut2.
  apply simp_or_comm.
  apply H.
Qed.


Lemma simp_ors_self_equiv_L φ ψ:
  (φ ∨ ψ) ≼ simp_ors φ ψ.
Proof.
generalize ψ.
induction φ;
intro ψ0;
destruct ψ0; simpl; try (eapply simp_or_equiv_L; apply generalised_axiom);
try (apply simp_or_comm_ctx_R; apply simp_or_equiv_L; apply generalised_axiom).
assert (H: φ1 ∨ ψ0_1 ∨ φ2 ∨ ψ0_2 ≼ φ1 ⊻ (ψ0_1 ⊻ simp_ors φ2 ψ0_2)).
- apply simp_or_equiv_L.
  + apply generalised_axiom.
  + apply simp_or_equiv_L.
    * apply generalised_axiom.
    * apply IHφ2.
- eapply cut2.
  + apply or_assoc_ctx_L_R.
    apply OrL.
    * apply OrR1. apply generalised_axiom.
    * apply OrR2. apply or_comm_ctx_L.
      apply OrL.
      -- apply or_assoc_ctx_R_L. apply or_comm_ctx_L.
        apply or_comm_ctx_L.
        apply or_comm_ctx_R.
        apply or_assoc_ctx_R_L.
        apply OrR1.
        apply or_comm.
      -- apply OrR2; apply OrR1; apply generalised_axiom.
  + assumption.
Qed.


Lemma simp_equiv_or_L φ ψ : 
  (φ  ≼ simp φ) -> (ψ  ≼ simp ψ) ->
  (φ ∨ ψ) ≼ simp (φ ∨ ψ).
Proof.
intros Hφ Hψ.
eapply cut2.
apply or_congruence; [apply Hφ | apply Hψ].
apply simp_ors_self_equiv_L.
Qed.


Lemma simp_ors_self_equiv_R φ ψ:
  simp_ors φ ψ ≼ φ ∨ ψ.
Proof.
generalize ψ.
induction φ;
intro ψ0;
destruct ψ0; 
simpl; try (eapply simp_or_equiv_R; apply generalised_axiom);
try (apply simp_or_comm_ctx_L; apply simp_or_equiv_R; apply generalised_axiom).
assert (H: φ1 ⊻ (ψ0_1 ⊻ simp_ors φ2 ψ0_2) ≼ φ1 ∨ ψ0_1 ∨ φ2 ∨ ψ0_2).
- apply simp_or_equiv_R.
  + apply generalised_axiom.
  + apply simp_or_equiv_R.
    * apply generalised_axiom.
    * apply IHφ2.
- apply or_assoc_ctx_R_R.
  eapply cut2.
  + apply H.
  + apply OrL.
    * apply OrR1; apply generalised_axiom.
    * apply OrR2. apply or_comm_ctx_R. apply or_assoc_ctx_R_R.
      apply OrL.
      -- apply OrR1; apply generalised_axiom.
      -- apply OrR2; apply or_comm.
Qed.

Lemma simp_equiv_or_R φ ψ: 
  (simp φ ≼ φ) -> (simp ψ ≼ ψ) ->
  simp (φ ∨ ψ) ≼ (φ ∨ ψ).
Proof.
intros Hφ Hψ.
eapply cut2.
apply simp_ors_self_equiv_R.
apply or_congruence; [apply Hφ | apply Hψ].
Qed.

Lemma simp_equiv_or φ ψ: 
  (φ ≼ simp φ) * (simp φ ≼ φ) ->
  (ψ ≼ simp ψ) * (simp ψ ≼ ψ) ->
  ((φ ∨ ψ) ≼ simp (φ ∨ ψ)) * (simp (φ ∨ ψ) ≼ (φ ∨ ψ)).
Proof.
intros IHφ IHψ.
split; [ apply simp_equiv_or_L | apply simp_equiv_or_R]; try apply IHφ ; try apply IHψ.
Qed.


Lemma and_congruence φ ψ φ' ψ':
  (φ ≼ φ') -> (ψ ≼ ψ') ->
  (φ ∧ ψ) ≼ φ' ∧ ψ'.
Proof.
intros Hφ Hψ.
apply AndL.
apply AndR.
- apply weakening. apply Hφ. 
- exch 0. apply weakening. apply Hψ. 
Qed.


Lemma and_comm φ ψ:
  φ ∧ ψ ≼  ψ ∧ φ.
Proof.
apply AndL; apply AndR; [exch 0|]; apply weakening; apply generalised_axiom.
Qed.


Lemma and_comm_ctx_L φ ψ ϴ:
  (φ ∧ ψ ≼ ϴ) -> ψ ∧ φ ≼ ϴ.
Proof.
intro H.
eapply cut2.
apply and_comm.
assumption.
Qed.


Lemma and_assoc_R φ ψ ϴ :
  ((φ ∧ ψ) ∧ ϴ  ≼ φ ∧ (ψ ∧ ϴ)).
Proof.
  apply AndL; exch 0; apply AndL.
  apply AndR.
  - exch 0. apply generalised_axiom.
  - apply AndR.
    + apply generalised_axiom.
    +  exch 1. exch 0. apply generalised_axiom.
Qed.

Lemma and_assoc_L φ ψ ϴ :
  (φ ∧ (ψ ∧ ϴ)  ≼ (φ ∧ ψ) ∧ ϴ).
Proof.
  apply AndL; apply AndL.
  apply AndR.
  - apply AndR.
    + exch 1. exch 0. apply generalised_axiom.
    + exch 0. apply generalised_axiom.
  - apply generalised_axiom.
Qed.


Lemma and_assoc_ctx_L_R φ ψ ϴ a:
  (φ ∧ (ψ ∧ ϴ)  ≼ a) -> ((φ ∧ ψ) ∧ ϴ) ≼ a.
Proof.
intro H.
eapply cut2.
apply and_assoc_R.
assumption.
Qed.


Lemma and_assoc_ctx_R_L φ ψ ϴ a:
  (a ≼ (φ ∧ ψ) ∧ ϴ) -> a ≼ φ ∧ (ψ ∧ ϴ).
Proof.
intro H.
eapply cut2.
apply H.
apply and_assoc_R.
Qed.



Lemma and_assoc_ctx_R_R φ ψ ϴ a:
  (a ≼ φ ∧ (ψ ∧ ϴ)) -> a ≼ (φ ∧ ψ) ∧ ϴ.
Proof.
intro H.
eapply cut2.
apply H.
apply and_assoc_L.
Qed.

Lemma choose_and_equiv_L φ ψ φ' ψ':
  (φ ≼ φ') -> (ψ ≼ ψ') ->
  (φ ∧ ψ) ≼ choose_and φ' ψ'.
Proof.
intros Hφ Hψ.
unfold choose_and.
case (decide (obviously_smaller φ' ψ' = Lt)); [intro HLt | intro Hneq1].
- rewrite HLt. apply AndL. apply weakening. apply Hφ.
- case (decide (obviously_smaller φ' ψ' = Gt)); [intro HGt| intro Hneq2].
  + rewrite HGt. apply AndL. exch 0. apply weakening. apply Hψ.
  + case (decide (obviously_smaller φ' ψ' = Eq)); [intro HEq| intro Hneq3].
    * rewrite HEq. apply and_congruence; [apply Hφ | apply Hψ].
    * destruct (obviously_smaller φ' ψ'); [contradict Hneq3 | contradict Hneq1 |contradict Hneq2]; trivial.
Qed.


Lemma choose_and_equiv_R φ ψ φ' ψ':
  (φ' ≼ φ) -> (ψ' ≼ ψ) ->
  choose_and φ' ψ' ≼  φ ∧ ψ.
Proof.
intros Hφ Hψ.
unfold choose_and.
case (decide (obviously_smaller φ' ψ' = Lt)); [intro HLt | intro Hneq1].
- rewrite HLt. apply AndR.
  + assumption.
  + eapply cut2.
    * apply obviously_smaller_compatible_LT. apply HLt.
    * assumption.
- case (decide (obviously_smaller φ' ψ' = Gt)); [intro HGt| intro Hneq2].
  + rewrite HGt. apply AndR.
    * eapply cut2.
      -- apply obviously_smaller_compatible_GT. apply HGt.
      -- assumption.
    * assumption.
  + case (decide (obviously_smaller φ' ψ' = Eq)); [intro HEq| intro Hneq3].
    * rewrite HEq. apply and_congruence; [apply Hφ | apply Hψ].
    * destruct (obviously_smaller φ' ψ'); [contradict Hneq3 | contradict Hneq1 |contradict Hneq2]; trivial.
Qed.


Lemma simp_and_equiv_L φ ψ φ' ψ' : 
  (φ ≼ φ') -> (ψ ≼ ψ') ->
  (φ ∧ ψ) ≼ simp_and φ' ψ'.
Proof.
intros Hφ Hψ.
unfold simp_and.
destruct ψ'; try (apply choose_and_equiv_L; assumption).
case (decide (obviously_smaller φ' ψ'1 = Lt)); [intro HLt | intro Hneq1].
- rewrite HLt. apply and_congruence.
  + assumption.
  + apply AndR_rev in Hψ; apply Hψ.
- case (decide (obviously_smaller φ' ψ'1 = Gt)); [intro HGt| intro Hneq2].
  + rewrite HGt. apply AndL. exch 0. apply weakening. assumption.
  + case (decide (obviously_smaller φ' ψ'1 = Eq)); [intro HEq| intro Hneq3].
    * rewrite HEq. apply and_congruence; [apply Hφ | apply Hψ].
    * destruct (obviously_smaller φ' ψ'1); [contradict Hneq3 | contradict Hneq1 |contradict Hneq2]; trivial.
Qed.

Lemma simp_and_equiv_R φ ψ φ' ψ' : 
  (φ' ≼ φ) -> (ψ' ≼ ψ) ->
  simp_and φ' ψ' ≼  φ ∧ ψ.
Proof.
intros Hφ Hψ.
unfold simp_and.
destruct ψ'; try (apply choose_and_equiv_R; assumption).
case (decide (obviously_smaller φ' ψ'1 = Lt)); [intro HLt | intro Hneq1].
- rewrite HLt. apply AndR.
  + apply AndL. apply weakening; assumption.
  + apply (cut2 _ ( ψ'1 ∧ ψ'2) _).
    * apply and_congruence; 
      [now apply obviously_smaller_compatible_LT | apply generalised_axiom].
    * assumption.
- case (decide (obviously_smaller φ' ψ'1 = Gt)); [intro HGt| intro Hneq2].
  + rewrite HGt. apply AndR.
    * apply AndL. apply weakening. eapply cut2.
      -- apply obviously_smaller_compatible_GT; apply HGt.
      -- assumption.
    * assumption.
  + case (decide (obviously_smaller φ' ψ'1 = Eq)); [intro HEq| intro Hneq3].
    * rewrite HEq. apply and_congruence; [apply Hφ | apply Hψ].
    * destruct (obviously_smaller φ' ψ'1); [contradict Hneq3 | contradict Hneq1 |contradict Hneq2]; trivial.
Qed.

Lemma simp_and_comm φ ψ :
  (φ ⊼ ψ) ≼ (ψ ⊼ φ).
Proof.
  apply (cut2 _ (φ ∧ ψ) _).
  - apply simp_and_equiv_R; apply generalised_axiom.
  - apply (cut2 _ (ψ ∧ φ) _).
    + apply and_comm.
    + apply simp_and_equiv_L; apply generalised_axiom.
Qed.

Lemma simp_and_comm_ctx_R  a φ ψ :
  (a ≼ φ ⊼ ψ)  -> a ≼ ψ ⊼ φ.
Proof.
  intro H.
  eapply cut2.
  apply H.
  apply simp_and_comm.
Qed.

Lemma simp_and_comm_ctx_L  a φ ψ :
  (φ ⊼ ψ ≼ a)  ->  ψ ⊼ φ ≼ a.
Proof.
  intro H.
  eapply cut2.
  apply simp_and_comm.
  apply H.
Qed.

Lemma simp_ors_self_equiv_L2 φ ψ:
  (φ ∨ ψ) ≼ simp_ors φ ψ.
Proof.
generalize ψ.
induction φ;
intro ψ0;
destruct ψ0; simpl; try (eapply simp_or_equiv_L; apply generalised_axiom);
try (apply simp_or_comm_ctx_R; apply simp_or_equiv_L; apply generalised_axiom).
assert (H: φ1 ∨ ψ0_1 ∨ φ2 ∨ ψ0_2 ≼ φ1 ⊻ (ψ0_1 ⊻ simp_ors φ2 ψ0_2)).
- apply simp_or_equiv_L.
  + apply generalised_axiom.
  + apply simp_or_equiv_L.
    * apply generalised_axiom.
    * apply IHφ2.
- eapply cut2.
  + apply or_assoc_ctx_L_R.
    apply OrL.
    * apply OrR1. apply generalised_axiom.
    * apply OrR2. apply or_comm_ctx_L.
      apply OrL.
      -- apply or_assoc_ctx_R_L. apply or_comm_ctx_L.
        apply or_comm_ctx_L.
        apply or_comm_ctx_R.
        apply or_assoc_ctx_R_L.
        apply OrR1.
        apply or_comm.
      -- apply OrR2; apply OrR1; apply generalised_axiom.
  + assumption.
Qed.

Lemma simp_ands_self_equiv_L φ ψ:
  (φ ∧ ψ) ≼ simp_ands φ ψ.
Proof.
generalize ψ.
induction φ;
intro ψ0;
destruct ψ0; simpl; try (eapply simp_and_equiv_L; apply generalised_axiom);
try (apply simp_and_comm_ctx_R; apply simp_and_equiv_L; apply generalised_axiom).
assert (H: φ1 ∧ ψ0_1 ∧ φ2 ∧ ψ0_2 ≼ φ1 ⊼ (ψ0_1 ⊼ simp_ands φ2 ψ0_2)).
- apply simp_and_equiv_L.
  + apply generalised_axiom.
  + apply simp_and_equiv_L.
    * apply generalised_axiom.
    * apply IHφ2.
- eapply cut2.
  + apply and_assoc_ctx_L_R.
    do 3 (apply AndL).
    apply AndR.
    * exch 2. exch 1. exch 0. apply generalised_axiom.
    * apply AndR.
      -- exch 0. apply generalised_axiom.
      -- apply AndR.
         ++ exch 1. exch 0. apply generalised_axiom.
         ++ apply generalised_axiom.
  + assumption.
Qed.



Lemma simp_ands_self_equiv_R φ ψ:
  simp_ands φ ψ ≼ φ ∧ ψ.
Proof.
generalize ψ.
induction φ;
intro ψ0;
destruct ψ0; 
simpl; try (eapply simp_and_equiv_R; apply generalised_axiom);
try (apply simp_and_comm_ctx_L; apply simp_and_equiv_R; apply generalised_axiom).
assert (H: φ1 ⊼ (ψ0_1 ⊼ simp_ands φ2 ψ0_2) ≼ φ1 ∧ ψ0_1 ∧ φ2 ∧ ψ0_2).
- apply simp_and_equiv_R.
  + apply generalised_axiom.
  + apply simp_and_equiv_R.
    * apply generalised_axiom.
    * apply IHφ2.
- apply and_assoc_ctx_R_R.
  eapply cut2.
  + apply H.
  + do 3 (apply AndL).
    apply AndR.
    * exch 2. exch 1. exch 0. apply generalised_axiom.
    * apply AndR.
      -- exch 0. apply generalised_axiom.
      -- apply AndR.
         ++ exch 1. exch 0. apply generalised_axiom.
         ++ apply generalised_axiom.
Qed.


Lemma simp_equiv_and_L φ ψ : 
  (φ  ≼ simp φ) -> (ψ  ≼ simp ψ) ->
  (φ ∧ ψ) ≼ simp (φ ∧ ψ).
Proof.
intros Hφ Hψ.
eapply cut2.
apply and_congruence; [apply Hφ | apply Hψ].
apply simp_ands_self_equiv_L.
Qed.

Lemma simp_equiv_and_R φ ψ : 
  (simp φ ≼ φ) -> (simp ψ ≼ ψ) ->
  simp (φ ∧ ψ) ≼  φ ∧ ψ.
Proof.
intros Hφ Hψ.
eapply cut2.
apply simp_ands_self_equiv_R.
apply and_congruence; [apply Hφ | apply Hψ].
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
  - simpl in H. tauto.
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

Lemma or_vars_incl_L φ ψ V:
  vars_incl (Or φ ψ) V ->
  vars_incl φ V * vars_incl ψ V.
Proof.
  intros H.
  split; intros x H1; apply H; simpl; auto.
Qed.


Lemma or_vars_incl_R φ ψ V:
  vars_incl φ V ->
  vars_incl ψ V ->
  vars_incl (Or φ ψ) V.
Proof.
  unfold vars_incl.
  simpl.
  intuition.
Qed.

Lemma vars_incl_choose_or φ ψ V:
  vars_incl (Or φ ψ) V ->
  vars_incl (choose_or φ ψ) V.
Proof.
intros H.
unfold choose_or. 
destruct (obviously_smaller φ ψ).
- assumption.
- now apply (or_vars_incl_L  φ _).
- now apply (or_vars_incl_L  _ ψ).
Qed.

Lemma vars_incl_simp_or_equiv_or φ ψ V:
  vars_incl (Or φ ψ) V ->
  vars_incl (φ ⊻ ψ) V.
Proof.
intros H.
unfold simp_or.
destruct ψ; try (now apply vars_incl_choose_or).
destruct (obviously_smaller φ ψ1).
- assumption.
- now apply (or_vars_incl_L  φ _).
- apply or_vars_incl_R.
  + now apply (or_vars_incl_L _ (Or ψ1 ψ2)).
  + apply or_vars_incl_L in H. 
    apply (or_vars_incl_L ψ1 _).
    apply H.
Qed.

Lemma vars_incl_simp_ors φ ψ V :
  vars_incl φ V -> vars_incl ψ V ->
  vars_incl (simp_ors φ ψ) V.
Proof.
generalize ψ.
induction φ; intro ψ0; destruct ψ0; intros Hφ Hψ;
try ( apply vars_incl_simp_or_equiv_or; apply or_vars_incl_R; assumption).
simpl.
apply vars_incl_simp_or_equiv_or.
apply or_vars_incl_R.
- now apply (or_vars_incl_L _ φ2 _). 
- apply vars_incl_simp_or_equiv_or.
  apply or_vars_incl_R.
  + now apply (or_vars_incl_L _ ψ0_2 _). 
  +  apply IHφ2.
    * now apply (or_vars_incl_L  φ1 _ _). 
    * now apply (or_vars_incl_L  ψ0_1 _ _). 
Qed.


Lemma vars_incl_choose_and φ ψ V:
  vars_incl (And φ ψ) V ->
  vars_incl (choose_and φ ψ) V.
Proof.
intros H.
unfold choose_and. 
destruct (obviously_smaller φ ψ).
- assumption.
- now apply (and_vars_incl_L  _ ψ).
- now apply (and_vars_incl_L  φ _).
Qed.


Lemma vars_incl_simp_and_equiv_and φ ψ V:
  vars_incl (And φ ψ) V ->
  vars_incl (φ ⊼ ψ) V.
Proof.
intros H.
unfold simp_and.
destruct ψ; try (now apply vars_incl_choose_and).
destruct (obviously_smaller φ ψ1).
- assumption.
- apply and_vars_incl_R.
  + now apply (and_vars_incl_L _ (Or ψ1 ψ2)).
  + apply and_vars_incl_L in H. 
    apply (and_vars_incl_L ψ1 _).
    apply H.
- now apply (and_vars_incl_L  φ _).
Qed.

Lemma vars_incl_simp_ands φ ψ V :
  vars_incl φ V -> vars_incl ψ V ->
  vars_incl (simp_ands φ ψ) V.
Proof.
generalize ψ.
induction φ; intro ψ0; destruct ψ0; intros Hφ Hψ;
try ( apply vars_incl_simp_and_equiv_and; apply and_vars_incl_R; assumption).
simpl.
apply vars_incl_simp_and_equiv_and.
apply and_vars_incl_R.
- now apply (and_vars_incl_L _ φ2 _). 
- apply vars_incl_simp_and_equiv_and.
  apply and_vars_incl_R.
  + now apply (and_vars_incl_L _ ψ0_2 _). 
  +  apply IHφ2.
    * now apply (and_vars_incl_L  φ1 _ _). 
    * now apply (and_vars_incl_L  ψ0_1 _ _). 
Qed.

Lemma vars_incl_simp φ V :
  vars_incl φ V -> vars_incl (simp φ) V.
Proof.
intro H.
induction φ; auto.
- simpl. unfold simp_or. 
  apply vars_incl_simp_ands;
  [ apply IHφ1; apply (and_vars_incl_L _  φ2)|
  apply IHφ2; apply (and_vars_incl_L  φ1 _) ];
  assumption.
- simpl. unfold simp_or. 
  apply vars_incl_simp_ors;
  [ apply IHφ1; apply (or_vars_incl_L _  φ2)|
  apply IHφ2; apply (or_vars_incl_L  φ1 _) ];
  assumption.
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
