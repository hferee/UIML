Require Import ISL.Environments ISL.Sequents ISL.SequentProps ISL.Cut.

(* Checks "obvious" entailment conditions. If φ ⊢ ψ "obviously" then it returns Lt,
if ψ ⊢ φ "obviously" then it returns Gt. Eq corresponds to the unknown category, 
this means that we don't have enough information to determine a possible entailment. *)
Fixpoint obviously_smaller (φ : form) (ψ : form) :=
match (φ, ψ) with 
  |(Bot, _) => Lt
  |(_, Bot) => Gt
  |(Bot → _, _) => Gt
  |(_, Bot → _) => Lt
  |(φ ∧ ψ, ϴ) => match (obviously_smaller φ ϴ, obviously_smaller ψ ϴ) with
      | (Lt, _) | (_, Lt) => Lt
      | (Gt, Gt) => Gt
      | _ => Eq
      end
  |(φ ∨ ψ, ϴ) => match (obviously_smaller φ ϴ, obviously_smaller ψ ϴ) with
      | (Gt, _) | (_, Gt) => Gt
      | (Lt, Lt) => Lt
      | _ => Eq
      end
  |(φ, ψ) => if decide (φ = ψ) then Lt else Eq
end.


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
  | (φ, ψ1 ∧ ψ2) => 
      if decide (obviously_smaller φ ψ1 = Gt )
      then φ
      else φ ∨ (ψ1 ∧ ψ2)
  |(φ,ψ) => choose_or φ ψ
end.


Infix "⊻" := simp_or (at level 65).

(* Normalises a large disjunctions flattening them to the right. It assumes
that there are no disjuctions on the left of any of the input formulas, i.e.
φ and ψ cannot be of the form ((... ∨ ... ) ∨ ...). Since this function is called 
with the inputs previously simplified (see `simp`) this invariant is assured. *)
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
  | (φ, ψ1 ∨ ψ2) => 
      if decide (obviously_smaller φ ψ1 = Lt )
      then φ
      else φ ∧ (ψ1 ∨ ψ2)
  |(φ,ψ) => choose_and φ ψ
end.


Infix "⊼" := simp_and (at level 60).

(* Same as `simp_ors` but for large conjunctions. *)
Fixpoint simp_ands φ ψ :=
match (φ,ψ) with
  |(φ1 ∧ φ2, ψ1 ∧ ψ2) => φ1 ⊼ (ψ1 ⊼ (simp_ands φ2 ψ2))
  |(φ1 ∧ φ2, ψ) => ψ ⊼ (φ1 ∧ φ2)
  |(φ, ψ1 ∧ ψ2) => φ ⊼ (ψ1 ∧ ψ2)
  |(φ, ψ) => φ ⊼ ψ
end.


Definition simp_imp φ ψ :=
  if decide (obviously_smaller φ ψ = Lt) then ⊤
  else if decide (obviously_smaller φ ⊥ = Lt) then ⊤
  else if decide (obviously_smaller ψ ⊤ = Gt) then ⊤
  else if decide (obviously_smaller φ ⊤ = Gt) then ψ
  else if decide (obviously_smaller ψ ⊥ = Lt) then ¬φ
  else φ → ψ.

Fixpoint simp φ :=
match φ with
  | φ ∨ ψ => simp_ors (simp φ) (simp ψ)
  | φ ∧ ψ => simp_ands (simp φ) (simp ψ)
  | φ → ψ => simp_imp (simp φ) (simp ψ)
  | □ φ => □ (simp φ)
  | _ => φ
end.

Definition Lindenbaum_Tarski_preorder φ ψ :=
  ∅ • φ ⊢ ψ.

Notation "φ ≼ ψ" := (Lindenbaum_Tarski_preorder φ ψ) (at level 149).


Corollary weak_cut φ ψ θ:
  (φ ≼ ψ) -> (ψ ≼ θ) ->
  φ ≼ θ.
Proof.
intros H1 H2.
eapply additive_cut.
- apply H1.
- exch 0. apply weakening. apply H2.
Qed.


Lemma top_provable Γ :
 Γ ⊢ ⊤.
Proof.
  apply ImpR. apply ExFalso.
Qed.


(* Some tactics for the obviously_smaller proofs. *)

(* Solve goals involving the equality decision at the end of the match *)
Ltac eq_clean := match goal with 
| H : (if decide (?f1 = ?f2) then ?t else Eq) = ?t |- _ => 
    case decide in H;
    match goal with
    | e : ?f1 = ?f2 |- _ => rewrite e; apply generalised_axiom
    | _ => discriminate
    end
| H : (if decide (?f1 = ?f2) then Lt else Eq) = Gt |- _ => 
    case decide in H; discriminate
end.


(* Solve goals that involve directly using ExFalso *)
Ltac bot_clean  := match goal with
| [ |- Bot ≼ _] => apply ExFalso
| [ |- _ ≼ Bot  → _ ] => apply ImpR; apply ExFalso
| _ => idtac
end.

(* Solve induction goals *)
Ltac induction_auto := match goal with
| IH : obviously_smaller ?f ?f2 = Lt → ?f ≼ ?f2 , H :  obviously_smaller ?f ?f2 = Lt |- (∅ • ?f) ⊢ ?f2 => 
    apply IH; assumption
| IH : obviously_smaller ?f ?f2 = Gt → ?f2 ≼ ?f , H :  obviously_smaller ?f ?f2 = Gt |- (∅ • ?f2) ⊢ ?f => 
    apply IH; assumption

| IH : obviously_smaller ?f _ = Lt → ?f ≼ _ , H :  obviously_smaller ?f _ = Lt |- ?f ∧ _ ≼ _ => 
    apply AndL; apply weakening; apply IH; assumption
| IH : obviously_smaller ?f _ = Lt → ?f ≼ _ , H :  obviously_smaller ?f _ = Lt |- _ ∧ ?f ≼ _ =>
    apply AndL; exch 0; apply weakening; apply IH; assumption

| IH : obviously_smaller ?f _ = Gt → _ ≼ ?f , H :  obviously_smaller ?f _ = Gt |- _ ≼ ?f ∨ _ => 
    apply OrR1;  apply IH; assumption
| IH : obviously_smaller ?f _ = Gt → _ ≼ ?f , H :  obviously_smaller ?f _ = Gt |- _ ≼ _ ∨ ?f => 
    apply OrR2;  apply IH; assumption
| _ => idtac
end.

Lemma obviously_smaller_compatible_LT φ ψ :
  obviously_smaller φ ψ = Lt -> φ ≼ ψ.
Proof.
intro H.
induction φ; destruct ψ; 
try (unfold obviously_smaller in H; try discriminate;  eq_clean); bot_clean; 
repeat match goal with
  | [ H : obviously_smaller _ (?f → _) = Lt |- _ ≼ ?f → _ ] => 
      destruct f; simpl in H; try discriminate; bot_clean
  | |- _ ∧ _ ≼ ?f =>
    case_eq (obviously_smaller φ1 f); case_eq (obviously_smaller φ2 f); intros H0 H1; 
    simpl in H; rewrite H0 in H; rewrite H1 in H; try discriminate; induction_auto
  | |- _ ∨ _ ≼ ?f =>
    case_eq (obviously_smaller φ1 f); case_eq (obviously_smaller φ2 f); intros H0 H1; 
    simpl in H; rewrite H0 in H; rewrite H1 in H; try discriminate;
    apply OrL; induction_auto
  | |- (?f → _) ≼ _ => destruct f; try eq_clean; discriminate
end. 
Qed.


Lemma obviously_smaller_compatible_GT φ ψ :
  obviously_smaller φ ψ = Gt -> ψ ≼ φ .
Proof.
intro H.
induction φ; destruct ψ; 
try (unfold obviously_smaller in H; try discriminate; eq_clean); bot_clean;
repeat match goal with
  | |-  ?f ≼ _ ∧ _ =>
    case_eq (obviously_smaller φ1 f); case_eq (obviously_smaller φ2 f); intros H0 H1; 
    simpl in H; rewrite H0 in H; rewrite H1 in H; try discriminate; apply AndR; induction_auto
  | |- ?f ≼ _∨ _  =>
    case_eq (obviously_smaller φ1 f); case_eq (obviously_smaller φ2 f); intros H0 H1; 
    simpl in H; rewrite H0 in H; rewrite H1 in H; try discriminate; induction_auto
  | |- (?f1 → _) ≼ ?f2 → _ =>
    simpl in H; destruct f1; destruct f2; bot_clean; try eq_clean; discriminate
  | |- (?f → _) ≼ _ => destruct f; discriminate
  | |- (∅ • (?f → _)) ⊢ _ => destruct f; discriminate
  | |- _ ≼ (?f → _) => destruct f; bot_clean; discriminate
end.
Qed.

Lemma or_congruence φ ψ φ' ψ':
  (φ ≼ φ') -> (ψ ≼ ψ') -> (φ ∨ ψ) ≼ φ' ∨ ψ'.
Proof.
intros Hφ Hψ.
apply OrL.
- apply OrR1; apply Hφ. 
- apply OrR2; apply Hψ. 
Qed.


Lemma or_comm φ ψ: φ ∨ ψ ≼  ψ ∨ φ.
Proof.
apply OrL; [apply OrR2 | apply OrR1]; apply generalised_axiom.
Qed.


Lemma or_comm_ctx_L φ ψ ϴ: (φ ∨ ψ ≼ ϴ) -> ψ ∨ φ ≼ ϴ.
Proof.
intro H.
eapply weak_cut; [apply or_comm | assumption].
Qed.

Lemma or_comm_ctx_R φ ψ ϴ: (ϴ ≼ φ ∨ ψ ) -> ϴ ≼ ψ ∨ φ.
Proof.
intro H.
eapply weak_cut; [apply H | apply or_comm].
Qed.

Lemma or_assoc_R φ ψ ϴ : ((φ ∨ ψ) ∨ ϴ  ≼ φ ∨ (ψ ∨ ϴ)).
Proof.
  apply OrL.
  - apply OrL.
    + apply OrR1; apply generalised_axiom.
    + apply OrR2; apply OrR1; apply generalised_axiom.
  - apply OrR2; apply OrR2; apply generalised_axiom.
Qed.

Lemma or_assoc_L φ ψ ϴ : (φ ∨ (ψ ∨ ϴ)  ≼ (φ ∨ ψ) ∨ ϴ).
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
eapply weak_cut; [apply or_assoc_R | assumption].
Qed.

Lemma or_assoc_ctx_R_L φ ψ ϴ a:
  (a ≼ (φ ∨ ψ) ∨ ϴ)  ->a ≼ φ ∨ (ψ ∨ ϴ).
Proof.
intro H.
eapply weak_cut; [apply H | apply or_assoc_R].
Qed.

Lemma or_assoc_ctx_R_R φ ψ ϴ a:
  (a ≼ φ ∨ (ψ ∨ ϴ))  ->a ≼ (φ ∨ ψ) ∨ ϴ.
Proof.
intro H.
eapply weak_cut; [apply H | apply or_assoc_L].
Qed.

Lemma choose_or_equiv_L φ ψ φ' ψ':
  (φ ≼ φ') -> (ψ ≼ ψ') -> (φ ∨ ψ) ≼ choose_or φ' ψ'.
Proof.
intros Hφ Hψ.
unfold choose_or.
case_eq (obviously_smaller φ' ψ'); intro Heq.
- apply or_congruence; assumption.
- apply OrL.
  + eapply weak_cut. 
    * apply Hφ.
    * apply obviously_smaller_compatible_LT; assumption.
  + assumption. 
- apply OrL.
  + assumption.
  + eapply weak_cut.
    * eapply weak_cut.
      -- apply Hψ.
      -- apply obviously_smaller_compatible_GT. apply Heq.
    * apply generalised_axiom.
Qed.


Lemma choose_or_equiv_R φ ψ φ' ψ' : 
  (φ' ≼ φ) -> (ψ' ≼ ψ) -> choose_or φ' ψ' ≼  φ ∨ ψ.
Proof.
intros Hφ Hψ.
unfold choose_or.
case_eq (obviously_smaller φ' ψ'); intro Heq;
[apply or_congruence| apply OrR2| apply OrR1]; assumption.
Qed.

Lemma simp_or_equiv_L φ ψ φ' ψ' : 
  (φ ≼ φ') -> (ψ ≼ ψ') -> (φ ∨ ψ) ≼ φ' ⊻ ψ'.
Proof.
intros Hφ Hψ.
unfold simp_or.
destruct ψ'; try (apply choose_or_equiv_L; assumption).
- case (decide (obviously_smaller φ' ψ'1 = Gt)); [intro HGt | intro Hneq1].
  + apply OrL.
    * assumption.
    * eapply weak_cut.
      -- apply Hψ.
      -- apply AndL; apply weakening; now apply obviously_smaller_compatible_GT.
  + apply or_congruence; assumption.
- case_eq (obviously_smaller φ' ψ'1); intro Heq.
  + apply or_congruence; assumption.
  + apply OrL.
    * eapply weak_cut. 
      -- apply Hφ.
      -- apply OrR1. apply obviously_smaller_compatible_LT; assumption.
    * assumption.
  + apply OrL.
    * apply OrR1; assumption.
    * eapply weak_cut.
      -- apply Hψ. 
      -- apply or_congruence; [apply obviously_smaller_compatible_GT; assumption| apply generalised_axiom].
Qed.


Lemma simp_or_equiv_R φ ψ φ' ψ' : 
  (φ' ≼ φ) -> (ψ' ≼ ψ) -> φ' ⊻  ψ' ≼  φ ∨ ψ.
Proof.
intros Hφ Hψ.
unfold simp_or.
destruct ψ'.
- apply choose_or_equiv_R; assumption.
- apply choose_or_equiv_R; assumption.
- case (decide (obviously_smaller φ' ψ'1 = Gt)); intro.
  + now apply OrR1.
  + apply or_congruence; assumption.
- case_eq (obviously_smaller φ' ψ'1); intro Heq.
 + apply or_congruence; assumption.
 + apply OrR2; assumption.
 + apply OrL.
   * apply OrR1; assumption.
   * apply OrL_rev in Hψ.
     apply OrR2, Hψ.
- apply choose_or_equiv_R; assumption.
- apply choose_or_equiv_R; assumption.
Qed.

Lemma simp_or_comm φ ψ :
  (φ ⊻ ψ) ≼ (ψ ⊻  φ).
Proof.
apply (weak_cut _ (φ ∨ ψ) _).
- apply simp_or_equiv_R; apply generalised_axiom.
- apply (weak_cut _ (ψ ∨ φ) _).
  + apply or_comm.
  + apply simp_or_equiv_L; apply generalised_axiom.
Qed.

Lemma simp_or_comm_ctx_R  a φ ψ :
  (a ≼ φ ⊻ ψ)  -> a ≼ ψ ⊻ φ.
Proof.
intro H.
eapply weak_cut; [apply H | apply simp_or_comm].
Qed.

Lemma simp_or_comm_ctx_L  a φ ψ :
  (φ ⊻ ψ ≼ a) -> ψ ⊻ φ ≼ a.
Proof.
intro H.
eapply weak_cut; [apply simp_or_comm | apply H].
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
- eapply weak_cut.
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
eapply weak_cut; [apply or_congruence; [apply Hφ | apply Hψ] | apply simp_ors_self_equiv_L].
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
  eapply weak_cut.
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
eapply weak_cut; [ apply simp_ors_self_equiv_R | apply or_congruence; [apply Hφ | apply Hψ]].
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
  (φ ≼ φ') -> (ψ ≼ ψ') -> (φ ∧ ψ) ≼ φ' ∧ ψ'.
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
eapply weak_cut; [apply and_comm | assumption].
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
eapply weak_cut; [apply and_assoc_R | assumption].
Qed.

Lemma and_assoc_ctx_R_L φ ψ ϴ a:
  (a ≼ (φ ∧ ψ) ∧ ϴ) -> a ≼ φ ∧ (ψ ∧ ϴ).
Proof.
intro H.
eapply weak_cut; [apply H | apply and_assoc_R].
Qed.

Lemma and_assoc_ctx_R_R φ ψ ϴ a:
  (a ≼ φ ∧ (ψ ∧ ϴ)) -> a ≼ (φ ∧ ψ) ∧ ϴ.
Proof.
intro H.
eapply weak_cut; [apply H | apply and_assoc_L].
Qed.

Lemma choose_and_equiv_L φ ψ φ' ψ':
  (φ ≼ φ') -> (ψ ≼ ψ') -> (φ ∧ ψ) ≼ choose_and φ' ψ'.
Proof.
intros Hφ Hψ.
unfold choose_and.
case_eq (obviously_smaller φ' ψ'); intro Heq.
- apply and_congruence; assumption.
- apply AndL, weakening, Hφ.
- apply AndL. exch 0. apply weakening, Hψ.
Qed.


Lemma choose_and_equiv_R φ ψ φ' ψ':
  (φ' ≼ φ) -> (ψ' ≼ ψ) -> choose_and φ' ψ' ≼  φ ∧ ψ.
Proof.
intros Hφ Hψ.
unfold choose_and.
case_eq (obviously_smaller φ' ψ'); intro Heq.
- apply and_congruence; assumption.
- apply AndR.
  + assumption.
  + eapply weak_cut.
    * apply obviously_smaller_compatible_LT, Heq.
    * assumption.
- apply AndR.
  + eapply weak_cut.
    * apply obviously_smaller_compatible_GT, Heq.
    * assumption.
  + assumption.
Qed.


Lemma simp_and_equiv_L φ ψ φ' ψ' : 
  (φ ≼ φ') -> (ψ ≼ ψ') -> (φ ∧ ψ) ≼ φ' ⊼ ψ'.
Proof.
intros Hφ Hψ.
unfold simp_and.
destruct ψ'; try (apply choose_and_equiv_L; assumption).
- case_eq (obviously_smaller φ' ψ'1); intro Heq.
  + apply and_congruence; assumption.
  + apply and_congruence.
    * assumption.
    * apply AndR_rev in Hψ; apply Hψ.
  + apply AndL. exch 0. apply weakening. assumption.
- case (decide (obviously_smaller φ' ψ'1 = Lt)); intro.
  + apply AndL. now apply weakening.
  + apply and_congruence; assumption.
Qed.

Lemma simp_and_equiv_R φ ψ φ' ψ' : 
  (φ' ≼ φ) -> (ψ' ≼ ψ) -> φ' ⊼ ψ' ≼  φ ∧ ψ.
Proof.
intros Hφ Hψ.
unfold simp_and.
destruct  ψ'.
- apply choose_and_equiv_R; assumption.
- apply choose_and_equiv_R; assumption.
- case_eq (obviously_smaller φ' ψ'1); intro Heq.
  + apply and_congruence; assumption.
  + apply AndR.
    * apply AndL. apply weakening; assumption.
    * apply (weak_cut _ ( ψ'1 ∧ ψ'2) _).
      -- apply and_congruence; 
         [now apply obviously_smaller_compatible_LT | apply generalised_axiom].
      -- assumption.
  + apply AndR.
    * apply AndL. apply weakening. eapply weak_cut.
      -- apply obviously_smaller_compatible_GT; apply Heq.
      -- assumption.
    * assumption.
- case (decide (obviously_smaller φ' ψ'1 = Lt)); [intro HLt | intro Hneq].
  + apply AndR.
    * assumption.
    * eapply weak_cut.
      -- apply obviously_smaller_compatible_LT; apply HLt.
      -- apply OrL_rev in Hψ; apply Hψ.
  + apply and_congruence; assumption.
- apply choose_and_equiv_R; assumption.
- apply choose_and_equiv_R; assumption.
Qed.

Lemma simp_and_comm φ ψ :
  (φ ⊼ ψ) ≼ (ψ ⊼ φ).
Proof.
apply (weak_cut _ (φ ∧ ψ) _).
- apply simp_and_equiv_R; apply generalised_axiom.
- apply (weak_cut _ (ψ ∧ φ) _).
  + apply and_comm.
  + apply simp_and_equiv_L; apply generalised_axiom.
Qed.

Lemma simp_and_comm_ctx_R  a φ ψ :
  (a ≼ φ ⊼ ψ)  -> a ≼ ψ ⊼ φ.
Proof.
intro H.
eapply weak_cut; [apply H | apply simp_and_comm].
Qed.

Lemma simp_and_comm_ctx_L  a φ ψ :
  (φ ⊼ ψ ≼ a)  ->  ψ ⊼ φ ≼ a.
Proof.
intro H.
eapply weak_cut; [apply simp_and_comm | apply H].
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
- eapply weak_cut.
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
  eapply weak_cut.
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
  (φ  ≼ simp φ) -> (ψ  ≼ simp ψ) -> (φ ∧ ψ) ≼ simp (φ ∧ ψ).
Proof.
intros Hφ Hψ.
eapply weak_cut; [apply and_congruence; [apply Hφ | apply Hψ] | apply simp_ands_self_equiv_L].
Qed.

Lemma simp_equiv_and_R φ ψ : 
  (simp φ ≼ φ) -> (simp ψ ≼ ψ) -> simp (φ ∧ ψ) ≼  φ ∧ ψ.
Proof.
intros Hφ Hψ.
eapply weak_cut; [apply simp_ands_self_equiv_R | apply and_congruence; [apply Hφ | apply Hψ]].
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
  (simp φ ≼ φ) -> (ψ ≼ simp ψ) ->
  (φ → ψ) ≼ simp (φ → ψ).
Proof.
intros HφR HψL.
simpl. unfold simp_imp. 
case decide as [Heq |].
  - apply top_provable.
  - case decide as [HφBot |].
    + apply top_provable.
    + case decide as [HψTop |].
      * apply top_provable.
      * case decide as [HφTop |].
        -- apply weak_ImpL.
           ++ eapply additive_cut.
              ** apply top_provable.
              ** eapply additive_cut.
                 --- apply obviously_smaller_compatible_GT; apply HφTop.
                 --- exch 0. apply weakening. assumption.
           ++ assumption.
        -- case decide as [HψBot |].
           ++ apply ImpR. exch 0. apply ImpL.
              ** apply weakening. assumption.
              ** eapply additive_cut.
                 --- exch 0. apply weakening, HψL.
                 --- do 2 (exch 0; apply weakening). now apply obviously_smaller_compatible_LT.
           ++ apply ImpR. exch 0. apply ImpL.
              ** apply weakening. apply HφR.
              ** exch 0. apply weakening. apply HψL.
Qed.

Lemma simp_equiv_imp_R φ ψ : 
  (φ ≼ simp φ) -> (simp ψ ≼ ψ) ->
  simp (φ → ψ) ≼ (φ → ψ).
Proof.
intros HφR HψL.
simpl. unfold simp_imp. 
case decide as [Heq |].
  - apply weakening.
    apply ImpR.
    eapply weak_cut.
    + apply HφR.
    + eapply weak_cut.
      * apply obviously_smaller_compatible_LT. apply Heq.
      * assumption.
  - case decide as [HφBot |].
    + apply weakening.
      apply ImpR.
      eapply weak_cut.
      * apply HφR.
      * eapply weak_cut.
        -- apply obviously_smaller_compatible_LT. apply HφBot.
        -- apply ExFalso.
    + case decide as [HψTop |].
      * apply weakening.
        apply ImpR.
        eapply weak_cut.
        -- apply top_provable.
        -- eapply weak_cut.
           ++ apply obviously_smaller_compatible_GT. apply HψTop.
           ++ assumption.
      * case decide as [HφTop |].
        -- apply ImpR. apply weakening. assumption.
        -- case decide as [HψBot |].
           ++ apply ImpR. 
              eapply additive_cut.
              ** exch 0. apply weak_ImpL.
                 --- assumption.
                 --- apply ExFalso.
              ** apply generalised_axiom.
           ++ apply ImpR. exch 0. apply ImpL.
              ** apply weakening. apply HφR.
              ** exch 0. apply weakening. apply HψL.
Qed.

Lemma simp_equiv_imp φ ψ: 
  (φ ≼ simp φ) * (simp φ ≼ φ) ->
  (ψ ≼ simp ψ) * (simp ψ ≼ ψ) ->
  ((φ → ψ) ≼ simp (φ → ψ)) * (simp (φ → ψ) ≼ (φ → ψ)).
Proof.
intros IHφ IHψ.
split; [ apply simp_equiv_imp_L | apply simp_equiv_imp_R]; try apply IHφ ; try apply IHψ.
Qed.

Lemma box_congr φ ψ:
  (φ ≼ ψ) ->  □ φ ≼  □ ψ.
Proof. 
intro H.
apply BoxR.
box_tac. apply weakening.
ms.
Qed.

Lemma simp_equiv_box φ:
  (φ ≼ simp φ) * (simp φ ≼ φ) ->
  (□ φ ≼ □ (simp φ)) * (□ (simp φ) ≼ □ φ).
Proof.
intro IHφ.
split; apply box_congr; apply IHφ.
Qed.


Theorem simp_equiv φ : 
  (φ ≼ (simp φ)) * ((simp φ) ≼ φ).
Proof.
remember (weight φ) as w.
assert(Hle : weight φ  ≤ w) by lia.
clear Heqw. revert φ Hle.
induction w; intros φ Hle; [destruct φ ; simpl in Hle; lia|];
destruct φ; simpl; try (split ; apply generalised_axiom);
[eapply (simp_equiv_and φ1 φ2)|
 eapply (simp_equiv_or φ1 φ2)|
 eapply (simp_equiv_imp φ1 φ2)|
 eapply simp_equiv_box];
 apply IHw; 
match goal with
  | Hle : weight (?connector ?f1 ?f2) ≤ S ?w |- weight ?f1 ≤ ?w => simpl in Hle; lia
  | Hle : weight (?connector ?f1 ?f2) ≤ S ?w |- weight ?f2 ≤ ?w => simpl in Hle; lia
  | Hle : weight (□ ?f1) ≤ S ?w |- weight ?f1 ≤ ?w => simpl in Hle; lia
end.
Qed.

Require Import ISL.PropQuantifiers.

Definition E_simplified (p: variable) (ψ: form) := simp (Ef p ψ).
Definition A_simplified (p: variable) (ψ: form) := simp (Af p ψ).

Lemma bot_vars_incl V: vars_incl ⊥ V.
Proof.
  intros x H; unfold In; induction V; auto.
Qed.

Lemma top_vars_incl V: vars_incl ⊤ V.
Proof.
intros x H; unfold In; induction V; [simpl in H; tauto | auto].
Qed.


(* Solves simple variable inclusion goals *)
Ltac vars_incl_tac :=
repeat match goal with
| |- vars_incl ⊥ ?V => apply bot_vars_incl
| |- vars_incl ⊤ ?V => apply top_vars_incl

| H : vars_incl (?connector ?f1 ?f2) ?l |- vars_incl ?f1 ?l * vars_incl ?f2 ?l =>
        split; intros x H1; apply H; simpl; auto
| H : vars_incl (?connector ?f1 ?f2) ?l |- vars_incl ?f1 ?l =>
        intros x H1; apply H; simpl; auto
| H : vars_incl (?connector ?f1 ?f2) ?l |- vars_incl ?f2 ?l =>
        intros x H1; apply H; simpl; auto

| H: vars_incl ?f ?l |- vars_incl (_ ?f Bot) ?l =>  unfold vars_incl; simpl; intuition
| |- (vars_incl ?f1 ?l → vars_incl ?f2 ?l → vars_incl (?connector ?f1 ?f2) ?l) => 
        unfold vars_incl; simpl; intuition
| H1: vars_incl ?f1 ?l, H2: vars_incl ?f2 ?l |- vars_incl (?connector ?f1 ?f2) ?l => 
        unfold vars_incl; simpl; intuition

| |- _ * _  => split; [intro| intros]
end.

Lemma or_vars_incl φ ψ V:
  (vars_incl (Or φ ψ) V -> vars_incl φ V * vars_incl ψ V) *
  ( vars_incl φ V -> vars_incl ψ V -> vars_incl (Or φ ψ) V).
Proof. vars_incl_tac. Qed.


Lemma vars_incl_choose_or φ ψ V:
  vars_incl (Or φ ψ) V -> vars_incl (choose_or φ ψ) V.
Proof.
intros H.
unfold choose_or. 
destruct (obviously_smaller φ ψ); vars_incl_tac; assumption.
Qed.

Lemma vars_incl_simp_or_equiv_or φ ψ V:
  vars_incl (Or φ ψ) V -> vars_incl (φ ⊻ ψ) V.
Proof.
intros H.
unfold simp_or.
destruct ψ; try (now apply vars_incl_choose_or);
destruct (obviously_smaller φ ψ1); try assumption; vars_incl_tac.
apply or_vars_incl.
- now apply (or_vars_incl _ (Or ψ1 ψ2)).
- apply or_vars_incl in H. 
  apply (or_vars_incl ψ1 _).
  apply H.
Qed.

Lemma vars_incl_simp_ors φ ψ V :
  vars_incl φ V -> vars_incl ψ V -> vars_incl (simp_ors φ ψ) V.
Proof.
generalize ψ.
induction φ; intro ψ0; destruct ψ0; intros Hφ Hψ;
try ( apply vars_incl_simp_or_equiv_or; apply or_vars_incl; assumption).
simpl.
apply vars_incl_simp_or_equiv_or.
apply or_vars_incl.
- now apply (or_vars_incl _ φ2 _). 
- apply vars_incl_simp_or_equiv_or.
  apply or_vars_incl.
  + now apply (or_vars_incl _ ψ0_2 _). 
  +  apply IHφ2.
    * now apply (or_vars_incl  φ1 _ _). 
    * now apply (or_vars_incl  ψ0_1 _ _). 
Qed.


Lemma and_vars_incl φ ψ V:
  (vars_incl (And φ ψ) V -> vars_incl φ V * vars_incl ψ V) *
  (vars_incl φ V -> vars_incl ψ V -> vars_incl (And φ ψ) V).
Proof. vars_incl_tac. Qed.


Lemma vars_incl_choose_and φ ψ V:
  vars_incl (And φ ψ) V -> vars_incl (choose_and φ ψ) V.
Proof.
intros H.
unfold choose_and. 
destruct (obviously_smaller φ ψ); vars_incl_tac; assumption.
Qed.


Lemma vars_incl_simp_and_equiv_and φ ψ V:
  vars_incl (And φ ψ) V -> vars_incl (φ ⊼ ψ) V.
Proof.
intros H.
unfold simp_and.
destruct ψ; try (now apply vars_incl_choose_and); 
destruct (obviously_smaller φ ψ1); try assumption; vars_incl_tac.
apply and_vars_incl.
- vars_incl_tac.
- apply and_vars_incl in H. 
  apply (and_vars_incl ψ1 _).
  apply H.
Qed.

Lemma vars_incl_simp_ands φ ψ V :
  vars_incl φ V -> vars_incl ψ V -> vars_incl (simp_ands φ ψ) V.
Proof.
generalize ψ.
induction φ; intro ψ0; destruct ψ0; intros Hφ Hψ;
try (apply vars_incl_simp_and_equiv_and; apply and_vars_incl; assumption).
simpl.
apply vars_incl_simp_and_equiv_and.
apply and_vars_incl.
- vars_incl_tac.
- apply vars_incl_simp_and_equiv_and. 
  apply and_vars_incl.
  + vars_incl_tac.
  + apply IHφ2; vars_incl_tac.
Qed.

Lemma vars_incl_simp_imp φ ψ V :
  vars_incl φ V -> vars_incl ψ V -> vars_incl (simp_imp φ ψ) V.
Proof.
intros Hφ Hψ.
simpl. unfold simp_imp. 
case decide as [].
  + vars_incl_tac.
  + case decide as [].
    * vars_incl_tac.
    * case decide as [].
      -- vars_incl_tac.
      -- case decide as [].
         ++ assumption.
         ++ case decide as []; vars_incl_tac.
Qed.

Lemma vars_incl_simp φ V :
  vars_incl φ V -> vars_incl (simp φ) V.
Proof.
intro H.
induction φ; auto; simpl;
[ apply vars_incl_simp_ands; [apply IHφ1| apply IHφ2]|
  apply vars_incl_simp_ors; [apply IHφ1| apply IHφ2]| 
  apply vars_incl_simp_imp; [apply IHφ1| apply IHφ2] 
]; vars_incl_tac.
Qed.


Lemma preorder_singleton  φ ψ:
  {[φ]} ⊢ ψ -> (φ ≼ ψ).
Proof.
intro H.
assert (H': ∅ • φ ⊢ ψ ) by peapply H.
apply H'.
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
  + eapply weak_cut.
    * assert (Hef: ({[φ]} ⊢ Ef p φ)) by apply Hislφ.
      apply preorder_singleton.
      apply Hef.
    * apply (simp_equiv  (Ef p φ)).
  + intros ψ Hψ Hyp.
    eapply weak_cut.
    * apply (simp_equiv  (Ef p φ)).
    * assert (Hef: ({[Ef p φ]} ⊢ ψ)) by (apply Hislφ; [apply Hψ | peapply Hyp]).
      apply preorder_singleton.
      apply Hef.
  + intros Hx.
    eapply vars_incl_simp.
    apply Hislφ.
  + eapply weak_cut.
    * apply (simp_equiv  (Af p φ)).
    * apply preorder_singleton.
      apply Hislφ.
  + intros ψ Hψ Hyp.
    eapply weak_cut.
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
