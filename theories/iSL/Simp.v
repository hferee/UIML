Require Import ISL.Environments ISL.Sequents ISL.SequentProps ISL.Cut.
Require Import Decidable.
Definition is_double_negation φ ψ := φ = ¬ ¬ ψ.
Global Instance decidable_is_double_negation φ ψ : Decision (is_double_negation φ ψ) := decide (φ =  ¬ ¬ ψ).

Definition is_implication φ ψ := exists θ, φ = (θ → ψ).
Global Instance decidable_is_implication φ ψ : Decision (is_implication φ ψ).
Proof.
unfold is_implication.
destruct φ; try solve[right; intros [θ Hθ]; discriminate].
case (decide (φ2 = ψ)).
- intro; subst. left. eexists; reflexivity.
- intro. right; intros [θ Hθ]; inversion Hθ. subst. tauto.
Defined.

Definition is_negation φ ψ := φ = ¬ ψ.
Global Instance decidable_is_negation φ ψ : Decision (is_negation φ ψ) := decide (φ =  ¬ ψ).

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
  |(φ, ψ) => if decide (φ = ψ) then Lt else
                       if decide (is_double_negation φ ψ) then Gt else
                       if decide (is_double_negation ψ φ) then Lt else
                       if decide (is_implication φ ψ) then Gt else
                       if decide (is_implication ψ φ ) then Lt else
                       Eq
end.


Definition choose_or φ ψ :=
match obviously_smaller φ ψ with
  | Lt => ψ
  | Gt => φ
  | Eq =>match obviously_smaller ψ φ with
    | Lt => φ
    | Gt => ψ
    | Eq => φ ∨ ψ
    end
 end.

Definition simp_or φ ψ := 
match ψ with
  | ψ1 ∨ ψ2 => 
      match obviously_smaller φ ψ1 with
      | Lt => ψ1 ∨ ψ2
      | Gt => φ ∨ ψ2
      | Eq => φ ∨ (ψ1 ∨ ψ2)
      end
  | ψ1 ∧ ψ2 => 
      if decide (obviously_smaller φ ψ1 = Gt )
      then φ
      else φ ∨ (ψ1 ∧ ψ2)
  |_ => choose_or φ ψ
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
match ψ with
  | ψ1 ∧ ψ2 => 
      match obviously_smaller φ ψ1 with
      | Lt => φ ∧ ψ2
      | Gt => ψ1 ∧ ψ2
      | Eq => φ ∧ (ψ1 ∧ ψ2)
      end
  | ψ1 ∨ ψ2 => 
      if decide (obviously_smaller φ ψ1 = Lt )
      then φ
      else φ ∧ (ψ1 ∨ ψ2)
  | ψ1 → ψ2 => if decide (obviously_smaller φ ψ1 = Lt) then choose_and φ ψ2 else choose_and φ ψ
  | ψ => choose_and φ ψ
end.


Infix "⊼" := simp_and (at level 60).

(* Same as `simp_ors` but for large conjunctions. *)
Fixpoint simp_ands φ ψ :=
match (φ,ψ) with
  | (φ1 ∧ φ2, ψ1 ∧ ψ2) => φ1 ⊼ (ψ1 ⊼ (simp_ands φ2 ψ2))
  | (φ1 ∧ φ2, ψ) => ψ ⊼ (φ1 ∧ φ2)
  | (φ, ψ1 ∧ ψ2) => φ ⊼ (ψ1 ∧ ψ2)
    (* TODO: use simp_ands recursively *)
(*  | (φ,  ψ1 → ψ2) => if decide (obviously_smaller φ ψ1 = Lt) then φ ⊼ ψ2 else φ ⊼ ψ *)
  | (φ1 → φ2, ψ) => if decide (obviously_smaller ψ φ1 = Lt) then simp_ands φ2 ψ else φ ⊼ ψ
  |(φ, ψ) => φ ⊼ ψ
end.


Definition simp_imp φ ψ :=
  if decide (obviously_smaller φ ψ = Lt) then ⊤
  else if decide (obviously_smaller φ ⊥ = Lt) then ⊤
  else if decide (obviously_smaller ψ ⊤ = Gt) then ⊤
  else if decide (obviously_smaller φ ⊤ = Gt) then ψ
  else if decide (obviously_smaller ψ ⊥ = Lt) then ¬φ
  else if decide (is_negation φ ψ) then ¬φ
  else if decide (is_negation ψ φ) then ψ
  else φ → ψ.

(* Same as `simp_ors` but for nested implications. *)
Fixpoint simp_imps φ ψ :=
match (φ,ψ) with
  |(φ1, ψ1 → ψ2) => simp_imps (simp_ands φ1 ψ1) ψ2
  |(φ, ψ) => simp_imp φ ψ
end.

Fixpoint simp φ :=
match φ with
  | φ ∨ ψ => simp_ors (simp φ) (simp ψ)
  | φ ∧ ψ => simp_ands (simp φ) (simp ψ)
  | φ → ψ => simp_imps (simp φ) (simp ψ)
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
| H : match ?φ with _ => _ end = _ |- _ => destruct φ; try discriminate; eq_clean
end.

Ltac eq_clean' := match goal with 
| H : (if decide (?f1 = ?f2) then ?t else Eq) = ?t |- _ => 
    case decide in H;
    match goal with
    | e : ?f1 = ?f2 |- _ => rewrite e; apply generalised_axiom
    | _ => discriminate
    end
| H : (if decide (?f1 = ?f2) then Lt else Eq) = Gt |- _ => 
    case decide in H; discriminate
| H : match ?φ with _ => _ end = _ |- _ => destruct φ; try discriminate; try eq_clean
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

Lemma double_negation_obviously_smaller φ ψ:
 is_double_negation φ ψ -> ψ ≼ φ.
Proof.
intro H; rewrite H. apply ImpR; auto with proof.
Qed.

Lemma is_implication_obviously_smaller φ ψ:
 is_implication φ ψ -> ψ ≼ φ.
Proof.
unfold is_implication. intro H.
destruct φ; try (contradict H; intros [θ Hθ]; discriminate).
case (decide (φ2 = ψ)).
- intro; subst. apply ImpR, weakening, generalised_axiom.
- intro Hneq. contradict H; intros [θ Hθ]. inversion Hθ. tauto.
Qed.


Lemma obviously_smaller_compatible_LT φ ψ :
  obviously_smaller φ ψ = Lt -> φ ≼ ψ.
Proof.
intro H.
induction φ; destruct ψ;
repeat (unfold obviously_smaller in H; fold obviously_smaller in H; try discriminate; eq_clean); bot_clean;

repeat match goal with
  | [ H : obviously_smaller _ (?f → _) = Lt |- _ ≼ ?f → _ ] => 
      destruct f; simpl in H; try discriminate; bot_clean
  | |- _ ∧ _ ≼ ?f =>
    case_eq (obviously_smaller φ1 f); case_eq (obviously_smaller φ2 f); 
    intros H0 H1;
    simpl in H; try rewrite H0 in H; try rewrite H1 in H; try discriminate; induction_auto
  | |- _ ∨ _ ≼ ?f =>
    case_eq (obviously_smaller φ1 f); case_eq (obviously_smaller φ2 f);
    intros H0 H1; 
    simpl in H; rewrite H0 in H; rewrite H1 in H; try discriminate;
    apply OrL; induction_auto
  | |- (?f → _) ≼ _ => destruct f; try eq_clean; discriminate
end;
try destruct ψ1; try discriminate; bot_clean;
simpl in H; try case decide in H; try discriminate; bot_clean;
try (now apply double_negation_obviously_smaller);
try case decide in H;
try (now apply is_implication_obviously_smaller);
try (inversion e; subst; apply generalised_axiom);
try solve[destruct φ1; inversion H];
destruct φ1; repeat case decide in H; try discriminate;
   try (now apply is_implication_obviously_smaller);
   try (now apply double_negation_obviously_smaller).
Qed.


Lemma obviously_smaller_compatible_GT φ ψ :
  obviously_smaller φ ψ = Gt -> ψ ≼ φ .
Proof.
intro H.
induction φ; destruct ψ;
try match goal with H : ?H0 -> _ |- _ => assert(Hw' : H0) by lia; specialize (Hw Hw') end;
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
end;
simpl in H;
try solve[destruct ψ1; try discriminate; eq_clean];
  destruct φ1; try discriminate; repeat eq_clean;
  try destruct ψ1;
 try (unfold obviously_smaller in H; try discriminate; eq_clean); bot_clean;
 repeat case decide in H; try discriminate; bot_clean;
try (now apply double_negation_obviously_smaller);
try (now apply is_implication_obviously_smaller);
try (now apply ImpR, weakening, IHφ2).
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
- case_eq (obviously_smaller ψ' φ'); intro Heq'.
  + apply or_congruence; assumption.
  + apply OrL. assumption.
       eapply weak_cut. 
        * apply Hψ.
        * apply obviously_smaller_compatible_LT; assumption.
  + apply OrL; [| assumption].
       eapply weak_cut. 
        * apply Hφ.
        * apply obviously_smaller_compatible_GT; assumption.
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
[| apply OrR2| apply OrR1]; try assumption.
case_eq (obviously_smaller ψ' φ'); intro Heq';
[apply or_congruence| apply OrR1| apply OrR2]; try assumption.
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

Lemma Lindenbaum_Tarski_preorder_refl x : x ≼ x.
Proof. apply generalised_axiom. Qed.

Global Hint Resolve Lindenbaum_Tarski_preorder_refl : proof.
Global Hint Resolve choose_or_equiv_L : proof.
Global Hint Resolve choose_or_equiv_R : proof.


Lemma simp_ors_self_equiv_L φ ψ:
  (φ ∨ ψ) ≼ simp_ors φ ψ.
Proof.
generalize ψ.
induction φ;
intro ψ0;
destruct ψ0; try (eapply simp_or_equiv_L; apply generalised_axiom);
try (apply simp_or_comm_ctx_R; apply simp_or_equiv_L; apply generalised_axiom);
try solve[auto with proof].
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
destruct ψ0; unfold simp_ors; fold simp_ors;
try solve[apply simp_or_equiv_R; apply generalised_axiom];
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

Hint Unfold Lindenbaum_Tarski_preorder : proof.
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
- case (decide (obviously_smaller φ' ψ'1 = Lt)); intro.
  + apply weak_cut with (φ ∧ (φ ∧ ψ)). 
     * apply AndR; auto with proof.
     * apply choose_and_equiv_L. assumption.
        apply obviously_smaller_compatible_LT in e. 
        apply contraction, ImpR_rev. apply weak_cut with ψ'1. 
        -- apply weak_cut with φ'; auto with proof.
        -- apply ImpR. exch 0. apply ImpR_rev, AndL. exch 0. apply weakening, Hψ.
  + apply choose_and_equiv_L; assumption.
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
- case decide; intro Heq.
  + apply choose_and_equiv_R. assumption. eapply weak_cut; [|exact Hψ]. auto with proof.
  + apply choose_and_equiv_R; assumption.
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
destruct ψ0; unfold simp_ands; repeat case decide; intros; try (eapply simp_and_equiv_L; apply generalised_axiom);
try (apply obviously_smaller_compatible_LT in e;
  eapply weak_cut; [|apply IHφ2]; apply AndL, AndR; auto with proof; exch 0; apply ImpL; auto with proof);
try (apply simp_and_comm_ctx_R; apply simp_and_equiv_L; apply generalised_axiom);
 fold simp_ands.
 -
assert (H: φ1 ∧ ψ0_1 ∧ φ2 ∧ ψ0_2 ≼ φ1 ⊼ (ψ0_1 ⊼ simp_ands φ2 ψ0_2)).
{apply simp_and_equiv_L.
  + apply generalised_axiom.
  + apply simp_and_equiv_L.
    * apply generalised_axiom.
    * apply IHφ2.
}
eapply weak_cut.
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
unfold simp_ands; fold simp_ands;
try (case decide; [intro e;  apply obviously_smaller_compatible_LT in e;
  eapply weak_cut; [apply IHφ2|]; apply AndL, AndR; auto with proof; exch 0; apply ImpL; auto with proof|intro Hneq]);
try (eapply simp_and_equiv_R; apply generalised_axiom);
try (apply simp_and_comm_ctx_L; apply simp_and_equiv_R; apply generalised_axiom).
assert (H: φ1 ⊼ (ψ0_1 ⊼ simp_ands φ2 ψ0_2) ≼ φ1 ∧ ψ0_1 ∧ φ2 ∧ ψ0_2).
{apply simp_and_equiv_R.
  + apply generalised_axiom.
  + apply simp_and_equiv_R.
    * apply generalised_axiom.
    * apply IHφ2.
}
apply and_assoc_ctx_R_R.
eapply weak_cut.
- apply H.
- do 3 (apply AndL).
  apply AndR.
  + exch 2. exch 1. exch 0. apply generalised_axiom.
  + apply AndR.
      * exch 0. apply generalised_axiom.
      * apply AndR.
     -- exch 1. exch 0. apply generalised_axiom.
     -- apply generalised_axiom.
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

Lemma simp_imp_self_equiv_L φ ψ:
  (φ → ψ) ≼ simp_imp φ ψ.
Proof.
unfold simp_imp.
case decide as [Heq |]; [apply top_provable|].
case decide as [HφBot |]; [apply top_provable|].
case decide as [HψTop |]; [apply top_provable|].
case decide as [HφTop |].
- apply weak_ImpL.
  + eapply additive_cut.
      * apply top_provable.
      * eapply additive_cut.
       -- apply obviously_smaller_compatible_GT; apply HφTop.
       -- apply generalised_axiom.
  + apply generalised_axiom.
- case decide as [HψBot |].
  + apply ImpR. exch 0. apply ImpL.
      * apply weakening. apply generalised_axiom.
      * eapply additive_cut with ⊥.
       -- exch 0. apply weakening, obviously_smaller_compatible_LT, HψBot.
       -- do 2 (exch 0; apply weakening). now apply obviously_smaller_compatible_LT.
  + case decide; intro Heq. 
    * rewrite Heq. apply ImpR, ImpL; auto with proof.
    * case decide; intro Heq'.
      -- rewrite Heq'. apply ImpR. auto with proof.
      -- auto with proof.
Qed.

Lemma simp_imp_self_equiv_R φ ψ:
  simp_imp φ ψ ≼ φ → ψ.
Proof.
unfold simp_imp.
case decide as [Heq |].
  - apply weakening, ImpR, obviously_smaller_compatible_LT, Heq.
  - case decide as [HφBot |].
    + apply weakening.
      apply ImpR.
      eapply weak_cut with ⊥.
      * apply obviously_smaller_compatible_LT, HφBot.
      * apply ExFalso.
    + case decide as [HψTop |].
      * apply weakening.
        apply ImpR.
        eapply weak_cut.
        -- apply top_provable.
        -- apply obviously_smaller_compatible_GT, HψTop.
      * case decide as [HφTop |].
        -- apply ImpR. apply weakening, generalised_axiom.
        -- case decide as [HψBot |].
           ++ apply ImpR.
              eapply additive_cut with ψ.
              ** exch 0. apply weak_ImpL.
                 --- apply generalised_axiom.
                 --- apply ExFalso.
              ** apply generalised_axiom.
           ++ case decide; intro Heq.
             ** rewrite Heq. apply ImpR. exch 0. apply ImpL; auto with proof.
             ** case decide; intro Heq'.
             --- rewrite Heq'. auto with proof.
             --- auto with proof.
Qed.

Lemma simp_imps_self_equiv_L φ ψ:
  (φ → ψ) ≼ simp_imps φ ψ.
Proof.
revert φ; induction ψ; intro φ; unfold simp_imps;
auto using simp_imp_self_equiv_L.
fold simp_imps. apply ImpLAnd_rev.
eapply weak_cut; [| apply IHψ2].
apply ImpR. exch 0. apply ImpL.
- apply weakening, simp_ands_self_equiv_R.
- apply generalised_axiom.
Qed.

Lemma simp_imps_self_equiv_R φ ψ:
  simp_imps φ ψ ≼ (φ → ψ).
Proof.
revert φ; induction ψ; intro φ; unfold simp_imps;
auto using simp_imp_self_equiv_R.
fold simp_imps. apply ImpR, ImpR, AndL_rev, ImpR_rev.
eapply weak_cut; [apply IHψ2|].
apply ImpR. exch 0. apply ImpL.
- apply weakening, simp_ands_self_equiv_L.
- apply generalised_axiom.
Qed.

Lemma simp_equiv_imp_L φ ψ : 
  (simp φ ≼ φ) -> (ψ ≼ simp ψ) ->
  (φ → ψ) ≼ simp (φ → ψ).
Proof.
intros HφR HψL.
simpl.
eapply weak_cut; [| apply simp_imps_self_equiv_L]. apply ImpR. exch 0.
apply ImpL.
- apply weakening. apply HφR.
- exch 0. apply weakening. apply HψL.
Qed.

Lemma simp_equiv_imp_R φ ψ : 
  (φ ≼ simp φ) -> (simp ψ ≼ ψ) ->
  simp (φ → ψ) ≼ (φ → ψ).
Proof.
intros HφR HψL.
simpl.
eapply weak_cut with (simp φ → simp ψ).
- apply simp_imps_self_equiv_R.
- apply ImpR. exch 0. apply ImpL.
  + apply weakening, HφR.
  + exch 0. apply weakening, HψL.
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
destruct (obviously_smaller φ ψ); vars_incl_tac; 
destruct (obviously_smaller ψ φ); vars_incl_tac; 
assumption.
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
  apply (and_vars_incl ψ1 _), H.
- case decide; intro; try discriminate. now apply vars_incl_choose_and.
- apply and_vars_incl in H. destruct H. case decide; intro; try discriminate. apply vars_incl_choose_and.
  + apply and_vars_incl; intuition. vars_incl_tac.
  + vars_incl_tac.
- case decide; intro. discriminate. apply vars_incl_choose_and, and_vars_incl; vars_incl_tac.
Qed.

Lemma vars_incl_simp_ands φ ψ V :
  vars_incl φ V -> vars_incl ψ V -> vars_incl (simp_ands φ ψ) V.
Proof.
generalize ψ.
induction φ; intro ψ0; destruct ψ0; intros Hφ Hψ;
unfold simp_ands; fold simp_ands;try (case decide; intro);
try (apply IHφ2; trivial; intros x Hx; apply Hφ; simpl; tauto);
try (apply vars_incl_simp_and_equiv_and; apply and_vars_incl; assumption).
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
    *  repeat (case decide as []; vars_incl_tac); assumption.
Qed.

Lemma vars_incl_simp_imps φ ψ V :
  vars_incl φ V -> vars_incl ψ V -> vars_incl (simp_imps φ ψ) V.
Proof.
revert φ; induction ψ; intros φ Hφ Hψ; simpl;
try apply vars_incl_simp_imp; trivial.
apply IHψ2.
- apply vars_incl_simp_ands; trivial.
  intros ? ?; apply Hψ; simpl; tauto.
-   intros ? ?; apply Hψ; simpl; tauto.
Qed.

Lemma vars_incl_simp φ V :
  vars_incl φ V -> vars_incl (simp φ) V.
Proof.
intro H.
induction φ; auto; simpl;
[ apply vars_incl_simp_ands; [apply IHφ1| apply IHφ2]|
  apply vars_incl_simp_ors; [apply IHφ1| apply IHφ2]| 
  apply vars_incl_simp_imps; [apply IHφ1| apply IHφ2] 
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

Example ex6: simp (Or (Var "q") (Implies (Var "r") (Var "q"))) = Implies (Var "r") (Var "q").
Proof. reflexivity. Qed.

Example ex7: simp (And (Implies (Var "r") (Var "q")) (Var "q") ) = Var "q".
Proof. reflexivity. Qed.