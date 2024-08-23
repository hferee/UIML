Require Import ISL.Environments ISL.Sequents ISL.SequentProps ISL.Cut.
Require Import Program Equality.

Definition Lindenbaum_Tarski_preorder φ ψ :=
  ∅ • φ ⊢ ψ.

Notation "φ ≼ ψ" := (Lindenbaum_Tarski_preorder φ ψ) (at level 150).

Corollary weak_cut φ ψ θ:
  (φ ≼ ψ) -> (ψ ≼ θ) ->
  φ ≼ θ.
Proof.
intros H1 H2.
eapply additive_cut.
- apply H1.
- exch 0. now apply weakening.
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


Lemma and_congruence φ ψ φ' ψ':
  (φ ≼ φ') -> (ψ ≼ ψ') -> (φ ∧ ψ) ≼ φ' ∧ ψ'.
Proof.
intros Hφ Hψ.
apply AndL.
apply AndR.
- now apply weakening.
- exch 0. now apply weakening.
Qed.


Lemma choose_conj_equiv_L φ ψ φ' ψ':
  (φ ≼ φ') -> (ψ ≼ ψ') -> (φ ∧ ψ) ≼ choose_conj φ' ψ'.
Proof.
intros Hφ Hψ.
unfold choose_conj.
case_eq (obviously_smaller φ' ψ'); intro Heq.
- apply and_congruence; assumption.
- apply AndL, weakening, Hφ.
- apply AndL. exch 0. apply weakening, Hψ.
Qed.


Lemma choose_conj_equiv_R φ ψ φ' ψ':
  (φ' ≼ φ) -> (ψ' ≼ ψ) -> choose_conj φ' ψ' ≼  φ ∧ ψ.
Proof.
intros Hφ Hψ.
unfold choose_conj.
case_eq (obviously_smaller φ' ψ'); intro Heq.
- now apply and_congruence.
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

Lemma make_conj_equiv_L φ ψ φ' ψ' : 
  (φ ≼ φ') -> (ψ ≼ ψ') -> (φ ∧ ψ) ≼ φ' ⊼ ψ'.
Proof.
intros Hφ Hψ.
unfold make_conj.
destruct ψ'; try (apply choose_conj_equiv_L; assumption).
- destruct φ'; try (apply choose_conj_equiv_L; assumption).
  case decide; intro; try (apply choose_conj_equiv_L; assumption).
  apply obviously_smaller_compatible_LT in e.
  apply weak_cut with ((φ ∧ φ'1) ∧ ψ).
  + apply AndL; repeat apply AndR.  auto with proof.
      * exch 0. apply weakening;  apply weak_cut with v; assumption.
      * apply generalised_axiom.
  + apply choose_conj_equiv_L; auto with proof.
- apply exfalso, AndL. exch 0. apply weakening, Hψ.
- case_eq (obviously_smaller φ' ψ'1); intro Heq.
  + apply and_congruence; assumption.
  + apply and_congruence.
    * assumption.
    * apply AndR_rev in Hψ; apply Hψ.
  + apply AndL. exch 0. apply weakening. assumption.
- repeat case decide; intros.
  + apply AndL. now apply weakening.
  + apply AndL. now apply weakening.
  + apply choose_conj_equiv_L ; assumption.
- case (decide (obviously_smaller φ' ψ'1 = Lt)); intro.
  + apply weak_cut with (φ ∧ (φ ∧ ψ)).
     * apply AndR; auto with proof.
     * apply choose_conj_equiv_L. assumption.
        apply obviously_smaller_compatible_LT in e.
        apply contraction, ImpR_rev. apply weak_cut with ψ'1.
        -- apply weak_cut with φ'; auto with proof.
        -- apply ImpR. exch 0. apply ImpR_rev, AndL. exch 0. apply weakening, Hψ.
  + apply choose_conj_equiv_L; assumption.
- destruct φ'; try (apply choose_conj_equiv_L; assumption).
  case decide; intro; try (apply choose_conj_equiv_L; assumption).
  apply weak_cut with (ψ ∧ (φ ∧ φ'1)).
  + apply AndL, AndR. auto with proof. apply AndR. auto with proof.
      exch 0. apply weakening. apply weak_cut with (□ ψ'). auto with proof.
      now apply obviously_smaller_compatible_LT.
  + apply weak_cut with ((φ ∧ φ'1) ∧ ψ).
     * apply AndR; auto with proof.
     * apply choose_conj_equiv_L; auto with proof.
Qed.

Lemma make_conj_equiv_R φ ψ φ' ψ' : 
  (φ' ≼ φ) -> (ψ' ≼ ψ) -> φ' ⊼ ψ' ≼  φ ∧ ψ.
Proof.
intros Hφ Hψ.
unfold make_conj.
destruct  ψ'.
- destruct φ'; try case decide; intros; apply choose_conj_equiv_R; try assumption.
  eapply imp_cut; eassumption.
- destruct φ'; try case decide; intros; apply choose_conj_equiv_R; try assumption.
   eapply imp_cut; eassumption.
- case_eq (obviously_smaller φ' ψ'1); intro Heq.
  + now apply and_congruence.
  + apply AndR.
    * apply AndL. now apply weakening.
    * apply (weak_cut _ ( ψ'1 ∧ ψ'2) _).
      -- apply and_congruence; 
         [now apply obviously_smaller_compatible_LT | apply generalised_axiom].
      -- assumption.
  + apply AndR.
    * apply AndL. apply weakening. eapply weak_cut.
      -- apply obviously_smaller_compatible_GT; apply Heq.
      -- assumption.
    * assumption.
- repeat case decide; intros.
  + apply AndR.
    * assumption.
    * eapply weak_cut.
      -- apply obviously_smaller_compatible_LT; eassumption.
      -- apply OrL_rev in Hψ; apply Hψ.
  + apply AndR.
    * assumption.
    * eapply weak_cut.
      -- apply obviously_smaller_compatible_LT; eassumption.
      -- apply OrL_rev in Hψ; apply Hψ.
  + apply choose_conj_equiv_R; assumption.
- case decide; intro Heq.
  + apply choose_conj_equiv_R. assumption. eapply weak_cut; [|exact Hψ]. auto with proof.
  + apply choose_conj_equiv_R; assumption.
- destruct φ'; try case decide; intros; apply choose_conj_equiv_R; try assumption.
  eapply imp_cut; eassumption.
Qed.

Lemma specialised_weakening Γ φ ψ : (φ ≼ ψ) ->  Γ•φ ⊢ ψ.
Proof.
intro H. 
apply generalised_weakeningL.
peapply H.
Qed.

Lemma make_conj_sound_L Γ φ ψ θ : Γ•φ ∧ψ ⊢ θ -> Γ• φ ⊼ ψ ⊢ θ.
Proof.
intro H.
eapply additive_cut.
- apply specialised_weakening.
  apply make_conj_equiv_R; apply generalised_axiom.
- exch 0. now apply weakening.
Qed.

Global Hint Resolve make_conj_sound_L : proof.

Lemma make_conj_complete_L Γ φ ψ θ : Γ• φ ⊼ ψ ⊢ θ -> Γ•φ ∧ψ ⊢ θ.
Proof.
intro H.
eapply additive_cut.
- apply specialised_weakening.
  apply make_conj_equiv_L; apply generalised_axiom.
- exch 0. now apply weakening.
Qed.

Lemma make_conj_sound_R Γ φ ψ : Γ  ⊢ φ ∧ψ -> Γ ⊢ φ ⊼ ψ.
Proof.
intro H.
eapply additive_cut.
- apply H.
- apply make_conj_complete_L, generalised_axiom.
Qed.

Global Hint Resolve make_conj_sound_R : proof.

Lemma make_conj_complete_R Γ φ ψ : Γ  ⊢ φ ⊼ ψ -> Γ  ⊢ φ ∧ψ.
Proof.
intro H.
eapply additive_cut.
- apply H.
- apply make_conj_sound_L, generalised_axiom.
Qed.



Lemma or_congruence φ ψ φ' ψ':
  (φ ≼ φ') -> (ψ ≼ ψ') -> (φ ∨ ψ) ≼ φ' ∨ ψ'.
Proof.
intros Hφ Hψ.
apply OrL.
- now apply OrR1.
- now apply OrR2.
Qed.

Lemma choose_disj_equiv_L φ ψ φ' ψ':
  (φ ≼ φ') -> (ψ ≼ ψ') -> (φ ∨ ψ) ≼ choose_disj φ' ψ'.
Proof.
intros Hφ Hψ.
unfold choose_disj.
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



Lemma choose_disj_equiv_R φ ψ φ' ψ' : 
  (φ' ≼ φ) -> (ψ' ≼ ψ) -> choose_disj φ' ψ' ≼  φ ∨ ψ.
Proof.
intros Hφ Hψ.
unfold choose_disj.
case_eq (obviously_smaller φ' ψ'); intro Heq;
[| apply OrR2| apply OrR1]; try assumption.
case_eq (obviously_smaller ψ' φ'); intro Heq';
[apply or_congruence| apply OrR1| apply OrR2]; try assumption.
Qed.

Lemma make_disj_equiv_L φ ψ φ' ψ' : 
  (φ ≼ φ') -> (ψ ≼ ψ') -> (φ ∨ ψ) ≼ φ' ⊻ ψ'.
Proof.
intros Hφ Hψ.
unfold make_disj.
destruct ψ'; try (apply choose_disj_equiv_L; assumption).
- repeat case decide; intros.
  + apply OrL.
    * assumption.
    * eapply weak_cut.
      -- apply Hψ.
      -- apply AndL; apply weakening; now apply obviously_smaller_compatible_GT.
  + apply OrL.
    * assumption.
    * eapply weak_cut.
      -- apply Hψ.
      -- apply AndL; exch 0. apply weakening; now apply obviously_smaller_compatible_GT.
  + now apply choose_disj_equiv_L.
- case_eq (obviously_smaller φ' ψ'1); intro Heq.
  + now apply or_congruence.
  + apply OrL.
    * eapply weak_cut. 
      -- apply Hφ.
      -- apply OrR1. now apply obviously_smaller_compatible_LT.
    * assumption.
  + apply OrL.
    * now apply OrR1.
    * eapply weak_cut.
      -- apply Hψ. 
      -- apply or_congruence; [apply obviously_smaller_compatible_GT; assumption| apply generalised_axiom].
Qed.


Lemma make_disj_equiv_R φ ψ φ' ψ' : 
  (φ' ≼ φ) -> (ψ' ≼ ψ) -> φ' ⊻  ψ' ≼  φ ∨ ψ.
Proof.
intros Hφ Hψ.
unfold make_disj.
destruct ψ'.
- now apply choose_disj_equiv_R.
- now apply choose_disj_equiv_R.
- repeat case decide; intros.
  + now apply OrR1.
  + now apply OrR1.
  + now apply choose_disj_equiv_R.
- case_eq (obviously_smaller φ' ψ'1); intro Heq.
 + now apply or_congruence.
 + now apply OrR2.
 + apply OrL.
   * now apply OrR1.
   * apply OrL_rev in Hψ.
     apply OrR2, Hψ.
- now apply choose_disj_equiv_R.
- now apply choose_disj_equiv_R.
Qed.

Lemma make_disj_sound_L Γ φ ψ θ : Γ•φ ∨ψ ⊢ θ -> Γ•make_disj φ ψ ⊢ θ.
Proof.
intro H.
eapply additive_cut.
- apply specialised_weakening.
  apply make_disj_equiv_R; apply generalised_axiom.
- exch 0. now apply weakening.
Qed.

Global Hint Resolve make_disj_sound_L : proof.

Lemma make_disj_complete_L Γ φ ψ θ : Γ•make_disj φ ψ ⊢ θ -> Γ•φ ∨ψ ⊢ θ.
Proof.
intro H.
eapply additive_cut.
- apply specialised_weakening.
  apply make_disj_equiv_L; apply generalised_axiom.
- exch 0. now apply weakening.
Qed.

Lemma make_disj_sound_R Γ φ ψ : Γ  ⊢ φ ∨ψ -> Γ ⊢ make_disj φ ψ.
Proof.
intro H.
eapply additive_cut.
- apply H.
- apply make_disj_complete_L, generalised_axiom.
Qed.

Global Hint Resolve make_disj_sound_R : proof.

Lemma make_disj_complete_R Γ φ ψ : Γ  ⊢ make_disj φ ψ -> Γ  ⊢ φ ∨ψ.
Proof.
intro H.
eapply additive_cut.
- apply H.
- apply make_disj_sound_L, generalised_axiom.
Qed.

(** * Generalized rules 

In this section we prove that generalizations of or-left and and-right rules
that take more than two formulas are admissible and invertible in the calculus
G4ip. This is important in the correctness proof of propositional quantifiers
because the propositional quantifiers are defined as large disjunctions /
conjunctions of various individual formulas.
*)

(** ** Generalized OrL and its invertibility *)

Lemma disjunction_L Γ Δ θ :
  ((forall φ, φ ∈ Δ -> (Γ•φ ⊢ θ)) -> (Γ•⋁ Δ ⊢ θ)) *
  ((Γ•⋁ Δ ⊢ θ) -> (forall φ, φ ∈ Δ -> (Γ•φ ⊢ θ))).
Proof.
unfold disjunction.
assert(Hcut :
  (forall ψ, (Γ•ψ ⊢ θ) -> (forall φ, φ ∈ Δ -> (Γ•φ ⊢ θ)) ->
    (Γ•foldl make_disj ψ  (nodup form_eq_dec Δ) ⊢ θ)) *
  (forall ψ,((Γ•foldl make_disj ψ  (nodup form_eq_dec Δ)) ⊢ θ ->
    (Γ•ψ ⊢ θ) * (∀ φ : form, φ ∈ Δ → (Γ•φ) ⊢ θ)))).
{
  induction Δ; simpl; split; intros ψ Hψ.
  - intro. apply Hψ.
  - split; trivial. intros φ Hin. contradict Hin. auto with *.
  - intro Hall. case in_dec; intro; apply (fst IHΔ); auto with *.
  - case in_dec in Hψ; apply IHΔ in Hψ;
    destruct Hψ as [Hψ Hind].
    + split; trivial;  intros φ Hin; destruct (decide (φ = a)); auto 2 with *.
        subst. apply Hind. now apply elem_of_list_In.
    + apply make_disj_complete_L in Hψ.
        apply OrL_rev in Hψ as [Hψ Ha].
        split; trivial;  intros φ Hin; destruct (decide (φ = a)); auto with *.
}
split; apply Hcut. constructor 2.
Qed.


(** ** Generalized OrR *)

Lemma disjunction_R Γ Δ φ : (φ ∈ Δ) -> (Γ  ⊢ φ) -> (Γ  ⊢ ⋁ Δ).
Proof.
intros Hin Hprov. unfold disjunction. revert Hin.
assert(Hcut : forall θ, ((Γ ⊢ θ) + (φ ∈ Δ)) -> Γ ⊢ foldl make_disj θ (nodup form_eq_dec Δ)).
{
  induction Δ; simpl; intros θ [Hθ | Hin].
  - assumption.
  - contradict Hin; auto with *.
  - case in_dec; intro; apply IHΔ; left; trivial. apply make_disj_sound_R. now apply OrR1.
  - apply elem_of_cons in Hin.
    destruct (decide (φ = a)).
    + subst. case in_dec; intro; apply IHΔ.
        * right. now apply elem_of_list_In.
        *  left. apply make_disj_sound_R. now apply OrR2.
    + case in_dec; intro; apply IHΔ; right; tauto.
}
intro Hin. apply Hcut; now right.
Qed.  

(** ** Generalized invertibility of AndR *)



(** ** Generalized AndR *)

Lemma conjunction_R1 Γ Δ : (forall φ, φ ∈ Δ -> Γ  ⊢ φ) -> (Γ  ⊢ ⋀ Δ).
Proof.
intro Hprov. unfold conjunction.
assert(Hcut : forall θ, Γ ⊢ θ -> Γ ⊢ foldl make_conj θ (nodup form_eq_dec Δ)).
{
  induction Δ; intros θ Hθ; simpl; trivial.
  case in_dec; intro; auto with *.
  apply IHΔ.
  - intros; apply Hprov. now right.
  - apply make_conj_sound_R, AndR; trivial. apply Hprov. now left.
}
apply Hcut. apply ImpR, ExFalso.
Qed.

Lemma conjunction_R2 Γ Δ : (Γ  ⊢ ⋀ Δ) -> (forall φ, φ ∈ Δ -> Γ  ⊢ φ).
Proof.
 unfold conjunction.
assert(Hcut : forall θ, Γ ⊢ foldl make_conj θ (nodup form_eq_dec Δ) -> (Γ ⊢ θ) * (forall φ, φ ∈ Δ -> Γ  ⊢ φ)).
{
  induction Δ; simpl; intros θ Hθ.
  - split; trivial. intros φ Hin; contradict Hin. auto with *.
  - case in_dec in Hθ; destruct (IHΔ _ Hθ) as (Hθ' & Hi);
     try (apply make_conj_complete_R in Hθ'; destruct (AndR_rev Hθ')); split; trivial;
     intros φ Hin; apply elem_of_cons in Hin;
     destruct (decide (φ = a)); subst; trivial.
     + apply Hi.  rewrite elem_of_list_In; tauto.
     + apply (IHΔ _ Hθ). tauto.
     + apply (IHΔ _ Hθ). tauto.
}
apply Hcut.
Qed.

(** ** Generalized AndL *)

Lemma conjunction_L Γ Δ φ θ: (φ ∈ Δ) -> (Γ•φ ⊢ θ) -> (Γ•⋀ Δ ⊢ θ).
Proof.
intros Hin Hprov. unfold conjunction. revert Hin.
assert(Hcut : forall ψ, ((φ ∈ Δ) + (Γ•ψ ⊢ θ)) -> (Γ•foldl make_conj ψ (nodup form_eq_dec Δ) ⊢ θ)).
{
  induction Δ; simpl; intros ψ [Hin | Hψ].
  - contradict Hin; auto with *.
  - trivial.
  - case in_dec; intro; apply IHΔ; destruct (decide (φ = a)).
    + subst. left. now apply elem_of_list_In.
    + left. auto with *.
    + subst. right. apply make_conj_sound_L. auto with proof.
    + left. auto with *.
  - case in_dec; intro; apply IHΔ; right; trivial.
     apply make_conj_sound_L. auto with proof.
}
intro Hin. apply Hcut. now left.
Qed.



(* TODO move up *)
(** * Correctness of optimizations 

To make the definitions of the propositional quantifiers that we extract from the Coq definition more readable, we introduced functions "make_impl", "make_conj" and "make_disj" in Environments.v which perform obvious simplifications such as reducing φ ∧ ⊥ to ⊥ and φ ∨ ⊥ to φ. The following results show that the definitions of these functions are correct, in the sense that it does not make a difference for provability of a sequent whether one uses the literal conjunction, disjunction, and implication, or its optimized version. *)

(* TODO: suitable name *)
Lemma tautology_cut {Γ} {φ ψ θ : form} : Γ • (φ → ψ) ⊢ θ -> (φ ≼ ψ) -> Γ ⊢ θ.
Proof.
intros Hp H.
apply additive_cut with (φ → ψ).
  + apply ImpR, generalised_weakeningL. peapply H.
  + apply Hp.
Qed.

Lemma Lindenbaum_Tarski_preorder_Bot φ : ⊥ ≼ φ.
Proof. apply ExFalso. Qed.

Local Hint Resolve Lindenbaum_Tarski_preorder_Bot : proof.


Lemma make_impl_sound_L Γ φ ψ θ: Γ•(φ → ψ) ⊢ θ -> Γ•(φ ⇢ ψ) ⊢ θ.
Proof.
revert φ. induction ψ; intros φ HP; simpl; repeat case decide; intros;
repeat match goal with
| H : obviously_smaller _ _ = Lt |- _ => apply obviously_smaller_compatible_LT in H
| H : obviously_smaller _ _ = Gt |- _ => apply obviously_smaller_compatible_GT in H
| H : is_negation _ _ |- _ =>  eapply additive_cut; [| exch 0; apply weakening, HP]; apply ImpR, exfalso; exch 0; auto with proof
end; trivial; try (solve [eapply imp_cut; eauto]);
try solve[apply weakening, (tautology_cut HP); trivial; try apply weak_cut with ⊥; auto with proof].
apply IHψ2.
apply ImpLAnd in HP.
apply additive_cut with ((φ ∧ ψ1 → ψ2) → θ).
- apply weakening, ImpR, HP.
- apply ImpL; [|auto with proof].
  apply weakening, ImpR. exch 0. apply ImpL; [|auto with proof].
  apply weakening, make_conj_complete_L, generalised_axiom.
Qed.

Global Hint Resolve make_impl_sound_L : proof.


Lemma make_impl_sound_R Γ φ ψ: Γ ⊢ (φ → ψ) -> Γ ⊢ φ ⇢ ψ.
Proof.
revert φ. induction ψ; intros φ HP; simpl; repeat case decide; intros;
repeat match goal with
| H : obviously_smaller _ _ = Lt |- _ => apply obviously_smaller_compatible_LT in H
| H : obviously_smaller _ _ = Gt |- _ => apply obviously_smaller_compatible_GT in H
| H : is_negation _ _ |- _ =>  rewrite H  in *; apply ImpR;  eapply additive_cut; [apply ImpR_rev, HP| exch 0; auto with *]
end; trivial; auto with proof;
try (solve[peapply (cut ∅ Γ φ); auto with proof; eapply TopL_rev; eauto]).
apply IHψ2, ImpR, make_conj_sound_L, AndL, ImpR_rev, ImpR_rev, HP.
Qed.

Global Hint Resolve make_impl_sound_R : proof.


Lemma make_impl_sound_L2 Γ φ1 φ2 ψ θ: Γ•(φ1 → (φ2 → ψ)) ⊢ θ -> Γ•(φ1 ⇢ (φ2 ⇢ ψ)) ⊢ θ.
Proof.
intro HP. apply make_impl_sound_L in HP.
apply additive_cut with (φ1 ⇢ (φ2 → ψ)).
- apply make_impl_sound_L, make_impl_sound_R.
  apply ImpR. exch 0. apply ImpL.
  + apply weakening, generalised_axiom.
  + exch 0. apply weakening, make_impl_sound_L, generalised_axiom.
- exch 0. apply weakening, HP. 
Qed.

Global Hint Resolve make_impl_sound_L2: proof.

Lemma make_impl_sound_L2' Γ φ1 φ2 ψ θ: Γ•((φ1 → φ2) → ψ) ⊢ θ -> Γ•((φ1 ⇢ φ2) ⇢ ψ) ⊢ θ.
Proof.
intro HP. apply make_impl_sound_L.
apply additive_cut with ((φ1 → φ2) → ψ); [|exch 0; apply weakening, HP].
apply ImpR. exch 0. apply ImpL.
- apply weakening, make_impl_sound_R, generalised_axiom.
- apply generalised_axiom.
Qed.

Lemma make_impl_complete_L Γ φ ψ θ: Γ•(φ ⇢ ψ) ⊢ θ -> Γ•(φ → ψ) ⊢ θ.
Proof.
intro HP.
apply additive_cut with (φ ⇢ ψ); [|exch 0; apply weakening, HP].
apply make_impl_sound_R, generalised_axiom.
Qed.

Lemma make_impl_complete_L2 Γ φ1 φ2 ψ θ: Γ•(φ1 ⇢ (φ2 ⇢ ψ)) ⊢ θ -> Γ•(φ1 → (φ2 → ψ)) ⊢ θ.
Proof.
intro HP. apply make_impl_complete_L in HP.
apply additive_cut with (φ1 → φ2 ⇢ ψ);  [|exch 0; apply weakening, HP].
apply ImpR. exch 0. apply ImpL.
-  apply weakening, generalised_axiom.
- exch 0. apply weakening, make_impl_sound_R, generalised_axiom.
Qed.

Lemma make_impl_complete_R Γ φ ψ: Γ ⊢ φ ⇢ ψ -> Γ ⊢ (φ → ψ).
Proof.
intro HP.
apply additive_cut with (φ ⇢ ψ); [apply HP| apply make_impl_sound_L, generalised_axiom ].
Qed.


Lemma OrR_idemp Γ ψ : Γ ⊢ ψ ∨ ψ -> Γ ⊢ ψ.
Proof. intro Hp. dependent induction Hp; auto with proof. Qed.


Lemma strongness φ : ∅ •  φ ⊢ □ φ.
Proof.
apply BoxR. box_tac. apply weakening, open_box_L, generalised_axiom.
Qed.
