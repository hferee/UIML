Require Import ISL.Environments ISL.Sequents ISL.SequentProps ISL.Cut ISL.DecisionProcedure.
Require Import Program Equality.

(** * Optimizations of formulas

   This file sets up a series of functions that simplify formulas, while maintaining equivalence.
  We also introduce the Lindenbaum-Tarski preorder ≼ on formulas to formalize this.
  We rely on the decision procedure to decide when φ ≼ ψ holds.
  We then introduce the functions "make_impl", "make_conj" and "make_disj", which
  perform obvious simplifications such as reducing φ ∧ ⊥ to ⊥ and φ ∨ ⊥ to φ.
  We also formally verify that these reductions maintain equivalence and do not introduce any
  new variables.
*)

Definition Lindenbaum_Tarski_preorder {K : Kind} φ ψ :=
  ∅ • φ ⊢ ψ.

Declare Scope provability.
Open Scope provability.

Notation "φ ≼ ψ" := (Lindenbaum_Tarski_preorder φ ψ) (at level 150) : provability.

(* Particular case of `additive_cut` easier to use *)
Corollary weak_cut {K : Kind} φ ψ θ:
  (φ ≼ ψ) -> (ψ ≼ θ) ->
  φ ≼ θ.
Proof.
intros H1 H2.
eapply additive_cut.
- apply H1.
- exch 0. now apply weakening.
Qed.


Lemma top_provable {K : Kind} Γ : Γ ⊢ ⊤.
Proof. apply ImpR. apply ExFalso. Qed.

(* TODO *)
Hint Resolve top_provable : proof.

(* Decides whether one formula entails the other or not ; in the latter case return Eq.
   It uses the decision procedure for iSL defined at `DecisionProcedure.v`
*)
Definition obviously_smaller {K : Kind} φ ψ :=
  if [φ] ⊢? ψ then Lt
  else if [ψ] ⊢? φ then Gt
  else Eq.

Definition choose_conj {K : Kind} φ ψ :=
match obviously_smaller φ ψ with
  | Lt => φ
  | Gt => ψ
  | Eq => φ ∧ ψ
 end.


Lemma occurs_in_choose_conj {K : Kind} v φ ψ :
  occurs_in v (choose_conj φ ψ) -> occurs_in v φ \/ occurs_in v ψ.
Proof. unfold choose_conj; destruct obviously_smaller; simpl; intros; tauto. Qed.


Local Definition f_inj {K K': Kind} (Heq : K = K') (φ : @form K) : @form K' :=
  eq_rect K (fun K => form) φ K' Heq.


Definition make_conj {K : Kind} (φ ψ : @form K) : @form K :=
match ψ in @form K' return (K' = K -> @form K) with
  | ψ1 ∧ ψ2 => fun HK =>
      match obviously_smaller φ (f_inj HK ψ1) with
        | Lt => φ ∧ f_inj HK ψ2
      | Gt => ψ
      | Eq => φ ∧ ψ
      end
  | ψ1 → ψ2 => fun HK =>
      if decide (obviously_smaller φ (f_inj HK  ψ1) = Lt)
      then choose_conj φ (f_inj HK ψ2)
      else choose_conj φ ψ
  | _ => fun _ =>
      match φ in @form K'' return (K'' = K -> @form K) with
      | φ1 → φ2 => fun HK' =>
          if decide (obviously_smaller ψ (f_inj HK' φ1) = Lt)
          then choose_conj (f_inj HK' φ2) ψ
          else choose_conj φ ψ
      | _ => fun HK' => choose_conj φ ψ
       end eq_refl
end eq_refl.

Infix "⊼" := make_conj (at level 60).

Lemma occurs_in_make_conj {K : Kind} v (φ ψ : form) :
  occurs_in v (φ ⊼ ψ) -> occurs_in v φ \/ occurs_in v ψ.
Proof.
generalize ψ.
induction φ; intro ψ0; dependent destruction ψ0;
intro H; unfold make_conj in H; unfold choose_conj in H;
repeat match goal with
    | H: occurs_in _  (if ?cond then _ else _) |- _ => case decide in H
    | H: occurs_in _ (match ?x with _ => _ end) |- _ => destruct x
    | |- _ => simpl; simpl in H; tauto
end.
Qed.


Definition choose_disj {K : Kind} φ ψ :=
match obviously_smaller φ ψ with
  | Lt => ψ
  | Gt => φ
  | Eq => φ ∨ ψ
 end.

Definition make_disj {K : Kind} φ ψ:=
match ψ in @form K' return (K' = K -> @form K) with
  | ψ1 ∨ ψ2 => fun HK =>
      match obviously_smaller φ (f_inj HK ψ1) with
      | Lt => ψ
      | Gt => φ ∨ f_inj HK ψ2
      | Eq => φ ∨ ψ
      end
  | ψ1 ∧ ψ2 => fun HK =>
      if decide (obviously_smaller φ (f_inj HK ψ1) = Gt ) then φ
      else if decide (obviously_smaller φ (f_inj HK ψ2) = Gt) then φ
      else choose_disj φ ψ
  |_ => fun _ => choose_disj φ ψ
end eq_refl.

Infix "⊻" := make_disj (at level 65).

Lemma occurs_in_choose_disj {K : Kind} v φ ψ :
  occurs_in v (choose_disj φ ψ) -> occurs_in v φ \/ occurs_in v ψ.
Proof. unfold choose_disj; destruct obviously_smaller; simpl; intros; tauto. Qed.

Lemma occurs_in_make_disj {K : Kind} v φ ψ :
  occurs_in v (φ ⊻ ψ) -> occurs_in v φ ∨ occurs_in v ψ.
Proof.
generalize ψ.
induction φ; intro ψ0; dependent destruction ψ0;
intro H; unfold make_disj in H; unfold choose_disj in H;
repeat match goal with
    | H: occurs_in _  (if ?cond then _ else _) |- _ => case decide in H
    | H: occurs_in _ (match ?x with _ => _ end) |- _ => destruct x
    | |- _ => simpl; simpl in H; tauto
end.
Qed.


(* "lazy" implication, which produces a potentially simpler, equivalent formula *)

Definition choose_impl {K : Kind} φ ψ:=
     if decide (obviously_smaller φ ψ = Lt) then ⊤
     else if decide (obviously_smaller φ ⊥ = Lt) then ⊤
     else if decide (obviously_smaller ⊤ ψ = Lt) then ⊤
     else if decide (obviously_smaller ⊤ φ = Lt) then ψ
     else if decide (obviously_smaller ψ ⊥ = Lt) then ¬φ
     else if decide (is_negation φ ψ) then ¬φ
     else if decide (is_negation ψ φ) then ψ
    else φ → ψ.

Fixpoint make_impl {K : Kind} φ ψ :=
match ψ in @form K' return (K' = K -> @form K) with
  |(ψ1 → ψ2) => fun HK => make_impl (make_conj φ (f_inj HK ψ1)) (f_inj HK ψ2)
  |_ => fun _ => choose_impl φ ψ
end eq_refl.

Infix "⇢" := make_impl (at level 66).

Lemma occurs_in_choose_impl {K : Kind} v x y : occurs_in v (choose_impl x y) -> occurs_in v x ∨ occurs_in v y.
Proof.
intro H; unfold choose_impl in H; fold make_impl in H;
repeat match goal with
    | H: occurs_in _  (if ?cond then _ else _) |- _ => case decide in H
    | H: occurs_in _ (match ?x with _ => _ end) |- _ => destruct x
    | |- _ => simpl; simpl in H; tauto
end.
Qed.

Lemma occurs_in_make_impl {K : Kind}  v x y :
  occurs_in v (x ⇢ y) -> occurs_in v x ∨ occurs_in v y.
Proof.
revert x.
induction y; intro ψ0;
intro H; unfold make_impl in H; try apply occurs_in_choose_impl in H; try tauto.
apply IHy2 in H.
- destruct H as [H|H]; [ apply occurs_in_make_conj in H|]; simpl; tauto.
Qed.

Lemma occurs_in_make_impl2 {K : Kind}  v x y z:
  occurs_in v (x ⇢ (y ⇢ z)) -> occurs_in v x ∨ occurs_in v y ∨ occurs_in v z.
Proof.
intro H. apply occurs_in_make_impl in H. destruct H as [H|H]; try tauto.
apply occurs_in_make_impl in H. tauto.
Qed.

(** To be noted: we remove duplicates first *)
Definition conjunction {K : Kind} l := foldl make_conj (⊥→ ⊥) (nodup form_eq_dec l).
Notation "⋀" := conjunction.

Definition disjunction {K : Kind}  l := foldl make_disj ⊥ (nodup form_eq_dec l).
Notation "⋁" := disjunction.

Lemma variables_conjunction {K : Kind}  x l : occurs_in x (⋀ l) -> exists φ, φ ∈ l /\ occurs_in x φ.
Proof.
unfold conjunction.
assert (Hcut : forall ψ, occurs_in x (foldl make_conj ψ (nodup form_eq_dec l))
  -> occurs_in x ψ \/ (∃ φ, (φ ∈ l ∧ occurs_in x φ)%type)).
{
induction l; simpl.
- tauto.
- intros ψ Hocc.
  case in_dec in Hocc; apply IHl in Hocc; simpl in Hocc;
  destruct Hocc as [Hx|(φ&Hin&Hx)]; try tauto.
  + right. exists φ. split; auto with *.
  + apply occurs_in_make_conj in Hx; destruct Hx as [Hx|Hx]; auto with *.
      right. exists a. auto with *.
  + right. exists φ. split; auto with *.
}
intro Hocc. apply Hcut in Hocc. simpl in Hocc. tauto.
Qed.

Lemma variables_disjunction {K : Kind}  x l :
  occurs_in x (⋁ l) -> exists φ, φ ∈ l /\ occurs_in x φ.
Proof.
unfold disjunction.
assert (Hcut : forall ψ, occurs_in x (foldl make_disj ψ (nodup form_eq_dec l))
  -> occurs_in x ψ \/ (∃ φ, (φ ∈ l ∧ occurs_in x φ)%type)).
{
induction l; simpl.
- tauto.
- intros ψ Hocc.
  case in_dec in Hocc; apply IHl in Hocc; simpl in Hocc;
  destruct Hocc as [Hx|(φ&Hin&Hx)]; try tauto.
  + right. exists φ. split; auto with *.
  + apply occurs_in_make_disj in Hx; destruct Hx as [Hx|Hx]; auto with *.
      right. exists a. auto with *.
  + right. exists φ. split; auto with *.
}
intro Hocc. apply Hcut in Hocc. simpl in Hocc. tauto.
Qed.


(** ** Correctness of optimizations

    The following results show that the definitions of these functions are correct, in the sense that it does not make a difference for
    provability of a sequent whether one uses the literal conjunction, disjunction, and implication, or its optimized version.
*)


(** Useful lemmas about `obviously_smaller` *)

Lemma double_negation_obviously_smaller {K : Kind} φ ψ:
 is_double_negation φ ψ -> ψ ≼ φ.
Proof.
intro H; rewrite H. apply ImpR; auto with proof.
Qed.

Lemma is_implication_obviously_smaller {K : Kind} φ ψ:
 is_implication φ ψ -> ψ ≼ φ.
Proof.
unfold is_implication. intro H.
destruct φ; try (contradict H; intros [θ Hθ]; discriminate).
case (decide (φ2 = ψ)).
- intro; subst. apply ImpR, weakening, generalised_axiom.
- intro Hneq. contradict H; intros [θ Hθ]. dependent destruction Hθ. tauto.
Qed.


Lemma obviously_smaller_compatible_LT {K : Kind} φ ψ :
  (obviously_smaller φ ψ = Lt -> φ ≼ ψ) *
  ((φ ≼ ψ) -> obviously_smaller φ ψ = Lt ).
Proof.
unfold obviously_smaller, Lindenbaum_Tarski_preorder.
case ([φ] ⊢? ψ); intros Hp.
- apply Provable_dec_of_Prop in Hp. split; intro.  peapply Hp. trivial.
- split; intro Hf.
  + contradict Hf. case ([ψ] ⊢? φ); discriminate.
  + tauto.
Qed.

Lemma obviously_smaller_compatible_GT {K : Kind} φ ψ :
  (obviously_smaller φ ψ = Gt -> ψ ≼ φ) *
  (((φ ≼ ψ) -> False) -> (ψ ≼ φ) -> obviously_smaller φ ψ = Gt ).
Proof.
unfold obviously_smaller, Lindenbaum_Tarski_preorder.
case ([ψ] ⊢? φ); intro Hp; case ([φ] ⊢? ψ); intro Hp'; split; try discriminate; trivial.
- intros Hf _. destruct Hp'. contradict Hf. tauto.
- intros. apply Provable_dec_of_Prop in Hp.  peapply Hp.
- intros _ Hf. destruct Hp'. contradict Hf. tauto.
- intros _ Hf. destruct Hp'. contradict Hf. tauto.
Qed.


(** Equivalence of the conjunction optimizations *)

Lemma and_congruence {K : Kind} φ ψ φ' ψ':
  (φ ≼ φ') -> (ψ ≼ ψ') -> (φ ∧ ψ) ≼ φ' ∧ ψ'.
Proof.
intros Hφ Hψ.
apply AndL.
apply AndR.
- now apply weakening.
- exch 0. now apply weakening.
Qed.

Lemma choose_conj_topL {K : Kind} φ : (choose_conj φ ⊤ = φ).
Proof.
unfold choose_conj.
rewrite (obviously_smaller_compatible_LT _ _).2. trivial.
apply ImpR, ExFalso.
Qed.

Lemma choose_conj_sound_L {K : Kind} Δ φ ψ:
  (Δ ⊢ φ) -> (Δ ⊢ ψ) -> Δ ⊢ choose_conj φ ψ.
Proof.
intros Hφ Hψ.
unfold choose_conj. case obviously_smaller; auto with proof.
Qed.

Corollary choose_conj_equiv_L {K : Kind} φ ψ φ' ψ':
  (φ ≼ φ') -> (ψ ≼ ψ') -> (φ ∧ ψ) ≼ choose_conj φ' ψ'.
Proof.
intros H1 H2. apply choose_conj_sound_L; apply AndL; auto with proof.
Qed.

Lemma choose_conj_equiv_R {K : Kind} φ ψ φ' ψ':
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

Local Ltac inj_tac := unfold f_inj in *; rewrite <- eq_rect_eq in *.

Lemma make_conj_equiv_L {K : Kind} φ ψ φ' ψ' :
  (φ ≼ φ') -> (ψ ≼ ψ') -> (φ ∧ ψ) ≼ φ' ⊼ ψ'.
Proof.
intros Hφ Hψ.
unfold make_conj.
destruct ψ'; try (apply choose_conj_equiv_L; assumption); try inj_tac.
- destruct φ'; try (apply choose_conj_equiv_L; assumption).
  case decide; intro; try (apply choose_conj_equiv_L; assumption).
  apply obviously_smaller_compatible_LT in e. inj_tac.
  apply weak_cut with ((φ ∧ φ'1) ∧ ψ).
  + apply AndL; repeat apply AndR.  auto with proof.
      * exch 0. apply weakening;  apply weak_cut with v; assumption.
      * apply generalised_axiom.
  + apply choose_conj_equiv_L; auto with proof.
- apply exfalso, AndL. exch 0. apply weakening, Hψ.
- inj_tac. case_eq (obviously_smaller φ' ψ'1); intro Heq.
  + apply and_congruence; assumption.
  + apply and_congruence.
    * assumption.
    * apply AndR_rev in Hψ; apply Hψ.
  + apply AndL. exch 0. apply weakening. assumption.
- destruct φ'; try (apply choose_conj_equiv_L; assumption).
  case decide; intro; try (apply choose_conj_equiv_L; assumption).
  apply obviously_smaller_compatible_LT in e.
  apply weak_cut with ((φ ∧ φ'1) ∧ ψ).
  + apply AndL; repeat apply AndR.  auto with proof.
      * exch 0. apply weakening;  apply weak_cut with (ψ'1 ∨ ψ'2); assumption.
      * apply generalised_axiom.
  + apply choose_conj_equiv_L; auto with proof.
- case (decide (obviously_smaller φ' ψ'1 = Lt)); intro.
  + apply weak_cut with (φ ∧ (φ ∧ ψ)).
     * apply AndR; auto with proof.
     * apply choose_conj_equiv_L. assumption.
        apply obviously_smaller_compatible_LT in e.
        apply contraction, ImpR_rev. apply weak_cut with ψ'1.
        -- apply weak_cut with φ'; auto with proof.
        -- apply ImpR. exch 0. apply ImpR_rev, AndL. exch 0. apply weakening, Hψ.
  + apply choose_conj_equiv_L; assumption.
- dependent destruction φ'; try (apply choose_conj_equiv_L; assumption).
  case decide; intro; try (apply choose_conj_equiv_L; assumption).
  apply weak_cut with (ψ ∧ (φ ∧ φ'1)).
  + apply AndL, AndR. auto with proof. apply AndR. auto with proof.
      exch 0. apply weakening. apply weak_cut with (□ ψ'). auto with proof.
      now apply obviously_smaller_compatible_LT.
  + apply weak_cut with ((φ ∧ φ'1) ∧ ψ).
     * apply AndR; auto with proof.
     * apply choose_conj_equiv_L; auto with proof.
Qed.

Lemma make_conj_equiv_R {K : Kind} φ ψ φ' ψ' :
  (φ' ≼ φ) -> (ψ' ≼ ψ) -> φ' ⊼ ψ' ≼  φ ∧ ψ.
Proof.
intros Hφ Hψ.
unfold make_conj.
destruct  ψ'; try inj_tac.
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
- destruct φ'; try case decide; intros; apply choose_conj_equiv_R; try assumption.
   eapply imp_cut; eassumption.
- case decide; intro Heq.
  + apply choose_conj_equiv_R. assumption. eapply weak_cut; [|exact Hψ]. auto with proof.
  + apply choose_conj_equiv_R; assumption.
- dependent destruction φ'; try case decide; intros; apply choose_conj_equiv_R; try assumption.
  eapply imp_cut; eassumption.
Qed.

Lemma specialised_weakening {K : Kind} Γ φ ψ : (φ ≼ ψ) ->  Γ•φ ⊢ ψ.
Proof.
intro H.
apply generalised_weakeningL.
peapply H.
Qed.

Lemma make_conj_sound_L {K : Kind} Γ φ ψ θ : Γ•φ ∧ψ ⊢ θ -> Γ• φ ⊼ ψ ⊢ θ.
Proof.
intro H.
eapply additive_cut.
- apply specialised_weakening.
  apply make_conj_equiv_R; apply generalised_axiom.
- exch 0. now apply weakening.
Qed.

Global Hint Resolve make_conj_sound_L : proof.

Lemma make_conj_complete_L {K : Kind} Γ φ ψ θ : Γ• φ ⊼ ψ ⊢ θ -> Γ•φ ∧ψ ⊢ θ.
Proof.
intro H.
eapply additive_cut.
- apply specialised_weakening.
  apply make_conj_equiv_L; apply generalised_axiom.
- exch 0. now apply weakening.
Qed.

Lemma make_conj_sound_R {K : Kind} Γ φ ψ : Γ  ⊢ φ ∧ψ -> Γ ⊢ φ ⊼ ψ.
Proof.
intro H.
eapply additive_cut.
- apply H.
- apply make_conj_complete_L, generalised_axiom.
Qed.

Global Hint Resolve make_conj_sound_R : proof.

Lemma make_conj_complete_R {K : Kind} Γ φ ψ : Γ  ⊢ φ ⊼ ψ -> Γ  ⊢ φ ∧ψ.
Proof.
intro H.
eapply additive_cut.
- apply H.
- apply make_conj_sound_L, generalised_axiom.
Qed.


(** Equivalence of the disjonction optimizations *)

Lemma or_congruence {K : Kind} φ ψ φ' ψ':
  (φ ≼ φ') -> (ψ ≼ ψ') -> (φ ∨ ψ) ≼ φ' ∨ ψ'.
Proof.
intros Hφ Hψ.
apply OrL.
- now apply OrR1.
- now apply OrR2.
Qed.

Lemma choose_disj_sound_L1 {K : Kind} Δ φ ψ:
  (Δ ⊢ φ) -> Δ ⊢ choose_disj φ ψ.
Proof.
intros Hφ.
unfold choose_disj. case_eq (obviously_smaller φ ψ); auto with proof.
intro Hs. apply obviously_smaller_compatible_LT in Hs.
apply additive_cut with φ. trivial. now apply specialised_weakening.
Qed.

Lemma choose_disj_sound_L2 {K : Kind} Δ φ ψ:
  (Δ ⊢ ψ) -> Δ ⊢ choose_disj φ ψ.
Proof.
intros Hφ.
unfold choose_disj. case_eq (obviously_smaller φ ψ); auto with proof.
intro Hs. apply obviously_smaller_compatible_GT in Hs.
apply additive_cut with ψ. trivial. now apply specialised_weakening.
Qed.

Lemma choose_disj_equiv_L {K : Kind} φ ψ φ' ψ':
  (φ ≼ φ') -> (ψ ≼ ψ') -> (φ ∨ ψ) ≼ choose_disj φ' ψ'.
Proof.
intros Hφ Hψ.
unfold choose_disj.
case_eq (obviously_smaller φ' ψ'); intro Heq.
- case_eq (obviously_smaller ψ' φ'); intro Heq'.
  + apply or_congruence; assumption.
  + auto with proof.
  + auto with proof.
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

Lemma choose_disj_equiv_R {K : Kind} φ ψ φ' ψ' :
  (φ' ≼ φ) -> (ψ' ≼ ψ) -> choose_disj φ' ψ' ≼  φ ∨ ψ.
Proof.
intros Hφ Hψ.
unfold choose_disj.
case_eq (obviously_smaller φ' ψ'); intro Heq;
[| apply OrR2| apply OrR1]; try assumption.
auto with proof.
Qed.

Lemma make_disj_equiv_L {K : Kind} φ ψ φ' ψ' :
  (φ ≼ φ') -> (ψ ≼ ψ') -> (φ ∨ ψ) ≼ φ' ⊻ ψ'.
Proof.
intros Hφ Hψ.
unfold make_disj.
destruct ψ'; try (apply choose_disj_equiv_L; assumption); try inj_tac.
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


Lemma make_disj_equiv_R {K : Kind} φ ψ φ' ψ' :
  (φ' ≼ φ) -> (ψ' ≼ ψ) -> φ' ⊻  ψ' ≼  φ ∨ ψ.
Proof.
intros Hφ Hψ.
unfold make_disj.
destruct ψ'; try inj_tac.
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

Lemma make_disj_sound_L {K : Kind} Γ φ ψ θ :
  Γ•φ ∨ψ ⊢ θ -> Γ•make_disj φ ψ ⊢ θ.
Proof.
intro H.
eapply additive_cut.
- apply specialised_weakening.
  apply make_disj_equiv_R; apply generalised_axiom.
- exch 0. now apply weakening.
Qed.

Global Hint Resolve make_disj_sound_L : proof.

Lemma make_disj_complete_L {K : Kind} Γ φ ψ θ :
  Γ • make_disj φ ψ ⊢ θ -> Γ • φ ∨ψ ⊢ θ.
Proof.
intro H.
eapply additive_cut.
- apply specialised_weakening.
  apply make_disj_equiv_L; apply generalised_axiom.
- exch 0. now apply weakening.
Qed.

Lemma make_disj_sound_R {K : Kind} Γ φ ψ : Γ  ⊢ φ ∨ψ -> Γ ⊢ make_disj φ ψ.
Proof.
intro H.
eapply additive_cut.
- apply H.
- apply make_disj_complete_L, generalised_axiom.
Qed.

Global Hint Resolve make_disj_sound_R : proof.

Lemma make_disj_complete_R {K : Kind} Γ φ ψ : Γ  ⊢ make_disj φ ψ -> Γ  ⊢ φ ∨ψ.
Proof.
intro H.
eapply additive_cut.
- apply H.
- apply make_disj_sound_L, generalised_axiom.
Qed.


(** Equivalence of the implication optimizations *)


(* TODO: suitable name *)
Lemma tautology_cut {K : Kind} {Γ} {φ ψ θ} :
  Γ • (φ → ψ) ⊢ θ -> (φ ≼ ψ) -> Γ ⊢ θ.
Proof.
intros Hp H.
apply additive_cut with (φ → ψ).
  + apply ImpR, generalised_weakeningL. peapply H.
  + apply Hp.
Qed.

Lemma Lindenbaum_Tarski_preorder_Bot {K : Kind} φ : ⊥ ≼ φ.
Proof. apply ExFalso. Qed.

Local Hint Resolve Lindenbaum_Tarski_preorder_Bot : proof.


Lemma choose_impl_sound_L {K : Kind} Γ φ ψ θ: Γ•(φ → ψ) ⊢ θ -> Γ•(choose_impl φ ψ) ⊢ θ.
Proof.
intro HP.
unfold choose_impl; repeat case decide; intros;
repeat match goal with
| H : obviously_smaller _ _ = Lt |- _ => apply obviously_smaller_compatible_LT in H
| H : obviously_smaller _ _ = Gt |- _ => apply obviously_smaller_compatible_GT in H
| H : is_negation _ _ |- _ =>  eapply additive_cut; [| exch 0; apply weakening, HP]; apply ImpR, exfalso; exch 0; auto with proof
end; trivial; try (solve [eapply imp_cut; eauto]);
try solve[apply weakening, (tautology_cut HP); trivial; try apply weak_cut with ⊥; auto with proof].
- apply weakening, (tautology_cut HP); trivial. apply additive_cut with (φ := ⊤); auto with proof.
- eapply additive_cut with (φ :=  (φ → ψ)).
  + apply ImpR. exch 0. apply ImpL; auto with proof.
  + auto with proof.
- unfold is_negation in *. subst. auto with proof.
Qed.

Lemma make_impl_sound_L {K : Kind} Γ φ ψ θ: Γ•(φ → ψ) ⊢ θ -> Γ•(φ ⇢ ψ) ⊢ θ.
Proof.
revert φ. induction ψ; intros φ HP; simpl; repeat case decide; intros.
1-4, 6: now apply choose_impl_sound_L.
apply IHψ2.
apply ImpLAnd in HP.
apply additive_cut with ((φ ∧ ψ1 → ψ2) → θ).
- apply weakening, ImpR, HP.
- apply ImpL; [|auto with proof].
  apply weakening, ImpR. exch 0. apply ImpL; [|auto with proof].
  apply weakening, make_conj_complete_L, generalised_axiom.
Qed.

Global Hint Resolve make_impl_sound_L : proof.

Lemma choose_impl_sound_R {K : Kind} Γ φ ψ: Γ ⊢ (φ → ψ) -> Γ ⊢ choose_impl φ ψ.
Proof.
unfold choose_impl.
 repeat case decide; intros;
repeat match goal with
| |- _ ⊢ ⊤ => apply ImpR, ExFalso
| H : obviously_smaller _ _ = Lt |- _ => apply obviously_smaller_compatible_LT in H
| H : obviously_smaller _ _ = Gt |- _ => apply obviously_smaller_compatible_GT in H
| H : is_negation _ _ |- _ =>  rewrite H  in *; apply ImpR;  eapply additive_cut; [apply ImpR_rev, HP| exch 0; auto with *]
end; trivial; auto with proof;
try (solve[peapply (cut ∅ Γ φ); auto with proof; eapply TopL_rev; eauto]).
- apply ImpR, additive_cut with (φ:= ψ).
  + now apply ImpR_rev.
  + apply generalised_weakeningL. peapply e.
- unfold is_negation in *. subst. auto with proof.
- unfold is_negation in *. subst. auto with proof.
Qed.


Lemma make_impl_sound_R {K : Kind} Γ φ ψ: Γ ⊢ (φ → ψ) -> Γ ⊢ φ ⇢ ψ.
Proof.
revert φ. induction ψ; intros φ HP; simpl.
1-4, 6: now apply choose_impl_sound_R.
apply IHψ2, ImpR, make_conj_sound_L, AndL, ImpR_rev, ImpR_rev, HP.
Qed.

Global Hint Resolve make_impl_sound_R : proof.

Lemma make_impl_sound_L2 {K : Kind} Γ φ1 φ2 ψ θ:
  Γ•(φ1 → (φ2 → ψ)) ⊢ θ -> Γ•(φ1 ⇢ (φ2 ⇢ ψ)) ⊢ θ.
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

Lemma make_impl_sound_L2' {K : Kind} Γ φ1 φ2 ψ θ:
  Γ•((φ1 → φ2) → ψ) ⊢ θ -> Γ•((φ1 ⇢ φ2) ⇢ ψ) ⊢ θ.
Proof.
intro HP. apply make_impl_sound_L.
apply additive_cut with ((φ1 → φ2) → ψ); [|exch 0; apply weakening, HP].
apply ImpR. exch 0. apply ImpL.
- apply weakening, make_impl_sound_R, generalised_axiom.
- apply generalised_axiom.
Qed.

Lemma make_impl_complete_L {K : Kind} Γ φ ψ θ:
  Γ•(φ ⇢ ψ) ⊢ θ -> Γ•(φ → ψ) ⊢ θ.
Proof.
intro HP.
apply additive_cut with (φ ⇢ ψ); [|exch 0; apply weakening, HP].
apply make_impl_sound_R, generalised_axiom.
Qed.

Lemma make_impl_complete_L2 {K : Kind} Γ φ1 φ2 ψ θ:
  Γ•(φ1 ⇢ (φ2 ⇢ ψ)) ⊢ θ -> Γ•(φ1 → (φ2 → ψ)) ⊢ θ.
Proof.
intro HP. apply make_impl_complete_L in HP.
apply additive_cut with (φ1 → φ2 ⇢ ψ);  [|exch 0; apply weakening, HP].
apply ImpR. exch 0. apply ImpL.
-  apply weakening, generalised_axiom.
- exch 0. apply weakening, make_impl_sound_R, generalised_axiom.
Qed.

Lemma make_impl_complete_R {K : Kind} Γ φ ψ:
  Γ ⊢ φ ⇢ ψ -> Γ ⊢ (φ → ψ).
Proof.
intro HP.
apply additive_cut with (φ ⇢ ψ); [apply HP| apply make_impl_sound_L, generalised_axiom ].
Qed.

(** ** Generalized rules

In this section we prove that generalizations of or-left and and-right rules
that take more than two formulas are admissible and invertible in the calculus
G4ip. This is important in the correctness proof of propositional quantifiers
because the propositional quantifiers are defined as large disjunctions /
conjunctions of various individual formulas.
*)

(** *** Generalized OrL and its invertibility *)

Lemma disjunction_L {K : Kind} Γ Δ θ :
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
  - intro Hall. case in_dec; intro; apply (fst IHΔ).
    + exact Hψ.
    + auto with *.
    + simpl. apply make_disj_sound_L, OrL; auto with *.
    + auto with *.
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


(** *** Generalized OrR *)

Lemma disjunction_R {K : Kind} Γ Δ φ : (φ ∈ Δ) -> (Γ  ⊢ φ) -> (Γ  ⊢ ⋁ Δ).
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

(** *** Generalized AndR *)

Lemma conjunction_R1 {K : Kind} Γ Δ : (forall φ, φ ∈ Δ -> Γ  ⊢ φ) -> (Γ  ⊢ ⋀ Δ).
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


(** *** Generalized invertibility of AndR *)

Lemma conjunction_R2 {K : Kind} Γ Δ : (Γ  ⊢ ⋀ Δ) -> (forall φ, φ ∈ Δ -> Γ  ⊢ φ).
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

(** *** Generalized AndL *)

Lemma conjunction_L {K : Kind} Γ Δ φ θ: (φ ∈ Δ) -> (Γ•φ ⊢ θ) -> (Γ•⋀ Δ ⊢ θ).
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

Lemma conjunction_L' {K : Kind} Γ Δ ϕ: (Γ ⊎ {[⋀ Δ]} ⊢ ϕ) -> Γ ⊎ list_to_set_disj Δ ⊢ ϕ.
Proof.
revert ϕ. unfold conjunction.
assert( Hstrong: ∀ θ ϕ : form, Γ ⊎ {[foldl make_conj θ (nodup form_eq_dec Δ)]} ⊢ ϕ
  → (Γ ⊎ list_to_set_disj Δ) ⊎ {[θ]} ⊢ ϕ).
{
  induction Δ as [|δ Δ]; intros θ ϕ; simpl.
  - intro Hp. peapply Hp.
  - case in_dec; intros Hin Hp.
    + peapply (weakening δ). apply IHΔ, Hp. ms.
    + simpl in Hp. apply IHΔ in Hp.
        peapply (AndL_rev (Γ ⊎ list_to_set_disj Δ) θ δ). apply make_conj_complete_L, Hp.
}
  intros; apply additive_cut with (φ := ⊤); eauto with proof.
Qed.

Lemma conjunction_R {K : Kind} Δ: list_to_set_disj Δ ⊢ ⋀ Δ.
Proof.
apply conjunction_R1. intros φ Hφ. apply elem_of_list_to_set_disj in Hφ.
exhibit Hφ 0. apply generalised_axiom.
Qed.

Lemma conjunction_L'' {K : Kind} Γ Δ ϕ:
  Γ ⊎ list_to_set_disj Δ ⊢ ϕ -> (Γ ⊎ {[⋀ Δ]} ⊢ ϕ).
Proof.
revert ϕ. unfold conjunction.
assert( Hstrong: ∀ θ ϕ : form,(Γ ⊎ list_to_set_disj Δ) ⊎ {[θ]} ⊢ ϕ -> Γ ⊎ {[foldl make_conj θ (nodup form_eq_dec Δ)]} ⊢ ϕ).
{
  induction Δ as [|δ Δ]; intros θ ϕ; simpl.
  - intro Hp. peapply Hp.
  - case in_dec; intros Hin Hp.
    + apply IHΔ.
         assert(Hin' : δ ∈ (Γ ⊎ list_to_set_disj Δ)).
         { apply gmultiset_elem_of_disj_union; right; apply elem_of_list_to_set_disj, elem_of_list_In, Hin. }
           exhibit Hin' 1.
           rewrite (proper_Provable _ _ (env_add_comm _ _ _) _ _ eq_refl).
           apply contraction. exch 1. exch 0.
           rw (symmetry (difference_singleton _ _ Hin')) 2. peapply Hp.
    + simpl. apply IHΔ. apply make_conj_sound_L, AndL. peapply Hp.
}
intros. apply Hstrong, weakening. assumption.
Qed.

(* begin details *)
(**
  - [choose_impl_weight]: The weight of the chosen implication is less than or equal to the weight of the implication.
  - [choose_impl_top_weight]: The weight of the chosen implication with ⊤ is less than or equal to the weight of the formula.
  - [obviously_smaller_top_not_Eq]: ⊤ is not obviously smaller than any formula.
  - [contextual_simp_form_weight]: The simplified form of a formula in a given context is either ⊤, or has a weight less than or equal to the original formula.
*)
(* end details *)


Lemma choose_impl_weight {K : Kind} φ ψ: weight (choose_impl φ ψ) ≤ weight (φ → ψ).
Proof.
pose (weight_pos φ). pose (weight_pos ψ).
unfold choose_impl; repeat case decide; intros; simpl; lia.
Qed.

Lemma choose_impl_top_weight {K : Kind} ψ: weight (choose_impl ⊤ ψ) ≤ weight ψ.
Proof.
pose (weight_pos ψ).
unfold choose_impl; repeat case decide; intros; try lia.
- destruct (weight_tautology ψ).
  + apply obviously_smaller_compatible_LT in e.
    apply additive_cut with ⊤; auto with proof.
  + subst; simpl in *; tauto || lia.
  + subst; simpl in *; tauto || lia.
- destruct (weight_tautology ψ).
  + apply obviously_smaller_compatible_LT in e.
    apply additive_cut with ⊤; auto with proof.
  + subst; simpl in *; tauto || lia.
  + subst; simpl in *; tauto || lia.
- contradict n. apply obviously_smaller_compatible_LT. auto with proof.
- contradict n0. apply obviously_smaller_compatible_LT. auto with proof.
- contradict n2. apply obviously_smaller_compatible_LT. auto with proof.
Qed.

Lemma obviously_smaller_top_not_Eq {K : Kind} φ: obviously_smaller ⊤ φ ≠ Eq.
Proof.
unfold obviously_smaller.
case Provable_dec. discriminate. intro. case Provable_dec. discriminate.
intro Hf. contradict Hf. auto with proof.
Qed.

