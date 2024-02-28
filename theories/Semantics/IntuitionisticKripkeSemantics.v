Require Import Coq.Classes.RelationClasses Coq.Program.Basics.

Require Import Formulas Sequents.


(* Source: A New Calculus for Intuitionistic Strong Löb Logic *)

(* for iSL *)
(* TODO: give names *)
Class IntuitionisticModalKripkeModel
  (W : Type) (R : relation W) (V: variable -> W -> Prop) (kle : relation W) (PreOrder_kle : `(PreOrder kle)) :=
   {
    Transitive_R: `(Transitive R);
    Subrelation_R_kle: `(subrelation R kle);
    Subrelation_R_kle_R: (forall x y z, kle x z -> R z y -> R x y);
    V_kle : (forall p w v, kle w v -> V p w -> V p v);
    R_wf : well_founded (flip R)
    }.

Reserved Infix "⊨" (at level 80).
Fixpoint forces `{M : IntuitionisticModalKripkeModel} (w : W) (φ : form) : Prop :=
match φ with
| Var p => V p w
| Bot => False
| And φ ψ => w ⊨ φ /\ w ⊨ ψ
| Or φ ψ => w ⊨ φ \/ w ⊨ ψ
| Implies φ ψ => forall v, kle w v -> v ⊨ φ /\ v ⊨ ψ
| Box φ => forall v, R w v -> v ⊨ φ
end
where "w ⊨ φ" := (forces w φ).
(* Note that we this is usually denoted M, w ⊨ φ, i.e. with M explicit *)

Lemma persistence `{M : IntuitionisticModalKripkeModel} φ w v: kle w v -> w ⊨ φ -> v ⊨ φ.
Proof.
Proof.
revert w v. induction φ; intros w w' Hle Hw; simpl.
- apply V_kle with w; auto.
- tauto.
- destruct Hw. eauto.
- destruct Hw; eauto.
- intros z Hz. apply Hw. transitivity w'; trivial.
- intros z Hz. eapply Hw. apply Subrelation_R_kle_R with w'; trivial.
Qed.

Definition sequent := (env * form)%type.

(* slight adaptation to intuitionistic. Check equivalence *)
Definition forces_sequent `{M : IntuitionisticModalKripkeModel} (w : W) (s : sequent) := 
  let (Γ, δ) := s in (∀ φ, φ ∈ Γ -> forces w φ) -> (forces w δ).
Notation "w '⊨s' s" := (forces_sequent w s) (at level 80).

Definition sequents_equivalence (S T : list sequent) : Prop := ∀ W `(M : IntuitionisticModalKripkeModel W) (w : W), 
  (∀ s, In s S -> forces_sequent w s) <->  (∀ t, In t T -> forces_sequent w t).

(* TODO: check confusion between R and kle *)
Definition bisimilar (p : variable) {W R V W' R' V'}
  `{M : IntuitionisticModalKripkeModel W R V kle} (x : W) `{M' : IntuitionisticModalKripkeModel W' R' V' kle'} (x' : W') :=
{ Z | Z x x' /\ ∀ w w', Z w w' ->
  (∀q, p ≠ q -> (V q w <-> V' q w' )) /\
  (∀ v, kle w v -> exists v', Z v v' /\ kle' w' v') /\
  (∀ v', kle' w' v' -> exists v, Z v v' /\ kle w v)
}. (* TODO: should Z preserve R as well? *)

Lemma bisimilarity_spec p ψ `(M : IntuitionisticModalKripkeModel W R V) w `(M' : IntuitionisticModalKripkeModel W' R' V') w': `(bisimilar p w w') ->
  (~ occurs_in p ψ)  -> (forces w ψ <-> forces w' ψ).
Proof.
revert w w'. induction ψ; intros w w' Hb Hvar; simpl in *; try tauto.
- destruct Hb as [Z [Hww' HZ]]; destruct (HZ w w' Hww') as (Hv & HR & HR');
  now apply Hv.
- rewrite (IHψ1 w w'), (IHψ2 w w'); tauto.
- rewrite (IHψ1 w w'), (IHψ2 w w'); tauto.
- split.
  + intros Hi v' Hw'v'.
      destruct Hb as [Z [Hww' HZ]]; destruct (HZ w w' Hww') as (Hv & HR & HR').
      apply HR' in Hw'v'. destruct Hw'v' as (v & HZv & Hwv).
      assert(Hb' : bisimilar p v v' ) by (exists Z; split; trivial).
      rewrite <- (IHψ1 v v'), <- (IHψ2 v v'); try tauto. now apply Hi.
  + intros Hi v Hwv.
      destruct Hb as [Z [Hww' HZ]]; destruct (HZ w w' Hww') as (Hv & HR & HR').
      apply HR in Hwv. destruct Hwv as (v' & HZv' & Hw'v').
      assert(Hb' : bisimilar p v v' ) by (exists Z; split; trivial).
      rewrite (IHψ1 v v'), (IHψ2 v v'); try tauto. now apply Hi.
- split.
  + intros Hi v' Hw'v'.
      destruct Hb as [Z [Hww' HZ]]; destruct (HZ w w' Hww') as (Hv & HR & HR').
      destruct (HR' _ (Subrelation_R_kle _ _ Hw'v')) as (v & HZv & Hwv).
      assert(Hb' : bisimilar p v v' ) by (exists Z; split; trivial).
      rewrite <- (IHψ v v'); try tauto. apply Hi. admit.
Admitted.

Require Import Coq.Program.Equality.

Local Instance empty_model: IntuitionisticModalKripkeModel () (λ _ _ : (), False) (λ (_ : variable) (_ : ()), True)
  (λ _ _ : (), True) (Equivalence_PreOrder unit_equivalence).
Proof. split; auto. intros x y. tauto. intro a. constructor. simpl. tauto. Qed.

(* iSL:  class of finite frames where R is transitive and irreflexive. *)
(* probably proved by generalising over sequents *)
(* TODO: missing finiteness *)
Lemma FMP_iSL_sequent Γ ψ:
  CRelationClasses.iffT
    (Provable Γ ψ)
    (exists `(M : IntuitionisticModalKripkeModel W R) (w : W), Irreflexive R /\ (w ⊨s (Γ, ψ))).
Proof.
split.
- intro Hψ. dependent induction Hψ. (* this is going to be tedious *)
  + exists unit. exists (λ _ _, False). exists (λ v _, True).
      exists (λ _ _, True). eexists. exists empty_model. exists (). split; simpl; trivial. intros _ F; exact F.
  + exists unit. exists (λ _ _, False). exists (λ v _, True).
      exists (λ _ _, True). eexists. exists empty_model. exists ().  split; simpl; trivial. intros _ F; exact F.
      intro H. destruct (H ⊥). ms.
  + destruct IHHψ1 as (W1 & R1 & V1 & le1 & HO1 & M1 & w1 & Ir1 & Hf1).
      destruct IHHψ2 as (W2 & R2 & V2 & le2 & HO2 & M2 & w2 & Ir2 & Hf2).
      (* TODO: this is clearly not the way we want to build models *)
      exists (W1 * W2)%type. exists (λ _ _, False).
      exists (λ var v, V1 var v.1 /\ V2 var v.2).
      exists (prod_relation le1 le2). eexists. eexists. exists (w1, w2). split.
      * intros [x x'] Hxx'. tauto.
      * intro H. simpl in *. admit.
      Unshelve.
      split. now apply prod_relation_refl. apply prod_relation_trans; [apply HO1| apply HO2].
      split; eauto. intro; tauto. intuition; destruct H; simpl in *. destruct M1;  eauto. destruct M2; eauto.
      intro. constructor. simpl. tauto.
  + 