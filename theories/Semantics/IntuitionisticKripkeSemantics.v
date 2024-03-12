Require Import Coq.Classes.RelationClasses Coq.Program.Basics.

Require Import Formulas Sequents.


(* Source: A New Calculus for Intuitionistic Strong Löb Logic *)

(* TODO: better naming convention? *)
Class IntuitionisticFrame (W : Type) (R : relation W).

Class IntuitionisticModalFrame W R (kle : relation W) :=
 { IntuitionisticModalFrame_IntuitionisticFrame :: IntuitionisticFrame W R;
   IntuitionisticModalFrame_PartialOrder :: PartialOrder kle;
   RBox : forall x y z, kle x z -> R z y -> R x y}.

Class IntuitionisticK4Frame W R :=
  { IntuitionisticK4Frame_IntuitionisticFrame ::  IntuitionisticFrame W R;
   transitive_frame :: Transitive R}.

Class StrongFrame W R (kle : relation W) :=
  { StrongFrame_IntuitionisticModalFrame ::  IntuitionisticModalFrame W R kle;
     strongness : subrelation R kle}.

(* Class IntuitionisticTFrame `(IntuitionisticFrame) := {reflexive_frame : reflexive R}. *)

Class ValuatedFrame W R (kle : relation W) (var : Type) (V: var -> W -> Prop) :=
 { ValuatedFrame_IntuitionisticFrame :: IntuitionisticFrame W R;
  valuation_monotonicity : forall p w v, kle w v -> V p w -> V p v}.

(* TODO: should Valuation extend IntuitionisticFrame? *)

(* an ISL Frame … *)
Class ISLFrame {W} {R} {kle : relation W} {var} {V : var -> W -> Prop} :=
 { ISL_Frame_Strong :: StrongFrame W R kle; (* is in particular a strong frame ; *)
   ISL_Frame_K4 :: IntuitionisticK4Frame W R; (* and a K4 frame ; *)
   ISLFrame_ValuatedFrame :: ValuatedFrame W R kle var V; (* it has a valuation *)
   convWf :  well_founded (flip R) (* R is converse well-founded *)
   }.

Reserved Infix "⊨" (at level 80).
Fixpoint forces `{ValuatedFrame W R kle variable V} (w : W) (φ : form) : Prop :=
match φ with
| Var p => V p w
| Bot => False
| And φ ψ => w ⊨ φ /\ w ⊨ ψ
| Or φ ψ => w ⊨ φ \/ w ⊨ ψ
| Implies φ ψ => forall v, kle w v -> v ⊨ φ -> v ⊨ ψ
| Box φ => forall v, R w v -> v ⊨ φ
end
where "w ⊨ φ" := (forces w φ).
(* Note that we this is usually denoted M, w ⊨ φ, i.e. with M explicit *)


(* TODO: "we say that (W, ≤, R, V )
is a model over P ⊆ Prop if the codomain of V is P(P )." *)

Lemma persistence `{ISLFrame W R kle variable} φ w v: kle w v -> w ⊨ φ -> v ⊨ φ.
Proof.
revert w v. induction φ; intros w w' Hle Hw; simpl.
- apply valuation_monotonicity with w; auto.
- tauto.
- destruct Hw. eauto.
- destruct Hw; eauto.
- intros z Hz. apply Hw. transitivity w'; trivial.
- intros z Hz. apply Hw. now apply (RBox _ _ w').
Qed.

Definition sequent := (env * form)%type.

(* slight adaptation to intuitionistic. Check equivalence *)
Definition forces_sequent `{ValuatedFrame W R kle variable V} (w : W) (s : sequent) := 
  let (Γ, δ) := s in (∀ φ, φ ∈ Γ -> forces w φ) -> (forces w δ).
Notation "w '⊨s' s" := (forces_sequent w s) (at level 80).


(* TODO: prove soundness for iSL *)

Definition sequents_equivalence (S T : list sequent) : Prop := ∀ W `(M : ValuatedFrame W R kle variable V) (w : W), 
  (∀ s, In s S -> forces_sequent w s) <->  (∀ t, In t T -> forces_sequent w t).

(* TODO: check confusion between R and kle *)
Definition bisimilar (p : variable) {W R V W' R' V'}
  `{M : ValuatedFrame W R kle variable V} (x : W) `{M' : ValuatedFrame W' R' kle' variable V'} (x' : W') :=
{ Z | Z x x' /\ ∀ w w', Z w w' ->
  (∀q, p ≠ q -> (V q w <-> V' q w' )) /\
  (∀ v, kle w v -> exists v', Z v v' /\ kle' w' v') /\
  (∀ v', kle' w' v' -> exists v, Z v v' /\ kle w v)
}. (* TODO: should Z preserve R as well?  YES *)

Lemma bisimilarity_spec p ψ `(M : ValuatedFrame W R kle variable V) w `(M' : ValuatedFrame W' R' kle' variable V') w': `(bisimilar p w w') ->
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
      (*
      destruct (HR' _ (strongness _ _ Hw'v')) as (v & HZv & Hwv).
      assert(Hb' : bisimilar p v v' ) by (exists Z; split; trivial).
      rewrite <- (IHψ v v'); try tauto. apply Hi. admit. *)
Admitted.

Require Import Coq.Program.Equality.

Lemma ISL_sound Γ ψ : (Provable Γ ψ) -> forall `(ISLFrame W R kle variable V), forall w, w ⊨s (Γ, ψ).
Proof.
intro H. dependent induction H;intros W R kle V F w; simpl; intro Hf.
- apply (Hf p). ms.
- apply (Hf ⊥). ms.
- split.
  + now apply IHProvable1.
  + now apply IHProvable2.
- destruct (Hf (φ ∧ ψ)); [ms|]. fold forces in *.
  apply IHProvable. intros φ0 Hφ0. apply env_in_add in Hφ0.
  destruct Hφ0 as [Hl|Hr]; [subst; auto|].
  apply env_in_add in Hr.
  destruct Hr as [Hl|Hr]; [subst; auto|].
  apply Hf. ms.
- left. apply IHProvable. intros. apply Hf. ms.
- right. apply IHProvable. intros. apply Hf. ms.
- destruct (Hf (φ ∨ ψ)); [ms| |]; fold forces in *.
  + apply IHProvable1. intros φ0 Hφ0. apply env_in_add in Hφ0.
      destruct Hφ0 as [Hl|Hr]; [subst; auto|]. apply Hf. ms.
  + apply IHProvable2. intros φ0 Hφ0. apply env_in_add in Hφ0.
      destruct Hφ0 as [Hl|Hr]; [subst; auto|]. apply Hf. ms.
- intros v Hv Hφ. apply IHProvable. intros φ0 Hφ0. apply env_in_add in Hφ0.
  destruct Hφ0 as [Hl|Hr]; [subst; trivial|].
  apply persistence with w. trivial. apply Hf. ms. 
- apply IHProvable. intros φ0 Hφ0. apply env_in_add in Hφ0.
  destruct Hφ0 as [Hl|Hr]; [subst|apply Hf; ms].
  apply (Hf (p → φ));[ms|reflexivity|]. apply (Hf p). ms.
- apply IHProvable. intros φ0 Hφ0. apply env_in_add in Hφ0.
  destruct Hφ0 as [Hl|Hr]; [subst|apply Hf; ms].
  simpl. intros v Hv Hφ1 v' Hv' Hφ2. apply (Hf (φ1 ∧ φ2 → φ3)).
  + ms.
  + now transitivity v.
  + fold forces in *. split; trivial. now apply persistence with v.
- apply IHProvable. intros φ0 Hφ0. apply env_in_add in Hφ0.
  destruct Hφ0 as [Hl|Hr]; [subst|].
  + simpl. intros v Hv Hφ2. apply (Hf (φ1 ∨ φ2 → φ3)); [ms|trivial|tauto].
  + apply env_in_add in Hr. destruct Hr as [Hl|Hr]; [subst; auto|apply Hf; ms].
      intros v Hv Hφ1. apply (Hf (φ1 ∨ φ2 → φ3)); [ms|trivial|tauto].
- apply IHProvable2. intros φ0 Hφ0. apply env_in_add in Hφ0.
  destruct Hφ0 as [Hl|Hr]; [subst|apply Hf; ms].
  apply (Hf ((φ1 → φ2) → φ3)). ms. reflexivity. apply IHProvable1.
  intros φ0 Hφ0. apply env_in_add in Hφ0.
  destruct Hφ0 as [Hl|Hr]; [subst|apply Hf; ms].
  intros v Hv Hφ2. apply (Hf ((φ1 → φ2) → φ3)). ms. trivial. fold forces.
  intros v' Hv' Hφ1. now apply persistence with v.
- apply IHProvable2. intros φ0 Hφ0. apply env_in_add in Hφ0.
  destruct Hφ0 as [Hl|Hr]; [subst|apply Hf; ms]. clear IHProvable2.
  apply (Hf (□ φ1 → φ2));[ms| reflexivity|fold forces].
  induction v as [v Hind] using (well_founded_induction convWf).
  intros Hv. apply IHProvable1. intros φ0 Hφ0.
  apply env_in_add in Hφ0. destruct Hφ0 as [Hl|Hr]; [subst|].
  + apply (Hf (□ φ1 → φ2));[ms| now apply strongness |fold forces].
      intros v' Hv'. apply Hind. trivial. now transitivity v.
  + apply env_in_add in Hr. destruct Hr as [Hl|Hr]; [subst|].
      * simpl. intros v' Hv'. apply Hind. trivial.  now transitivity v.
      * apply open_boxes_spec in Hr. destruct Hr as [[Hl Hbox] | Hr].
        -- apply persistence with w. apply strongness, Hv. apply Hf. ms.
        -- apply (Hf (□φ0)). ms.  trivial.
- induction w as [x Hind] using (well_founded_induction convWf).
  intros v HRv. apply IHProvable. intros φ0 Hφ0. apply env_in_add in Hφ0.
  destruct Hφ0 as [Hl|Hr]; [subst|].
  + simpl. intros v' HRv'. apply IHProvable. intros φ0 Hφ0.
       apply env_in_add in Hφ0. destruct Hφ0 as [Hl|Hr]; [subst|].
       * simpl. apply Hind.
        --  simpl. now apply transitive_frame with v.
        -- intros φ0 Hφ0. apply persistence with x.
          ++ transitivity v; now apply strongness.
          ++ now apply Hf.
       * apply open_boxes_spec in Hr. destruct Hr as [[Hl Hbox] | Hr].
          -- apply persistence with x; [transitivity v; now apply strongness|]. now apply Hf.
          -- apply Hf in Hr. apply Hr. now transitivity v.
  + apply open_boxes_spec in Hr. destruct Hr as [[Hl Hbox] | Hr].
      * apply persistence with x. apply strongness, HRv. now apply Hf.
      * apply Hf in Hr. now apply Hr.
Qed.

Local Instance empty_model: ISLFrame () (λ _ _ : (), False) (λ _, (_ : ()), True)
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
Admitted.

*)