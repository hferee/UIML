Require Import Coq.Classes.RelationClasses Coq.Program.Basics.

Require Import Formulas.


(* Source: A New Calculus for Intuitionistic Strong Löb Logic *)

Context `(PreOrder_kle : PreOrder W kle).

Infix "≤" := kle (at level 80).

(* for iSL *)
(* TODO: give names *)
Class IntuitionisticModalKripkeModel
  R (ℑ: variable -> W -> Prop)
   `(Transitive W R)
   `(Subrelation_R_kle: Subrelation R kle)
   `(Subrelation_R_kle_R: Subrelation (fun x y => exists z, x ≤ z /\ R z y) R)
   (I: variable -> W -> Prop) :=
   {
   (* doesn't work as a Subrelation typeclass? *)
   Subrelation_R_kle_R: forall x y z, x ≤ z -> R z y -> R x y;
   I_kle : (forall p w v, w ≤ v -> ℑ p w -> ℑ p v);
   R_wf : well_founded (flip R)
    }.

(* let's fix a Kripke model for now *)
Context `{M : IntuitionisticModalKripkeModel R ℑ}.

Reserved Infix "⊨" (at level 80).
Fixpoint forces (w : W) (φ : form) : Prop :=
match φ with
| Var p => ℑ p w
| Bot => False
| And φ ψ => w ⊨ φ /\ w ⊨ ψ
| Or φ ψ => w ⊨ φ \/ w ⊨ ψ
| Implies φ ψ => forall v, w ≤ v -> v ⊨ φ /\ v ⊨ ψ
| Box φ => forall v, R w v -> v ⊨ φ
end
where "w ⊨ φ" := (forces w φ).
(* Note that we this is usually denoted M, w ⊨ φ, i.e. with M explicit *)

Lemma persistence φ w v: w ≤ v -> w ⊨ φ -> v ⊨ φ.
Proof.
Proof.
revert w v. induction φ; intros w w' Hle Hw; simpl.
- apply I_kle with w; auto.
- tauto.
- destruct Hw. eauto.
- destruct Hw; eauto.
- intros z Hz. apply Hw. transitivity w'; trivial.
- intros z Hz. eapply Hw. apply Subrelation_R_kle_R with w'; trivial.
Qed.

