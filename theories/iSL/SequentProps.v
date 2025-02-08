Require Import ISL.Sequents.

(* Required for dependent induction. *)
Require Import Coq.Program.Equality.

(** * Admissible rules in G4ip sequent calculus

This file contains important properties of the sequent calculus G4ip, defined in
Sequents.v, namely the admissibility of various inversion rules, weakening and
contraction. We draw various consequences from this that are used extensively in
the proof of correctness of propositional quantifiers. The first part of this
file closely follows proof in the paper:

(Dyckhoff and Negri 2000). R. Dyckhoff and S. Negri, Admissibility of Structural
Rules for Contraction-Free Systems of Intuitionistic Logic, Journal of Symbolic
Logic (65):4.
*)

(** ** Weakening *)

Lemma open_boxes_add'
     {K : Kind} (Γ : @env K) (φ : @form K) : (⊗ (Γ • φ)) = (⊗ Γ • ⊙ φ).
Proof. apply open_boxes_add. Qed.
(*
Global Hint Rewrite open_boxes_add' : proof.
*)
(** We prove the admissibility of the weakening rule. *)

Theorem weakening {K : Kind} φ' Γ φ : Γ ⊢ φ -> Γ•φ' ⊢ φ.
Proof with (auto with proof).
intro H. revert φ'.  induction H; intro φ'; auto with proof; try (exch 0; auto with proof).
- constructor 4. exch 1; exch 0...
- constructor 7; exch 0...
- constructor 8; exch 0...
- exch 1; constructor 9; exch 1; exch 0...
- constructor 10; exch 0...
- constructor 11. exch 1; exch 0...
- constructor 12; exch 0...
- apply ImpBox; box_tac.
  + peapply (IHProvable1 (open_box φ')).
  + exch 0...
- apply BoxR. box_tac. exch 0...
Qed.

Global Hint Resolve weakening : proof.

Theorem generalised_weakeningL {K : Kind} (Γ Γ' : env) φ: Γ ⊢ φ -> Γ' ⊎ Γ ⊢ φ.
Proof.
intro Hp.
induction Γ' as [| x Γ' IHΓ'] using gmultiset_rec.
- peapply Hp.
- peapply (weakening x). exact IHΓ'. ms.
Qed.

Theorem generalised_weakeningR {K : Kind} (Γ Γ' : env) φ: Γ' ⊢ φ -> Γ' ⊎ Γ ⊢ φ.
Proof.
intro Hp.
induction Γ as [| x Γ IHΓ] using gmultiset_rec.
- peapply Hp.
- peapply (weakening x). exact IHΓ. ms.
Qed.

Global Hint Extern 5 (?a <= ?b) => simpl in *; lia : proof.

(** ** Inversion rules *)

(** We prove that the following rules are invertible: implication right, and
  left, or left, top left (i.e., the appliction of weakening for the formula
  top), the four implication left rules, the and right rule and the application of the or right rule with bottom. *)

Lemma ImpR_rev {K : Kind} Γ φ ψ :
  (Γ ⊢ (φ →  ψ))
    -> Γ•φ ⊢  ψ.
Proof with (auto with proof).
intro Hp. dependent induction Hp; auto with proof; try exch 0.
- constructor 4. exch 1; exch 0...
- constructor 7; exch 0...
- exch 1; constructor 9; exch 1; exch 0...
- constructor 10; exch 0...
- constructor 11. exch 1; exch 0...
- constructor 12; exch 0...
- constructor 13; box_tac...
  + exch 1; exch 0. apply weakening...
  + exch 0. auto with proof.
Qed.

Global Hint Resolve ImpR_rev : proof.

Theorem generalised_axiom {K : Kind} Γ φ : Γ • φ ⊢ φ.
Proof with (auto with proof).
remember (weight φ) as w.
assert(Hle : weight φ ≤ w) by lia.
clear Heqw. revert Γ φ Hle.
induction w; intros Γ φ Hle.
- assert (Hφ := weight_pos φ). lia.
- destruct φ; simpl in Hle...
  dependent destruction φ1.
  + constructor 8. exch 0...
  + auto with proof.
  + apply ImpR, AndL. exch 1; exch 0. apply ImpLAnd.
    exch 0. apply ImpR_rev. exch 0...
  + apply ImpR. exch 0. apply ImpLOr.
    exch 1; exch 0...
  + apply ImpR. exch 0...
  + apply ImpR. exch 0. apply ImpBox; box_tac...
  + apply BoxR; box_tac...
Qed.

Global Hint Resolve generalised_axiom : proof.

Local Ltac lazy_apply th:=
(erewrite proper_Provable;  [| |reflexivity]);  [eapply th|].

Lemma open_box_L {K : Kind} Γ φ ψ : Γ • φ ⊢ ψ -> Γ • ⊙ φ ⊢ ψ.
Proof.
intro Hp.
remember (Γ•φ) as Γ' eqn:HH.
assert (Heq: Γ ≡ Γ' ∖ {[ φ ]}) by ms.
assert(Hin : φ ∈ Γ')by ms.
rw Heq 1. clear Γ HH Heq. revert φ Hin.
dependent induction Hp generalizing Γ' Hp; intros φ0 Hin.
- case (decide (φ0 = Var p)).
  + intro; subst. simpl. auto with proof.
  + intro. forward. auto with proof.
- case (decide (φ0 = ⊥)).
  + intro; subst. simpl. auto with proof.
  + intro. forward. auto with proof.
- apply AndR; auto.
- case (decide (φ0 = (φ ∧ ψ))).
  + intro; subst. simpl. apply AndL. peapply Hp.
  + intro. forward. apply AndL. exch 0. do 2 backward.
    peapply (IHHp); trivial. ms.
- apply OrR1; auto.
- apply OrR2; auto.
- case (decide (φ0 = (φ ∨ ψ))).
  + intro; subst. simpl. apply OrL.
      * peapply Hp1.
      * peapply Hp2.
  + intro. forward. apply OrL.
      * backward. peapply IHHp1; trivial. ms.
      * backward. peapply IHHp2; trivial. ms.
- apply ImpR. backward. apply IHHp; trivial. ms.
- case (decide (φ0 = Var p)).
  + intro; subst; simpl. forward. apply ImpLVar. peapply Hp.
  + intro. case (decide (φ0 = (Var p → φ))).
      * intro; subst; simpl. peapply (ImpLVar Γ). exact Hp. ms.
      * intro. do 2 forward. exch 0. apply ImpLVar. exch 0. do 2 backward.
         apply IHHp; trivial. ms.
- case (decide (φ0 =  (φ1 ∧ φ2 → φ3))).
  + intro; subst; simpl. apply ImpLAnd. peapply Hp.
  + intro. forward. apply ImpLAnd. backward. apply IHHp; trivial. ms.
- case (decide (φ0 =  (φ1 ∨ φ2 → φ3))).
  + intro; subst; simpl. apply ImpLOr. peapply Hp.
  + intro. forward. apply ImpLOr. exch  0. do 2 backward. apply IHHp; trivial. ms.
- case (decide (φ0 =  ((φ1 → φ2) → φ3))).
  + intro; subst; simpl. apply ImpLImp. peapply Hp1. peapply Hp2.
  + intro. forward. apply ImpLImp.
      * backward. apply IHHp1; trivial. ms.
      * backward. apply IHHp2; trivial. ms.
- case (decide (φ0 =  (□ φ1 → φ2))).
  + intro; subst; simpl. apply ImpBox.
      * box_tac. lazy_apply Hp1. autorewrite with proof. ms.
      * peapply Hp2.
  + intro. forward.
      case (decide (open_box φ0 = □ φ1)).
      * intro Heq. repeat rewrite Heq. apply ImpBox; box_tac.
        -- exch 1; exch 0. apply generalised_axiom.
        -- backward. rewrite <- Heq. apply IHHp2; trivial. auto with *.
      * intro Hneq. case (decide (open_box φ0 = φ2)).
          -- intro Heq. subst φ2. apply ImpBox; box_tac.
              ++ (erewrite proper_Provable;  [| |reflexivity]);  [eapply (IHHp1 (⊙ φ0))|]. ms.
                 autorewrite with proof; [|ms]. repeat rewrite env_replace.
                     ** ms.
                     ** auto with proof.
                     ** apply env_in_add. right. auto with proof; ms.
              ++ box_tac. backward. apply IHHp2; trivial. auto with *.
          -- intro Hneq'. apply ImpBox; repeat box_tac.
            ++ exch 0. box_tac. assert((⊙ φ0) ∈ (⊗ Γ)) by (now apply In_open_boxes).
                    backward. backward. eapply IHHp1; trivial. ms.
            ++ backward. apply IHHp2; trivial. apply env_in_add. now right.
- case (decide (open_box φ0 = □ φ)).
  + intro Heq; rewrite Heq. apply generalised_axiom.
  + intro. backward. apply BoxR. box_tac.
      case (decide (open_box φ0 = open_box (open_box φ0))).
      * intro Heq. lazy_apply Hp. autorewrite with proof. rewrite <- Heq. ms. ms.
      * intro. assert( open_box φ0 ∈ open_boxes Γ) by (now apply In_open_boxes).
        lazy_apply (IHHp (open_box φ0)).
        -- ms.
        -- autorewrite with proof. repeat rewrite env_replace; ms. ms.
Qed.

Local Hint Resolve env_in_add : proof.

Lemma open_boxes_R {K : Kind} (Γ : env) φ ψ: (Γ • φ) ⊢ ψ → (⊗Γ) • φ ⊢ ψ.
Proof.
revert ψ.
induction Γ using gmultiset_rec; intro ψ.
- rewrite open_boxes_empty. trivial.
- intro HP. lazy_apply (open_box_L (⊗ Γ • φ) x ψ).
  + apply ImpR_rev, IHΓ, ImpR. peapply HP.
  + rewrite open_boxes_disj_union, open_boxes_singleton; ms.
Qed.

Lemma AndL_rev {K : Kind} Γ φ ψ θ: (Γ•φ ∧ ψ) ⊢ θ  → (Γ•φ•ψ) ⊢ θ.
Proof.
intro Hp.
remember (Γ•φ ∧ ψ) as Γ' eqn:HH.
assert (Heq: Γ ≡ Γ' ∖ {[ φ ∧ ψ ]}) by ms.
assert(Hin : (φ ∧ ψ) ∈ Γ')by ms.
rw Heq 2. clear Γ HH Heq. revert φ ψ Hin.
(* we massaged the goal so that the environment of the derivation on which we do
   the induction is not composite anymore *)
induction Hp; intros φ0 ψ0 Hin.
(* auto takes care of the right rules easily *)
- forward. auto with proof.
- forward. auto with proof.
- apply AndR; auto with proof.
(* the main case *)
- (* TODO: forward gets stuck there. *)
  case(decide ((φ ∧ ψ) = (φ0 ∧ ψ0))); intro Heq0.
  + dependent destruction Heq0; subst. peapply Hp.
  + forward. constructor 4. exch 0. backward. backward. apply IHHp. ms.
(* only left rules remain. Now it's all a matter of putting the right principal
   formula at the front, apply the rule; and put back the front formula at the back
   before applying the induction hypothesis *)
- apply OrR1. auto with proof.
- apply OrR2. auto with proof.
- forward. constructor 7; backward; [apply IHHp1 | apply IHHp2]; ms.
- constructor 8. backward. apply IHHp. ms.
- forward. forward. exch 0. constructor 9. exch 0. do 2 backward. apply IHHp. ms.
- forward. constructor 10. backward. apply IHHp. ms.
- forward. constructor 11. exch 0. do 2 backward. apply IHHp. ms.
- forward. constructor 12; backward.
  + apply IHHp1. ms.
  + apply IHHp2. ms.
- forward. constructor 13; repeat box_tac.
  + exch 0. box_tac.
      apply In_open_boxes in Hin0. backward. backward. apply open_box_L. exch 0. apply open_box_L. exch 0.
      apply IHHp1. ms.
  + backward. apply IHHp2. ms.
- constructor 14. repeat box_tac.
  exch 0. apply open_box_L.
  exch 1; exch 0. apply open_box_L.
  lazy_apply (IHHp φ0 ψ0).
  + apply env_in_add. right. apply In_open_boxes in Hin. auto with proof.
  + autorewrite with proof. simpl. rewrite <- env_replace. ms.
      apply In_open_boxes in Hin. auto with proof.
Qed.

Lemma OrL_rev {K : Kind} Γ φ ψ θ: (Γ•φ ∨ ψ) ⊢ θ  → (Γ•φ ⊢ θ) * (Γ•ψ ⊢ θ).
Proof.
intro Hp.
remember (Γ•φ ∨ ψ) as Γ' eqn:HH.
assert (Heq: Γ ≡ Γ' ∖ {[ φ ∨ ψ ]}) by ms.
assert(Hin : (φ ∨ ψ) ∈ Γ')by ms.
assert(Heq' : ((Γ' ∖ {[φ ∨ ψ]}•φ) ⊢ θ) * ((Γ' ∖ {[φ ∨ ψ]}•ψ) ⊢ θ));
[| split; rw Heq 1; tauto].
clear Γ HH Heq.
induction Hp.
- split; forward; auto with proof.
- split; forward; auto with proof.
- split; constructor 3; now (apply IHHp1 || apply IHHp2).
- split; forward; constructor 4; exch 0; do 2 backward; apply IHHp; ms.
- split; constructor 5; now apply IHHp.
- split; apply OrR2; now apply IHHp.
- case (decide ((φ0 ∨ ψ0) = (φ ∨ ψ))); intro Heq0.
  + dependent destruction Heq0; subst. split; [peapply Hp1| peapply Hp2].
  + split; forward; constructor 7; backward; (apply IHHp1||apply IHHp2); ms.
- split; constructor 8; backward; apply IHHp; ms.
- split; do 2 forward; exch 0; constructor 9; exch 0; do 2 backward; apply IHHp; ms.
- split; forward; constructor 10; backward; apply IHHp; ms.
- split; forward; constructor 11; exch 0; do 2 backward; apply IHHp; ms.
- split; forward; constructor 12; backward; (apply IHHp1 || apply IHHp2); ms.
- split; forward; assert(Hin' : (φ ∨ ψ) ∈ (⊗ Γ • □ φ1 • φ2))
  by (apply env_in_add; right; apply env_in_add; right; eauto with proof);
  assert((φ ∨ ψ) ∈ ⊗Γ) by eauto with proof;
  (constructor 13; repeat box_tac; exch 0;
    [do 2 backward; apply open_box_L; apply IHHp1|exch 0; backward; apply IHHp2];ms).
-  assert (Hin' : (φ ∨ ψ) ∈ (⊗ Γ • □ φ0)) by (apply env_in_add; right; eauto with proof).
    split; constructor 14; repeat box_tac; backward; apply open_box_L; now apply IHHp.
Qed.
(*
Lemma open_boxes_spec Γ φ : φ ∈ open_boxes Γ -> {φ ∈ Γ ∧ is_box φ = false} + {(□ φ) ∈ Γ}.
Admitted.
  Global Hint Resolve open_boxes_spec : proof.

*)
Lemma TopL_rev {K : Kind} Γ φ θ: Γ•(⊥ → φ) ⊢ θ -> Γ ⊢ θ.
Proof.
remember (Γ•(⊥ → φ)) as Γ' eqn:HH.
assert (Heq: Γ ≡ Γ' ∖ {[ ⊥ → φ ]}) by ms.
assert(Hin : (⊥ → φ) ∈ Γ')by ms. clear HH.
intro Hp. rw Heq 0. clear Γ Heq. induction Hp;
try forward.
- auto with proof.
- auto with proof.
- auto with proof.
- constructor 4. exch 0. do 2 backward. apply IHHp.  ms.
- auto with proof.
- auto with proof.
- constructor 7; backward; [apply IHHp1 | apply IHHp2];  ms.
- constructor 8. backward. apply IHHp. ms.
- forward. exch 0. constructor 9. exch 0. do 2 backward. apply IHHp. ms.
- constructor 10. backward. apply IHHp. ms.
- constructor 11. exch 0. do 2 backward. apply IHHp. ms.
- constructor 12; backward;  [apply IHHp1 | apply IHHp2];  ms.
- constructor 13; box_tac.
  + exch 0. do 2 backward.  apply IHHp1. ms.
  + backward. apply IHHp2. ms.
- constructor 14. box_tac.  backward.  apply IHHp. ms.
Qed.

Local Hint Immediate TopL_rev : proof.

Lemma ImpLVar_rev {K : Kind} Γ p φ ψ: (Γ•Var p•(p → φ)) ⊢ ψ  → (Γ•Var p•φ) ⊢ ψ.
Proof.
intro Hp.
remember (Γ•Var p•(p → φ)) as Γ' eqn:HH.
assert (Heq: (Γ•Var p) ≡ Γ' ∖ {[Var p → φ]}) by ms.
assert(Hin : (p → φ) ∈ Γ')by ms.
rw Heq 1. clear Γ HH Heq.
induction Hp.
- forward; auto with proof.
- forward; auto with proof.
- apply AndR; auto with proof.
- forward; apply AndL. exch 0. do 2 backward. apply IHHp. ms.
- apply OrR1. auto with proof.
- apply OrR2. auto with proof.
- forward; apply OrL; backward; apply IHHp1 || apply IHHp2; ms.
- apply ImpR. backward. apply IHHp. ms.
- case (decide ((Var p0 → φ0) = (Var p → φ))); intro Heq0.
  + dependent destruction Heq0; subst. peapply Hp.
  + do 2 forward. exch 0. apply ImpLVar. exch 0; do 2 backward. apply IHHp. ms.
- forward; apply ImpLAnd. backward. apply IHHp. ms.
- forward; apply ImpLOr. exch 0; do 2 backward. apply IHHp. ms.
- forward; apply ImpLImp; backward; (apply IHHp1 || apply IHHp2); ms.
- forward; apply ImpBox; repeat box_tac.
   +  exch 0; do 2 backward. apply open_box_L. apply IHHp1. ms.
   + backward. apply IHHp2. ms.
- apply BoxR. repeat box_tac. backward. apply open_box_L. apply IHHp. ms.
Qed.

(* inversion for ImpLImp is only partial *)
Lemma ImpLImp_prev {K : Kind} Γ φ1 φ2 φ3 ψ: (Γ•((φ1 → φ2) → φ3)) ⊢ ψ -> (Γ•φ3) ⊢ ψ.
Proof.
intro Hp.
remember (Γ •((φ1 → φ2) → φ3)) as Γ' eqn:HH.
assert (Heq: Γ ≡ Γ' ∖ {[ ((φ1 → φ2) → φ3) ]}) by ms.
assert(Hin :((φ1 → φ2) → φ3) ∈ Γ')by ms.
rw Heq 1. clear Γ HH Heq.
induction Hp.
- forward; auto with proof.
- forward; auto with proof.
- apply AndR; auto with proof.
- forward; apply AndL. exch 0; do 2 backward. apply IHHp. ms.
- apply OrR1. auto with proof.
- apply OrR2. auto with proof.
- forward; apply OrL; backward; [apply IHHp1 | apply IHHp2]; ms.
- apply ImpR. backward. apply IHHp. ms.
- do 2 forward. exch 0. apply ImpLVar. exch 0. do 2 backward. apply IHHp. ms.
- forward; apply ImpLAnd. backward. apply IHHp. ms.
- forward; apply ImpLOr. exch 0. do 2 backward. apply IHHp. ms.
- case (decide (((φ0 → φ4) → φ5) = ((φ1 → φ2) → φ3))); intro Heq0.
  + dependent destruction Heq0; subst. peapply Hp2.
  + forward. apply ImpLImp; backward; (apply IHHp1 || apply IHHp2); ms.
- forward; apply ImpBox; repeat box_tac.
  + exch 0; do 2 backward. apply open_box_L. apply IHHp1. ms.
  + backward. apply IHHp2. ms.
- apply BoxR. repeat box_tac. backward. apply open_box_L. apply IHHp. ms.
Qed.

(* inversion for ImpLbox is only partial too *)
Lemma ImpLBox_prev Γ φ1 φ2 ψ: (Γ•((□φ1) → φ2)) ⊢ ψ -> (Γ•φ2) ⊢ ψ.
Proof.
intro Hp.
remember (Γ •((□φ1) → φ2)) as Γ' eqn:HH.
assert (Heq: Γ ≡ Γ' ∖ {[ ((□φ1) → φ2) ]}) by ms.
assert(Hin :((□φ1) → φ2) ∈ Γ')by ms.
rw Heq 1. clear Γ HH Heq.
dependent induction Hp.
- forward; auto with proof.
- forward; auto with proof.
- apply AndR; auto with proof.
- forward; apply AndL. exch 0; do 2 backward. apply IHHp; trivial. ms.
- apply OrR1. auto with proof.
- apply OrR2. auto with proof.
- forward; apply OrL; backward; [apply IHHp1 | apply IHHp2]; ms.
- apply ImpR. backward. apply IHHp; trivial. ms.
- do 2 forward. exch 0. apply ImpLVar. exch 0. do 2 backward.
  apply IHHp; trivial. ms.
- forward; apply ImpLAnd. backward. apply IHHp; trivial. ms.
- forward; apply ImpLOr. exch 0. do 2 backward. apply IHHp; trivial. ms.
- forward; apply ImpLImp; backward.
  + apply IHHp1; trivial. ms.
  + apply IHHp2; trivial. ms.
- case (decide((□φ0 → φ3) = (□φ1 → φ2))).
  + intro Heq; dependent destruction Heq; subst. peapply Hp2.
  + intro Hneq. forward. apply ImpBox; repeat box_tac.
     * exch 0; do 2 backward. apply open_box_L; apply IHHp1; trivial. ms.
     * backward. apply IHHp2; trivial. ms.
- apply BoxR. repeat box_tac. backward. apply open_box_L. apply IHHp; trivial. ms.
Qed.

Lemma ImpLOr_rev {K : Kind} Γ φ1 φ2 φ3 ψ:
  Γ•((φ1 ∨ φ2) → φ3) ⊢ ψ -> Γ•(φ1 → φ3)•(φ2 → φ3) ⊢ ψ.
Proof.
intro Hp.
remember (Γ •((φ1 ∨ φ2) → φ3)) as Γ' eqn:HH.
assert (Heq: Γ ≡ Γ' ∖ {[ ((φ1 ∨ φ2) → φ3) ]}) by ms.
assert(Hin :((φ1 ∨ φ2) → φ3) ∈ Γ')by ms.
rw Heq 2. clear Γ HH Heq.
induction Hp.
- forward; auto with proof.
- forward; auto with proof.
- apply AndR; auto with proof.
- forward; constructor 4. exch 0; do 2 backward. apply IHHp. ms.
- apply OrR1. auto with proof.
- apply OrR2. auto with proof.
- forward; constructor 7; backward; [apply IHHp1 | apply IHHp2]; ms.
- constructor 8. backward. apply IHHp. ms.
- do 2 forward. exch 0. constructor 9. exch 0. do 2 backward. apply IHHp. ms.
- forward; constructor 10. backward. apply IHHp. ms.
- case (decide (((φ0 ∨ φ4) → φ5) = ((φ1 ∨ φ2) → φ3))); intro Heq0.
  + dependent destruction Heq0; subst. peapply Hp.
  + forward. constructor 11; exch 0; do 2 backward; apply IHHp; ms.
- forward; constructor 12; backward; (apply IHHp1 || apply IHHp2); ms.
- forward; apply ImpBox; repeat box_tac.
  + exch 0; do 2 backward. apply IHHp1. ms.
  + backward. apply IHHp2. ms.
- apply BoxR. repeat box_tac. backward. apply IHHp. ms.
Qed.

Lemma ImpLAnd_rev {K : Kind} Γ φ1 φ2 φ3 ψ: (Γ•(φ1 ∧ φ2 → φ3)) ⊢ ψ ->  (Γ•(φ1 → φ2 → φ3)) ⊢ ψ .
Proof.
intro Hp.
remember (Γ •((φ1 ∧ φ2) → φ3)) as Γ' eqn:HH.
assert (Heq: Γ ≡ Γ' ∖ {[ ((φ1 ∧ φ2) → φ3) ]}) by ms.
assert(Hin :((φ1 ∧ φ2) → φ3) ∈ Γ')by ms.
rw Heq 1. clear Γ HH Heq.
induction Hp.
- forward; auto with proof.
- forward; auto with proof.
- apply AndR; auto with proof.
- forward; constructor 4. exch 0; do 2 backward. apply IHHp. ms.
- apply OrR1. auto with proof.
- apply OrR2. auto with proof.
- forward; constructor 7; backward; [apply IHHp1 | apply IHHp2]; ms.
- constructor 8. backward. apply IHHp. ms.
- do 2 forward. exch 0. constructor 9. exch 0. do 2 backward. apply IHHp. ms.
- case (decide (((φ0 ∧ φ4) → φ5) = ((φ1 ∧ φ2) → φ3))); intro Heq0.
  + dependent destruction Heq0; subst. peapply Hp.
  + forward. constructor 10. backward. apply IHHp. ms.
- forward; constructor 11; exch 0; do 2 backward; apply IHHp; ms.
- forward; constructor 12; backward; (apply IHHp1 || apply IHHp2); ms.
- forward; apply ImpBox; repeat box_tac.
  + exch 0; do 2 backward. apply IHHp1. ms.
  + backward. apply IHHp2. ms.
- apply BoxR. repeat box_tac. backward. apply IHHp. ms.
Qed.

Global Hint Resolve AndL_rev : proof.
Global Hint Resolve OrL_rev : proof.
Global Hint Resolve ImpLVar_rev : proof.
Global Hint Resolve ImpLOr_rev : proof.
Global Hint Resolve ImpLAnd_rev : proof.
Global Hint Resolve ImpLBox_prev : proof.


Lemma exfalso {K : Kind} Γ φ: Γ ⊢ ⊥ -> Γ ⊢ φ.
Proof.
intro Hp. dependent induction Hp; try tauto; auto with proof; tauto.
Qed.

Global Hint Immediate exfalso : proof.

Lemma AndR_rev {K : Kind} {Γ φ1 φ2} : Γ ⊢ φ1 ∧ φ2 -> (Γ ⊢ φ1) * (Γ ⊢ φ2).
Proof.
  intro Hp. dependent induction Hp generalizing φ1 φ2 Hp;
  try specialize (IHHp _ _ eq_refl);
  try specialize (IHHp1 _ _ eq_refl);
  try specialize (IHHp2 _ _ eq_refl);
  intuition;
  auto with proof.
Qed.


(** A general inversion rule for disjunction is not admissible. However, inversion holds if one of the formulas is ⊥. *)

Lemma OrR1Bot_rev {K : Kind} Γ φ :  Γ ⊢ φ ∨ ⊥ -> Γ ⊢ φ.
Proof. intro Hd.
 dependent induction Hd generalizing φ; auto using exfalso with proof. Qed.

Lemma OrR2Bot_rev {K : Kind} Γ φ :  Γ ⊢ ⊥ ∨ φ -> Γ ⊢ φ.
Proof. intro Hd. dependent induction Hd; auto using exfalso with proof. Qed.


(** We prove Lemma 4.1 of (Dyckhoff & Negri 2000). This lemma shows that a
    weaker version of the ImpL rule of Gentzen's original calculus LJ is still
    admissible in G4ip. The proof is simple, but requires the inversion lemmas
    proved above.
  *)

Lemma weak_ImpL {K : Kind} Γ φ ψ θ :Γ ⊢ φ -> Γ•ψ ⊢ θ -> Γ•(φ → ψ) ⊢ θ.
Proof with (auto with proof).
intro Hp. revert ψ θ. induction Hp; intros ψ0 θ0 Hp'.
- apply ImpLVar, Hp'.
- auto with proof.
- auto with proof.
- exch 0; constructor 4; exch 1; exch 0...
- auto with proof.
- apply ImpLOr. exch 0...
- exch 0; constructor 7; exch 0.
  + apply IHHp1. exch 0. eapply fst, OrL_rev. exch 0. exact Hp'.
  + apply IHHp2. exch 0. eapply snd, OrL_rev. exch 0. exact Hp'.
- auto with proof.
- exch 0; exch 1. constructor 9. exch 1; exch 0...
- exch 0. apply ImpLAnd. exch 0...
- exch 0. apply ImpLOr. exch 1; exch 0...
- exch 0. apply ImpLImp; exch 0. auto with proof. apply IHHp2. exch 0.
  eapply ImpLImp_prev. exch 0. eassumption.
- exch 0. apply ImpBox; box_tac.
  + exch 1; exch 0...
  + exch 0. apply IHHp2. exch 0. apply ImpLBox_prev with φ1. exch 0. exact Hp'.
- auto with proof.
Qed.

Global Hint Resolve weak_ImpL : proof.

(** ** Contraction

 The aim of this section is to prove that the contraction rule is admissible in
 G4ip. *)

(** An auxiliary definition of **height** of a proof, measured along the leftmost branch. *)
Fixpoint height {K : Kind} {Γ φ} (Hp : Γ ⊢ φ) := match Hp with
| Atom _ _ => 1
| ExFalso _ _ => 1
| AndR Γ φ ψ H1 H2 => 1 + height H1 + height H2
| AndL Γ φ ψ θ H => 1 + height H
| OrR1 Γ φ ψ H => 1 + height H
| OrR2 Γ φ ψ H => 1 + height H
| OrL Γ φ ψ θ H1 H2 => 1 + height H1 + height H2
| ImpR Γ φ ψ H => 1 + height H
| ImpLVar Γ p φ ψ H => 1 + height H
| ImpLAnd Γ φ1 φ2 φ3 ψ H => 1 + height H
| ImpLOr Γ φ1 φ2 φ3 ψ H => 1 + height H
| ImpLImp Γ φ1 φ2 φ3 ψ H1 H2 => 1 + height H1 + height H2
| ImpBox Γ φ1 φ2 ψ H1 H2 => 1 + height H1 + height H2
| BoxR Γ φ H => 1 + height H
end.

Lemma height_0 {K : Kind} {Γ φ} (Hp : Γ ⊢ φ) : height Hp <> 0.
Proof. destruct Hp; simpl; lia. Qed.

(** Lemma 4.2 in (Dyckhoff & Negri 2000), showing that a "duplication" in the context of the implication-case of the implication-left rule is admissible. *)

Lemma ImpLImp_dup {K : Kind} Γ φ1 φ2 φ3 θ:
  Γ•((φ1 → φ2) → φ3) ⊢ θ ->
    Γ•φ1 •(φ2 → φ3) •(φ2 → φ3) ⊢ θ.
Proof.
intro Hp.
remember (Γ•((φ1 → φ2) → φ3)) as Γ0 eqn:Heq0.
assert(HeqΓ : Γ ≡ Γ0 ∖ {[((φ1 → φ2) → φ3)]}) by ms.
rw HeqΓ 3.
assert(Hin : ((φ1 → φ2) → φ3) ∈ Γ0) by (subst Γ0; ms).
clear Γ HeqΓ Heq0.
(* by induction on the height of the derivation *)
remember (height Hp) as h.
assert(Hleh : height Hp ≤ h) by lia. clear Heqh.
revert Γ0 θ Hp Hleh Hin. induction h as [|h]; intros Γ θ Hp Hleh Hin;
[pose (height_0 Hp); lia|].
destruct Hp; simpl in Hleh.
- forward. auto with proof.
- forward. auto with proof.
- apply AndR.
  + apply IHh with Hp1. lia. ms.
  + apply IHh with Hp2. lia. ms.
- forward. apply AndL. exch 0. do 2 backward. apply IHh with Hp. lia. ms.
- apply OrR1. apply IHh with Hp. lia. ms.
- apply OrR2. apply IHh with Hp. lia. ms.
- forward. apply OrL; backward.
  + apply IHh with Hp1. lia. ms.
  + apply IHh with Hp2. lia. ms.
- apply ImpR. backward. apply IHh with Hp. lia. ms.
- do 2 forward. exch 0. apply ImpLVar. exch 0. do 2 backward.
  apply IHh with Hp. lia. ms.
- forward. apply ImpLAnd. backward. apply IHh with Hp. lia. ms.
- forward. apply ImpLOr. exch 0. do 2 backward. apply IHh with Hp. lia. ms.
- case (decide (((φ0 → φ4) → φ5) = ((φ1 → φ2) → φ3))); intro Heq.
  + dependent destruction Heq; subst.
    apply weak_ImpL.
    * exch 0. apply ImpR_rev. peapply Hp1.
    * do 2 (exch 0; apply weakening). peapply Hp2.
  + forward. apply ImpLImp; backward.
    * apply IHh with Hp1. lia. ms.
    * apply IHh with Hp2. lia. ms.
- forward. apply ImpBox; repeat box_tac.
  + exch 0. do 2 backward.
      exch 1; exch 0. apply open_box_L; exch 0; exch 1.
      apply IHh with Hp1. lia. ms.
  + backward. apply IHh with Hp2. lia. ms.
- apply BoxR. repeat box_tac. backward.
  exch 1; exch 0; apply open_box_L; exch 0; exch 1.
  apply IHh with Hp. lia. ms.
Qed.

Lemma ImpBox_dup Γ φ1 φ2 θ:
  Γ•(□φ1 → φ2)  ⊢ θ ->
    Γ • □ φ1 • □ φ1 • φ2 ⊢ θ.
Proof.
intro Hp.
remember (Γ• (□ φ1 → φ2)) as Γ0 eqn:Heq0.
assert(HeqΓ : Γ ≡ Γ0 ∖ {[(□ φ1 → φ2)]}) by ms.
rw HeqΓ 3.
assert(Hin : (□ φ1 → φ2) ∈ Γ0) by (subst Γ0; ms).
clear Γ HeqΓ Heq0.
(* by induction on the height of the derivation *)
remember (height Hp) as h.
assert(Hleh : height Hp ≤ h) by lia. clear Heqh.
revert Γ0 θ Hp Hleh Hin. induction h as [|h]; intros Γ θ Hp Hleh Hin;
[pose (height_0 Hp); lia|].
dependent destruction Hp; simpl in Hleh.
- forward. auto with proof.
- forward. auto with proof.
- apply AndR.
  + apply IHh with Hp1. lia. ms.
  + apply IHh with Hp2. lia. ms.
- forward. apply AndL. exch 0. do 2 backward. apply IHh with Hp. lia. ms.
- apply OrR1. apply IHh with Hp. lia. ms.
- apply OrR2. apply IHh with Hp. lia. ms.
- forward. apply OrL; backward.
  + apply IHh with Hp1. lia. ms.
  + apply IHh with Hp2. lia. ms.
- apply ImpR. backward. apply IHh with Hp. lia. ms.
- do 2 forward. exch 0. apply ImpLVar. exch 0. do 2 backward.
  apply IHh with Hp. lia. ms.
- forward. apply ImpLAnd. backward. apply IHh with Hp. lia. ms.
- forward. apply ImpLOr. exch 0. do 2 backward. apply IHh with Hp. lia. ms.
- forward. apply ImpLImp.
  + backward. apply IHh with Hp1. lia. ms.
  + backward. apply IHh with Hp2. lia. ms.
- case (decide ((□ φ0 → φ3) = □ φ1 → φ2)); intro Heq.
  + dependent destruction Heq; subst.
      exch 0. apply weakening. exch 0. apply weakening. peapply Hp2.
  + forward. apply ImpBox; repeat box_tac.
      * exch 0. do 2 backward.
         replace (φ1) with (⊙ (□ φ1)) by trivial.
         apply open_box_L; exch 0. apply open_box_L; exch 1; exch 0. apply open_box_L.
         exch 1; exch 0. simpl.
         apply IHh with Hp1. lia. ms.
      * backward. apply IHh with Hp2. lia. ms.
- apply BoxR. repeat box_tac. backward.
   replace (φ1) with (⊙ (□ φ1)) by trivial.
   apply open_box_L; exch 0. apply open_box_L; exch 1; exch 0. apply open_box_L.
   exch 1; exch 0. simpl.
  apply IHh with Hp. lia. ms.
Qed.

(* technical lemma for contraction *)
Local Lemma p_contr {K : Kind} Γ φ θ:
  (Γ•φ•φ) ∖ {[φ]} ⊢ θ ->
  ((Γ•φ) ⊢ θ).
Proof. intros * Hd; peapply Hd. Qed.

Lemma is_box_weight_open_box {K : Kind} φ : is_box φ = true -> weight (⊙ φ) = weight φ -1.
Proof. dependent destruction φ; simpl; lia. Qed.

Lemma weight_open_box {K : Kind} φ : weight (⊙ φ) ≤ weight φ.
Proof. dependent destruction φ; simpl; lia. Qed.


(** Admissibility of contraction in G4ip. *)
Lemma contraction {K : Kind} Γ ψ θ : Γ • ψ • ψ ⊢ θ -> Γ • ψ ⊢ θ.
Proof.
remember (Γ•ψ•ψ) as Γ0 eqn:Heq0.
assert(HeqΓ : (Γ•ψ) ≡ Γ0 ∖ {[ψ]}) by ms.
intro Hp. rw HeqΓ 0.
assert(Hin : ψ ∈ Γ0) by (subst Γ0; ms).
assert(Hin' : ψ ∈ Γ0 ∖ {[ψ]}) by(rewrite <- HeqΓ; ms).
clear Γ HeqΓ Heq0. revert Hp.
(* by induction on the weight of ψ *)
remember (weight ψ) as w.
assert(Hle : weight ψ ≤ w) by lia.
clear Heqw. revert Γ0 ψ θ Hle Hin Hin'.
induction w; intros Γ ψ θ Hle Hin Hin' Hp; [destruct ψ; simpl in Hle; lia|].
(* by induction on the height of the premise *)
remember (height Hp) as h.
assert(Hleh : height Hp ≤ h) by lia. clear Heqh.
revert Γ θ Hp Hleh Hin Hin'. revert ψ Hle; induction h as [|h]; intros ψ Hle Γ θ Hp Hleh Hin Hin';
[pose (height_0 Hp); lia|].
destruct Hp; simpl in Hleh, Hle.
- case(decide (ψ = Var p)).
  + intro; subst. exhibit Hin' 0. apply Atom.
  + intro Hneq. forward. apply Atom.
- case(decide (ψ = ⊥)).
  + intro; subst. exhibit Hin' 0. apply ExFalso.
  + intro. forward. apply ExFalso.
- apply AndR.
  + apply (IHh ψ Hle) with Hp1. lia. ms. ms.
  + apply (IHh ψ Hle) with Hp2. lia. ms. ms.
- case (decide (ψ = (φ ∧ ψ0))); intro Heq.
  + subst. exhibit Hin' 0. apply AndL.
    apply p_contr. simpl in Hle. apply IHw. lia. ms. rewrite union_difference_R; ms.
    exch 1. exch 0. apply p_contr. apply IHw. lia. ms. rewrite union_difference_R; ms.
    exch 1. exch 0. apply AndL_rev. exch 0. exch 1. lazy_apply Hp.
    rewrite <- (difference_singleton _ _ Hin'). ms.
  + rewrite union_difference_L in Hin' by ms.
    forward. apply AndL. exch 0. do 2 backward. apply (IHh ψ Hle) with Hp. lia. ms. ms.
- apply OrR1. apply (IHh ψ Hle) with Hp. lia. ms. ms.
- apply OrR2. apply (IHh ψ Hle) with Hp. lia. ms. ms.
- case (decide (ψ = (φ ∨ ψ0))); intro Heq.
  + subst. exhibit Hin' 0.
    apply OrL.
    * apply p_contr. simpl in Hle. apply IHw. lia. ms. rewrite union_difference_R; ms.
      refine (fst (OrL_rev _ φ ψ0 _ _)). exch 0. lazy_apply Hp1.
      rewrite <- env_replace; ms.
    * apply p_contr. simpl in Hle. apply IHw. lia. ms. rewrite union_difference_R; ms.
      refine (snd (OrL_rev _ φ ψ0 _ _)). exch 0. lazy_apply Hp2.
      rewrite <- env_replace; ms.
  + rewrite union_difference_L in Hin' by ms.
    forward. apply OrL; backward.
    * apply (IHh ψ Hle) with Hp1. lia. ms. ms.
    * apply (IHh ψ Hle) with Hp2. lia. ms. ms.
- apply ImpR. backward. apply (IHh ψ Hle) with Hp. lia. ms. ms.
- case (decide (ψ = (p → φ))); intro Heq.
  + subst. exhibit Hin' 0. rewrite union_difference_R in Hin' by ms.
    assert(Hcut : (((Γ•Var p) ∖ {[Var p → φ]}•(Var p → φ)) ⊢ ψ0)); [|peapply Hcut].
    forward. exch 0. apply ImpLVar, p_contr.
    apply IHw. simpl in Hle; lia. ms.  rewrite union_difference_L; ms.
    exch 1. apply ImpLVar_rev. exch 0; exch 1. lazy_apply Hp.
    rewrite <- env_replace; ms.
  + rewrite union_difference_L in Hin' by ms.
      forward. case (decide (ψ = Var p)).
      * intro; subst. forward. exch 0. apply ImpLVar. exch 0.
         do 2 backward. apply (IHh (Var p) Hle) with Hp. lia. ms. ms.
      * intro. forward. exch 0. apply ImpLVar; exch 0; do 2 backward.
         apply (IHh ψ Hle) with Hp. lia. ms. ms.
- case (decide (ψ = (φ1 ∧ φ2 → φ3))); intro Heq.
  + subst. exhibit Hin' 0. rewrite union_difference_R in Hin' by ms.
    apply ImpLAnd. apply p_contr.
    apply IHw. simpl in *; lia. ms.  rewrite union_difference_L; ms.
    apply ImpLAnd_rev. exch 0. lazy_apply Hp.
    rewrite <- env_replace; ms.
  + rewrite union_difference_L in Hin' by ms.
    forward. apply ImpLAnd. backward. apply (IHh ψ Hle) with Hp. lia. ms. ms.
- case (decide (ψ = (φ1 ∨ φ2 → φ3))); intro Heq.
  + subst. exhibit Hin' 0. rewrite union_difference_R in Hin' by ms.
    apply ImpLOr. apply p_contr.
    apply IHw. simpl in *; lia. ms. rewrite union_difference_L; ms.
    exch 1; exch 0. apply p_contr.
    apply IHw. simpl in *. lia. ms. rewrite union_difference_L; ms.
    exch 1; exch 0. apply ImpLOr_rev. exch 0. exch 1. lazy_apply Hp.
    rewrite <- env_replace; ms.
  + rewrite union_difference_L in Hin' by ms.
    forward. apply ImpLOr. exch 0. do 2 backward. apply (IHh ψ Hle) with Hp. lia. ms. ms.
- case (decide (ψ = ((φ1 → φ2) → φ3))); intro Heq.
  + subst. exhibit Hin' 0. rewrite union_difference_R in Hin' by ms.
    apply ImpLImp.
    * apply ImpR.
      do 3 (exch 0; apply p_contr; apply IHw; [simpl in *; lia|ms|rewrite union_difference_L; ms|exch 1]).
      exch 1; apply ImpLImp_dup. (* key lemma *)
      exch 0; exch 1. apply ImpR_rev.
      lazy_apply Hp1. rewrite <- env_replace; ms.
    * apply p_contr; apply IHw; [simpl in *; lia|ms|rewrite union_difference_L; ms|].
      apply (ImpLImp_prev _ φ1 φ2 φ3). exch 0.
      peapply Hp2. rewrite <- env_replace; ms.
  + rewrite union_difference_L in Hin' by ms.
    forward. apply ImpLImp; backward.
    * apply (IHh ψ Hle) with Hp1. lia. ms. ms.
    * apply (IHh ψ Hle) with Hp2. lia. ms. ms.
-  case (decide (ψ = (□ φ1 → φ2))); intro Heq.
  + subst. exhibit Hin' 0.
    apply ImpBox.
    * assert (Hr := open_boxes_remove _ _ Hin'). simpl in Hr. box_tac. symmetry in Hr. rw Hr 2.
        clear Hr.
        do 3 (exch 0; apply p_contr; apply IHw; [simpl in *; lia|ms|rewrite union_difference_L; ms|exch 1]).
       exch 0.
       assert(Heq : (⊗ (Γ • (□ φ1 → φ2)) ∖ {[□ φ1 → φ2]} ∖ {[□ φ1 → φ2]}) ≡ (⊗ (Γ∖ {[□ φ1 → φ2]})))
       by (autorewrite with proof; simpl; ms).
       rw Heq 5. clear Heq.
       apply ImpBox_dup. exch 0; exch 1. lazy_apply Hp1. rewrite open_boxes_remove; [|ms]. simpl.
       rewrite <- difference_singleton. ms. apply open_boxes_spec'.  left. simpl; split; trivial. ms.
      * apply p_contr; apply IHw; [simpl in *; lia|ms|rewrite union_difference_L; ms|].
         apply (ImpLBox_prev _ φ1 φ2). exch 0.
         lazy_apply Hp2. rewrite <- env_replace; ms.
  + rewrite union_difference_L in Hin' by ms.
      assert(Hinψ : ψ ∈ (Γ ∖ {[ψ]})) by ms. apply In_open_boxes in Hinψ.
      forward. apply ImpBox. box_tac. exch 0; do 2 backward.
      * rewrite open_boxes_remove in Hinψ by trivial.
         case_eq (is_box ψ); intro Hψ.
       -- apply is_box_weight_open_box in Hψ.
          assert (Hle' : weight(⊙ψ) ≤ S w) by lia.
          apply (IHh (⊙ ψ) Hle') with  Hp1. lia. ms. ms.
      -- apply is_not_box_open_box in Hψ. rewrite Hψ. apply IHh with Hp1.
          trivial. lia. rewrite <- Hψ. ms. trivial. rewrite <- Hψ. ms.
      * backward. apply (IHh ψ Hle) with Hp2. lia. ms. ms.
-  assert(Hinψ : ψ ∈ (Γ ∖ {[ψ]})) by ms. apply In_open_boxes in Hinψ.
   rewrite open_boxes_remove in Hinψ by trivial.
  apply BoxR. box_tac. backward. apply IHh with Hp.
    etransitivity. apply weight_open_box. trivial.
    lia.
    ms.
    ms.
Qed.

Global Hint Resolve contraction : proof.

Theorem generalised_contraction {K : Kind} (Γ Γ' : env) φ:
  Γ' ⊎ Γ' ⊎ Γ ⊢ φ -> Γ' ⊎ Γ ⊢ φ.
Proof.
revert Γ.
induction Γ' as [| x Γ' IHΓ'] using gmultiset_rec; intros Γ Hp.
- peapply Hp.
- peapply (contraction (Γ' ⊎ Γ) x). peapply (IHΓ' (Γ•x•x)). peapply Hp.
Qed.

(** ** Admissibility of LJ's implication left rule *)

(** We show that the general implication left rule of LJ is admissible in G4ip.
  This is Proposition 5.2 in (Dyckhoff Negri 2000). *)

Lemma ImpL {K : Kind} Γ φ ψ θ: Γ•(φ → ψ) ⊢ φ -> Γ•ψ  ⊢ θ -> Γ•(φ → ψ) ⊢ θ.
Proof. intros H1 H2. apply contraction, weak_ImpL; auto with proof. Qed.


(* Lemma 5.3 (Dyckhoff Negri 2000) shows that an implication on the left may be
   weakened. *)

Lemma imp_cut {K : Kind} φ Γ ψ θ: Γ•(φ → ψ) ⊢ θ -> Γ•ψ ⊢ θ.
Proof.
intro Hp.
remember (Γ•(φ → ψ)) as Γ0 eqn:HH.
assert (Heq: Γ ≡ Γ0 ∖ {[(φ → ψ)]}) by ms.
assert(Hin : (φ → ψ) ∈ Γ0) by ms. clear HH.
rw Heq 1. clear Heq Γ.
remember (weight φ) as w.
assert(Hle : weight φ ≤ w) by lia.
clear Heqw. revert Γ0 φ ψ θ Hle Hin Hp.
induction w; intros  Γ φ ψ θ Hle Hin Hp;
 [destruct φ; simpl in Hle; lia|].
induction Hp.
- forward. auto with proof.
- forward. auto with proof.
-apply AndR; intuition.
- forward; apply AndL. exch 0. do 2 backward. apply IHHp; trivial. ms.
- apply OrR1; intuition.
- apply OrR2; intuition.
- forward. apply OrL; backward; [apply IHHp1 | apply IHHp2]; ms.
- apply ImpR. backward. apply IHHp; trivial. ms.
- case (decide ((p → φ0) = (φ → ψ))); intro Heq0.
  + dependent destruction Heq0; subst. peapply Hp.
  + do 2 forward. exch 0. apply ImpLVar. exch 0. do 2 backward. apply IHHp; ms.
- case (decide ((φ1 ∧ φ2 → φ3) = (φ → ψ))); intro Heq0.
  + dependent destruction Heq0; subst.
    assert(Heq1 : ((Γ•(φ1 ∧ φ2 → ψ)) ∖ {[φ1 ∧ φ2 → ψ]}) ≡ Γ) by ms;
    rw Heq1 1; clear Heq1. simpl in Hle.
    peapply (IHw (Γ•(φ2 → ψ)) φ2 ψ ψ0); [lia|ms|].
    peapply (IHw (Γ•(φ1 → φ2 → ψ)) φ1 (φ2 → ψ) ψ0); [lia|ms|trivial].
  + forward. apply ImpLAnd. backward. apply IHHp; trivial. ms.
- case (decide ((φ1 ∨ φ2 → φ3) = (φ → ψ))); intro Heq0.
  + dependent destruction Heq0.
    apply contraction. simpl in Hle.
    peapply (IHw (Γ•ψ•(φ1 → ψ)) φ1 ψ); [lia|ms|].
    exch 0.
    peapply (IHw (Γ•(φ1 → ψ)•(φ2 → ψ)) φ2 ψ); trivial; [lia|ms].
  + forward. apply ImpLOr; exch 0; do 2 backward; apply IHHp; ms.
- case (decide (((φ1 → φ2) → φ3) = (φ → ψ))); intro Heq0.
  + dependent destruction Heq0. peapply Hp2.
  + forward. apply ImpLImp; backward; (apply IHHp1 || apply IHHp2); ms.
- case (decide((□φ1 → φ2) = (φ → ψ))).
  + intro Heq. dependent destruction Heq. peapply Hp2.
  + intro Hneq. forward. apply ImpBox; repeat box_tac.
      * exch 0. do 2 backward. apply open_box_L. apply IHHp1; trivial. ms.
      * backward. apply IHHp2; trivial. ms.
- apply BoxR.  repeat box_tac. backward. apply open_box_L, IHHp; trivial.
  apply env_in_add. right. auto with proof.
Qed.

Global Hint Resolve imp_cut : proof.

Lemma open_boxes_case Δ : {φ | (□ φ) ∈ Δ} + {Δ ≡ ⊗Δ}.
Proof.
unfold open_boxes.
induction Δ as [|ψ Δ IH] using gmultiset_rec.
- right. ms.
- case_eq(is_box ψ); intro Hbox.
  + left. exists (⊙ψ).
    dependent destruction ψ; try discriminate Hbox. ms.
  + destruct IH as [[φ Hφ]| Heq].
     * left. exists φ. ms.
     * right. symmetry. etransitivity.
        -- apply env_equiv_eq, list_to_set_disj_perm, Permutation_map.
            apply gmultiset_elements_disj_union.
        -- rewrite map_app, list_to_set_disj_app. rewrite <- Heq. apply env_equiv_eq.
            f_equal.
            unfold elements. apply is_not_box_open_box in Hbox.  rewrite <- Hbox at 2.
            transitivity (list_to_set_disj (map open_box (id [ψ])) : @env Modal).
            ++ apply list_to_set_disj_perm, Permutation_map.
                    apply Permutation_refl', gmultiset_elements_singleton.
            ++ simpl. ms.
Qed.

Lemma OrR_idemp {K : Kind} Γ ψ : Γ ⊢ ψ ∨ ψ -> Γ ⊢ ψ.
Proof. intro Hp. dependent induction Hp; auto with proof. Qed.


Lemma strongness φ : ∅ •  φ ⊢ □ φ.
Proof.
apply BoxR. box_tac. apply weakening, open_box_L, generalised_axiom.
Qed.

(**
  - [var_not_tautology]: A variable cannot be a tautology.
  - [bot_not_tautology]: ⊥ is not a tautology.
  - [box_var_not_tautology]: A boxed variable cannot be a tautology.
  - [box_bot_not_tautology]: A boxed ⊥ cannot be a tautology.
*)

Lemma bot_not_tautology {K : Kind} : (∅ ⊢ ⊥) -> False.
Proof.
intro Hf. dependent destruction Hf; simpl in *;
match goal with x : _ ⊎ {[+?φ+]} = _ |- _ =>
exfalso; eapply (gmultiset_elem_of_empty φ); setoid_rewrite <- x; ms end.
Qed.

Lemma var_not_tautology {K : Kind} v: (∅ ⊢ Var v) -> False.
Proof.
intro Hp.
remember ∅ as Γ.
dependent induction Hp;
match goal with | Heq : (_ • ?f%stdpp) = _ |- _ => symmetry in Heq;
  pose(Heq' := env_equiv_eq _ _ Heq);
  apply (gmultiset_not_elem_of_empty f); rewrite Heq'; ms
  end.
Qed.

Lemma box_var_not_tautology v: (∅ ⊢ □ (Var v)) -> False.
Proof.
intro Hp.
remember ∅ as Γ.
dependent induction Hp;
try match goal with | Heq : (_ • ?f%stdpp) = _ |- _ => symmetry in Heq;
  pose(Heq' := env_equiv_eq _ _ Heq);
  apply (gmultiset_not_elem_of_empty f); rewrite Heq'; ms
  end.
rewrite open_boxes_empty in Hp.
clear IHHp.
dependent induction Hp;
try match goal with | Heq : (_ • ?f%stdpp) = _ |- _ => symmetry in Heq;
  pose(Heq' := env_equiv_eq _ _ Heq); apply env_add_inv' in Heq';
  apply (gmultiset_not_elem_of_empty f); rewrite Heq'; apply in_difference;
  [discriminate|ms]
  end.
Qed.

Lemma box_bot_not_tautology: (∅ ⊢ □⊥) -> False.
Proof.
 intro Hp.

dependent induction Hp;
try match goal with | Heq : (_ • ?f%stdpp) = _ |- _ => symmetry in Heq;
  pose(Heq' := env_equiv_eq _ _ Heq);
  apply (gmultiset_not_elem_of_empty f); rewrite Heq'; ms
  end.
rewrite open_boxes_empty in Hp.
clear IHHp.
dependent induction Hp;
try match goal with | Heq : (_ • ?f%stdpp) = _ |- _ => symmetry in Heq;
  pose(Heq' := env_equiv_eq _ _ Heq); apply env_add_inv' in Heq';
  apply (gmultiset_not_elem_of_empty f); rewrite Heq'; apply in_difference;
  [discriminate|ms]
  end.
Qed.

(* A tautology is either equal to ⊤ or has a weight of at least 3. *)
Lemma weight_tautology {K : Kind} φ: (∅ ⊢ φ) -> {φ = ⊤} + {3 ≤ weight φ}.
Proof.
intro Hp.
destruct φ.
- contradict Hp. apply  var_not_tautology.
- contradict Hp. apply bot_not_tautology.
- right. simpl. pose(weight_pos φ1). pose(weight_pos φ2). lia.
- right. simpl. pose(weight_pos φ1). pose(weight_pos φ2). lia.
- right. simpl. pose(weight_pos φ1). pose(weight_pos φ2). lia.
- dependent destruction φ.
  + contradict Hp. apply  box_var_not_tautology.
  + contradict Hp. apply box_bot_not_tautology.
  + right. simpl. pose(weight_pos φ1). pose(weight_pos φ2). lia.
  + right. simpl. pose(weight_pos φ1). pose(weight_pos φ2). lia.
  + right. simpl. pose(weight_pos φ1). pose(weight_pos φ2). lia.
  + right. simpl. pose(weight_pos φ). lia.
Qed.

