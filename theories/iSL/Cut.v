Require Import ISL.Formulas ISL.Sequents ISL.Order.
Require Import ISL.SequentProps .

(* TODO: move *)
Lemma open_boxes_R (Γ : env) (φ ψ : form): (Γ • φ) ⊢ ψ → ((⊗Γ) • φ) ⊢ ψ.
Proof.
revert ψ.
induction Γ using gmultiset_rec; intro ψ.
- rewrite open_boxes_empty. trivial.
- intro HP. peapply (open_box_L  (⊗ Γ • φ) x ψ).
  + apply ImpR_rev, IHΓ, ImpR. peapply HP.
  + rewrite open_boxes_disj_union, open_boxes_singleton; ms.
Qed.

(* From "A New Calculus for Intuitionistic Strong Löb Logic" *)
Theorem cut Γ φ ψ :
  Γ ⊢ φ  -> Γ • φ ⊢ ψ ->
  Γ ⊢ ψ.
Proof.
remember (weight φ) as w. assert(Hw : weight φ ≤ w) by lia. clear Heqw.
revert φ Hw ψ Γ.
induction w; intros φ Hw; [pose (weight_pos φ); lia|].
intros ψ Γ.
remember (env_weight (Γ • ψ)) as W. assert(HW : env_weight (Γ • ψ) ≤ W) by lia. 
clear HeqW.
revert ψ Γ HW.
induction W; intros ψ Γ HW HPφ HPψ;
[rewrite env_weight_add in HW; pose (Order.pow5_gt_0 (weight ψ)); lia|].
destruct HPφ; simpl in Hw.
- now apply contraction.
- apply ExFalso.
- apply AndL_rev in HPψ. do 2 apply IHw in HPψ; trivial; try lia; apply weakening; assumption.
- apply AndL. apply IHW; auto with proof.
  admit. (*order *)
- apply OrL_rev in HPψ; apply (IHw φ); [lia| |]; tauto.
- apply OrL_rev in HPψ; apply (IHw ψ0); [lia| |]; tauto.
- apply OrL; apply IHW; auto with proof.
  + admit.
  + exch 0. eapply (OrL_rev _ φ ψ0). exch 0. exact HPψ.
  + admit.
  + exch 0. eapply (OrL_rev _ φ ψ0). exch 0. exact HPψ.
- (* (V) *) (* hard:  *)
(* START *)
  remember (Γ • (φ → ψ0)) as Γ' eqn:HH.
  assert (Heq: Γ ≡ Γ' ∖ {[ φ → ψ0]}) by ms.
  assert(Hin : (φ → ψ0) ∈ Γ')by ms.
  rw Heq 0. destruct HPψ.
  + forward. auto with proof.
  + forward. auto with proof.
  + apply AndR.
     * apply IHW.
     -- admit.
     -- rw (symmetry Heq) 0. now apply ImpR.
     -- peapply HPψ1.
     * apply IHW.
       -- admit.
       -- apply ImpR. box_tac. peapply HPφ.
       -- peapply HPψ2.
  + forward. apply AndL. apply IHW.
     * admit.
     * apply AndL_rev. backward. rw (symmetry Heq) 0. apply ImpR, HPφ.
     * backward. peapply HPψ.
  + apply OrR1, IHW.
    * admit.
    * rw (symmetry Heq) 0. apply ImpR, HPφ.
    * peapply HPψ.
  + apply OrR2, IHW.
    * admit.
    * rw (symmetry Heq) 0. apply ImpR, HPφ.
    * peapply HPψ.
  + forward. apply ImpR in HPφ.
       assert(Hin' : (φ0 ∨ ψ) ∈ ((Γ0 • φ0 ∨ ψ) ∖ {[φ→ ψ0]}))
            by (apply in_difference; [discriminate|ms]).
       assert(HPφ' : (((Γ0 • φ0 ∨ ψ) ∖ {[φ→ ψ0]}) ∖ {[φ0 ∨ ψ]} • φ0 ∨ ψ) ⊢ (φ → ψ0))
            by (rw (symmetry (difference_singleton _ (φ0 ∨ψ) Hin')) 0; peapply HPφ).
       assert (HP := (OrL_rev  _ φ0 ψ (φ → ψ0) HPφ')).
       apply OrL.
      * apply IHW.
        -- admit.
        -- peapply HP.1.
        -- exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ1.
      * apply IHW.
        -- admit.
        -- peapply HP.2.
        -- exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ2.
  + rw (symmetry Heq) 0. apply ImpR, IHW.
      -- admit.
      -- apply weakening, ImpR,  HPφ.
      -- exch 0.  rewrite <- HH. exact HPψ.
  + (* check for equality (p → φ0)) ∖ {[φ → ψ0]} 
  do 2 forward. exch 0. apply ImpLVar, IHW.
    * admit.
    * apply imp_cut with (φ := Var p). exch 0. do 2 backward.
       rewrite HH. apply BoxR in HPφ. peapply HPφ.
    * exch 0; exch 1. rw (symmetry (difference_singleton _ _ Hin1)) 2. exact HPψ.
    *)
    admit.
  + admit. (* forward. apply ImpLAnd, IHW.
    * admit.
    * apply BoxR in HPφ. apply ImpLAnd_rev. backward. rewrite HH. peapply HPφ.
    * exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ. *)
  + admit. (* forward. apply ImpLOr, IHW.
    * admit.
    * apply BoxR in HPφ. apply ImpLOr_rev. backward. rewrite HH. peapply HPφ.
    * exch 0. exch 1. rw (symmetry (difference_singleton _ _ Hin0)) 2. exact HPψ. *)
  + admit. (* (V-d) *)
  (* (V-f ) *)
  + (* (V-f ) 
   forward. apply ImpBox.
    * apply IHW.
      -- admit.
      -- admit.
      -- exch 0.  exch 1. box_tac. peapply HPψ1.  simpl .apply ImpLBox_prev with (φ1 := φ1).
          exch 1. rw (symmetry (difference_singleton _ _ Hin0)) 2.
    * apply IHW.
      -- admit.
      -- apply ImpLBox_prev with (φ1 := φ1).
          backward. rw (symmetry Heq) 0. apply BoxR, HPφ.
      -- exch 0.  rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ2.
      *)
      admit.
  + subst. rw (symmetry Heq) 0. rewrite open_boxes_add in HPψ. simpl in HPψ.
      apply BoxR. apply IHW.
    * admit. (* todo: count rhs twice *)
    * apply open_boxes_R, weakening, ImpR, HPφ.
    * exch 0. exact HPψ.
- apply ImpLVar. eapply IHW; eauto.
  + admit.
  + exch 0. apply (imp_cut (Var p)). exch 0; exact HPψ.
- apply ImpLAnd. eapply IHW; eauto.
  + admit.
  + exch 0. apply ImpLAnd_rev. exch 0. exact HPψ.
- apply ImpLOr. eapply IHW; eauto.
  + admit.
  + exch 0. exch 1. apply ImpLOr_rev. exch 0. exact HPψ.
- apply ImpLImp; [assumption|].
  apply IHW.
  + admit.
  + assumption.
  + exch 0. eapply ImpLImp_prev. exch 0. exact HPψ.
- apply ImpBox. trivial. apply IHW.
  * admit.
  * assumption.
  * exch 0. eapply ImpLBox_prev. exch 0. exact HPψ.
  Require Import Coq.Program.Equality.
(* (VIII) *)
- remember (Γ • □ φ) as Γ' eqn:HH.
  assert (Heq: Γ ≡ Γ' ∖ {[ □ φ ]}) by ms.
  assert(Hin : (□ φ) ∈ Γ')by ms.
  rw Heq 0. destruct HPψ.
  + forward. auto with proof.
  + forward. auto with proof.
  + apply AndR.
     * apply IHW.
     -- admit.
     -- rw (symmetry Heq) 0. now apply BoxR.
     -- peapply HPψ1.
     * apply IHW.
       -- admit.
       -- apply BoxR. box_tac. peapply HPφ. rewrite Heq.
           rewrite open_boxes_remove; trivial.
       -- peapply HPψ2.
  + forward. apply AndL. apply IHW.
     * admit.
     * apply AndL_rev. backward. rw (symmetry Heq) 0. apply BoxR, HPφ.
     * backward. peapply HPψ.
  + apply OrR1, IHW.
    * admit.
    * rw (symmetry Heq) 0. apply BoxR, HPφ.
    * peapply HPψ.
  + apply OrR2, IHW.
    * admit.
    * rw (symmetry Heq) 0. apply BoxR, HPφ.
    * peapply HPψ.
  + forward. apply BoxR in HPφ.
       assert(Hin' : (φ0 ∨ ψ) ∈ ((Γ0 • φ0 ∨ ψ) ∖ {[□ φ]}))
            by (apply in_difference; [discriminate|ms]).
       assert(HPφ' : (((Γ0 • φ0 ∨ ψ) ∖ {[□ φ]}) ∖ {[φ0 ∨ ψ]} • φ0 ∨ ψ) ⊢ □ φ)
            by (rw (symmetry (difference_singleton _ (φ0 ∨ψ) Hin')) 0; peapply HPφ).
       assert (HP := (OrL_rev  _ φ0 ψ (□φ) HPφ')).
       apply OrL.
      * apply IHW.
        -- admit.
        -- peapply HP.1.
        -- exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ1.
      * apply IHW.
        -- admit.
        -- peapply HP.2.
        -- exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ2.
  + rw (symmetry Heq) 0. apply ImpR, IHW.
      -- admit.
      -- apply weakening, BoxR,  HPφ.
      -- exch 0.  rewrite <- HH. exact HPψ.
  + do 2 forward. exch 0. apply ImpLVar, IHW.
    * admit.
    * apply imp_cut with (φ := Var p). exch 0. do 2 backward.
       rewrite HH. apply BoxR in HPφ. peapply HPφ.
    * exch 0; exch 1. rw (symmetry (difference_singleton _ _ Hin1)) 2. exact HPψ.
  + forward. apply ImpLAnd, IHW.
    * admit.
    * apply BoxR in HPφ. apply ImpLAnd_rev. backward. rewrite HH. peapply HPφ.
    * exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ.
  + forward. apply ImpLOr, IHW.
    * admit.
    * apply BoxR in HPφ. apply ImpLOr_rev. backward. rewrite HH. peapply HPφ.
    * exch 0. exch 1. rw (symmetry (difference_singleton _ _ Hin0)) 2. exact HPψ.
  + admit. (* hard *)
  (* (VIII-b) *)
  + forward. apply ImpBox.
    * (* π0 *)
       apply IHW.
      -- admit.
      -- apply ImpLBox_prev with (φ1 := φ1).
          exch 0. apply weakening.
          apply open_boxes_R. backward. rw (symmetry Heq) 0. apply BoxR, HPφ.
      -- (* π1 *)
          apply (IHw φ).
          ++ lia.
          ++ exch 1; exch 0. apply weakening.
                  exch 0. apply ImpLBox_prev with (φ1 := φ1). exch 0.
                  replace (□ φ1 → φ2) with (⊙ (□ φ1 → φ2)) by trivial.
                  rewrite <- (open_boxes_add (Γ0 ∖ {[□φ]})  (□ φ1 → φ2)).
                  assert(Heq0 : (Γ0 ∖ {[□ φ]} • (□ φ1 → φ2)) ≡ Γ)
                      by (rewrite Heq; now rewrite env_replace).
                 rw (proper_open_boxes _ _ Heq0) 1. exact HPφ.
          ++ box_tac. exch 0. apply weakening. exch 0. exch 1.
                  assert(Hin1 : φ ∈ ⊗ Γ0) by(apply In_open_boxes in Hin0; now simpl).
                  rw (symmetry (difference_singleton _ _ Hin1)) 2. exact HPψ1.
    * apply IHW.
      -- admit.
      -- apply ImpLBox_prev with (φ1 := φ1). backward.
          rw (symmetry Heq) 0.  apply BoxR, HPφ.
      -- exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ2.
  + subst. rw (symmetry Heq) 0. rewrite open_boxes_add in HPψ. simpl in HPψ.
      apply BoxR. apply IHW.
    * admit. (* todo: count rhs twice *)
    * apply open_boxes_R, weakening, BoxR, HPφ.
    * apply (IHw φ).
      -- lia.
      -- exch 0. apply weakening, HPφ.
      -- exch 0. apply weakening. exch 0. exact HPψ.
Admitted.



Theorem additive_cut Γ Γ' φ ψ :
  Γ ⊢ φ  -> Γ' • φ ⊢ ψ ->
  Γ ⊎ Γ' ⊢ ψ.
Proof.
intros π1 π2. apply cut with φ.
- apply generalised_weakeningR, π1.
- replace (Γ ⊎ Γ' • φ) with (Γ ⊎ (Γ' • φ)) by ms. apply generalised_weakeningL, π2.
Qed.