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

Instance proper_env_order:  Proper ((≡@{env}) ==> (≡@{env}) ==>(=)) env_order.
Proof.
Admitted.

Lemma env_add_remove : ∀ (Γ: env) (φ : form), (Γ • φ) ∖ {[φ]} =Γ.
Proof. intros; ms. Qed.

(* From "A New Calculus for Intuitionistic Strong Löb Logic" *)
Theorem additive_cut Γ φ ψ :
  Γ ⊢ φ  -> Γ • φ ⊢ ψ ->
  Γ ⊢ ψ.
Proof. (*
Ltac order_tac := try (apply le_S_n; etransitivity; [|exact HW]); apply Nat.le_succ_l;
match goal with |- env_weight .order_tac. *)
remember (weight φ) as w. assert(Hw : weight φ ≤ w) by lia. clear Heqw.
revert φ Hw ψ Γ.
induction w; intros φ Hw; [pose (weight_pos φ); lia|].
intros ψ Γ.
remember (Γ, ψ) as pe.
replace Γ with pe.1 by now subst.
replace ψ with pe.2 by now subst. clear Heqpe Γ ψ. revert pe.
refine  (@well_founded_induction _ _ wf_pointed_order _ _).
intros (Γ &ψ). simpl. intro IHW'. assert (IHW := fun Γ0 => fun ψ0 => IHW' (Γ0, ψ0)).
simpl in IHW. clear IHW'. intros HPφ HPψ.
Ltac otac Heq := subst; repeat rewrite env_replace in Heq by trivial; repeat rewrite env_add_remove by trivial; order_tac; rewrite Heq; order_tac.
destruct HPφ; simpl in Hw.
- now apply contraction.
- apply ExFalso.
- apply AndL_rev in HPψ. do 2 apply IHw in HPψ; trivial; try lia; apply weakening; assumption.
- apply AndL. apply IHW; auto with proof. order_tac.
- apply OrL_rev in HPψ; apply (IHw φ); [lia| |]; tauto.
- apply OrL_rev in HPψ; apply (IHw ψ0); [lia| |]; tauto.
- apply OrL; apply IHW; auto with proof.
  + otac Heq.
  + exch 0. eapply (OrL_rev _ φ ψ0). exch 0. exact HPψ.
  + order_tac.
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
     * rw (symmetry Heq) 0. apply IHW.
     -- order_tac.
     -- now apply ImpR.
     -- peapply HPψ1.
     * rw (symmetry Heq) 0. apply IHW.
       -- order_tac.
       -- apply ImpR. box_tac. peapply HPφ.
       -- peapply HPψ2.
  + forward. apply AndL. apply IHW.
     * otac Heq.
     * apply AndL_rev. backward. rw (symmetry Heq) 0. apply ImpR, HPφ.
     * backward. peapply HPψ.
  + apply OrR1, IHW.
    * rewrite HH, env_add_remove. order_tac.
    * rw (symmetry Heq) 0. apply ImpR, HPφ.
    * peapply HPψ.
  + apply OrR2, IHW.
    * rewrite HH, env_add_remove. order_tac.
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
        -- rewrite env_replace in Heq by trivial. order_tac. rewrite Heq. order_tac.
        -- peapply HP.1.
        -- exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ1.
      * apply IHW.
        -- rewrite env_replace in Heq by trivial. order_tac. rewrite Heq. order_tac.
        -- peapply HP.2.
        -- exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ2.
  + rw (symmetry Heq) 0. apply ImpR, IHW.
      -- order_tac.
      -- apply weakening, ImpR,  HPφ.
      -- exch 0.  rewrite <- HH. exact HPψ.
  + case (decide ((Var p → φ0) = (φ → ψ0))).
      * intro Heq'; inversion Heq'; subst. clear Heq'.
         replace ((Γ0 • Var p • (p → ψ0)) ∖ {[p → ψ0]}) with (Γ0 • Var p) by ms.
         apply (IHw ψ0).
        -- lia.
        -- apply contraction. peapply HPφ.
        -- assumption.
      * intro Hneq. do 2 forward. exch 0. apply ImpLVar, IHW.
        -- repeat rewrite env_replace in Heq by trivial. order_tac. rewrite Heq. order_tac.
        -- apply imp_cut with (φ := Var p). exch 0. do 2 backward.
            rw (symmetry Heq) 0. apply ImpR, HPφ.
        -- exch 0; exch 1. rw (symmetry (difference_singleton _ _ Hin1)) 2. exact HPψ.
  + case (decide (((φ1 ∧ φ2) → φ3)= (φ → ψ0))).
      * intro Heq'; inversion Heq'; subst. clear Heq'. rw (symmetry Heq) 0.
         apply (IHw (φ1 → φ2 → ψ0)).
        -- simpl in *. lia.
        -- apply ImpR, ImpR, AndL_rev, HPφ.
        -- peapply HPψ.
      * intro Hneq. forward. apply ImpLAnd, IHW.
        -- rewrite env_replace in Heq by trivial. order_tac. rewrite Heq. order_tac.
        -- apply ImpLAnd_rev. backward. rw (symmetry Heq) 0. apply ImpR, HPφ.
        -- exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ.
  + case (decide (((φ1 ∨ φ2) → φ3)= (φ → ψ0))).
      * intro Heq'; inversion Heq'; subst. clear Heq'. rw (symmetry Heq) 0. apply OrL_rev in HPφ.
         apply (IHw (φ1 → ψ0)).
        -- simpl in *. lia.
        -- apply (IHw (φ2 → ψ0)).
           ++ simpl in *; lia.
           ++ apply ImpR, HPφ.
           ++ apply weakening, ImpR, HPφ.
        -- apply (IHw (φ2 → ψ0)).
           ++ simpl in *; lia.
           ++ apply weakening, ImpR, HPφ.
           ++ peapply HPψ.
      * intro Hneq. forward. apply ImpLOr, IHW.
        -- rewrite env_replace in Heq by trivial. order_tac. rewrite Heq. order_tac.
        -- apply ImpLOr_rev. backward. rw (symmetry Heq) 0. apply ImpR, HPφ.
        -- exch 0. exch 1. rw (symmetry (difference_singleton _ _ Hin0)) 2. exact HPψ.
  + case (decide (((φ1 → φ2) → φ3) = (φ → ψ0))).
     * intro Heq'. inversion Heq'; subst. clear Heq'. rw (symmetry Heq) 0. apply (IHw ψ0).
      -- lia.
      -- apply (IHw(φ1 → φ2)).
        ++ lia.
        ++ apply (IHw (φ2 → ψ0)).
            ** simpl in *. lia.
            ** apply ImpR. eapply imp_cut, HPφ.
            ** peapply HPψ1.
        ++ exact HPφ.
    -- peapply HPψ2.
   *  (* (V-d) *)
       intro Hneq. forward. apply ImpLImp.
      -- apply ImpR, IHW.
        ++ otac Heq.
        ++ exch 0. apply contraction, ImpLImp_dup. backward. rw (symmetry Heq) 0.
                apply ImpR, HPφ.
        ++ exch 0. apply ImpR_rev. exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1.
                exact HPψ1.
      -- apply IHW.
        ++ otac Heq.
        ++ apply imp_cut with (φ1 → φ2). backward. rw (symmetry Heq) 0.
                apply ImpR, HPφ.
        ++ exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ2.
  + case (decide ((□ φ1 → φ2) = (φ → ψ0))).
     * intro Heq'. inversion Heq'; subst. clear Heq'. rw (symmetry Heq) 0.
        assert(Γ = Γ0) by ms. subst Γ0. clear Hin.
        apply (IHw (□ φ1)).
      -- lia.
      -- apply BoxR, (IHw(ψ0)).
        ++ lia.
        ++ apply open_boxes_R, HPφ.
        ++ exact HPψ1.
     --  apply (IHw(ψ0)).
        ++ lia.
        ++ exact HPφ.
        ++ exch 0. apply weakening, HPψ2.
    *  (* (V-f ) *)
       intro Hneq. forward. apply ImpBox.
       -- apply IHW.
        ++ otac Heq.
        ++ apply ImpR_rev, open_boxes_R, ImpR.
                apply ImpLBox_prev with φ1. exch 0. apply weakening.
                backward. rw (symmetry Heq) 0. apply ImpR, HPφ.
        ++ exch 0. exch 1. box_tac. apply In_open_boxes in Hin0. simpl in Hin0.
               rw (symmetry (difference_singleton _ _ Hin0)) 2. exact HPψ1.
       -- apply IHW.
        ++ otac Heq.
        ++ apply ImpLBox_prev with φ1. backward. rw (symmetry Heq) 0.
                apply ImpR, HPφ.
        ++ exch 0.  rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ2.
  + subst. rw (symmetry Heq) 0. rewrite open_boxes_add in HPψ. simpl in HPψ.
      apply BoxR. apply IHW.
    * otac Heq. (* todo: count rhs twice *)
    * apply open_boxes_R, weakening, ImpR, HPφ.
    * exch 0. exact HPψ.
- apply ImpLVar. eapply IHW; eauto.
  + otac Heq.
  + exch 0. apply (imp_cut (Var p)). exch 0; exact HPψ.
- apply ImpLAnd. eapply IHW; eauto.
  + otac Heq.
  + exch 0. apply ImpLAnd_rev. exch 0. exact HPψ.
- apply ImpLOr. eapply IHW; eauto.
  + otac Heq.
  + exch 0. exch 1. apply ImpLOr_rev. exch 0. exact HPψ.
- apply ImpLImp; [assumption|].
  apply IHW.
  + otac Heq.
  + assumption.
  + exch 0. eapply ImpLImp_prev. exch 0. exact HPψ.
- apply ImpBox. trivial. apply IHW.
  * otac Heq.
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
     -- subst. rewrite env_add_remove. otac H.
     -- rw (symmetry Heq) 0. now apply BoxR.
     -- peapply HPψ1.
     * apply IHW.
       -- otac Heq.
       -- apply BoxR. box_tac. peapply HPφ. rewrite Heq.
           rewrite open_boxes_remove; trivial.
       -- peapply HPψ2.
  + forward. apply AndL. apply IHW.
     * otac Heq.
     * apply AndL_rev. backward. rw (symmetry Heq) 0. apply BoxR, HPφ.
     * backward. peapply HPψ.
  + apply OrR1, IHW.
    * otac Heq.
    * rw (symmetry Heq) 0. apply BoxR, HPφ.
    * peapply HPψ.
  + apply OrR2, IHW.
    * otac Heq.
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
        -- otac Heq.
        -- peapply HP.1.
        -- exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ1.
      * apply IHW.
        -- otac Heq.
        -- peapply HP.2.
        -- exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ2.
  + rw (symmetry Heq) 0. apply ImpR, IHW.
      -- otac Heq.
      -- apply weakening, BoxR,  HPφ.
      -- exch 0.  rewrite <- HH. exact HPψ.
  + do 2 forward. exch 0. apply ImpLVar, IHW.
      * otac Heq.
      * apply imp_cut with (φ := Var p). exch 0. do 2 backward.
         rewrite HH. apply BoxR in HPφ. peapply HPφ.
      * exch 0; exch 1. rw (symmetry (difference_singleton _ _ Hin1)) 2. exact HPψ.
  + forward. apply ImpLAnd, IHW.
      * otac Heq.
      * apply BoxR in HPφ. apply ImpLAnd_rev. backward. rewrite HH. peapply HPφ.
      * exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ.
  + forward. apply ImpLOr, IHW.
      * otac Heq.
      * apply BoxR in HPφ. apply ImpLOr_rev. backward. rewrite HH. peapply HPφ.
      * exch 0. exch 1. rw (symmetry (difference_singleton _ _ Hin0)) 2. exact HPψ.
  + forward. apply ImpLImp.
      -- apply ImpR, IHW.
        ++ otac Heq.
        ++ exch 0. apply contraction, ImpLImp_dup. backward. rw (symmetry Heq) 0.
                apply BoxR, HPφ.
        ++ exch 0. apply ImpR_rev. exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1.
                exact HPψ1.
      -- apply IHW.
        ++ otac Heq.
        ++ apply imp_cut with (φ1 → φ2). backward. rw (symmetry Heq) 0.
                apply BoxR, HPφ.
        ++ exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ2.
  + (* (VIII-b) *) 
      forward. apply ImpBox.
     * (* π0 *)
        apply IHW.
      -- otac Heq.
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
      -- otac Heq.
      -- apply ImpLBox_prev with (φ1 := φ1). backward.
          rw (symmetry Heq) 0.  apply BoxR, HPφ.
      -- exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ2.
  + (* (VIII-c) *)
      subst. rw (symmetry Heq) 0. rewrite open_boxes_add in HPψ. simpl in HPψ.
      apply BoxR. apply IHW.
    * otac Heq. (* todo: count rhs twice *)
    * apply open_boxes_R, weakening, BoxR, HPφ.
    * apply (IHw φ).
      -- lia.
      -- exch 0. apply weakening, HPφ.
      -- exch 0. apply weakening. exch 0. exact HPψ.
Qed.

(* Multiplicative cut rule *)
Theorem cut Γ Γ' φ ψ :
  Γ ⊢ φ  -> Γ' • φ ⊢ ψ ->
  Γ ⊎ Γ' ⊢ ψ.
Proof.
intros π1 π2. apply additive_cut with φ.
- apply generalised_weakeningR, π1.
- replace (Γ ⊎ Γ' • φ) with (Γ ⊎ (Γ' • φ)) by ms. apply generalised_weakeningL, π2.
Qed.