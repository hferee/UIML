(** * Decision Procedure *)
Require Import ISL.Sequents ISL.SequentProps ISL.Order.

(**
  This file implements a decision procedure for iSL. There are two versions, with the same proof.
  `Proof_tree_dec` computes a proof tree for the sequent, while `Provable_dec` only decides the provability
  of the sequent.
*)

Global Instance proper_rm : Proper ((=) ==> (≡ₚ) ==> (≡ₚ)) rm.
Proof.
intros x y Heq. subst y.
induction 1; simpl; trivial.
- case form_eq_dec; auto with *.
- case form_eq_dec; auto with * ; 
   case form_eq_dec; auto with *. intros. apply Permutation_swap.
- now rewrite IHPermutation1.
Qed.

Definition exists_dec {A : Type} (P : A -> bool) (l : list A): {x & (In x l) /\ P x} + {forall x, In x l -> ¬ P x}.
Proof.
induction l as [|x l].
- right. tauto.
- case_eq (P x); intro Heq.
  + left. exists x. split; auto with *.
  + destruct IHl as [(y & Hin & Hy)|Hf].
    * left. exists y. split; auto with *.
    * right. simpl. intros z [Hz|Hz]; subst; try rewrite Heq; auto with *.
Defined.

(** The function [Proof_tree_dec] computes a proof tree of a sequent, if there is one, or produces a proof that there is none.
   The proof is performed by induction on the  well-ordering or pointed environments and tries to apply
   all the sequent rules to reduce the weight of the environment.
 *)
Proposition Proof_tree_dec Γ φ :
  {_ : list_to_set_disj Γ ⊢ φ & True} + {forall H : list_to_set_disj  Γ ⊢ φ, False}.
Proof.
(* duplicate *)
Ltac l_tac := repeat rewrite list_to_set_disj_open_boxes;
    rewrite (proper_Provable _ _ (list_to_set_disj_env_add _ _) _ _ eq_refl)
|| rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (list_to_set_disj_env_add _ _)) _ _ eq_refl)
|| rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (equiv_disj_union_compat_r (list_to_set_disj_env_add _ _))) _ _ eq_refl)
|| rewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r (equiv_disj_union_compat_r (list_to_set_disj_env_add _ _)))) _ _ eq_refl).
remember (Γ, φ) as pe.
replace Γ with pe.1 by now inversion Heqpe.
replace φ with pe.2 by now inversion Heqpe. clear Heqpe Γ φ.
revert pe.
(* Induction on the  well-ordering of pointed environments *)
refine  (@well_founded_induction _ _ wf_pointed_order _ _).

(* Cleaning up the induction hypothesis *)
intros (Γ& φ) Hind; simpl.
assert(Hind' := λ Γ' φ', Hind(Γ', φ')). simpl in Hind'. clear Hind. rename Hind' into Hind.

(* ExFalso *)
case (decide (⊥ ∈ Γ)); intro Hbot.
{ left. eexists; trivial. apply elem_of_list_to_set_disj in Hbot. exhibit Hbot 0. apply ExFalso. }



(* Atom *)
assert(Hvar : {p & φ = Var p & Var p ∈ Γ} + {∀ p, φ = Var p -> Var p ∈ Γ -> False}). {
  destruct φ. 2-6: right; auto with *.
  case (decide (Var v ∈ Γ)); intro Hin.
  - left. exists v; trivial.
  - right; auto with *. }
destruct Hvar as [[p Heq Hp]|Hvar].
{ subst. left. eexists; trivial. apply elem_of_list_to_set_disj in Hp. exhibit Hp 0. apply Atom. }

(* AndL *)
assert(HAndL : {ψ1 & {ψ2 & (And ψ1 ψ2) ∈ Γ}} + {∀ ψ1 ψ2, (And ψ1 ψ2) ∈ Γ -> False}). {
  pose (fA := (fun θ => match θ with |And _ _ => true | _ => false end)).
  destruct (exists_dec fA Γ) as [(θ & Hin & Hθ) | Hf].
  - left. subst fA. destruct θ. 3: { eexists. eexists. apply elem_of_list_In. eauto. }
    all:  auto with *.
  - right. intros ψ1 ψ2 Hψ. rewrite elem_of_list_In in Hψ. apply Hf in Hψ. subst fA. simpl in Hψ. tauto.
}
destruct HAndL as [(ψ1 & ψ2 & Hin)|HAndL].
{ destruct (Hind (ψ1 :: ψ2 :: rm (And ψ1 ψ2) Γ) φ) as [[Hp' _] | Hf]. order_tac.
  - left. eexists; trivial. apply elem_of_list_to_set_disj in Hin.  
    exhibit Hin 0.
    rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (list_to_set_disj_rm _ _)) _ _ eq_refl).
    apply AndL. peapply Hp'.
 - right. intro Hf'. apply Hf.
   rw (symmetry (list_to_set_disj_env_add (ψ2 :: rm (And ψ1 ψ2) Γ) ψ1)) 0.
   rw (symmetry (list_to_set_disj_env_add (rm (And ψ1 ψ2) Γ) ψ2)) 1.
   exch 0. apply AndL_rev.
   rw (symmetry (list_to_set_disj_rm Γ(And ψ1 ψ2))) 1.
   apply elem_of_list_to_set_disj in Hin.
   pose (difference_singleton (list_to_set_disj Γ) (And ψ1 ψ2)).
   peapply Hf'.
}

(* ImpR *)
assert(HImpR : {φ1 & {φ2 & φ = (Implies φ1 φ2)}} + {∀ φ1 φ2, φ ≠ (Implies φ1 φ2)}) by (destruct φ; eauto).
destruct HImpR as [(φ1 & φ2 & Heq) | HImpR].
{ subst.
  destruct (Hind (φ1 :: Γ) φ2) as [(Hp1&_) | H1]. order_tac.
  - left. eexists; trivial. apply ImpR. peapply Hp1.
  - right. intro Hf. apply H1. apply ImpR_rev in Hf. peapply Hf.
}

(* OrL *)
assert(HOrL : {ψ1 & {ψ2 & (Or ψ1 ψ2) ∈ Γ}} + {∀ ψ1 ψ2, (Or ψ1 ψ2) ∈ Γ -> False}). {
  pose (fA := (fun θ => match θ with |Or _ _ => true | _ => false end)).
  destruct (exists_dec fA Γ) as [(θ & Hin & Hθ) | Hf].
  - left. subst fA. destruct θ. 4: { eexists. eexists. apply elem_of_list_In. eauto. }
    all:  auto with *.
  - right. intros ψ1 ψ2 Hψ. rewrite elem_of_list_In in Hψ. apply Hf in Hψ. subst fA. simpl in Hψ. tauto.
}
destruct HOrL as [(ψ1 & ψ2 & Hin)|HOrL].
{ apply elem_of_list_to_set_disj in Hin.
  destruct (Hind (ψ1 :: rm (Or ψ1 ψ2) Γ) φ) as [[Hp1 _] | Hf]. order_tac.
  - destruct (Hind (ψ2 :: rm (Or ψ1 ψ2) Γ) φ) as [[Hp2 _] | Hf]. order_tac.
    + left. eexists; trivial. exhibit Hin 0.
         rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (list_to_set_disj_rm _ _)) _ _ eq_refl).
         apply OrL. peapply Hp1. peapply Hp2.
    + right; intro Hf'. assert(Hf'' :list_to_set_disj (rm (Or ψ1 ψ2) Γ) • Or ψ1 ψ2 ⊢ φ). {
          rw (symmetry (list_to_set_disj_rm Γ(Or ψ1 ψ2))) 1.
          pose (difference_singleton (list_to_set_disj Γ) (Or ψ1 ψ2)). peapply Hf'.
         }
        apply OrL_rev in Hf''. apply Hf. peapply Hf''.
  - right; intro Hf'. assert(Hf'' :list_to_set_disj (rm (Or ψ1 ψ2) Γ) • Or ψ1 ψ2 ⊢ φ). {
          rw (symmetry (list_to_set_disj_rm Γ(Or ψ1 ψ2))) 1.
          pose (difference_singleton (list_to_set_disj Γ) (Or ψ1 ψ2)). peapply Hf'.
         }
        apply OrL_rev in Hf''. apply Hf. peapply Hf''.1.
}

(* AndR *)
assert(HAndR : {φ1 & {φ2 & φ = (And φ1 φ2)}} + {∀ φ1 φ2, φ ≠ (And φ1 φ2)}) by (destruct φ; eauto).
destruct HAndR as [(φ1 & φ2 & Heq) | HAndR].
{ subst.
  destruct (Hind Γ φ1) as [(Hp1&_) | H1]. order_tac.
  - destruct (Hind Γ φ2) as [(Hp2&_) | H2]. order_tac.
    + left. eexists; trivial. apply AndR; assumption.
    + right. intro Hp. apply AndR_rev in Hp. tauto.
  - right. intro Hp. apply AndR_rev in Hp. tauto.
}

(* ImpLVar *)
assert(HImpLVar : {p & {ψ & Var p ∈ Γ /\ (Implies (Var p) ψ) ∈ Γ}} + 
                                 {∀ p ψ, Var p ∈ Γ -> (Implies (Var p) ψ) ∈ Γ -> False}). {
  pose (fIp :=λ p θ, match θ with | Implies (Var q) _ => if decide (p = q) then true else false | _ => false end).
  pose (fp:= (fun θ => match θ with |Var p => if (exists_dec (fIp p) Γ) then true else false | _ => false end)).
  destruct (exists_dec fp Γ) as [(θ & Hin & Hθ) | Hf].
  - left. subst fp. destruct θ. 2-6: auto with *.
    case exists_dec as [(ψ &Hinψ & Hψ)|] in Hθ; [|auto with *]. 
    unfold fIp in Hψ. destruct ψ.  1-4, 6: auto with *.
    destruct ψ1. 2-6: auto with *. case decide in Hψ; [|auto with *].
    subst. apply elem_of_list_In in Hinψ, Hin.
    do 2 eexists. split; eauto.
  - right. intros p ψ Hp Hψ. rewrite elem_of_list_In in Hp, Hψ. apply Hf in Hp. subst fp fIp.
    simpl in Hp. case exists_dec as [|Hf'] in Hp. auto with *.
    apply (Hf' _ Hψ). rewrite decide_True; trivial. auto with *.
}
destruct HImpLVar as [[p [ψ [Hinp Hinψ]]]|HImpLVar].
{ apply elem_of_list_to_set_disj in Hinp.
  apply elem_of_list_to_set_disj in Hinψ.
  assert(Hinp' : Var p ∈ (list_to_set_disj Γ ∖ {[Implies p ψ]} : env))
    by (apply in_difference; [discriminate| assumption]).
  destruct (Hind (ψ :: rm (Implies (Var p) ψ) Γ) φ) as [[Hp _]|Hf]. order_tac.
  - left. eexists; trivial. exhibit Hinψ 0.
     exhibit Hinp' 1. apply ImpLVar.
     rw (symmetry (difference_singleton (list_to_set_disj Γ ∖ {[Implies p ψ]}) (Var p) Hinp')) 1.
     rw (list_to_set_disj_rm Γ(Implies p ψ)) 1. l_tac. exact Hp.
  - right. intro Hf'. apply Hf.
     rw (symmetry (list_to_set_disj_env_add (rm (Implies p ψ) Γ) ψ)) 0.
     rw (symmetry (list_to_set_disj_rm Γ(Implies p ψ))) 1.
     exhibit Hinp' 1. apply ImpLVar_rev.
     rw (symmetry (difference_singleton _ _ Hinp')) 1.
     rw (symmetry (difference_singleton _ _ Hinψ)) 0.
     exact Hf'.
}

(* ImpLAnd *)
assert(HImpLAnd : {φ1 & {φ2 & {φ3 &  (Implies (And φ1 φ2) φ3) ∈ Γ}}} +
                                 {∀ φ1 φ2 φ3, (Implies (And φ1 φ2) φ3) ∈ Γ -> False}). {
    pose (fII := (fun θ => match θ with |Implies (And _ _) _ => true | _ => false end)).
   destruct (exists_dec fII Γ) as [(θ & Hin & Hθ) | Hf].
    - left. subst fII. destruct θ. 1-4, 6: auto with *.
      destruct θ1. 1-2,4-6: auto with *. do 3 eexists; apply elem_of_list_In; eauto.
    - right. intros ψ1 ψ2 ψ3 Hψ. rewrite elem_of_list_In in Hψ. apply Hf in Hψ. subst fII. simpl in Hψ. tauto.
}
destruct HImpLAnd as [(φ1&φ2&φ3&Hin)|HImpLAnd].
{ apply elem_of_list_to_set_disj in Hin.
  destruct (Hind (Implies φ1 (Implies φ2 φ3) :: rm (Implies (And φ1 φ2) φ3) Γ) φ) as [[Hp _]|Hf]. order_tac.
  - left. eexists; trivial. exhibit Hin 0. apply ImpLAnd.
     rw (list_to_set_disj_rm Γ(Implies (And φ1 φ2) φ3)) 1. l_tac. exact Hp.
  - right. intro Hf'. apply Hf.
     rw (symmetry (list_to_set_disj_env_add (rm (Implies (And φ1 φ2) φ3) Γ) (Implies φ1 (Implies φ2 φ3)))) 0.
     rw (symmetry (list_to_set_disj_rm Γ(Implies (And φ1 φ2) φ3))) 1.
     apply ImpLAnd_rev.
     rw (symmetry (difference_singleton _ _ Hin)) 0. exact Hf'.
}

(* ImpLOr *)
assert(HImpLOr : {φ1 & {φ2 & {φ3 &  (Implies (Or φ1 φ2) φ3) ∈ Γ}}} +
                                 {∀ φ1 φ2 φ3, (Implies (Or φ1 φ2) φ3) ∈ Γ -> False}). {
    pose (fII := (fun θ => match θ with |Implies (Or _ _) _ => true | _ => false end)).
   destruct (exists_dec fII Γ) as [(θ & Hin & Hθ) | Hf].
    - left. subst fII. destruct θ. 1-4, 6: auto with *.
      destruct θ1. 1-3, 5-6: auto with *. do 3 eexists; apply elem_of_list_In; eauto.
    - right. intros ψ1 ψ2 ψ3 Hψ. rewrite elem_of_list_In in Hψ. apply Hf in Hψ. subst fII. simpl in Hψ. tauto.
}
destruct HImpLOr as [(φ1&φ2&φ3&Hin)|HImpLOr].
{ apply elem_of_list_to_set_disj in Hin.
  destruct (Hind (Implies φ2 φ3 :: Implies φ1 φ3 :: rm (Implies (Or φ1 φ2) φ3) Γ) φ) as [[Hp _]|Hf]. order_tac.
  - left. eexists; trivial. exhibit Hin 0. apply ImpLOr.
     rw (list_to_set_disj_rm Γ(Implies (Or φ1 φ2) φ3)) 2. do 2 l_tac. exact Hp.
  - right. intro Hf'. apply Hf.
     rw (symmetry (list_to_set_disj_env_add ( Implies φ1 φ3 :: rm (Implies (Or φ1 φ2) φ3) Γ) (Implies φ2 φ3))) 0.
     rw (symmetry (list_to_set_disj_env_add (rm (Implies (Or φ1 φ2) φ3) Γ) (Implies φ1 φ3))) 1.
     rw (symmetry (list_to_set_disj_rm Γ(Implies (Or φ1 φ2) φ3))) 2.
     apply ImpLOr_rev.
     rw (symmetry (difference_singleton _ _ Hin)) 0. exact Hf'.
}

(* non invertible right rules *)

(* OrR1 *)
assert(HOrR1 : {φ1 & {φ2 & {Hp : (list_to_set_disj Γ ⊢ φ1) & φ = (Or φ1 φ2)}}} +
                       {∀ φ1 φ2, ∀ (H : list_to_set_disj Γ ⊢ φ1), φ = (Or φ1 φ2) -> False}).
{
  destruct φ. 4: { destruct (Hind Γ φ1)as [[Hp _]|Hf]. order_tac.
  - left. do 3 eexists; eauto.
  - right. intros ? ? Hp Heq. inversion Heq. subst. tauto.
  }
  all: right; auto with *.
}
destruct HOrR1 as [(φ1 & φ2 & Hp & Heq)| HOrR1].
{ subst. left. eexists; trivial. apply OrR1, Hp. }
assert(HOrR2 : {φ1 & {φ2 & {Hp : (list_to_set_disj Γ ⊢ φ2) & φ = (Or φ1 φ2)}}} +
                       {∀ φ1 φ2, ∀ (H : list_to_set_disj Γ ⊢ φ2), φ = (Or φ1 φ2) -> False}).
{
  destruct φ. 4: { destruct (Hind Γ φ2)as [[Hp _]|Hf]. order_tac.
  - left. do 3 eexists; eauto.
  - right. intros ? ? Hp Heq. inversion Heq. subst. tauto.
  }
  all: right; auto with *.
}

(* OrR2 *)
destruct HOrR2 as [(φ1 & φ2 & Hp & Heq)| HOrR2 ].
{ subst. left. eexists; trivial. apply OrR2, Hp. }
assert(HBoxR : {φ' & {Hp : (⊗ (list_to_set_disj Γ) • □ φ' ⊢ φ') & φ = (□ φ')}} +
                       {∀ φ', ∀ (H : ⊗ (list_to_set_disj Γ) • □ φ' ⊢ φ'), φ = (□ φ') -> False}).
{
  destruct φ. 6: { destruct (Hind  ((□ φ) :: map open_box Γ) φ)as [[Hp _]|Hf]. order_tac.
  - left. do 2 eexists; eauto. l_tac. exact Hp.
  - right. intros ? Hp Heq. inversion Heq. subst. apply Hf.
     rw (symmetry (list_to_set_disj_env_add (map open_box Γ) (□ φ'))) 0.
     rewrite <- list_to_set_disj_open_boxes. exact Hp.
  }
  all: right; auto with *.
}

(* BoxR *)
destruct HBoxR as [(φ' & Hp & Heq)| HBoxR ].
{ left. subst. eexists; trivial. apply BoxR, Hp. }
assert(Hempty: ∀ (Δ : env) φ,((Δ • φ) = ∅) -> False).
{
  intros Δ θ Heq. assert (Hm:= multiplicity_empty θ).
  unfold base.empty in *.
  rewrite <- Heq, union_mult, singleton_mult_in in Hm by trivial. lia.
}

(* non invertible left rules *)

(* ImpLImp *)
assert(HImpLImp : ∀Γ2 Γ1, Γ1 ++ Γ2 = Γ -> {φ1 & {φ2 & {φ3 &{H2312 : ((list_to_set_disj (rm (Implies (Implies φ1 φ2) φ3) Γ) • (Implies φ2 φ3)) ⊢ (Implies φ1 φ2))
                                          & {H3: (list_to_set_disj (rm (Implies (Implies φ1 φ2) φ3) Γ) • φ3 ⊢ φ) & (Implies (Implies φ1 φ2) φ3) ∈ Γ2}}}}} +
    {∀ φ1 φ2 φ3 (_ : (list_to_set_disj (rm (Implies (Implies φ1 φ2) φ3) Γ) • (Implies φ2 φ3)) ⊢ (Implies φ1 φ2))
                              (_: list_to_set_disj (rm (Implies (Implies φ1 φ2) φ3) Γ) • φ3 ⊢ φ),
                               Implies (Implies φ1 φ2) φ3 ∈ Γ2 → False}).
{
  induction Γ2 as [|θ Γ2]; intros Γ1 Heq.
  - right. intros φ1 φ2 φ3 _ _ Hin. inversion Hin.
  - assert(Heq' : (Γ1 ++ [θ]) ++ Γ2 = Γ) by (subst; auto with *).
    destruct (IHΓ2 (Γ1 ++  [θ]) Heq') as [(φ1 & φ2 & φ3 & Hp1 & Hp2 & Hin)|Hf].
   + left. repeat eexists; eauto. now right.
   + destruct θ.
        5: destruct θ1.
        9 : {
        destruct (Hind  (Implies θ1_2 θ2 :: rm (Implies (Implies θ1_1 θ1_2) θ2) Γ) (Implies θ1_1 θ1_2))
          as [[Hp1 _] | Hf'].
        - order_tac. rewrite <- Permutation_middle. unfold rm.
          destruct form_eq_dec; [|tauto]. order_tac.
        - destruct (Hind  (θ2 :: rm (Implies (Implies θ1_1 θ1_2) θ2) Γ) φ) as [[Hp2 _] | Hf''].
          + order_tac. rewrite <- Permutation_middle. unfold rm.
               destruct form_eq_dec; [|tauto]. order_tac.
          + left. repeat eexists; try l_tac; eauto. ms.
          + right; intros φ1 φ2 φ3 Hp1' Hp2 He; apply elem_of_list_In in He;
               destruct He as [Heq''| Hin]; [|apply elem_of_list_In in Hin; eapply Hf; eauto].
               inversion Heq''. subst. apply Hf''. peapply Hp2.
      - right; intros φ1 φ2 φ3 Hp1 Hp2 He; apply elem_of_list_In in He;
               destruct He as [Heq''| Hin]; [|apply elem_of_list_In in Hin; eapply Hf; eauto].
               inversion Heq''. subst. apply Hf'. peapply Hp1.
        }
        all: (right; intros φ1 φ2 φ3 Hp1 Hp2 He; apply elem_of_list_In in He; destruct He as [Heq''| Hin];
     [discriminate|apply elem_of_list_In in Hin; eapply Hf; eauto]).
}
destruct (HImpLImp Γ [] (app_nil_l _)) as [(φ1 & φ2 & φ3 & Hp1 & Hp2 & Hin)|HfImpl].
{ apply elem_of_list_to_set_disj in Hin.
  left. eexists; trivial. exhibit Hin 0. rw (list_to_set_disj_rm Γ(Implies (Implies φ1 φ2) φ3)) 1.
  apply ImpLImp; assumption.
} 

(* ImpLBox *)
assert(HImpLBox : ∀Γ2 Γ1, Γ1 ++ Γ2 = Γ -> {φ1 & {φ2 & {H2312 : ((⊗(list_to_set_disj ((rm (Implies (□ φ1) φ2) Γ))) • □ φ1 • φ2) ⊢φ1)
                                          & {H3: (list_to_set_disj (rm (Implies (□ φ1) φ2) Γ) • φ2 ⊢ φ) & (Implies (□ φ1) φ2) ∈ Γ2}}}} +
    {∀ φ1 φ2 (_ : ((⊗ (list_to_set_disj ((rm (Implies (□ φ1) φ2) Γ))) • □ φ1 • φ2) ⊢φ1))
                              (_: list_to_set_disj (rm (Implies (□ φ1) φ2) Γ) • φ2 ⊢ φ),
                               Implies (□ φ1) φ2 ∈ Γ2 → False}).
{
  induction Γ2 as [|θ Γ2]; intros Γ1 Heq.
  - right. intros φ1 φ2 _ _ Hin. inversion Hin.
  - assert(Heq' : (Γ1 ++ [θ]) ++ Γ2 = Γ) by (subst; auto with *).
    destruct (IHΓ2 (Γ1 ++  [θ]) Heq') as [(φ1 & φ2 & Hp1 & Hp2 & Hin)|Hf].
   + left. repeat eexists; eauto. now right.
   + destruct θ.
        5: destruct θ1.
        10 : {
        destruct (Hind  (θ2 :: (□θ1) :: map open_box (rm (Implies (□ θ1) θ2) Γ)) θ1)
          as [[Hp1 _] | Hf'].
        - order_tac. rewrite <- Permutation_middle. unfold rm.
          destruct form_eq_dec; [|tauto]. order_tac.
        - destruct (Hind  (θ2 :: rm (Implies (□ θ1) θ2) Γ) φ) as [[Hp2 _] | Hf''].
          + order_tac. rewrite <- Permutation_middle. unfold rm.
              destruct form_eq_dec; [|tauto]. order_tac.
          + left. repeat eexists; repeat l_tac; eauto. ms.
          + right; intros φ1 φ2 Hp1' Hp2 He; apply elem_of_list_In in He;
               destruct He as [Heq''| Hin]; [|apply elem_of_list_In in Hin; eapply Hf; eauto].
               inversion Heq''. subst. apply Hf''. peapply Hp2.
      - right; intros φ1 φ2 Hp1 Hp2 He; apply elem_of_list_In in He;
               destruct He as [Heq''| Hin]; [|apply elem_of_list_In in Hin; eapply Hf; eauto].
               inversion Heq''. subst. apply Hf'.
             (erewrite proper_Provable;  [| |reflexivity]);  [eapply Hp1|].
             repeat rewrite <- ?list_to_set_disj_env_add, list_to_set_disj_open_boxes. trivial.
        }
        all: (right; intros φ1 φ2 Hp1 Hp2 He; apply elem_of_list_In in He; destruct He as [Heq''| Hin];
     [discriminate|apply elem_of_list_In in Hin; eapply Hf; eauto]).
}
destruct (HImpLBox Γ [] (app_nil_l _)) as [(φ1 & φ2 & Hp1 & Hp2 & Hin)|HfImpLBox].
{ apply elem_of_list_to_set_disj in Hin.
  left. eexists; trivial. exhibit Hin 0. rw (list_to_set_disj_rm Γ(Implies (□ φ1) φ2)) 1.
  apply ImpBox; assumption.
}

(* All the sequent rules have been applied *)
clear Hind HImpLImp HImpLBox.
right.
Ltac eqt := match goal with | H : (_ • ?φ) = list_to_set_disj ?Γ |- _ =>
  let Heq := fresh "Heq" in assert(Heq := H);
  assert(Hinφ : φ ∈ Γ) by (apply elem_of_list_to_set_disj; setoid_rewrite <- H; ms);
  apply env_equiv_eq, env_add_inv', symmetry in Heq; rewrite list_to_set_disj_rm in Heq end.
intro Hp. inversion Hp; subst; try eqt; eauto 2.
- eapply HAndR; eauto.
- eapply HImpR; eauto.
- eapply HImpLVar; eauto. apply elem_of_list_to_set_disj. setoid_rewrite <- H; ms.
- eapply HfImpl; eauto.
  + now rw Heq 1.
  + now rw Heq 1.
- eapply HfImpLBox; eauto.
  + now rw (proper_open_boxes _ _ Heq) 2.
  + now rw Heq 1.
Defined.


(** The function [Provable_dec] decides whether a sequent is provable.
   The proof is essentially the same as the definition of [Proof_tree_dec].
 *)
Proposition Provable_dec Γ φ :
  (exists _ : list_to_set_disj Γ ⊢ φ, True) + (forall H : list_to_set_disj  Γ ⊢ φ, False).
Proof.
remember (Γ, φ) as pe.
replace Γ with pe.1 by now inversion Heqpe.
replace φ with pe.2 by now inversion Heqpe. clear Heqpe Γ φ.
revert pe.
refine  (@well_founded_induction _ _ wf_pointed_order _ _).
intros (Γ& φ) Hind; simpl.
assert(Hind' := λ Γ' φ', Hind(Γ', φ')). simpl in Hind'. clear Hind. rename Hind' into Hind.

case (decide (⊥ ∈ Γ)); intro Hbot.
{ left. eexists; trivial. apply elem_of_list_to_set_disj in Hbot. exhibit Hbot 0. apply ExFalso. }
assert(HAndR : {φ1 & {φ2 & φ = (And φ1 φ2)}} + {∀ φ1 φ2, φ ≠ (And φ1 φ2)}) by (destruct φ; eauto).
assert(Hvar : {p & φ = Var p & Var p ∈ Γ} + {∀ p, φ = Var p -> Var p ∈ Γ -> False}). {
  destruct φ. 2-6: right; auto with *.
  case (decide (Var v ∈ Γ)); intro Hin.
  - left. exists v; trivial.
  - right; auto with *. }
destruct Hvar as [[p Heq Hp]|Hvar].
{ subst. left. eexists; trivial. apply elem_of_list_to_set_disj in Hp. exhibit Hp 0. apply Atom. }

assert(HAndL : {ψ1 & {ψ2 & (And ψ1 ψ2) ∈ Γ}} + {∀ ψ1 ψ2, (And ψ1 ψ2) ∈ Γ -> False}). {
  pose (fA := (fun θ => match θ with |And _ _ => true | _ => false end)).
  destruct (exists_dec fA Γ) as [(θ & Hin & Hθ) | Hf].
  - left. subst fA. destruct θ. 3: { eexists. eexists. apply elem_of_list_In. eauto. }
    all:  auto with *.
  - right. intros ψ1 ψ2 Hψ. rewrite elem_of_list_In in Hψ. apply Hf in Hψ. subst fA. simpl in Hψ. tauto.
}
destruct HAndL as [(ψ1 & ψ2 & Hin)|HAndL].
{ destruct (Hind (ψ1 :: ψ2 :: rm (And ψ1 ψ2) Γ) φ) as [Hp' | Hf]. order_tac.
  - left. destruct Hp' as [Hp' _]. eexists; trivial. apply elem_of_list_to_set_disj in Hin.  
    exhibit Hin 0.
    rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (list_to_set_disj_rm _ _)) _ _ eq_refl).
    apply AndL. peapply Hp'.
 - right. intro Hf'. apply Hf.
   rw (symmetry (list_to_set_disj_env_add (ψ2 :: rm (And ψ1 ψ2) Γ) ψ1)) 0.
   rw (symmetry (list_to_set_disj_env_add (rm (And ψ1 ψ2) Γ) ψ2)) 1.
   exch 0. apply AndL_rev.
   rw (symmetry (list_to_set_disj_rm Γ(And ψ1 ψ2))) 1.
   apply elem_of_list_to_set_disj in Hin.
   pose (difference_singleton (list_to_set_disj Γ) (And ψ1 ψ2)).
   peapply Hf'.
}
assert(HImpR : {φ1 & {φ2 & φ = (Implies φ1 φ2)}} + {∀ φ1 φ2, φ ≠ (Implies φ1 φ2)}) by (destruct φ; eauto).
destruct HImpR as [(φ1 & φ2 & Heq) | HImpR].
{ subst.
  destruct (Hind (φ1 :: Γ) φ2) as [Hp1| H1]. order_tac.
  - left. destruct Hp1 as [Hp1 _]. eexists; trivial. apply ImpR. peapply Hp1.
  - right. intro Hf. apply H1. apply ImpR_rev in Hf. peapply Hf.
}
assert(HImpLVar : {p & {ψ & Var p ∈ Γ /\ (Implies (Var p) ψ) ∈ Γ}} + 
                                 {∀ p ψ, Var p ∈ Γ -> (Implies (Var p) ψ) ∈ Γ -> False}). {
  pose (fIp :=λ p θ, match θ with | Implies (Var q) _ => if decide (p = q) then true else false | _ => false end).
  pose (fp:= (fun θ => match θ with |Var p => if (exists_dec (fIp p) Γ) then true else false | _ => false end)).
  destruct (exists_dec fp Γ) as [(θ & Hin & Hθ) | Hf].
  - left. subst fp. destruct θ. 2-6: auto with *.
    case exists_dec as [(ψ &Hinψ & Hψ)|] in Hθ; [|auto with *]. 
    unfold fIp in Hψ. destruct ψ.  1-4, 6: auto with *.
    destruct ψ1. 2-6: auto with *. case decide in Hψ; [|auto with *].
    subst. apply elem_of_list_In in Hinψ, Hin.
    do 2 eexists. split; eauto.
  - right. intros p ψ Hp Hψ. rewrite elem_of_list_In in Hp, Hψ. apply Hf in Hp. subst fp fIp.
    simpl in Hp. case exists_dec as [|Hf'] in Hp. auto with *.
    apply (Hf' _ Hψ). rewrite decide_True; trivial. auto with *.
}
destruct HImpLVar as [[p [ψ [Hinp Hinψ]]]|HImpLVar].
{ apply elem_of_list_to_set_disj in Hinp.
  apply elem_of_list_to_set_disj in Hinψ.
  assert(Hinp' : Var p ∈ (list_to_set_disj Γ ∖ {[Implies p ψ]} : env))
    by (apply in_difference; [discriminate| assumption]).
  destruct (Hind (ψ :: rm (Implies (Var p) ψ) Γ) φ) as [Hp|Hf]. order_tac.
  - left. destruct Hp as [Hp _]. eexists; trivial. exhibit Hinψ 0.
     exhibit Hinp' 1. apply ImpLVar.
     rw (symmetry (difference_singleton (list_to_set_disj Γ ∖ {[Implies p ψ]}) (Var p) Hinp')) 1.
     rw (list_to_set_disj_rm Γ(Implies p ψ)) 1. l_tac. exact Hp.
  - right. intro Hf'. apply Hf.
     rw (symmetry (list_to_set_disj_env_add (rm (Implies p ψ) Γ) ψ)) 0.
     rw (symmetry (list_to_set_disj_rm Γ(Implies p ψ))) 1.
     exhibit Hinp' 1. apply ImpLVar_rev.
     rw (symmetry (difference_singleton _ _ Hinp')) 1.
     rw (symmetry (difference_singleton _ _ Hinψ)) 0.
     exact Hf'.
}
assert(HImpLAnd : {φ1 & {φ2 & {φ3 &  (Implies (And φ1 φ2) φ3) ∈ Γ}}} +
                                 {∀ φ1 φ2 φ3, (Implies (And φ1 φ2) φ3) ∈ Γ -> False}). {
    pose (fII := (fun θ => match θ with |Implies (And _ _) _ => true | _ => false end)).
   destruct (exists_dec fII Γ) as [(θ & Hin & Hθ) | Hf].
    - left.  subst fII. destruct θ. 1-4, 6: auto with *.
      destruct θ1. 1-2,4-6: auto with *. do 3 eexists; apply elem_of_list_In; eauto.
    - right. intros ψ1 ψ2 ψ3 Hψ. rewrite elem_of_list_In in Hψ. apply Hf in Hψ. subst fII. simpl in Hψ. tauto.
}
destruct HImpLAnd as [(φ1&φ2&φ3&Hin)|HImpLAnd].
{ apply elem_of_list_to_set_disj in Hin.
  destruct (Hind (Implies φ1 (Implies φ2 φ3) :: rm (Implies (And φ1 φ2) φ3) Γ) φ) as [Hp|Hf]. order_tac.
  - left. destruct Hp as [Hp _]. eexists; trivial. exhibit Hin 0. apply ImpLAnd.
     rw (list_to_set_disj_rm Γ(Implies (And φ1 φ2) φ3)) 1. l_tac. exact Hp.
  - right. intro Hf'. apply Hf.
     rw (symmetry (list_to_set_disj_env_add (rm (Implies (And φ1 φ2) φ3) Γ) (Implies φ1 (Implies φ2 φ3)))) 0.
     rw (symmetry (list_to_set_disj_rm Γ(Implies (And φ1 φ2) φ3))) 1.
     apply ImpLAnd_rev.
     rw (symmetry (difference_singleton _ _ Hin)) 0. exact Hf'.
}
assert(HImpLOr : {φ1 & {φ2 & {φ3 &  (Implies (Or φ1 φ2) φ3) ∈ Γ}}} +
                                 {∀ φ1 φ2 φ3, (Implies (Or φ1 φ2) φ3) ∈ Γ -> False}). {
    pose (fII := (fun θ => match θ with |Implies (Or _ _) _ => true | _ => false end)).
   destruct (exists_dec fII Γ) as [(θ & Hin & Hθ) | Hf].
    - left. subst fII. destruct θ. 1-4, 6: auto with *.
      destruct θ1. 1-3, 5-6: auto with *. do 3 eexists; apply elem_of_list_In; eauto.
    - right. intros ψ1 ψ2 ψ3 Hψ. rewrite elem_of_list_In in Hψ. apply Hf in Hψ. subst fII. simpl in Hψ. tauto.
}
destruct HImpLOr as [(φ1&φ2&φ3&Hin)|HImpLOr].
{ apply elem_of_list_to_set_disj in Hin.
  destruct (Hind (Implies φ2 φ3 :: Implies φ1 φ3 :: rm (Implies (Or φ1 φ2) φ3) Γ) φ) as [Hp|Hf]. order_tac.
  - left. destruct Hp as [Hp _]. eexists; trivial. exhibit Hin 0. apply ImpLOr.
     rw (list_to_set_disj_rm Γ(Implies (Or φ1 φ2) φ3)) 2. do 2 l_tac. exact Hp.
  - right. intro Hf'. apply Hf.
     rw (symmetry (list_to_set_disj_env_add ( Implies φ1 φ3 :: rm (Implies (Or φ1 φ2) φ3) Γ) (Implies φ2 φ3))) 0.
     rw (symmetry (list_to_set_disj_env_add (rm (Implies (Or φ1 φ2) φ3) Γ) (Implies φ1 φ3))) 1.
     rw (symmetry (list_to_set_disj_rm Γ(Implies (Or φ1 φ2) φ3))) 2.
     apply ImpLOr_rev.
     rw (symmetry (difference_singleton _ _ Hin)) 0. exact Hf'.
}
assert(HOrL : {ψ1 & {ψ2 & (Or ψ1 ψ2) ∈ Γ}} + {∀ ψ1 ψ2, (Or ψ1 ψ2) ∈ Γ -> False}). {
  pose (fA := (fun θ => match θ with |Or _ _ => true | _ => false end)).
  destruct (exists_dec fA Γ) as [(θ & Hin & Hθ) | Hf].
  - left. subst fA. destruct θ. 4: { eexists. eexists. apply elem_of_list_In. eauto. }
    all:  auto with *.
  - right. intros ψ1 ψ2 Hψ. rewrite elem_of_list_In in Hψ. apply Hf in Hψ. subst fA. simpl in Hψ. tauto.
}
destruct HAndR as [(φ1 & φ2 & Heq) | HAndR].
{ subst.
  destruct (Hind Γ φ1) as [Hp1| H1]. order_tac.
  - destruct (Hind Γ φ2) as [Hp2| H2]. order_tac.
    + left. destruct Hp1, Hp2. eexists; trivial. apply AndR; assumption.
    + right. intro Hp. apply AndR_rev in Hp. tauto.
  - right. intro Hp. apply AndR_rev in Hp. tauto.
}
destruct HOrL as [(ψ1 & ψ2 & Hin)|HOrL].
{ apply elem_of_list_to_set_disj in Hin.
  destruct (Hind (ψ1 :: rm (Or ψ1 ψ2) Γ) φ) as [Hp1| Hf]. order_tac.
  - destruct (Hind (ψ2 :: rm (Or ψ1 ψ2) Γ) φ) as [Hp2| Hf]. order_tac.
    + left. destruct Hp1 as [Hp1 _]. destruct Hp2 as [Hp2 _]. eexists; trivial. exhibit Hin 0.
         rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (list_to_set_disj_rm _ _)) _ _ eq_refl).
         apply OrL. peapply Hp1. peapply Hp2.
    + right; intro Hf'. assert(Hf'' :list_to_set_disj (rm (Or ψ1 ψ2) Γ) • Or ψ1 ψ2 ⊢ φ). {
          rw (symmetry (list_to_set_disj_rm Γ(Or ψ1 ψ2))) 1.
          pose (difference_singleton (list_to_set_disj Γ) (Or ψ1 ψ2)). peapply Hf'.
         }
        apply OrL_rev in Hf''. apply Hf. peapply Hf''.
  - right; intro Hf'. assert(Hf'' :list_to_set_disj (rm (Or ψ1 ψ2) Γ) • Or ψ1 ψ2 ⊢ φ). {
          rw (symmetry (list_to_set_disj_rm Γ(Or ψ1 ψ2))) 1.
          pose (difference_singleton (list_to_set_disj Γ) (Or ψ1 ψ2)). peapply Hf'.
         }
        apply OrL_rev in Hf''. apply Hf. peapply Hf''.1.
}
(* non invertible right rules *)
assert(HOrR1 : {φ1 & {φ2 & (exists (_ : list_to_set_disj Γ ⊢ φ1), φ = (Or φ1 φ2))}} +
                       {∀ φ1 φ2, ∀ (H : list_to_set_disj Γ ⊢ φ1), φ = (Or φ1 φ2) -> False}).
{
  destruct φ. 4: { destruct (Hind Γ φ1)as [Hp|Hf]. order_tac.
  - left. do 2 eexists. destruct Hp as [Hp _]. eexists; eauto.
  - right. intros ? ? Hp Heq. inversion Heq. subst. tauto.
  }
  all: right; auto with *.
}
destruct HOrR1 as [(φ1 & φ2 & Hp)| HOrR1].
{ left. destruct Hp as (Hp & Heq). subst. eexists; trivial. apply OrR1, Hp. }
assert(HOrR2 : {φ1 & {φ2 & exists (_ : list_to_set_disj Γ ⊢ φ2), φ = (Or φ1 φ2)}} +
                       {∀ φ1 φ2, ∀ (H : list_to_set_disj Γ ⊢ φ2), φ = (Or φ1 φ2) -> False}).
{
  destruct φ. 4: { destruct (Hind Γ φ2)as [Hp|Hf]. order_tac.
  - left. do 2 eexists. destruct Hp as [Hp _]; eauto.
  - right. intros ? ? Hp Heq. inversion Heq. subst. tauto.
  }
  all: right; auto with *.
}
destruct HOrR2 as [(φ1 & φ2 & Hp)| HOrR2 ].
{ left. destruct Hp as [Hp Heq]. subst. eexists; trivial. apply OrR2, Hp. }
assert(HBoxR : {φ' & exists (_ : (⊗ (list_to_set_disj Γ) • □ φ' ⊢ φ')),  φ = (□ φ')} +
                       {∀ φ', ∀ (H : ⊗ (list_to_set_disj Γ) • □ φ' ⊢ φ'), φ = (□ φ') -> False}).
{
  destruct φ. 6: { destruct (Hind  ((□ φ) :: map open_box Γ) φ)as [Hp|Hf]. order_tac.
  - left. eexists. destruct Hp as [Hp _]. eexists; eauto. l_tac. exact Hp.
  - right. intros ? Hp Heq. inversion Heq. subst. apply Hf.
     rw (symmetry (list_to_set_disj_env_add (map open_box Γ) (□ φ'))) 0.
     rewrite <- list_to_set_disj_open_boxes. exact Hp.
  }
  all: right; auto with *.
}
destruct HBoxR as [(φ' & Hp)| HBoxR ].
{ left. destruct Hp as [Hp Heq]. subst. eexists; trivial. apply BoxR, Hp. }
assert(Hempty: ∀ (Δ : env) φ,((Δ • φ) = ∅) -> False).
{
  intros Δ θ Heq. assert (Hm:= multiplicity_empty θ).
  unfold base.empty in *.
  rewrite <- Heq, union_mult, singleton_mult_in in Hm by trivial. lia.
}
(* non invertible left rules *)
assert(HImpLImp : ∀Γ2 Γ1, Γ1 ++ Γ2 = Γ -> {φ1 & {φ2 & {φ3 & exists (_ : (list_to_set_disj (rm (Implies (Implies φ1 φ2) φ3) Γ) • (Implies φ2 φ3)) ⊢ (Implies φ1 φ2)),
                                          exists (_: list_to_set_disj (rm (Implies (Implies φ1 φ2) φ3) Γ) • φ3 ⊢ φ), (Implies (Implies φ1 φ2) φ3) ∈ Γ2}}} +
    {∀ φ1 φ2 φ3 (_ : (list_to_set_disj (rm (Implies (Implies φ1 φ2) φ3) Γ) • (Implies φ2 φ3)) ⊢ (Implies φ1 φ2))
                              (_: list_to_set_disj (rm (Implies (Implies φ1 φ2) φ3) Γ) • φ3 ⊢ φ),
                               Implies (Implies φ1 φ2) φ3 ∈ Γ2 → False}).
{
  induction Γ2 as [|θ Γ2]; intros Γ1 Heq.
  - right. intros φ1 φ2 φ3 _ _ Hin. inversion Hin.
  - assert(Heq' : (Γ1 ++ [θ]) ++ Γ2 = Γ) by (subst; auto with *).
    destruct (IHΓ2 (Γ1 ++  [θ]) Heq') as [(φ1 & φ2 & φ3 & Hp)|Hf].
   + left. do 3 eexists. destruct Hp as ( Hp1 & Hp2 & Hin). do 2 (eexists; eauto). now right.
   + destruct θ.
        5: destruct θ1.
        9 : {
        destruct (Hind  (Implies θ1_2 θ2 :: rm (Implies (Implies θ1_1 θ1_2) θ2) Γ) (Implies θ1_1 θ1_2))
          as [Hp1| Hf'].
        - order_tac. rewrite <- Permutation_middle. unfold rm.
          destruct form_eq_dec; [|tauto]. order_tac.
        - destruct (Hind  (θ2 :: rm (Implies (Implies θ1_1 θ1_2) θ2) Γ) φ) as [Hp2| Hf''].
          + order_tac. rewrite <- Permutation_middle. unfold rm.
               destruct form_eq_dec; [|tauto]. order_tac.
          + left. do 3 eexists. destruct Hp1 as [Hp1 _]. destruct Hp2 as [Hp2 _].
              eexists; try l_tac; eauto. ms.
          + right; intros φ1 φ2 φ3 Hp1' Hp2 He; apply elem_of_list_In in He;
               destruct He as [Heq''| Hin]; [|apply elem_of_list_In in Hin; eapply Hf; eauto].
               inversion Heq''. subst. apply Hf''. peapply Hp2.
      - right; intros φ1 φ2 φ3 Hp1 Hp2 He; apply elem_of_list_In in He;
               destruct He as [Heq''| Hin]; [|apply elem_of_list_In in Hin; eapply Hf; eauto].
               inversion Heq''. subst. apply Hf'. peapply Hp1.
        }
        all: (right; intros φ1 φ2 φ3 Hp1 Hp2 He; apply elem_of_list_In in He; destruct He as [Heq''| Hin];
     [discriminate|apply elem_of_list_In in Hin; eapply Hf; eauto]).
}
destruct (HImpLImp Γ [] (app_nil_l _)) as [(φ1 & φ2 & φ3 & Hp1)|HfImpl].
{ left. destruct Hp1 as (Hp1 & Hp2 & Hin). eexists; trivial.
  apply elem_of_list_to_set_disj in Hin. exhibit Hin 0.
  rw (list_to_set_disj_rm Γ(Implies (Implies φ1 φ2) φ3)) 1.
  apply ImpLImp; assumption.
} 
(* ImpBox *)
assert(HImpLBox : ∀Γ2 Γ1, Γ1 ++ Γ2 = Γ -> {φ1 & {φ2 & exists (_ : (⊗(list_to_set_disj ((rm (Implies (□ φ1) φ2) Γ))) • □ φ1 • φ2) ⊢φ1),
                                          exists (_ : list_to_set_disj (rm (Implies (□ φ1) φ2) Γ) • φ2 ⊢ φ),
                                          (Implies (□ φ1) φ2) ∈ Γ2}} +
    {∀ φ1 φ2 (_ : ((⊗ (list_to_set_disj ((rm (Implies (□ φ1) φ2) Γ))) • □ φ1 • φ2) ⊢φ1))
                              (_: list_to_set_disj (rm (Implies (□ φ1) φ2) Γ) • φ2 ⊢ φ),
                               Implies (□ φ1) φ2 ∈ Γ2 → False}).
{
  induction Γ2 as [|θ Γ2]; intros Γ1 Heq.
  - right. intros φ1 φ2 _ _ Hin. inversion Hin.
  - assert(Heq' : (Γ1 ++ [θ]) ++ Γ2 = Γ) by (subst; auto with *).
    destruct (IHΓ2 (Γ1 ++  [θ]) Heq') as [(φ1 & φ2 & Hp1)|Hf].
   + left. do 2 eexists. destruct Hp1 as (Hp1 & Hp2 & Hin). do 2 (eexists; eauto). now right.
   + destruct θ.
        5: destruct θ1.
        10 : {
        destruct (Hind  (θ2 :: (□θ1) :: map open_box (rm (Implies (□ θ1) θ2) Γ)) θ1)
          as [Hp1|Hf'].
        - order_tac. rewrite <- Permutation_middle. unfold rm.
          destruct form_eq_dec; [|tauto]. order_tac.
        - destruct (Hind  (θ2 :: rm (Implies (□ θ1) θ2) Γ) φ) as [Hp2| Hf''].
          + order_tac. rewrite <- Permutation_middle. unfold rm.
              destruct form_eq_dec; [|tauto]. order_tac.
          + left. do 2 eexists. destruct Hp1 as [Hp1 _]. destruct Hp2 as [Hp2 _].
               repeat eexists; repeat l_tac; eauto. ms.
          + right; intros φ1 φ2 Hp1' Hp2 He; apply elem_of_list_In in He;
               destruct He as [Heq''| Hin]; [|apply elem_of_list_In in Hin; eapply Hf; eauto].
               inversion Heq''. subst. apply Hf''. peapply Hp2.
      - right; intros φ1 φ2 Hp1 Hp2 He; apply elem_of_list_In in He;
               destruct He as [Heq''| Hin]; [|apply elem_of_list_In in Hin; eapply Hf; eauto].
               inversion Heq''. subst. apply Hf'.
             (erewrite proper_Provable;  [| |reflexivity]);  [eapply Hp1|].
             repeat rewrite <- ?list_to_set_disj_env_add, list_to_set_disj_open_boxes. trivial.
        }
        all: (right; intros φ1 φ2 Hp1 Hp2 He; apply elem_of_list_In in He; destruct He as [Heq''| Hin];
     [discriminate|apply elem_of_list_In in Hin; eapply Hf; eauto]).
}
destruct (HImpLBox Γ [] (app_nil_l _)) as [(φ1 & φ2 & Hp1)|HfImpLBox].
{ left. destruct Hp1 as (Hp1 & Hp2 & Hin). eexists; trivial.
  apply elem_of_list_to_set_disj in Hin. exhibit Hin 0.
  rw (list_to_set_disj_rm Γ(Implies (□ φ1) φ2)) 1.
  apply ImpBox; assumption.
}
clear Hind HImpLImp HImpLBox.
right.
intro Hp. inversion Hp; subst; try eqt; eauto 2.
- eapply HAndR; eauto.
- eapply HImpR; eauto.
- eapply HImpLVar; eauto. apply elem_of_list_to_set_disj. setoid_rewrite <- H; ms.
- eapply HfImpl; eauto.
  + now rw Heq 1.
  + now rw Heq 1.
- eapply HfImpLBox; eauto.
  + now rw (proper_open_boxes _ _ Heq) 2.
  + now rw Heq 1.
Defined.

Global Infix "⊢?" := Provable_dec (at level 80).

Lemma Provable_dec_of_Prop Γ φ: (∃ _ : list_to_set_disj Γ ⊢ φ, True) -> (list_to_set_disj Γ ⊢ φ).
Proof.
destruct (Proof_tree_dec Γ φ) as [[Hφ1' _] | Hf']. tauto.
intros Hf. exfalso. destruct Hf as [Hf _]. tauto.
Qed.
