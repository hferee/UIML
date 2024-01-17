Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import GLS_calcs.

Require Import GLS_termination_measure.
Require Import GLS_exch.
Require Import GLS_ctr.
Require Import GLS_wkn.
Require Import GLS_dec.
Require Import GLS_inv_ImpR_ImpL.
Require Import GLS_additive_cut.

Inductive CutRule : rlsT Seq :=
  | CutRule_I : forall A Γ0 Γ1 Δ0 Δ1,
          CutRule [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1) ; (Γ0 ++ A :: Γ1, Δ0 ++ Δ1)]
                    (Γ0 ++ Γ1, Δ0 ++ Δ1)
.

Inductive GLS_cut_rules : rlsT  Seq :=
  | GLS_woc : forall ps c, GLS_rules ps c -> GLS_cut_rules ps c
  | iGLS_cut : forall ps c, CutRule ps c -> GLS_cut_rules ps c
.

Definition GLS_cut_prv s := derrec GLS_cut_rules (fun _ => False) s.
Definition GLS_cut_drv s := derrec GLS_cut_rules (fun _ => True) s.

Theorem GLS_cut_elimination : forall s, (GLS_cut_prv s) -> (GLS_prv s).
Proof.
intros s D.
apply derrec_all_rect with
(Q:= fun x => (GLS_prv x))
in D ; auto.
- intros. inversion H.
- intros ps concl rule ders IH. inversion rule.
  * subst. apply derI with (ps:=ps) ; auto. apply dersrec_forall. intros. epose (@ForallTD_forall _ _ _ IH c H) ; auto.
  * subst. inversion H. subst. apply GLS_cut_adm with (A:=A).
    epose (@ForallTD_forall _ _ _ IH (Γ0 ++ Γ1, Δ0 ++ A :: Δ1)). apply g. apply InT_eq.
    epose (@ForallTD_forall _ _ _ IH (Γ0 ++ A :: Γ1, Δ0 ++ Δ1)). apply g. apply InT_cons ; apply InT_eq.
Defined.