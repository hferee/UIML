Require Import List.
Export ListNotations.
Require Import Lia.
Require Import PeanoNat.

Require Import KS_calc.
Require Import KS_termination_measure.
Require Import KS_termination.
Require Import KS_exch.
Require Import KS_ctr.
Require Import KS_wkn.
Require Import KS_dec.
Require Import KS_inv_ImpR_ImpL.
Require Import KS_additive_cut.

Inductive CutRule : rlsT Seq :=
  | CutRule_I : forall A Γ0 Γ1 Δ0 Δ1,
          CutRule [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1) ; (Γ0 ++ A :: Γ1, Δ0 ++ Δ1)]
                    (Γ0 ++ Γ1, Δ0 ++ Δ1)
.

Inductive KS_cut_rules : rlsT  Seq :=
  | KS_woc : forall ps c, KS_rules ps c -> KS_cut_rules ps c
  | KS_cut : forall ps c, CutRule ps c -> KS_cut_rules ps c
.

Definition KS_cut_prv s := derrec KS_cut_rules (fun _ => False) s.
Definition KS_cut_drv s := derrec KS_cut_rules (fun _ => True) s.

Theorem KS_cut_elimination : forall s, (KS_cut_prv s) -> (KS_prv s).
Proof.
intros s D.
apply derrec_all_rect with
(Q:= fun x => (KS_prv x))
in D ; auto.
- intros. inversion H.
- intros ps concl rule ders IH. inversion rule.
  * subst. apply derI with (ps:=ps) ; auto. apply dersrec_forall. intros. pose (ForallTD_forall IH H) ; auto.
  * subst. inversion H. subst. apply KS_cut_adm with (A:=A).
    pose (ForallTD_forall IH). apply k ; apply InT_eq.
    pose (ForallTD_forall IH). apply k ; apply InT_cons ; apply InT_eq.
Defined.