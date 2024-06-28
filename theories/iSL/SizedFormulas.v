Require Import Formulas.
From stdpp Require Import countable strings.


Local Open Scope string_scope.

Section Definitions.

(* formula with a counter *)
Inductive nform {p : variable}: nat -> Type :=
| nVar : forall (v : variable), nform (if decide (v = p) then 1 else 0)
| nBot : nform 0
| nAnd : forall {n m }, nform n -> nform m -> nform (n + m)
| nOr : forall {n m }, nform n -> nform m -> nform (n + m)
| nImplies : forall {n m }, nform n -> nform m -> nform (n + m)
| nBox : forall {n}, nform n -> nform n
.

(* erase the tally *)
Fixpoint form_of_nform {p n} (nf : @nform p n) := match nf with
| nVar v => Var v
| nBot => Bot
| @nAnd _  n m φ ψ => And (form_of_nform φ) (form_of_nform ψ)
| @nOr _ _n m φ ψ => Or (form_of_nform φ) (form_of_nform ψ)
| @nImplies _ n m φ ψ => Implies (form_of_nform φ) (form_of_nform ψ)
| @nBox _ n φ => Box (form_of_nform φ)
end.

Definition form_of_nform' {p} (nφ : {n & @nform p n}) := form_of_nform (projT2 nφ).

(*
Program Definition nform_irr_n {p n n'} (Heq : n = n') (φ: @nform p n): @nform p n' := φ.
Next Obligation.
intros. exact Heq.
Defined.
*)

Definition nform_of_form {p} (φ : form) : {n & {φ' : @nform p n | form_of_nform φ' = φ}}.
induction φ.
Proof.
- exists (if decide (v = p) then 1 else 0). exists (nVar v). trivial.
- exists 0. exists nBot; trivial.
- destruct IHφ1 as (n & φ' & Hφ'). destruct IHφ2 as (m & ψ' & Hψ').
  exists (n + m). exists (nAnd φ' ψ'). subst. trivial.
- destruct IHφ1 as (n & φ' & Hφ'). destruct IHφ2 as (m & ψ' & Hψ').
  exists (n + m). exists (nOr φ' ψ'). subst. trivial.
- destruct IHφ1 as (n & φ' & Hφ'). destruct IHφ2 as (m & ψ' & Hψ').
  exists (n + m). exists (nImplies φ' ψ'). subst. trivial.
- destruct IHφ as (n & φ' & Hφ').
  exists n. exists (nBox φ'). subst. trivial.
Defined.

(*
Lemma nform_irr {p n n'} (φ : nform n) (φ' : nform n'):
  @form_of_nform p n φ = @form_of_nform p n' φ' -> n = n'.
Proof.
revert n' φ'; induction φ; intros n' φ' Heq; destruct φ';
simpl in Heq; inversion Heq; clear Heq; subst; trivial.
- apply f_equal2_plus; [ eapply IHφ1 | eapply IHφ2]; eassumption.
- apply f_equal2_plus; [ eapply IHφ1 | eapply IHφ2]; eassumption.
- apply f_equal2_plus; [ eapply IHφ1 | eapply IHφ2]; eassumption.
- eapply IHφ; eassumption.
Qed.
*)

Lemma form_of_nform_dec p(nφ : {n & @nform p n}) (nφ'  : {n' & @nform p n'})
  (Heq : form_of_nform (projT2 nφ') = form_of_nform (projT2 nφ)): nφ =  nφ'.
Proof.
revert nφ' Heq. destruct nφ as [n φ]. induction φ; intros  [n' φ'] Heq;
simpl in *;
destruct φ'; try solve[subst; simpl in *; inversion Heq; subst].
- subst. simpl in Heq; inversion Heq; subst; trivial.
- simpl in Heq; inversion Heq; subst; trivial.
- simpl in Heq. inversion Heq as [[H0 H1]].
  specialize (IHφ1 (existT n0 φ'1) H0).  specialize (IHφ2 (existT m0 φ'2) H1).
  inversion IHφ1; inversion IHφ2; trivial.
- simpl in Heq. inversion Heq as [[H0 H1]].
  specialize (IHφ1 (existT n0 φ'1) H0).  specialize (IHφ2 (existT m0 φ'2) H1).
  inversion IHφ1; inversion IHφ2; trivial.
- simpl in Heq. inversion Heq as [[H0 H1]].
  specialize (IHφ1 (existT n0 φ'1) H0).  specialize (IHφ2 (existT m0 φ'2) H1).
  inversion IHφ1; inversion IHφ2; trivial.
- simpl in Heq. inversion Heq as [[Heq']]. specialize (IHφ (existT n0 φ') Heq').
  inversion IHφ. trivial.
Qed.

Definition pform p := {n : nat & @nform p n}.

Definition pform_of_nform {p n} (φ : @nform p n) : pform p := existT n φ.

Global Instance nform_eq_dec q : EqDecision (pform q).
Proof.
intros nφ nφ'.
case (decide (form_of_nform (projT2 nφ') = form_of_nform (projT2 nφ))).
- intro. left. destruct nφ as [n φ]; destruct nφ' as [n' φ']. now apply form_of_nform_dec.
- intro Hn. right. intro Hf. apply Hn. now case Hf.
Defined.

Lemma nform_occurs_in p n (φ : @nform p n) : occurs_in p (form_of_nform φ) <-> n <> 0.
Proof.
induction φ; simpl; split; try case decide; intros; subst;
 intuition auto; try lia;
(try destruct n; try destruct m; auto with *).
Qed.

Definition p_open_box {p} (nφ : pform p) : pform p :=match projT2 nφ with
| nBox φ0 => existT _ φ0
| _ => nφ end.

Definition p_open_boxes {p} := map (@p_open_box p).

End Definitions.

Global Infix "∧n" := (nAnd) (at level 80).
Global Infix "∨n" := (nOr) (at level 85).
Global Infix "→n" := (nImplies) (at level 99).
Notation "'□n' φ" := (nBox φ) (at level 75, φ at level 75).
Notation "'□⁻¹' Δ" := (p_open_boxes Δ) (at level 75, Δ at level 75).
