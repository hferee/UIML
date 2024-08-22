Require Import ISL.Environments ISL.Sequents ISL.SequentProps ISL.Cut ISL.Optimizations.

(* Normalises a large disjunctions flattening them to the right. It assumes
that there are no disjuctions on the left of any of the input formulas, i.e.
φ and ψ cannot be of the form ((... ∨ ... ) ∨ ...). Since this function is called 
with the inputs previously simplified (see `simp`) this invariant is assured. *)
Fixpoint simp φ :=
match φ with
  | φ ∨ ψ => make_disj (simp φ) (simp ψ)
  | φ ∧ ψ => make_conj (simp φ) (simp ψ)
  | φ → ψ => make_impl (simp φ) (simp ψ)
  | □ φ => □ (simp φ)
  | _ => φ
end.


Lemma simp_equiv_or_L φ ψ : 
  (φ  ≼ simp φ) -> (ψ  ≼ simp ψ) ->
  (φ ∨ ψ) ≼ simp (φ ∨ ψ).
Proof.
intros Hφ Hψ.
eapply weak_cut; [apply or_congruence; [apply Hφ | apply Hψ] | apply make_disj_equiv_L; apply generalised_axiom].
Qed.

Lemma simp_equiv_or_R φ ψ: 
  (simp φ ≼ φ) -> (simp ψ ≼ ψ) ->
  simp (φ ∨ ψ) ≼ (φ ∨ ψ).
Proof.
intros Hφ Hψ.
eapply weak_cut; [ apply make_disj_equiv_R; apply generalised_axiom | apply or_congruence; [apply Hφ | apply Hψ]].
Qed.

Lemma simp_equiv_or φ ψ: 
  (φ ≼ simp φ) * (simp φ ≼ φ) ->
  (ψ ≼ simp ψ) * (simp ψ ≼ ψ) ->
  ((φ ∨ ψ) ≼ simp (φ ∨ ψ)) * (simp (φ ∨ ψ) ≼ (φ ∨ ψ)).
Proof.
intros IHφ IHψ.
split; [ apply simp_equiv_or_L | apply simp_equiv_or_R]; try apply IHφ ; try apply IHψ.
Qed.


Lemma box_congr φ ψ:
  (φ ≼ ψ) ->  □ φ ≼  □ ψ.
Proof. 
intro H.
apply BoxR.
box_tac. apply weakening.
ms.
Qed.

Lemma simp_equiv_box φ:
  (φ ≼ simp φ) * (simp φ ≼ φ) ->
  (□ φ ≼ □ (simp φ)) * (□ (simp φ) ≼ □ φ).
Proof.
intro IHφ.
split; apply box_congr; apply IHφ.
Qed.

Lemma simp_equiv_and_L φ ψ : 
  (φ  ≼ simp φ) -> (ψ  ≼ simp ψ) -> (φ ∧ ψ) ≼ simp (φ ∧ ψ).
Proof.
intros Hφ Hψ.
eapply weak_cut; [apply and_congruence; [apply Hφ | apply Hψ] | apply make_conj_equiv_L; apply generalised_axiom].
Qed.

Lemma simp_equiv_and_R φ ψ : 
  (simp φ ≼ φ) -> (simp ψ ≼ ψ) -> simp (φ ∧ ψ) ≼  φ ∧ ψ.
Proof.
intros Hφ Hψ.
eapply weak_cut; [apply make_conj_equiv_R; apply generalised_axiom | apply and_congruence; [apply Hφ | apply Hψ]].
Qed.

Lemma simp_equiv_and φ ψ: 
  (φ ≼ simp φ) * (simp φ ≼ φ) ->
  (ψ ≼ simp ψ) * (simp ψ ≼ ψ) ->
  ((φ ∧ ψ) ≼ simp (φ ∧ ψ)) * (simp (φ ∧ ψ) ≼ (φ ∧ ψ)).
Proof.
intros IHφ IHψ.
split; [ apply simp_equiv_and_L | apply simp_equiv_and_R]; try apply IHφ ; try apply IHψ.
Qed.

Lemma simp_equiv_imp_L φ ψ : 
  (simp φ ≼ φ) -> (ψ ≼ simp ψ) ->
  (φ → ψ) ≼ simp (φ → ψ).
Proof.
intros HφR HψL.
simpl.
eapply weak_cut. apply make_impl_sound_R, generalised_axiom.
apply make_impl_sound_R, make_impl_sound_L.
apply ImpR. exch 0. apply ImpL.
- apply weakening. apply HφR.
- exch 0. apply weakening. apply HψL.
Qed.

Lemma simp_equiv_imp_R φ ψ : 
  (φ ≼ simp φ) -> (simp ψ ≼ ψ) ->
  simp (φ → ψ) ≼ (φ → ψ).
Proof.
intros HφR HψL.
simpl.
eapply weak_cut with (simp φ → simp ψ).
- apply make_impl_complete_R, generalised_axiom.
- apply ImpR. exch 0. apply ImpL.
  + apply weakening, HφR.
  + exch 0. apply weakening, HψL.
Qed.

Lemma simp_equiv_imp φ ψ: 
  (φ ≼ simp φ) * (simp φ ≼ φ) ->
  (ψ ≼ simp ψ) * (simp ψ ≼ ψ) ->
  ((φ → ψ) ≼ simp (φ → ψ)) * (simp (φ → ψ) ≼ (φ → ψ)).
Proof.
intros IHφ IHψ.
split; [ apply simp_equiv_imp_L | apply simp_equiv_imp_R]; try apply IHφ ; try apply IHψ.
Qed.


Theorem simp_equiv φ : 
  (φ ≼ (simp φ)) * ((simp φ) ≼ φ).
Proof.
remember (weight φ) as w.
assert(Hle : weight φ  ≤ w) by lia.
clear Heqw. revert φ Hle.
induction w; intros φ Hle; [destruct φ ; simpl in Hle; lia|];
destruct φ; simpl; try (split ; apply generalised_axiom);
[eapply (simp_equiv_and φ1 φ2)|
 eapply (simp_equiv_or φ1 φ2)|
 eapply (simp_equiv_imp φ1 φ2)|
 eapply simp_equiv_box];
 apply IHw; 
match goal with
  | Hle : weight (?connector ?f1 ?f2) ≤ S ?w |- weight ?f1 ≤ ?w => simpl in Hle; lia
  | Hle : weight (?connector ?f1 ?f2) ≤ S ?w |- weight ?f2 ≤ ?w => simpl in Hle; lia
  | Hle : weight (□ ?f1) ≤ S ?w |- weight ?f1 ≤ ?w => simpl in Hle; lia
end.
Qed.

Require Import ISL.PropQuantifiers.

Definition E_simplified (p: variable) (ψ: form) := simp (Ef p ψ).
Definition A_simplified (p: variable) (ψ: form) := simp (Af p ψ).

Lemma bot_vars_incl V: vars_incl ⊥ V.
Proof.
  intros x H; unfold In; induction V; auto.
Qed.

Lemma top_vars_incl V: vars_incl ⊤ V.
Proof.
intros x H; unfold In; induction V; [simpl in H; tauto | auto].
Qed.


(* Solves simple variable inclusion goals *)
Ltac vars_incl_tac :=
repeat match goal with
| |- vars_incl ⊥ ?V => apply bot_vars_incl
| |- vars_incl ⊤ ?V => apply top_vars_incl

| H : vars_incl (?connector ?f1 ?f2) ?l |- vars_incl ?f1 ?l * vars_incl ?f2 ?l =>
        split; intros x H1; apply H; simpl; auto
| H : vars_incl (?connector ?f1 ?f2) ?l |- vars_incl ?f1 ?l =>
        intros x H1; apply H; simpl; auto
| H : vars_incl (?connector ?f1 ?f2) ?l |- vars_incl ?f2 ?l =>
        intros x H1; apply H; simpl; auto

| H: vars_incl ?f ?l |- vars_incl (_ ?f Bot) ?l =>  unfold vars_incl; simpl; intuition
| |- (vars_incl ?f1 ?l → vars_incl ?f2 ?l → vars_incl (?connector ?f1 ?f2) ?l) => 
        unfold vars_incl; simpl; intuition
| H1: vars_incl ?f1 ?l, H2: vars_incl ?f2 ?l |- vars_incl (?connector ?f1 ?f2) ?l => 
        unfold vars_incl; simpl; intuition

| |- _ * _  => split; [intro| intros]
end.

Lemma or_vars_incl φ ψ V:
  (vars_incl (Or φ ψ) V -> vars_incl φ V * vars_incl ψ V) *
  ( vars_incl φ V -> vars_incl ψ V -> vars_incl (Or φ ψ) V).
Proof. vars_incl_tac. Qed.


Lemma vars_incl_choose_disj φ ψ V:
  vars_incl (Or φ ψ) V -> vars_incl (choose_disj φ ψ) V.
Proof.
intros H.
unfold choose_disj.
destruct (obviously_smaller φ ψ); vars_incl_tac.
destruct (obviously_smaller ψ φ); vars_incl_tac. assumption.
Qed.

Lemma vars_incl_make_disj_equiv_disj φ ψ V:
  vars_incl (Or φ ψ) V -> vars_incl (φ ⊻ ψ) V.
Proof.
intros H.
unfold make_disj.
destruct ψ; try (now apply vars_incl_choose_disj);
destruct (obviously_smaller φ ψ1); try assumption; vars_incl_tac.
apply or_vars_incl.
- now apply (or_vars_incl _ (Or ψ1 ψ2)).
- apply or_vars_incl in H. 
  apply (or_vars_incl ψ1 _).
  apply H.
Qed.

Lemma vars_incl_make_disj φ ψ V :
  vars_incl φ V -> vars_incl ψ V -> vars_incl (make_disj φ ψ) V.
Proof.
generalize ψ.
induction φ; intro ψ0; destruct ψ0; intros Hφ Hψ;
try ( apply vars_incl_make_disj_equiv_disj; apply or_vars_incl; assumption).
Qed.


Lemma and_vars_incl φ ψ V:
  (vars_incl (And φ ψ) V -> vars_incl φ V * vars_incl ψ V) *
  (vars_incl φ V -> vars_incl ψ V -> vars_incl (And φ ψ) V).
Proof. vars_incl_tac. Qed.


Lemma vars_incl_choose_conj φ ψ V:
  vars_incl (And φ ψ) V -> vars_incl (choose_conj φ ψ) V.
Proof.
intros H.
unfold choose_conj. 
destruct (obviously_smaller φ ψ); vars_incl_tac; assumption.
Qed.


Lemma vars_incl_make_conj_equiv_conj φ ψ V:
  vars_incl (And φ ψ) V -> vars_incl (φ ⊼ ψ) V.
Proof.
intros H.
unfold make_conj.
destruct ψ; try (now apply vars_incl_choose_conj);
destruct (obviously_smaller φ ψ1); repeat case decide; intros; try discriminate; try assumption; vars_incl_tac;
try apply vars_incl_choose_conj; apply and_vars_incl;
vars_incl_tac; apply and_vars_incl in H; vars_tac; vars_incl_tac.
Qed.

Lemma vars_incl_make_conj φ ψ V :
  vars_incl φ V -> vars_incl ψ V -> vars_incl (make_conj φ ψ) V.
Proof.
generalize ψ.
induction φ; intro ψ0; destruct ψ0; intros Hφ Hψ;
try (apply vars_incl_make_conj_equiv_conj; apply and_vars_incl; assumption).
Qed.

Lemma vars_incl_make_impl φ ψ V :
  vars_incl φ V -> vars_incl ψ V -> vars_incl (make_impl φ ψ) V.
Proof.
intros Hφ Hψ x Hx. apply occurs_in_make_impl in Hx. intuition.
Qed.

Lemma vars_incl_simp φ V :
  vars_incl φ V -> vars_incl (simp φ) V.
Proof.
intro H.
induction φ; auto; simpl;
[ apply vars_incl_make_conj; [apply IHφ1| apply IHφ2]|
  apply vars_incl_make_disj; [apply IHφ1| apply IHφ2]| 
  apply vars_incl_make_impl; [apply IHφ1| apply IHφ2] 
]; vars_incl_tac.
Qed.


Lemma preorder_singleton  φ ψ:
  {[φ]} ⊢ ψ -> (φ ≼ ψ).
Proof.
intro H.
assert (H': ∅ • φ ⊢ ψ ) by peapply H.
apply H'.
Qed.

Theorem iSL_uniform_interpolation_simp p V: p ∉ V ->
  ∀ φ, vars_incl φ (p :: V) ->
  (vars_incl (E_simplified p φ) V)
  * (φ ≼ E_simplified p φ)
  * (∀ ψ, vars_incl ψ V -> (φ ≼ ψ) -> E_simplified p φ ≼ ψ)
  * (vars_incl (A_simplified p φ) V)
  * (A_simplified p φ ≼ φ)
  * (∀ θ, vars_incl θ V -> (θ ≼ φ) -> (θ ≼ A_simplified p φ)).
Proof.
intros Hp φ Hvarsφ.
assert (Hislφ : 
    (vars_incl (Ef p φ) V)
  * ({[φ]} ⊢ (Ef p φ))
  * (∀ ψ, vars_incl ψ V -> {[φ]} ⊢ ψ -> {[Ef p φ]} ⊢ ψ)
  * (vars_incl (Af p φ) V)
  * ({[Af p φ]} ⊢ φ)
  * (∀ θ, vars_incl θ V -> {[θ]} ⊢ φ -> {[θ]} ⊢ Af p φ)) by 
    (apply iSL_uniform_interpolation; [apply Hp | apply Hvarsφ]).
repeat split.
  + intros Hx.
    eapply vars_incl_simp.
    apply Hislφ.
  + eapply weak_cut.
    * assert (Hef: ({[φ]} ⊢ Ef p φ)) by apply Hislφ.
      apply preorder_singleton.
      apply Hef.
    * apply (simp_equiv  (Ef p φ)).
  + intros ψ Hψ Hyp.
    eapply weak_cut.
    * apply (simp_equiv  (Ef p φ)).
    * assert (Hef: ({[Ef p φ]} ⊢ ψ)) by (apply Hislφ; [apply Hψ | peapply Hyp]).
      apply preorder_singleton.
      apply Hef.
  + intros Hx.
    eapply vars_incl_simp.
    apply Hislφ.
  + eapply weak_cut.
    * apply (simp_equiv  (Af p φ)).
    * apply preorder_singleton.
      apply Hislφ.
  + intros ψ Hψ Hyp.
    eapply weak_cut.
    * assert (Hef: ({[ψ]} ⊢ Af p φ)) by (apply Hislφ; [apply Hψ | peapply Hyp]).
      apply preorder_singleton.
      apply Hef.
    * apply (simp_equiv  (Af p φ)).
Qed.



Require Import String.
Local Open Scope string_scope.

Example ex1: simp (Implies (Var "a")  (And (Var "b") (Var "b" ))) = Implies (Var "a")  (Var "b").
Proof. reflexivity. Qed.


Example ex2: simp (Implies (Var "a")  (Or (Var "b") (Var "b" ))) = Implies (Var "a")  (Var "b").
Proof. reflexivity. Qed.


Example ex3: simp (Implies (Var "a")  (Var "a")) = Implies Bot Bot.
Proof. reflexivity. Qed.


Example ex4: simp (Or (Implies (Var "a")  (Var "a")) (Implies (Var "a")  (Var "a"))) = Implies Bot Bot.
Proof. reflexivity. Qed.

Example ex5: simp (And (Implies (Var "a")  (Var "a")) (Implies (Var "a")  (Var "a"))) = Implies Bot Bot.
Proof. reflexivity. Qed.

