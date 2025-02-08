(** * Ordering *)
Require Export ISL.Environments.
Require Import Coq.Program.Equality.

(* Note 3 or 4 would suffice for IPC ; iSL requires 5 *)
Definition env_weight {K : Kind} Γ :=
  list_sum (map (fun x => 5^ weight x) Γ).

Lemma env_weight_disj_union {K : Kind} Γ Δ :
  env_weight (Γ ++ Δ) = env_weight Γ +  env_weight Δ.
Proof. 
unfold env_weight. now rewrite map_app, list_sum_app.
Qed.

Notation "Δ '•' φ" := (cons φ Δ) : list_scope.

Lemma env_weight_add (K : Kind) Γ φ :
  env_weight (Γ • φ) = env_weight Γ +  (5 ^ weight φ).
Proof.
unfold env_weight. simpl. lia.
Qed.

Global Hint Rewrite env_weight_add : order.

Definition env_order {K : Kind} := ltof _ env_weight.
Infix "≺" := env_order (at level 150).

Lemma env_weight_singleton {K : Kind} (φ : form) :
  env_weight [ φ ] = 5 ^ weight φ.
Proof.
unfold env_weight, ltof. simpl. lia.
Qed.

Lemma env_order_singleton {K : Kind}  φ ψ :
  weight φ < weight ψ -> [φ ] ≺ [ ψ ].
Proof.
intro Hw. unfold env_order, ltof. do 2 rewrite env_weight_singleton.
apply Nat.pow_lt_mono_r. lia. trivial.
Qed.

Definition env_order_refl {K : Kind} Δ Δ' := (env_weight Δ) ≤(env_weight Δ').

Global Notation "Δ ≼ Δ'" := (env_order_refl Δ Δ') (at level 150).

Lemma env_order_env_order_refl {K : Kind} Δ Δ' :
  env_order Δ Δ' -> env_order_refl Δ Δ'.
Proof. unfold env_order, env_order_refl, ltof. lia. Qed.

Global Hint Resolve env_order_env_order_refl: order.

Lemma env_order_self {K : Kind} Δ : Δ ≼ Δ.
Proof. unfold env_order_refl. trivial. Qed.

Global Instance Proper_env_weight {K : Kind} : Proper ((≡ₚ) ==> (=)) env_weight.
Proof.
intros Γ Δ Heq. unfold env_weight. now rewrite Heq.
Qed.


Global Instance Proper_env_order_refl_env_weight {K : Kind}:
  Proper ((env_order_refl) ==> le) env_weight.
Proof. intros Γ Δ Hle. auto with *. Qed.

Global Hint Resolve Proper_env_order_refl_env_weight : order.

Global Hint Unfold form_order : mset.


Global Instance env_order_trans {K : Kind} : Transitive env_order.
Proof. unfold env_order, env_weight, ltof. auto with *. Qed.

Definition wf_env_order {K : Kind} : well_founded env_order.
Proof. now apply well_founded_lt_compat with env_weight.
Defined.

(* We introduce a notion of "pointed" environment, which is simply
 * a pair (Δ, φ), where Δ is an environment and φ is a formula,
 * not necessarily an element of Δ.  *)
Definition pointed_env {K : Kind} := (list (form) * form)%type.


(* The order on pointed environments is given by considering the
 * environment order on the sum of Δ and {φ}. *)
Definition pointed_env_order {K : Kind} (pe1 : pointed_env) (pe2 : pointed_env) :=
  env_order (fst pe1 • snd pe1 • snd pe1) (fst pe2 • snd pe2 •  snd pe2).

Lemma wf_pointed_order {K : Kind} : well_founded pointed_env_order.
Proof. apply well_founded_ltof. Qed.

Definition pointed_env_ms_order {K : Kind} (Γφ Δψ : env * form) :=
  pointed_env_order (elements Γφ.1, Γφ.2) (elements Δψ.1, Δψ.2).

Lemma wf_pointed_env_ms_order {K : Kind}: well_founded pointed_env_ms_order.
Proof. apply well_founded_ltof. Qed.

Infix "≺·" := pointed_env_order (at level 150).

Lemma env_order_equiv_right_compat {K : Kind} {Δ Δ' Δ'' }:
  Δ' ≡ₚ Δ'' ->
  (Δ ≺ Δ'') ->
  Δ ≺ Δ'.
Proof. 
unfold equiv, env_order, ltof, env_weight. intro Heq. rewrite Heq. trivial.
Qed.

Lemma env_order_equiv_left_compat {K : Kind} {Δ Δ' Δ'' }:
  Δ ≡ₚ Δ'' ->
  (Δ'' ≺ Δ') ->
  Δ ≺ Δ'.
Proof. unfold equiv, env_order, ltof, env_weight. intro Heq. rewrite Heq. trivial. Qed.


Global Instance Proper_env_order {K : Kind}:
  Proper ((≡ₚ) ==> (≡ₚ) ==> (fun x y => x <-> y)) env_order.
Proof.
  intros Δ1 Δ2 H12 Δ3 Δ4 H34; unfold equiv, env_order, ltof, env_weight.
  rewrite H12, H34. tauto.
Qed.

Global Instance Proper_env_order_refl {K : Kind}:
  Proper ((≡ₚ) ==> (≡ₚ) ==> (fun x y => x <-> y)) env_order_refl.
Proof.
intros Δ1 Δ2 H12 Δ3 Δ4 H34; unfold equiv, env_order, ltof, env_weight, env_order_refl.
now rewrite H12, H34.
Qed.

Lemma env_order_1 {K : Kind} Δ φ1 φ : weight φ1 < weight φ -> Δ • φ1 ≺ Δ • φ.
Proof.
intros Hw.  unfold env_order, ltof. do 2 rewrite env_weight_add.
apply Nat.add_lt_mono_l. apply Nat.pow_lt_mono_r. lia. trivial.
Qed.

Local Hint Resolve Nat.pow_lt_mono_r : order.

Lemma env_order_compat {K : Kind} Δ Δ' φ1 φ :
  weight φ1 < weight φ -> (Δ' ≼ Δ) -> Δ' • φ1 ≺ Δ • φ.
Proof.
intros.  unfold env_order, ltof. repeat rewrite env_weight_add.
apply Nat.add_le_lt_mono; auto with *.
Qed.

Global Hint Resolve env_order_compat : order.

Lemma env_order_compat' {K : Kind} Δ Δ' φ1 φ :
  weight φ1 ≤ weight φ -> (Δ' ≺ Δ) -> Δ' • φ1 ≺ Δ • φ.
Proof.
intros.  unfold env_order, ltof. repeat rewrite env_weight_add.
apply Nat.add_lt_le_mono; auto with *. now apply Nat.pow_le_mono_r.
Qed.

Global Hint Resolve env_order_compat' : order.

Lemma env_order_add_compat {K : Kind} Δ Δ' φ : (Δ ≺ Δ') -> (Δ • φ) ≺ (Δ' • φ).
Proof.
unfold env_order, ltof. do 2 rewrite env_weight_add. lia.
Qed.

Lemma env_order_disj_union_compat_left {K : Kind} Δ Δ' Δ'':
  (Δ ≺ Δ'') -> Δ ++ Δ' ≺ Δ'' ++ Δ'.
Proof.
unfold env_order, ltof. intro. do 2 rewrite env_weight_disj_union. lia.
Qed.

Lemma env_order_disj_union_compat_right {K : Kind} Δ Δ' Δ'':
  (Δ ≺ Δ'') -> Δ' ++ Δ ≺ Δ' ++ Δ''.
Proof.
unfold env_order, ltof. repeat rewrite env_weight_disj_union. lia.
Qed.

Global Hint Resolve env_order_disj_union_compat_right : order.

Lemma env_order_disj_union_compat {K : Kind} Δ Δ' Δ'' Δ''':
  (Δ ≺ Δ'') -> (Δ' ≺ Δ''') -> Δ ++ Δ' ≺ Δ'' ++ Δ'''.
Proof.
unfold env_order, ltof. repeat rewrite env_weight_disj_union. lia.
Qed.

Lemma env_order_refl_disj_union_compat {K : Kind} Δ Δ' Δ'' Δ''':
  (env_order_refl Δ Δ'') -> (env_order_refl Δ' Δ''') -> env_order_refl (Δ ++ Δ') (Δ'' ++ Δ''').
Proof.
unfold env_order_refl, env_order, ltof. repeat rewrite env_weight_disj_union.
intros Hle1 Hle2; try rewrite Heq1; try rewrite Heq2; try lia.
Qed.

Global Hint Resolve env_order_refl_disj_union_compat : order.

Hint Unfold env_order_refl : order.
Lemma env_order_disj_union_compat_strong_right {K : Kind} Δ Δ' Δ'' Δ''':
  (Δ ≺ Δ'') -> (Δ' ≼ Δ''') -> Δ ++ Δ' ≺ Δ'' ++ Δ'''.
Proof.
intros Hlt Hle. unfold env_order_refl, env_order, ltof in *. do 2 rewrite env_weight_disj_union. lia.
Qed.

Lemma env_order_disj_union_compat_strong_left {K : Kind} Δ Δ' Δ'' Δ''':
  (Δ ≼ Δ'') -> (Δ' ≺ Δ''') -> Δ ++ Δ' ≺ Δ'' ++ Δ'''.
Proof.
intros Hlt Hle. unfold env_order_refl, env_order, ltof in *. do 2 rewrite env_weight_disj_union. lia. Qed.

Global Hint Resolve env_order_disj_union_compat_strong_left : order.
Global Hint Resolve elements_open_boxes : order.

Lemma weight_open_box {K : Kind} φ : weight (⊙ φ) ≤ weight φ.
Proof. dependent destruction φ; simpl; lia. Qed.

Lemma open_boxes_env_order {K : Kind} Δ : (map open_box Δ) ≼ Δ.
Proof.
unfold env_order_refl.
induction Δ as [|φ Δ]; trivial.
simpl. do 2 rewrite env_weight_add. dependent destruction φ; simpl; lia.
Qed.

Global Hint Resolve open_boxes_env_order : order.

Lemma env_order_0 {K : Kind} Δ φ: Δ ≺ Δ • φ.
Proof.
unfold env_order, ltof. rewrite env_weight_add.
apply Nat.lt_add_pos_r. transitivity (5 ^ 0). simpl. lia. apply Nat.pow_lt_mono_r. lia.
apply weight_pos.
Qed.

Local Lemma pow5_gt_0 n : 1 ≤ 5 ^ n.
Proof. transitivity (5^0). simpl. lia. apply Nat.pow_le_mono_r; lia. Qed.

Local Hint Resolve pow5_gt_0: order.

Lemma env_order_2 {K : Kind} Δ Δ' φ1 φ2 φ: weight φ1 < weight φ -> weight φ2 < weight φ ->
  (Δ' ≼ Δ) -> Δ' • φ1 • φ2 ≺ Δ • φ.
Proof.
intros Hw1 Hw2 Hor.
unfold env_order, ltof. repeat rewrite env_weight_add.
apply Proper_env_order_refl_env_weight in Hor.
replace (weight φ) with (S (pred (weight φ))) by lia.
apply Nat.lt_le_pred in Hw1, Hw2.
simpl. repeat rewrite Nat.add_assoc.
pose (pow5_gt_0 (Init.Nat.pred (weight φ))).
rewrite Nat.add_0_r.
repeat (apply Nat.add_lt_le_mono; [|apply Nat.pow_le_mono_r; lia]).
pose (pow5_gt_0 (Init.Nat.pred (weight φ))).
lia.
Qed.

Lemma env_order_3 {K : Kind} Δ Δ' φ1 φ2 φ3 φ: 
  weight φ1 < weight φ -> weight φ2 < weight φ -> weight φ3 < weight φ -> (Δ' ≼ Δ) ->
  Δ' • φ1 • φ2  • φ3 ≺ Δ • φ.
Proof.
intros Hw1 Hw2 Hw3 Hor.
unfold env_order, ltof. repeat rewrite env_weight_add.
apply Proper_env_order_refl_env_weight in Hor.
replace (weight φ) with (S (pred (weight φ))) by lia.
apply Nat.lt_le_pred in Hw1, Hw2.
simpl. repeat rewrite Nat.add_assoc.
pose (pow5_gt_0 (Init.Nat.pred (weight φ))).
rewrite Nat.add_0_r.
do 3 (apply Nat.add_lt_le_mono; [|apply Nat.pow_le_mono_r; lia]).
pose (pow5_gt_0 (Init.Nat.pred (weight φ))).
lia.
Qed.

Lemma env_order_4 {K : Kind} Δ Δ' φ1 φ2 φ3 φ4 φ: 
  weight φ1 < weight φ -> weight φ2 < weight φ -> weight φ3 < weight φ -> weight φ4 < weight φ ->
   (Δ' ≼ Δ) -> Δ' • φ1 • φ2  • φ3 • φ4 ≺ Δ • φ.
Proof.
intros Hw1 Hw2 Hw3 Hw4 Hor.
unfold env_order, ltof. repeat rewrite env_weight_add.
apply Proper_env_order_refl_env_weight in Hor.
replace (weight φ) with (S (pred (weight φ))) by lia.
apply Nat.lt_le_pred in Hw1, Hw2.
simpl. repeat rewrite Nat.add_assoc.
pose (pow5_gt_0 (Init.Nat.pred (weight φ))).
rewrite Nat.add_0_r.
do 4 (apply Nat.add_lt_le_mono; [|apply Nat.pow_le_mono_r; lia]).
pose (pow5_gt_0 (Init.Nat.pred (weight φ))).
lia.
Qed.

Lemma env_order_cancel_right {K : Kind} Δ Δ' φ:  (Δ ≺ Δ') -> Δ ≺ (Δ' • φ).
Proof. etransitivity; [|apply env_order_0].	 assumption. Qed.

Lemma env_order_refl_add {K : Kind} Δ Δ' φ: (Δ ≼ Δ') -> (Δ • φ) ≼ (Δ' • φ).
Proof. unfold env_order_refl. do 2 rewrite env_weight_add. lia. Qed.

Lemma env_order_refl_add' {K : Kind} Δ Δ' φ φ': weight φ ≤ weight φ' -> (Δ ≼ Δ') -> (Δ • φ) ≼ (Δ' • φ').
Proof. unfold env_order_refl. do 2 rewrite env_weight_add.
intros. apply Nat.add_le_mono. lia. apply Nat.pow_le_mono_r; lia. Qed.

Global Hint Resolve env_order_0 : order.
Global Hint Resolve env_order_1 : order.
Global Hint Resolve env_order_2 : order.
Global Hint Resolve env_order_3 : order.
Global Hint Resolve env_order_4 : order.
Global Hint Resolve env_order_add_compat : order.
Global Hint Resolve env_order_cancel_right : order.
Global Hint Resolve env_order_refl_add : order.
Global Hint Resolve env_order_refl_add' : order.
Global Hint Extern 1 (?a < ?b) => subst; simpl; lia : order.

Ltac get_diff_form g := match g with
| ?Γ ∖{[?φ]} => φ
| _ (?Γ ∖{[?φ]}) => φ
| _ (rm ?φ _) => φ
| (rm ?φ _) => φ
| ?Γ ++ _ => get_diff_form Γ
| _ :: ?Γ => get_diff_form Γ
end.

Ltac get_diff_env g := match g with
| ?Γ ∖{[?φ]} => Γ
| _ :: ?Γ => get_diff_env Γ
end.

Lemma remove_env_order {K : Kind} Δ φ:  rm φ Δ ≼ Δ.
Proof.
unfold env_order_refl.
induction Δ as [|ψ Δ]. trivial. 
simpl. destruct form_eq_dec; repeat rewrite env_weight_add; lia.
Qed.

Global Hint Resolve remove_env_order : order.

Lemma remove_In_env_order_refl {K : Kind} Δ φ:  In φ Δ -> rm φ Δ • φ ≼ Δ.
Proof.
induction Δ as [|ψ Δ].
- intro Hf; contradict Hf.
- intros [Heq | Hin].
  + subst. simpl.  destruct form_eq_dec; [|tauto]. auto with order.
  + specialize (IHΔ Hin).  simpl. case form_eq_dec as [Heq | Hneq].
      * subst. auto with order.
      * rewrite (Permutation_swap ψ φ (rm φ Δ)). auto with order.
Qed.

Global Hint Resolve remove_In_env_order_refl : order.

Lemma env_order_lt_le_trans {K : Kind} Γ Γ' Γ'' : (Γ ≺ Γ') -> (Γ' ≼ Γ'') -> Γ ≺ Γ''.
Proof. unfold env_order, env_order_refl, ltof. lia. Qed.

Lemma env_order_le_lt_trans {K : Kind} Γ Γ' Γ'' : (Γ ≼ Γ') -> (Γ' ≺ Γ'') -> Γ ≺ Γ''.
Proof. unfold env_order, env_order_refl, ltof. lia. Qed.

Lemma remove_In_env_order {K : Kind} Δ φ:  In φ Δ -> rm φ Δ ≺ Δ.
Proof.
intro Hin. apply remove_In_env_order_refl in Hin.
eapply env_order_lt_le_trans; [|apply Hin]. auto with order.
Qed.

Global Hint Resolve remove_In_env_order : order.

Lemma elem_of_list_In_1 {A : Type}: ∀ (l : list A) (x : A), x ∈ l <-> In x l.
Proof. apply elem_of_list_In. Qed.

Global Hint Resolve  elem_of_list_In_1 : order.

Lemma elements_elem_of {K : Kind} {Γ : @env K} {φ : form} :
  φ ∈ Γ -> elements Γ ≡ₚ φ :: elements (Γ ∖ {[φ]}).
Proof.
  intro Hin. setoid_rewrite <- elements_env_add.
  apply Proper_elements, difference_singleton, Hin.
Qed.

Ltac prepare_order := 
repeat (apply env_order_add_compat);
unfold pointed_env_order; subst; simpl; repeat rewrite open_boxes_add; try match goal with
| Δ := _ |- _ => subst Δ; try prepare_order
| Hin : ?a ∈ ?Γ |- context[elements ?Γ] => rewrite (elements_elem_of Hin); try prepare_order
| H : _ ∈ list_to_set_disj _ |- _ => apply elem_of_list_to_set_disj in H; try prepare_order
| H : ?ψ ∈ ?Γ |- ?Γ' ≺ ?Γ => let ψ' := (get_diff_form Γ') in
    apply (env_order_equiv_right_compat (difference_singleton Γ ψ' H)) ||
    (eapply env_order_lt_le_trans ; [| apply (remove_In_env_order_refl _ ψ'); try apply elem_of_list_In; trivial])
| H : ?ψ ∈ ?Γ |- ?Γ' ≺ (?φ :: ?Γ)  => let ψ' := (get_diff_form Γ') in
    apply (env_order_equiv_right_compat (equiv_disj_union_compat_r(difference_singleton Γ ψ' H)))
| H : ?ψ ∈ ?Γ |- ?Γ' ≺ (_ :: _ :: ?Γ) => let ψ' := (get_diff_form Γ') in
apply (env_order_equiv_right_compat (equiv_disj_union_compat_r(equiv_disj_union_compat_r(difference_singleton Γ ψ' H)))) ||
(eapply env_order_le_lt_trans; [| apply env_order_add_compat; 
eapply env_order_lt_le_trans; [| (apply env_order_refl_add; apply (remove_In_env_order_refl _ ψ'); try apply elem_of_list_In; trivial) ] ] )
|H : ?a = _ |- context[?a] => rewrite H; try prepare_order
end.


(* ad hoc *)
Lemma openboxes_env_order Δ δ :  (map open_box Δ) • δ • δ ≺ Δ • □ δ.
Proof.
induction Δ as [|x Δ].
- simpl. unfold env_order, ltof, env_weight. simpl.
  repeat rewrite <- plus_n_O. apply Nat.add_lt_mono_l.
  rewrite plus_n_O at 1. auto with *.
- apply (@env_order_equiv_right_compat _ _  _ (Δ • □ δ • x)). constructor.
  simpl.
  eapply (@env_order_equiv_left_compat _ _ _ (map open_box Δ • δ • δ •  ⊙ x)).
  + do 2 (rewrite (Permutation_swap δ (⊙ x)); apply Permutation_skip). trivial.
  + dependent destruction x; intros; simpl; try (solve[now apply env_order_add_compat]).
      transitivity (x :: (□δ) :: Δ).
      * auto with *.
      * apply env_order_1. simpl. auto.
Qed.

Global Hint Resolve openboxes_env_order : order.

Lemma weight_Arrow_1 {K : Kind} φ ψ : 1 < weight (φ → ψ).
Proof. simpl. pose (weight_pos  φ). lia. Qed.

Lemma weight_Box_1 φ: 1 < weight (□ φ).
Proof. simpl. pose (weight_pos  φ). lia. Qed.

Global Hint Resolve weight_Arrow_1 : order.
Global Hint Resolve weight_Box_1 : order.

Ltac order_tac :=
try unfold pointed_env_ms_order; prepare_order;
repeat rewrite elements_env_add; 
simpl; auto 10 with order;
try (apply env_order_disj_union_compat_right; order_tac).

Global Hint Extern 5 (?a ≺ ?b) => order_tac : proof.
Hint Extern 5 (?a ≺· ?b) => order_tac : proof.

Lemma pointed_env_order_bot_R {K : Kind} pe Δ φ: (pe ≺· (Δ, ⊥)) -> pe ≺· (Δ, φ).
Proof.
intro Hlt. destruct pe as (Γ, ψ). unfold pointed_env_order. simpl.
eapply env_order_lt_le_trans. exact Hlt. simpl.
unfold env_order_refl. repeat rewrite env_weight_add.
assert(Hle: weight ⊥ ≤ weight φ) by (destruct φ; simpl; lia).
apply Nat.pow_le_mono_r with (a := 5) in Hle; lia.
Qed.

Hint Resolve pointed_env_order_bot_R : order.

Lemma pointed_env_order_bot_L {K : Kind} pe Δ φ: ((Δ, φ) ≺· pe) -> (Δ, ⊥) ≺· pe.
Proof.
intro Hlt. destruct pe as (Γ, ψ). unfold pointed_env_order. simpl.
eapply env_order_le_lt_trans; [|exact Hlt]. simpl.
unfold env_order_refl. repeat rewrite env_weight_add.
assert(Hle: weight ⊥ ≤ weight φ) by (destruct φ; simpl; lia).
apply Nat.pow_le_mono_r with (a := 5) in Hle; lia.
Qed.

Hint Resolve pointed_env_order_bot_L : order.

Lemma weight_or_bot {K : Kind} a b: weight(⊥) < weight (a ∨b).
Proof. destruct a; simpl; lia. Qed.

Hint Resolve weight_or_bot : order.

Definition pointed_env_order_refl {K : Kind} pe1 pe2 :=
  env_order_refl (pe1.2 :: pe1.2 :: pe1.1) (pe2.2 :: pe2.2 :: pe2.1).
