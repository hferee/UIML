Require Export ISL.Environments.

(* Note 3 or 4 would suffice for IPC ; iSL requires 5 *)
Definition env_weight (Γ : env) := list_sum (map (fun x => 5^ weight x) (elements Γ)).

Lemma env_weight_disj_union Γ Δ : env_weight (disj_union Γ Δ) = env_weight Γ +  env_weight Δ.
Proof. 
unfold env_weight. 
assert (Heq := gmultiset_elements_disj_union Γ Δ).
apply (Permutation_map (λ x : form, 5 ^ weight x)) in Heq.
apply Permutation_list_sum in Heq.
rewrite map_app, list_sum_app in Heq. exact Heq.
Qed.

Lemma env_weight_add Γ φ : env_weight (Γ • φ) = env_weight Γ +  (5 ^ weight φ).
Proof.
rewrite env_weight_disj_union. unfold env_weight at 2.
setoid_rewrite gmultiset_elements_singleton. simpl. lia.
Qed.

Global Hint Rewrite env_weight_add : order.

Definition env_order := ltof env env_weight.
Infix "≺" := env_order (at level 150).

Lemma env_weight_singleton (φ : form) : env_weight {[ φ ]} = 5 ^ weight φ.
Proof.
unfold env_weight, ltof.
replace (elements {[ φ ]}) with [φ]. simpl. lia. now rewrite <- gmultiset_elements_singleton.
Qed.

Lemma env_order_singleton (φ ψ : form) : weight φ < weight ψ -> {[+ φ +]}≺ {[+ ψ +]}.
Proof.
intro Hw. unfold env_order, ltof. do 2 rewrite env_weight_singleton.
apply Nat.pow_lt_mono_r. lia. trivial.
Qed.

Notation "Δ ≼ Δ'" := ((Δ ≺ Δ') \/ Δ = Δ') (at level 150).

Lemma env_le_weight Δ Δ' : (Δ' ≼ Δ) -> env_weight Δ' ≤ env_weight Δ.
Proof.
unfold env_order. intros [Hle | Heq].
- auto with *.
- subst; trivial.
Qed.

Global Hint Resolve env_le_weight : order.

Global Hint Unfold form_order : mset.


Global Instance env_order_trans : Transitive env_order.
Proof. unfold env_order, env_weight, ltof. auto with *. Qed.

Definition wf_env_order : well_founded env_order.
Proof. now apply well_founded_lt_compat with env_weight.
Defined.

(* We introduce a notion of "pointed" environment, which is simply
 * a pair (Δ, φ), where Δ is an environment and φ is a formula,
 * not necessarily an element of Δ.  *)
Definition pointed_env := (env * form)%type.

(* The order on pointed environments is given by considering the
 * environment order on the sum of Δ and {φ}. *)
 (* TODO: modified from G4IP : right-hand side counts twice, to account for the right box rule. Is this working? *)
Definition pointed_env_order (pe1 : pointed_env) (pe2 : pointed_env) :=
  env_order (fst pe1 • snd pe1 • snd pe1) (fst pe2 • snd pe2 •  snd pe2).

Lemma wf_pointed_order : well_founded pointed_env_order.
Proof. apply well_founded_ltof. Qed.

Infix "≺·" := pointed_env_order (at level 150).

Lemma env_order_equiv_right_compat {Δ Δ' Δ'' : env}:
  Δ' ≡ Δ'' ->
  (Δ ≺ Δ'') ->
  Δ ≺ Δ'.
Proof. ms. Qed.

Lemma env_order_equiv_left_compat {Δ Δ' Δ'' : env}:
  Δ ≡ Δ'' ->
  (Δ'' ≺ Δ') ->
  Δ ≺ Δ'.
Proof. ms. Qed.

Global Instance Proper_env_order : Proper ((≡@{env}) ==> (≡@{env}) ==> (fun x y => x <-> y)) env_order.
Proof. intros Δ1 Δ2 H12 Δ3 Δ4 H34; ms. Qed.


Lemma env_order_1  Δ φ1 φ : weight φ1 < weight φ -> Δ • φ1 ≺ Δ • φ.
Proof.
intros Hw.  unfold env_order, ltof. do 2 rewrite env_weight_add.
apply Nat.add_lt_mono_l. apply Nat.pow_lt_mono_r. lia. trivial.
Qed.

Local Hint Resolve Nat.pow_lt_mono_r : order.

Lemma env_order_compat  Δ Δ' φ1 φ : weight φ1 < weight φ -> (Δ' ≼ Δ) -> Δ' • φ1 ≺ Δ • φ.
Proof.
intros.  unfold env_order, ltof. repeat rewrite env_weight_add.
apply Nat.add_le_lt_mono; auto with *.
Qed.

Global Hint Resolve env_order_compat : order.

Lemma env_order_add_compat Δ Δ' φ : (Δ ≺ Δ') -> (Δ • φ) ≺ (Δ' • φ).
Proof.
unfold env_order, ltof. do 2 rewrite env_weight_add. lia.
Qed.

(* TODO: this is just a special case *)
Lemma env_order_disj_union_compat_left Δ Δ' Δ'':
  (Δ ≺ Δ'') -> Δ ⊎ Δ' ≺ Δ'' ⊎ Δ'.
Proof.
unfold env_order, ltof. intro. do 2 rewrite env_weight_disj_union. lia.
Qed.

Lemma env_order_disj_union_compat_right Δ Δ' Δ'':
  (Δ ≺ Δ'') -> Δ' ⊎ Δ ≺ Δ' ⊎ Δ''.
Proof.
intro H. eapply (Proper_env_order  _ (Δ ⊎ Δ') _ _ (Δ'' ⊎ Δ')) . ms. 
now apply env_order_disj_union_compat_left.
Unshelve. ms.
Qed.

Lemma env_order_disj_union_compat Δ Δ' Δ'' Δ''':
  (Δ ≺ Δ'') -> (Δ' ≺ Δ''') -> Δ ⊎ Δ' ≺ Δ'' ⊎ Δ'''.
Proof.
intros H1 H2.
transitivity (Δ  ⊎ Δ''').
- now apply env_order_disj_union_compat_right.
- now apply env_order_disj_union_compat_left.
Qed.


Lemma env_order_disj_union_compat_strong_right Δ Δ' Δ'' Δ''':
  (Δ ≺ Δ'') -> (Δ' ≼ Δ''') -> Δ ⊎ Δ' ≺ Δ'' ⊎ Δ'''.
Proof.
intros H1 H2. 
destruct H2 as [Hlt|Heq].
- unfold env_order, ltof in *. do 2 rewrite env_weight_disj_union. lia.
- rewrite Heq. now apply env_order_disj_union_compat_left.
Qed.

Lemma env_order_disj_union_compat_strong_left Δ Δ' Δ'' Δ''':
  (Δ ≼ Δ'') -> (Δ' ≺ Δ''') -> Δ ⊎ Δ' ≺ Δ'' ⊎ Δ'''.
Proof.
intros H1 H2. 
destruct H1 as [Hlt|Heq].
- unfold env_order, ltof in *. do 2 rewrite env_weight_disj_union. lia.
- rewrite Heq. now apply env_order_disj_union_compat_right.
Qed.

Lemma open_boxes_env_order Δ : (⊗Δ) ≼ Δ.
Proof.
induction Δ as [|φ Δ] using gmultiset_rec.
- right. autorewrite with proof. auto.
- destruct IHΔ as [Hlt | Heq].
  + left. autorewrite with proof.
      apply env_order_disj_union_compat_strong_left; trivial.
      destruct φ; simpl; try ms. left.
      apply env_order_singleton. simpl. lia.
  + rewrite open_boxes_disj_union, open_boxes_singleton, Heq.
      case_eq (is_box φ); intro Hbox; simpl.
      * left. apply env_order_disj_union_compat_strong_right; [|ms].
         destruct φ; simpl in *; try inversion Hbox.
         apply env_order_singleton. simpl. lia.
      * right. destruct φ; simpl in *; ms.
Qed.

Global Hint Resolve open_boxes_env_order : order.

Lemma env_order_0 Δ φ: Δ ≺ Δ • φ.
Proof.
unfold env_order, ltof. rewrite env_weight_disj_union, env_weight_singleton.
apply Nat.lt_add_pos_r. transitivity (5 ^ 0). simpl. lia. apply Nat.pow_lt_mono_r. lia.
apply weight_pos.
Qed.

(* TODO: ok? to replace env_order_* ?
Lemma env_order_l (Δ' Δ: env) φ1 φ: weight φ1 < weight φ -> (Δ' ≺ Δ • φ) -> (Δ' • φ1) ≺ (Δ • φ).
Proof.
*)

Local Lemma pow5_gt_0 n : 1 ≤ 5 ^ n.
Proof. transitivity (5^0). simpl. lia. apply Nat.pow_le_mono_r; lia. Qed.

Local Hint Resolve pow5_gt_0: order.

Lemma env_order_2  Δ Δ' φ1 φ2 φ: weight φ1 < weight φ -> weight φ2 < weight φ ->
  (Δ' ≼ Δ) -> Δ' • φ1 • φ2 ≺ Δ • φ.
Proof.
intros Hw1 Hw2 Hor.
unfold env_order, ltof. repeat rewrite env_weight_add.
apply env_le_weight in Hor.
replace (weight φ) with (S (pred (weight φ))) by lia.
apply Nat.lt_le_pred in Hw1, Hw2.
simpl. repeat rewrite Nat.add_assoc.
pose (pow5_gt_0 (Init.Nat.pred (weight φ))).
rewrite Nat.add_0_r.
repeat (apply Nat.add_lt_le_mono; [|apply Nat.pow_le_mono_r; lia]).
pose (pow5_gt_0 (Init.Nat.pred (weight φ))).
lia.
Qed.

Lemma env_order_3  Δ Δ' φ1 φ2 φ3 φ: 
  weight φ1 < weight φ -> weight φ2 < weight φ -> weight φ3 < weight φ -> (Δ' ≼ Δ) ->
  Δ' • φ1 • φ2  • φ3 ≺ Δ • φ.
Proof.
intros Hw1 Hw2 Hw3 Hor.
unfold env_order, ltof. repeat rewrite env_weight_add.
apply env_le_weight in Hor.
replace (weight φ) with (S (pred (weight φ))) by lia.
apply Nat.lt_le_pred in Hw1, Hw2.
simpl. repeat rewrite Nat.add_assoc.
pose (pow5_gt_0 (Init.Nat.pred (weight φ))).
rewrite Nat.add_0_r.
do 3 (apply Nat.add_lt_le_mono; [|apply Nat.pow_le_mono_r; lia]).
pose (pow5_gt_0 (Init.Nat.pred (weight φ))).
lia.
Qed.

Lemma env_order_4  Δ Δ' φ1 φ2 φ3 φ4 φ: 
  weight φ1 < weight φ -> weight φ2 < weight φ -> weight φ3 < weight φ -> weight φ4 < weight φ ->
   (Δ' ≼ Δ) -> Δ' • φ1 • φ2  • φ3 • φ4 ≺ Δ • φ.
Proof.
intros Hw1 Hw2 Hw3 Hw4 Hor.
unfold env_order, ltof. repeat rewrite env_weight_add.
apply env_le_weight in Hor.
replace (weight φ) with (S (pred (weight φ))) by lia.
apply Nat.lt_le_pred in Hw1, Hw2.
simpl. repeat rewrite Nat.add_assoc.
pose (pow5_gt_0 (Init.Nat.pred (weight φ))).
rewrite Nat.add_0_r.
do 4 (apply Nat.add_lt_le_mono; [|apply Nat.pow_le_mono_r; lia]).
pose (pow5_gt_0 (Init.Nat.pred (weight φ))).
lia.
Qed.



Lemma env_order_cancel_right Δ Δ' φ:  (Δ ≺ Δ') -> Δ ≺ (Δ' • φ).
Proof. etransitivity; [|apply env_order_0].	 assumption. Qed.


Lemma env_order_eq_add Δ Δ' φ: (Δ ≼ Δ') -> (Δ • φ) ≼ (Δ' • φ).
Proof. intros[Heq|Hlt]. left. now apply env_order_add_compat. right. ms. Qed.


Global Hint Resolve env_order_0 : order.
Global Hint Resolve env_order_1 : order.
Global Hint Resolve env_order_2 : order.
Global Hint Resolve env_order_3 : order.
Global Hint Resolve env_order_4 : order.
Global Hint Resolve env_order_add_compat : order.
Global Hint Resolve env_order_cancel_right : order.
Global Hint Resolve env_order_eq_add : order.
Global Hint Extern 1 (?a < ?b) => subst; simpl; lia : order.

Ltac get_diff_form g := match g with
| ?Γ ∖{[?φ]} => φ
| _ (?Γ ∖{[?φ]}) => φ
| ?Γ • _ => get_diff_form Γ
end.

Ltac get_diff_env g := match g with
| ?Γ ∖{[?φ]} => Γ
| ?Γ • _ => get_diff_env Γ
end.

Global Hint Rewrite open_boxes_remove : order.

Ltac prepare_order := 
repeat (apply env_order_add_compat);
unfold pointed_env_order; subst; simpl; repeat rewrite open_boxes_add; try match goal with
| Δ := _ |- _ => subst Δ; try prepare_order
| H : ?ψ ∈ ?Γ |- ?Γ' ≺ ?Γ => let ψ' := (get_diff_form Γ') in
    apply (env_order_equiv_right_compat (difference_singleton Γ ψ' H))
| H : ?ψ ∈ ?Γ |- ?Γ' ≺ ?Γ • ?φ => let ψ' := (get_diff_form Γ') in
    apply (env_order_equiv_right_compat (equiv_disj_union_compat_r(difference_singleton Γ ψ' H)))
| H : ?ψ ∈ ?Γ |- ?Γ' ≺ ?Γ • _ • _ => let ψ' := (get_diff_form Γ') in
apply (env_order_equiv_right_compat (equiv_disj_union_compat_r(equiv_disj_union_compat_r(difference_singleton Γ ψ' H))))
end.

(*
Lemma make_impl_weight φ ψ: weight (φ ⇢ ψ) <= weight (φ → ψ).
Proof.
assert (H := weight_pos ψ).
assert (H' := weight_pos φ).
revert φ H'; induction ψ; intros φ H';
unfold make_impl; repeat destruct decide; simpl; try lia.
fold make_impl.
etransitivity. apply IHψ2.
- apply weight_pos.
- apply weight_pos.
- simpl. assert(HH := make_conj_weight lia.
revert (IHψ2 (ma)
Qed.

Lemma make_impl_weight2 φ ψ θ: weight (φ ⇢ (ψ ⇢ θ)) <= weight (φ → (ψ → θ)).
Proof.
pose (make_impl_weight ψ θ).
pose (make_impl_weight φ (ψ ⇢ θ)).
simpl in *. lia.
Qed.


Global Hint Extern  5  (weight (?φ ⇢ ?ψ) < _) => (eapply Nat.le_lt_trans; [eapply make_impl_weight|]) : order.

Global Hint Extern  5  (weight (?φ ⇢ (?ψ ⇢ ?θ)) < _) => (eapply Nat.le_lt_trans; [eapply make_impl_weight2|]) : order.

*)

(* ad hoc *)
Lemma openboxes_env_order Δ δ :  (⊗ Δ) • δ • δ ≺ Δ • □ δ.
Proof.
induction Δ using gmultiset_rec.
- eapply @env_order_equiv_left_compat with  (∅ • δ • δ). 
  + now rewrite open_boxes_empty.
  + apply env_order_2; simpl; try lia. ms.
- apply (@env_order_equiv_right_compat _  _ (Δ • □ δ • x)); [ms|].
  eapply (@env_order_equiv_left_compat  _ _ (⊗ Δ • δ • δ •  ⊙ x)).
  rewrite open_boxes_disj_union, open_boxes_singleton. ms.
  case x; intros; simpl; try (solve[now apply env_order_add_compat]).
  transitivity (Δ • □δ • f).
  + auto with *.
  + apply env_order_1. simpl. auto.
Qed.

Global Hint Resolve openboxes_env_order : order.

Ltac order_tac := prepare_order; auto 10 with order.

