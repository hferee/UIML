Require Export ISL.Environments.

(* Note 3 or 4 would suffice for IPC ; iSL requires 5 *)
Definition env_weight (Γ : list form) := list_sum (map (fun x => 5^ weight x) Γ).

Lemma env_weight_disj_union Γ Δ : env_weight (Γ ++ Δ) = env_weight Γ +  env_weight Δ.
Proof. 
unfold env_weight. now rewrite map_app, list_sum_app.
Qed.

(* TODO: dirty hack *)
Local Notation "Δ '•' φ" := (cons φ Δ).

Lemma env_weight_add Γ φ : env_weight (Γ • φ) = env_weight Γ +  (5 ^ weight φ).
Proof.
unfold env_weight. simpl. lia.
Qed.

Global Hint Rewrite env_weight_add : order.

Definition env_order := ltof (list form) env_weight.
Infix "≺" := env_order (at level 150).

Lemma env_weight_singleton (φ : form) : env_weight [ φ ] = 5 ^ weight φ.
Proof.
unfold env_weight, ltof. simpl. lia.
Qed.

Lemma env_order_singleton (φ ψ : form) : weight φ < weight ψ -> [φ ] ≺ [ ψ ].
Proof.
intro Hw. unfold env_order, ltof. do 2 rewrite env_weight_singleton.
apply Nat.pow_lt_mono_r. lia. trivial.
Qed.

Definition env_order_refl Δ Δ' := (Δ ≺ Δ') \/ Δ ≡ₚ Δ'.

Local Notation "Δ ≼ Δ'" := (env_order_refl Δ Δ') (at level 150).

Global Instance Proper_env_weight: Proper ((≡ₚ) ==> (=)) env_weight.
Proof.
intros Γ Δ Heq. unfold env_weight. now rewrite Heq.
Qed.


Global Instance Proper_env_order_refl_env_weight:
  Proper ((env_order_refl) ==> le) env_weight.
Proof.
intros Γ Δ.
unfold env_order. intros [Hle | Heq].
- auto with *.
- now rewrite Heq.
Qed.

Global Hint Resolve Proper_env_order_refl_env_weight : order.

Global Hint Unfold form_order : mset.


Global Instance env_order_trans : Transitive env_order.
Proof. unfold env_order, env_weight, ltof. auto with *. Qed.

Definition wf_env_order : well_founded env_order.
Proof. now apply well_founded_lt_compat with env_weight.
Defined.

(* We introduce a notion of "pointed" environment, which is simply
 * a pair (Δ, φ), where Δ is an environment and φ is a formula,
 * not necessarily an element of Δ.  *)
Definition pointed_env := (list form * form)%type.




(* The order on pointed environments is given by considering the
 * environment order on the sum of Δ and {φ}. *)
 (* TODO: modified from G4IP : right-hand side counts twice, to account for the right box rule. Is this working? *)
Definition pointed_env_order (pe1 : pointed_env) (pe2 : pointed_env) :=
  env_order (fst pe1 • snd pe1 • snd pe1) (fst pe2 • snd pe2 •  snd pe2).

Lemma wf_pointed_order : well_founded pointed_env_order.
Proof. apply well_founded_ltof. Qed.

Definition pointed_env_ms_order (Γφ Δψ : env * form) :=
  pointed_env_order (elements Γφ.1, Γφ.2) (elements Δψ.1, Δψ.2).

Lemma wf_pointed_env_ms_order : well_founded pointed_env_ms_order.
Proof. apply well_founded_ltof. Qed.

Infix "≺·" := pointed_env_order (at level 150).

Lemma env_order_equiv_right_compat {Δ Δ' Δ'' }:
  Δ' ≡ₚ Δ'' ->
  (Δ ≺ Δ'') ->
  Δ ≺ Δ'.
Proof. 
unfold equiv, env_order, ltof, env_weight. intro Heq. rewrite Heq. trivial.
Qed.

Lemma env_order_equiv_left_compat {Δ Δ' Δ'' }:
  Δ ≡ₚ Δ'' ->
  (Δ'' ≺ Δ') ->
  Δ ≺ Δ'.
Proof. unfold equiv, env_order, ltof, env_weight. intro Heq. rewrite Heq. trivial. Qed.


Global Instance Proper_env_order : Proper ((≡ₚ) ==> (≡ₚ) ==> (fun x y => x <-> y)) env_order.
Proof. intros Δ1 Δ2 H12 Δ3 Δ4 H34; unfold equiv, env_order, ltof, env_weight.  rewrite H12, H34. tauto. Qed.

Global Instance Proper_env_order_refl : Proper ((≡ₚ) ==> (≡ₚ) ==> (fun x y => x <-> y)) env_order_refl.
Proof.
intros Δ1 Δ2 H12 Δ3 Δ4 H34; unfold equiv, env_order, ltof, env_weight, env_order_refl.
now rewrite H12, H34.
Qed.

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

Lemma env_order_compat'  Δ Δ' φ1 φ : weight φ1 ≤ weight φ -> (Δ' ≺ Δ) -> Δ' • φ1 ≺ Δ • φ.
Proof.
intros.  unfold env_order, ltof. repeat rewrite env_weight_add.
apply Nat.add_lt_le_mono; auto with *. now apply Nat.pow_le_mono_r.
Qed.

Lemma env_order_add_compat Δ Δ' φ : (Δ ≺ Δ') -> (Δ • φ) ≺ (Δ' • φ).
Proof.
unfold env_order, ltof. do 2 rewrite env_weight_add. lia.
Qed.

(* TODO: this is just a special case *)
Lemma env_order_disj_union_compat_left Δ Δ' Δ'':
  (Δ ≺ Δ'') -> Δ ++ Δ' ≺ Δ'' ++ Δ'.
Proof.
unfold env_order, ltof. intro. do 2 rewrite env_weight_disj_union. lia.
Qed.

Lemma env_order_disj_union_compat_right Δ Δ' Δ'':
  (Δ ≺ Δ'') -> Δ' ++ Δ ≺ Δ' ++ Δ''.
Proof.
unfold env_order, ltof. repeat rewrite env_weight_disj_union. lia.
Qed.

Global Hint Resolve env_order_disj_union_compat_right : order.

Lemma env_order_disj_union_compat Δ Δ' Δ'' Δ''':
  (Δ ≺ Δ'') -> (Δ' ≺ Δ''') -> Δ ++ Δ' ≺ Δ'' ++ Δ'''.
Proof.
unfold env_order, ltof. repeat rewrite env_weight_disj_union. lia.
Qed.

Lemma env_order_refl_disj_union_compat Δ Δ' Δ'' Δ''':
  (env_order_refl Δ Δ'') -> (env_order_refl Δ' Δ''') -> env_order_refl (Δ ++ Δ') (Δ'' ++ Δ''').
Proof.
unfold env_order_refl, env_order, ltof. repeat rewrite env_weight_disj_union.
intros [Hlt1 | Heq1] [Hlt2 | Heq2]; try rewrite Heq1; try rewrite Heq2; try lia.
right. trivial.
Qed.

Global Hint Resolve env_order_refl_disj_union_compat : order.

Hint Unfold env_order_refl : order.
Lemma env_order_disj_union_compat_strong_right Δ Δ' Δ'' Δ''':
  (Δ ≺ Δ'') -> (Δ' ≼ Δ''') -> Δ ++ Δ' ≺ Δ'' ++ Δ'''.
Proof.
intros H1 H2. 
destruct H2 as [Hlt|Heq].
- unfold env_order, ltof in *. do 2 rewrite env_weight_disj_union. lia.
- rewrite Heq. now apply env_order_disj_union_compat_left.
Qed.

Lemma env_order_disj_union_compat_strong_left Δ Δ' Δ'' Δ''':
  (Δ ≼ Δ'') -> (Δ' ≺ Δ''') -> Δ ++ Δ' ≺ Δ'' ++ Δ'''.
Proof.
intros H1 H2.
destruct H1 as [Hlt|Heq].
- unfold env_order, ltof in *. do 2 rewrite env_weight_disj_union. lia.
- rewrite Heq. now apply env_order_disj_union_compat_right.
Qed.

Global Hint Resolve env_order_disj_union_compat_strong_left : order.
Global Hint Rewrite elements_open_boxes : order.

Lemma weight_open_box φ : weight (⊙ φ) ≤ weight φ.
Proof. destruct φ; simpl; lia. Qed.

Lemma open_boxes_env_order Δ : (map open_box Δ) ≼ Δ.
Proof.
induction Δ as [|φ Δ].
- right. trivial.
- destruct IHΔ as [Hlt | Heq]; simpl.
  + left. apply env_order_compat'; trivial. apply weight_open_box. 
  + rewrite Heq. auto with order. destruct φ; simpl; try auto with order.
       left. auto with order.
Qed.

Global Hint Resolve open_boxes_env_order : order.

Lemma env_order_0 Δ φ: Δ ≺ Δ • φ.
Proof.
unfold env_order, ltof. rewrite env_weight_add.
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

Lemma env_order_3  Δ Δ' φ1 φ2 φ3 φ: 
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

Lemma env_order_4  Δ Δ' φ1 φ2 φ3 φ4 φ: 
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
| _ (rm ?φ _) => φ
| (rm ?φ _) => φ
| ?Γ ++ _ => get_diff_form Γ
| ?Γ • _ => get_diff_form Γ
end.

Ltac get_diff_env g := match g with
| ?Γ ∖{[?φ]} => Γ
| ?Γ • _ => get_diff_env Γ
end.

Global Hint Rewrite open_boxes_remove : order.

Lemma remove_env_order Δ φ:  rm φ Δ ≼ Δ.
Proof.
induction Δ as [|ψ Δ].
- simpl. right. auto.
- simpl.  destruct form_eq_dec; auto with order.
Qed.

Global Hint Resolve remove_env_order : order.

Lemma remove_In_env_order_refl Δ φ:  In φ Δ -> rm φ Δ • φ ≼ Δ.
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

Lemma env_order_lt_le_trans Γ Γ' Γ'' : (Γ ≺ Γ') -> (Γ' ≼ Γ'') -> Γ ≺ Γ''.
Proof. intros Hlt [Hlt' | Heq]. transitivity Γ'; auto with order. now rewrite <- Heq. Qed.

Lemma env_order_le_lt_trans Γ Γ' Γ'' : (Γ ≼ Γ') -> (Γ' ≺ Γ'') -> Γ ≺ Γ''.
Proof. intros [Hlt' | Heq] Hlt. transitivity Γ'; auto with order. now rewrite Heq. Qed.

Lemma remove_In_env_order Δ φ:  In φ Δ -> rm φ Δ ≺ Δ.
Proof.
intro Hin. apply remove_In_env_order_refl in Hin.
eapply env_order_lt_le_trans; [|apply Hin]. auto with order.
Qed.

Global Hint Resolve remove_In_env_order : order.

Lemma elem_of_list_In_1 {A : Type}: ∀ (l : list A) (x : A), x ∈ l -> In x l.
Proof. apply elem_of_list_In. Qed.

Global Hint Resolve  elem_of_list_In_1 : order.

Lemma elements_elem_of {Γ : env} {φ : form} : φ ∈ Γ -> elements Γ ≡ₚ φ :: elements (Γ ∖ {[φ]}).
Proof. intro Hin. rewrite <- elements_env_add. apply Proper_elements, difference_singleton, Hin. Qed.

Ltac prepare_order := 
repeat (apply env_order_add_compat);
unfold pointed_env_order; subst; simpl; repeat rewrite open_boxes_add; try match goal with
| Δ := _ |- _ => subst Δ; try prepare_order
| Hin : ?a ∈ ?Γ |- context[elements ?Γ] => rewrite (elements_elem_of Hin); try prepare_order
| H : _ ∈ list_to_set_disj _ |- _ => apply elem_of_list_to_set_disj in H; try prepare_order
| H : ?ψ ∈ ?Γ |- ?Γ' ≺ ?Γ => let ψ' := (get_diff_form Γ') in
    apply (env_order_equiv_right_compat (difference_singleton Γ ψ' H)) ||
    (eapply env_order_lt_le_trans ; [| apply (remove_In_env_order_refl _ ψ'); try apply elem_of_list_In; trivial])
| H : ?ψ ∈ ?Γ |- ?Γ' ≺ ?Γ • ?φ => let ψ' := (get_diff_form Γ') in
    apply (env_order_equiv_right_compat (equiv_disj_union_compat_r(difference_singleton Γ ψ' H)))
| H : ?ψ ∈ ?Γ |- ?Γ' ≺ ?Γ • _ • _ => let ψ' := (get_diff_form Γ') in
apply (env_order_equiv_right_compat (equiv_disj_union_compat_r(equiv_disj_union_compat_r(difference_singleton Γ ψ' H)))) ||
(eapply env_order_le_lt_trans; [| apply env_order_add_compat; 
eapply env_order_lt_le_trans; [| (apply env_order_eq_add; apply (remove_In_env_order_refl _ ψ'); try apply elem_of_list_In; trivial) ] ] )
end.


(* ad hoc *)
Lemma openboxes_env_order Δ δ :  (map open_box Δ) • δ • δ ≺ Δ • □ δ.
Proof.
induction Δ as [|x Δ].
- simpl. unfold env_order, ltof, env_weight. simpl.
  repeat rewrite <- plus_n_O. apply Nat.add_lt_mono_l.
  rewrite plus_n_O at 1. auto with *.
- apply (@env_order_equiv_right_compat _  _ (Δ • □ δ • x)). constructor.
  simpl.
  eapply (@env_order_equiv_left_compat  _ _ (map open_box Δ • δ • δ •  ⊙ x)).
  + do 2 (rewrite (Permutation_swap δ (⊙ x)); apply Permutation_skip). trivial.
  + case x; intros; simpl; try (solve[now apply env_order_add_compat]).
      transitivity (Δ • □δ • f).
      * auto with *.
      * apply env_order_1. simpl. auto.
Qed.

Global Hint Resolve openboxes_env_order : order.

Ltac order_tac :=
try unfold pointed_env_ms_order; prepare_order;
repeat rewrite elements_env_add; 
simpl; auto 10 with order;
try (apply env_order_disj_union_compat_right; order_tac).
