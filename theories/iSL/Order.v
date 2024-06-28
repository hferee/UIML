Require Export ISL.SizedFormulas ISL.Formulas.
Require Export List.
Require Export stdpp.gmultiset.
Require Import Coq.Program.Equality.

Section Definitions.

Set Implicit Arguments.
Variable p : variable.


Definition form_of_sig (s : {n & @nform p n}) : form := let (x, n) := s in form_of_nform n.
Definition senv  := list {n & @nform p n}.

Definition pow_weight nφ := 5^ weight (form_of_sig nφ).

(* Note 3 or 4 would suffice for IPC ; iSL requires 5 *)
Definition senv_weight (Γ : senv) := list_sum (map pow_weight Γ).

Lemma senv_weight_disj_union Γ Δ : senv_weight (Γ ++  Δ) = senv_weight Γ +  senv_weight Δ.
Proof. 
unfold senv_weight. 
now rewrite map_app, list_sum_app.
Qed.

Lemma senv_weight_add (Γ : senv) φ : senv_weight ((φ :: Γ)) = pow_weight φ + senv_weight Γ.
Proof.
unfold senv_weight. simpl. lia.
Qed.

Lemma senv_weight_remove_le Δ φ:
  senv_weight (remove (nform_eq_dec p) φ Δ) ≤ senv_weight Δ.
Proof.
induction Δ as [|φ' Δ HΔ]; trivial.
simpl. case nform_eq_dec;
intro; subst; repeat rewrite senv_weight_add; lia.
Qed.


Lemma senv_weight_open_boxes Δ : senv_weight (□⁻¹ Δ) ≤ senv_weight Δ. 
Proof.
unfold senv_weight.
induction Δ as [|[n φ] Δ]; simpl. lia.
apply Nat.add_le_mono; trivial.
apply Nat.pow_le_mono_r. lia.
simpl. destruct φ; simpl; constructor; trivial.
Qed.

Lemma pow_weight_gt φ : 5 <= 5 ^ weight φ.
Proof.
  rewrite <- (Nat.pow_1_r 5) at 1.
  apply Nat.pow_le_mono_r. lia. apply weight_pos.
Qed.

Definition senv_order := ltof senv senv_weight.
Infix "≺" := senv_order (at level 150).

Lemma senv_weight_singleton φ : senv_weight [ φ ] = 5 ^ weight (form_of_sig φ).
Proof.
unfold senv_weight, ltof. simpl. unfold pow_weight; lia.
Qed.
(*
Lemma env_order_singleton (φ ψ : form) : weight φ < weight ψ -> [ φ +]}≺ {[+ ψ +]}.
Proof.
intro Hw. unfold env_order, ltof. do 2 rewrite senv_weight_singleton.
apply Nat.pow_lt_mono_r. lia. trivial.
Qed.
*)
Notation "Δ ≼ Δ'" := ((Δ ≺ Δ') \/ Δ = Δ') (at level 150).

Lemma senv_le_weight Δ Δ' : (Δ' ≼ Δ) -> senv_weight Δ' ≤ senv_weight Δ.
Proof.
unfold senv_order. intros [Hle | Heq].
- auto with *.
- subst; trivial.
Qed.

Global Instance senv_order_trans : Transitive senv_order.
Proof. unfold senv_order, senv_weight, ltof. auto with *. Qed.

Definition wf_senv_order : well_founded senv_order.
Proof. now apply well_founded_lt_compat with senv_weight.
Defined.

(* We introduce a notion of "pointed" environment, which is simply
 * a pair (Δ, φ), where Δ is an environment and φ is a formula,
 * not necessarily an element of Δ.  *)
Definition pointed_senv := (senv * {n & @nform p n})%type.

(* The order on pointed environments is given by considering the
 * environment order on the sum of Δ and {φ}. *)
 (* TODO: modified from G4IP : right-hand side counts twice, to account for the right box rule. Is this working? *)
Definition pointed_senv_order (pe1 : pointed_senv) (pe2 : pointed_senv) :=
  senv_order (snd pe1 :: snd pe1 :: fst pe1) (snd pe2 :: snd pe2 :: fst pe2).

Lemma wf_pointed_order : well_founded pointed_senv_order.
Proof. apply well_founded_ltof. Qed.

(*
Global Instance Proper_senv_order : Proper ((≡@{senv}) ==> (≡@{senv}) ==> (fun x y => x <-> y)) senv_order.
Proof. intros Δ1 Δ2 H12 Δ3 Δ4 H34.
unfold senv_order, ltof,senv_weight.
unfold equiv, sets.set_equiv_instance in *.
 apply Permutation_list_sum in H12.
 Qed.

Lemma env_order_equiv_right_compat {Δ Δ' Δ'' : senv}:
  Δ' ≡ Δ'' ->
  (Δ ≺ Δ'') ->
  Δ ≺ Δ'.
Proof. unfold senv_order, ltof. unfold equiv.

 multiset_solver. Qed.



Lemma env_order_equiv_left_compat {Δ Δ' Δ'' : env}:
  Δ ≡ Δ'' ->
  (Δ'' ≺ Δ') ->
  Δ ≺ Δ'.
Proof. ms. Qed.

*)
(*
Lemma env_order_1  Δ φ1 φ : weight φ1 < weight φ -> Δ • φ1 ≺ Δ • φ.
Proof.
intros Hw.  unfold env_order, ltof. do 2 rewrite senv_weight_add.
apply Nat.add_lt_mono_l. apply Nat.pow_lt_mono_r. lia. trivial.
Qed.

Local Hint Resolve Nat.pow_lt_mono_r : order.

Lemma env_order_compat  Δ Δ' φ1 φ : weight φ1 < weight φ -> (Δ' ≼ Δ) -> Δ' • φ1 ≺ Δ • φ.
Proof.
intros.  unfold env_order, ltof. repeat rewrite senv_weight_add.
apply Nat.add_le_lt_mono; auto with *.
Qed.

Global Hint Resolve env_order_compat : order.
*)
Lemma env_order_add_compat Δ Δ' φ : (Δ ≺ Δ') -> (φ :: Δ) ≺ (φ :: Δ').
Proof.
unfold senv_order, ltof. do 2 rewrite senv_weight_add. lia.
Qed.
(*
(* TODO: this is just a special case *)
Lemma env_order_disj_union_compat_left Δ Δ' Δ'':
  (Δ ≺ Δ'') -> Δ ⊎ Δ' ≺ Δ'' ⊎ Δ'.
Proof.
unfold env_order, ltof. intro. do 2 rewrite senv_weight_disj_union. lia.
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
- unfold env_order, ltof in *. do 2 rewrite senv_weight_disj_union. lia.
- rewrite Heq. now apply env_order_disj_union_compat_left.
Qed.

Lemma env_order_disj_union_compat_strong_left Δ Δ' Δ'' Δ''':
  (Δ ≼ Δ'') -> (Δ' ≺ Δ''') -> Δ ⊎ Δ' ≺ Δ'' ⊎ Δ'''.
Proof.
intros H1 H2. 
destruct H1 as [Hlt|Heq].
- unfold env_order, ltof in *. do 2 rewrite senv_weight_disj_union. lia.
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
unfold env_order, ltof. rewrite senv_weight_disj_union, senv_weight_singleton.
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
unfold env_order, ltof. repeat rewrite senv_weight_add.
apply senv_le_weight in Hor.
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
unfold env_order, ltof. repeat rewrite senv_weight_add.
apply senv_le_weight in Hor.
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
unfold env_order, ltof. repeat rewrite senv_weight_add.
apply senv_le_weight in Hor.
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
*)
End Definitions.

(*
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
*)

Ltac prepare_order := idtac.
(*
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
Global Hint Extern 2 ((?Γ  ∖ {[?ψ]} , ?φ) ≺· (?Γ, ?φ)) => prepare_order : order.
Global Hint Extern 2 (?Γ  ∖ {[?ψ]} • ?φ' • ?φ'' ≺ ?Γ • ?φ) => prepare_order : order.
Global Hint Extern 2 (?Γ  ∖ {[?ψ]} • ?φ' • ?φ'' ≺ ?Γ • ?φ • ?φ''') => prepare_order : order.
Global Hint Extern 2 (?Γ  ∖ {[?ψ]} • ?φ' • ?φ'' • ?φ'''' ≺ ?Γ • ?φ • ?φ''') => prepare_order : order.
Global Hint Extern 2 (?Γ  ∖ {[?ψ]} • ?φ' ≺ ?Γ • ?φ) => prepare_order : order.
Global Hint Extern 2 (?Γ  ∖ {[?ψ]} • ?φ' ≺ ?Γ • ?φ  • ?φ') => prepare_order : order.
*)
Lemma make_impl_weight φ ψ: weight (φ ⇢ ψ) <= weight (φ → ψ).
Proof.
destruct (make_impl_spec φ ψ) as [[[Heq' Heq]|[Heq' Heq]]|Heq]; subst; rewrite Heq; simpl.
- assert (H := weight_pos ψ). lia.
-  lia.
- trivial.
Qed.

Lemma make_impl_weight2 φ ψ θ: weight (φ ⇢ (ψ ⇢ θ)) <= weight (φ → (ψ → θ)).
Proof.
pose (make_impl_weight ψ θ).
pose (make_impl_weight φ (ψ ⇢ θ)).
simpl in *. lia.
Qed.

Global Hint Extern  5  (weight (?φ ⇢ ?ψ) < _) => (eapply Nat.le_lt_trans; [eapply make_impl_weight|]) : order.

Global Hint Extern  5  (weight (?φ ⇢ (?ψ ⇢ ?θ)) < _) => (eapply Nat.le_lt_trans; [eapply make_impl_weight2|]) : order.

(* TODO: new *)

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
*)

Infix "≺·" := pointed_senv_order (at level 150).
Global Hint Rewrite senv_weight_add : order.
(* Global Hint Resolve openboxes_env_order : order. *)
Global Hint Resolve senv_le_weight : order.
Global Hint Unfold form_order : mset.

Lemma senv_order_remove_weak p d Δ φ:
  (@senv_weight p (remove d φ Δ)) <= @senv_weight p Δ.
Proof.
unfold senv_weight.
induction Δ as [| a Δ]; simpl.
- constructor.
- case d; intro; subst; simpl; lia.
Qed.

Lemma senv_order_remove p d Δ φ: φ ∈ Δ ->
  pow_weight φ + (@senv_weight p (remove d φ Δ)) <= @senv_weight p Δ.
Proof.
intro Hin.
induction Δ as [| a Δ]; simpl.
- contradict Hin. auto with *.
- rewrite senv_weight_add. case d; intro; subst; simpl.
  + pose (senv_order_remove_weak d Δ a). lia.
  + rewrite senv_weight_add.
      apply elem_of_cons in Hin. destruct Hin as [Hf | Hin]; [tauto|].
      specialize (IHΔ Hin). lia.
Qed.


(* TODO: technical. move *)

Lemma lt_le_add_trans_r a b c x :(a <= b -> c < x + a -> c < x + b).
Proof. lia. Qed.


Ltac order_tac :=
unfold pointed_senv_order;
repeat (apply env_order_add_compat); simpl;
unfold senv_order, ltof; repeat rewrite senv_weight_add;
try match goal with | Δ := _ |- _ => subst Δ end;
repeat match goal with
  | Heq : existT ?a _ = existT ?a _ |- _ => apply Eqdep.EqdepTheory.inj_pair2 in Heq; subst
  | Heq : existT ?a _ = existT _ _ |- _ => inversion Heq; subst a
  | Heq : existT ?n ?θ = _  |- _ =>
   try subst n; try subst θ; inversion Heq;
   rewrite <- sigT_eta in *; subst; simpl in * end;
repeat rewrite Nat.add_assoc;
   try match goal with Hin : ?ψ ∈ ?Γ |- context C [remove ?d ?ψ ?Γ] =>
   eapply Nat.lt_le_trans; [| exact (senv_order_remove (nform_eq_dec _) Hin)] ||
   eapply (lt_le_add_trans_r _ (senv_order_remove (nform_eq_dec _) Hin))
end;
repeat rewrite Nat.add_assoc;
try refine (Nat.add_lt_le_mono _ _ _ _ _ (senv_weight_open_boxes _));
unfold pow_weight, form_of_sig; simpl weight;
repeat apply Nat.add_lt_mono_r;
simpl Nat.pow;
repeat rewrite ?Nat.pow_succ_r', ?Nat.pow_add_r;
repeat match goal with
|  |- context C [Nat.pow 5 (weight ?δ)] =>
    lazymatch goal with 
    | H :  5 <=  5 ^ (weight δ) |- _ => fail 
    | _ => pose (pow_weight_gt δ) end end;
simpl; unfold pow_weight in *; 
try remember (senv_weight _) as W; try nia;
try match goal with |- context C [?a * ?b * ?c] =>
   (destruct (Nat.add_le_mul a b); [lia | lia | | lia]) end;
 try eapply (lt_le_add_trans_r _ (senv_weight_open_boxes _));
nia.
