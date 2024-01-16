Require Export ISL.Environments.


Definition env_order (Γ Δ : env): Prop := MO.MultisetGt form_order Δ Γ.
Infix "≺" := env_order (at level 150).

Notation "Δ ≼ Δ'" := ((Δ ≺ Δ') \/ Δ ≡ Δ') (at level 150).

Global Hint Unfold form_order : mset.


Global Instance env_order_trans : Transitive env_order.
Proof. unfold env_order. intros a b c H1 H2. now apply mord_trans with b. Qed.


(** Here we use the theorem of (Dershowitz Manna 1979), formalized in CoLoR as mord_wf, which says that the multiset ordering over a well-founded
     ordering (in our case, the one given by formula weight) is again well-founded. *)
Definition wf_env_order : well_founded env_order.
Proof.
  apply mord_wf.
  - unfold Sid.Eq.eqA. intros s y Heq; now subst.
  - now apply well_founded_lt_compat with (f := weight).
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
Proof.
  unfold pointed_env_order.
  apply Inverse_Image.wf_inverse_image, wf_env_order.
Qed.


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
intros Hw.
constructor. econstructor; [reflexivity| reflexivity|].
intros y Hy. apply MSet.member_singleton in Hy. rewrite Hy. trivial.
Qed.

Lemma env_order_compat  Δ Δ' φ1 φ : weight φ1 < weight φ -> (Δ' ≼ Δ) -> Δ' • φ1 ≺ Δ • φ.
Proof.
intros Hw [Hlt | Heq].
- transitivity (Δ' • φ); auto using env_order_1 with *.
  apply mord_ext_r; auto with *. apply irreflexive_form_order.
- subst. rewrite Heq. now apply env_order_1.
Qed.

Global Hint Resolve env_order_compat : order.

Lemma env_order_add_compat Δ Δ' φ : (Δ ≺ Δ') -> (Δ • φ) ≺ (Δ' • φ).
Proof.
  intro Hlt. induction Hlt as [Δ1 Δ2 Hlt | Δ1 Δ2 Δ0 Hlt1 IHHlt1 Hlt2 IHHlt2].
  - destruct Hlt as [Δ0 a Y Heq1 Heq2 Hall].
    constructor. apply (@MSetRed form_order _ _ (Δ0 • φ) a Y); ms.
  - unfold env_order. etransitivity; [exact IHHlt1| exact IHHlt2].
Qed.

(* TODO: this is just a special case *)
Lemma env_order_disj_union_compat_left Δ Δ' Δ'':
  (Δ ≺ Δ'') -> Δ ⊎ Δ' ≺ Δ'' ⊎ Δ'.
Proof.
intro Hlt. induction Hlt as [Δ1 Δ2 Hlt | Δ1 Δ2 Δ0 Hlt1 IHHlt1 Hlt2 IHHlt2].
- destruct Hlt as [Δ0 a Y Heq1 Heq2 Hall].
  constructor. apply (@MSetRed form_order _ _ (Δ0 ⊎ Δ') a Y); ms.
- unfold env_order. etransitivity; [exact IHHlt1| exact IHHlt2].
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
- apply Operators_Properties.clos_rt_t with (Δ''  ⊎ Δ').
  + apply RelUtil.tc_incl_rtc. now apply env_order_disj_union_compat_right.
  + now apply env_order_disj_union_compat_left.
- rewrite Heq. now apply env_order_disj_union_compat_left.
Qed.

(*
Lemma open_box_env_order(φ : form) : ({[+ ⊙φ +]} ≺ {[+ φ +]}) \/ ({[+ ⊙ φ +]} = {[+ φ +]}).
Proof.

Qed.
*)
Lemma open_boxes_env_order Δ : (⊗Δ) ≼ Δ.
Proof.
induction Δ as [|φ Δ] using gmultiset_rec.
- right. autorewrite with proof. auto.
- destruct IHΔ as [Hlt | Heq].
  + left. autorewrite with proof. eapply (Proper_env_order _ ((⊗Δ) • ⊙φ) _ _ (Δ•φ)). ms.
      apply env_order_disj_union_compat_strong_right. trivial.
      destruct φ; simpl; try ms. left. (* TODO: lemme *)
      eapply (Proper_env_order _ (∅ • φ) _ _ (∅•□φ) _ ). Unshelve. all: try ms.
      apply env_order_1. simpl. lia.
  + rewrite open_boxes_disj_union, open_boxes_singleton, Heq.
      case_eq (is_box φ); intro Hbox; simpl.
      * left. apply env_order_disj_union_compat_strong_right; [|ms].
         destruct φ; simpl in *; try inversion Hbox.
         eapply (Proper_env_order _ (∅ • φ) _ _ (∅•□φ) _ ). Unshelve. all: try ms. apply env_order_1. simpl. lia.
      * right. destruct φ; simpl in *; ms.
Qed.

Global Hint Resolve open_boxes_env_order : order.

Global Instance assoc_meq_union : Assoc meq union.
Proof. intros x y z. ms. Qed.

Lemma env_order_0 Δ φ: Δ ≺ Δ • φ.
Proof.
constructor. econstructor; [reflexivity| now rewrite MSet.union_empty|].
intros y Hy. exfalso. eapply MSet.not_empty; [exact Hy| ms].
Qed.

(* TODO: ok? to replace env_order_* ?
Lemma env_order_l (Δ' Δ: env) φ1 φ: weight φ1 < weight φ -> (Δ' ≺ Δ • φ) -> (Δ' • φ1) ≺ (Δ • φ).
Proof.
*)

Lemma env_order_2  Δ Δ' φ1 φ2 φ: weight φ1 < weight φ -> weight φ2 < weight φ ->
  (Δ' ≼ Δ) -> Δ' • φ1 • φ2 ≺ Δ • φ.
Proof.
intros Hw1 Hw2 Hor.
eapply (Proper_env_order  _ ((∅ • φ1 • φ2) ⊎ Δ') _ _ ((∅ • φ) ⊎ Δ)) . ms.
apply env_order_disj_union_compat_strong_right; trivial.
constructor. econstructor; [reflexivity| |].
- rewrite assoc; [reflexivity|]. apply assoc_meq_union.
- intros y Hy.
  apply MSet.member_union in Hy; destruct Hy as [Hy|Hy];
  apply MSet.member_singleton in Hy; now rewrite Hy.
Unshelve. ms.
Qed.

Lemma env_order_3  Δ Δ' φ1 φ2 φ3 φ: 
  weight φ1 < weight φ -> weight φ2 < weight φ -> weight φ3 < weight φ -> (Δ' ≼ Δ) ->
  Δ' • φ1 • φ2  • φ3 ≺ Δ • φ.
Proof.
intros Hw1 Hw2 Hw3 Hor.
eapply (Proper_env_order  _ ((∅ • φ1 • φ2 • φ3) ⊎ Δ') _ _ ((∅ • φ) ⊎ Δ)) . ms.
apply env_order_disj_union_compat_strong_right; trivial.
constructor. eapply MSetRed with (Y := ∅ • φ1 • φ2 • φ3); [reflexivity| |].
- ms.
- intros y Hy.
  repeat (apply MSet.member_union in Hy; destruct Hy as [Hy|Hy];
  [|apply MSet.member_singleton in Hy; now rewrite Hy]).
  apply MSet.not_empty in Hy; ms.
Unshelve. ms.
Qed.

Lemma env_order_4  Δ Δ' φ1 φ2 φ3 φ4 φ: 
  weight φ1 < weight φ -> weight φ2 < weight φ -> weight φ3 < weight φ -> weight φ4 < weight φ ->
   (Δ' ≼ Δ) -> Δ' • φ1 • φ2  • φ3 • φ4 ≺ Δ • φ.
Proof.
intros Hw1 Hw2 Hw3 Hw4 Hor.
eapply (Proper_env_order  _ ((∅ • φ1 • φ2 • φ3 • φ4) ⊎ Δ') _ _ ((∅ • φ) ⊎ Δ)) . ms.
apply env_order_disj_union_compat_strong_right; trivial.
constructor. eapply MSetRed with (Y := ∅ • φ1 • φ2 • φ3 • φ4); [reflexivity| |].
- ms.
- intros y Hy.
  repeat (apply MSet.member_union in Hy; destruct Hy as [Hy|Hy];
  [|apply MSet.member_singleton in Hy; now rewrite Hy]).
  apply MSet.not_empty in Hy; ms.
Unshelve. ms.
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

Global Hint Resolve openboxes_env_order : order.

Ltac order_tac := prepare_order; auto 10 with order.

