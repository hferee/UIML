(** * Environments

  An environment is a multiset of formulas. We rely on stdpp multisets
  mostly for their powerful multiset equivalence tactic.*)


(** Notion of wellfoundedness *)
Require Import Coq.Program.Wf.

(** Stdpp implementation of multisets *)
Require Export stdpp.gmultiset.

(** Our propositional formulas, including their countability. *)
Require Export ISL.Formulas.

Require Import Coq.Program.Equality.

(** An environment is defined as a finite multiset of formulas
(in the sense of the stdpp library).
This requires decidable equality and countability of the underlying set. *)
Definition env {K : Kind} := @gmultiset (@form K) form_eq_dec form_count.

Global Instance singleton {K : Kind} : Singleton form (@env K) := gmultiset_singleton.
Global Instance singletonMS {K : Kind} : SingletonMS form env := base.singleton.

Global Hint Unfold mult empty singleton union intersection env : mset.
(* useful notations :
  {[ x ]} : singleton
      ⊎ : disjoint union
   \: difference (setminus)
   {[ x; y; … ]} union of singletons
   [{[+ x; y; … +]}] *disjoint* union of singletons
      ⊂@ : include
*)

Definition empty {K : Kind} := ∅ : env.

Ltac ms :=
  unfold base.singletonMS, singletonMS, base.empty, gmultiset_empty in *;
  autounfold with mset in *; autounfold with mset;
  repeat rewrite gmultiset_elem_of_disj_union; try tauto;
  multiset_solver.

Notation "Γ • φ" := (disj_union Γ (base.singletonMS φ)) (at level 105, φ at level 85, left associativity).

Section GeneralEnvironments.
Context {K : Kind}.

Global Instance proper_elem_of : Proper ((=) ==> (≡@{env}) ==> (fun x y => x <-> y)) elem_of.
Proof. intros Γ Γ' Heq φ φ' Heq'. ms. Qed.

Global Instance proper_disj_union : Proper ((≡@{env}) ==> (≡@{env}) ==> (≡@{env})) disj_union.
Proof. intros Γ Γ' Heq Δ Δ' Heq'. ms. Qed.

Lemma elements_env_add (Γ : env) φ : elements(Γ • φ) ≡ₚ φ :: elements Γ.
Proof.
setoid_rewrite (gmultiset_elements_disj_union Γ).
setoid_rewrite (gmultiset_elements_singleton φ).
symmetry. apply Permutation_cons_append.
Qed.

(** ** Multiset utilities *)

Lemma multeq_meq (M N: env) : (forall x, multiplicity x M = multiplicity x N) -> M ≡  N.
  Proof. multiset_solver. Qed.

Lemma diff_mult (M N : env) x:
  multiplicity x (M ∖ N) = (multiplicity x M - multiplicity x N)%nat.
Proof. apply multiplicity_difference. Qed.

Lemma union_mult (M N : env) x :
  multiplicity x (M ⊎ N) = (multiplicity x M + multiplicity x N)%nat.
Proof. apply multiplicity_disj_union. Qed.

Lemma singleton_mult_in x y: x = y -> multiplicity x {[+ y +]} = 1.
Proof.
  intro Heq. rewrite Heq. apply multiplicity_singleton. Qed.

Lemma singleton_mult_notin x y: x <> y -> multiplicity x {[y]} = 0.
Proof. apply multiplicity_singleton_ne. Qed.

(* Two useful basic facts about multisets containing (or not) certain elements. *)
Lemma env_replace {Γ : env} φ {ψ}:
  (ψ ∈ Γ) -> (Γ • φ) ∖ {[ψ]} ≡ (Γ ∖ {[ψ]} • φ).
Proof.
intro Hin. apply multeq_meq. intros θ.
rewrite diff_mult, union_mult, union_mult, diff_mult.
apply PeanoNat.Nat.add_sub_swap.
case (decide (θ = ψ)); intro; subst.
- now rewrite singleton_mult_in.
- rewrite singleton_mult_notin; trivial. lia.
Qed.

Lemma diff_not_in (Γ : env) φ : φ ∉ Γ -> Γ ∖ {[φ]} ≡ Γ.
Proof.
intro Hf. apply multeq_meq. intros ψ.
rewrite diff_mult. rewrite (elem_of_multiplicity φ Γ) in Hf.
unfold mult.
case (decide (φ = ψ)).
- intro; subst. lia.
- intro Hneq. setoid_rewrite (multiplicity_singleton_ne ψ φ); trivial. lia.
  auto.
Qed.

Lemma env_add_remove : ∀ (Γ: env) φ, (Γ • φ) ∖ {[φ]} =Γ.
Proof. intros; ms. Qed.

(** ** Conjunction, disjunction, and implication *)
(** In the construction of propositional quantifiers, we often want to take the
    conjunction, disjunction, or implication of a (multi)set of formulas.
    The following results give some small optimizations of this process, by
    reducing "obvious" conjunctions such as ⊤ ∧ ϕ, ⊥ ∧ ϕ, etc. *)

Definition irreducible (Γ : env) :=
  (∀ p φ, (Var p → φ) ∈ Γ -> ¬ Var p ∈ Γ) /\
  ¬ ⊥ ∈ Γ /\
  ∀ φ ψ, ¬ (φ ∧ ψ) ∈ Γ /\ ¬ (φ ∨ ψ) ∈ Γ.


Definition is_double_negation φ ψ := φ = ¬ ¬ ψ.
Global Instance decidable_is_double_negation φ ψ :
  Decision (is_double_negation φ ψ) := decide (φ =  ¬ ¬ ψ).

Definition is_implication {K : Kind} (φ ψ : form) := exists θ, φ = (θ → ψ).
Global Instance decidable_is_implication φ ψ : Decision (is_implication φ ψ).
Proof.
unfold is_implication.
destruct φ; try solve[right; intros [θ Hθ]; discriminate].
case (decide (φ2 = ψ)).
- intro; subst. left. eexists; reflexivity.
- intro n. right; intros [θ Hθ]. now dependent destruction Hθ.
Defined.

Definition is_negation φ ψ := φ = ¬ ψ.
Global Instance decidable_is_negation φ ψ : Decision (is_negation φ ψ) := decide (φ =  ¬ ψ).

(** ** A dependent version of `map` *)
(* a dependent map on lists, with knowledge that we are on that list *)
(* should work with any set-like type *)

Program Fixpoint in_map_aux {A : Type} (Γ : list form) (f : forall φ, (φ ∈ Γ) -> A)
 Γ' (HΓ' : Γ' ⊆ Γ) : list A:=
match Γ' with
| [] => []
| a::Γ' => f a _ :: in_map_aux Γ f Γ' _
end.
Next Obligation.
intros. auto with *.
Qed.
Next Obligation. auto with *. Qed.


Definition in_map {A : Type} Γ
  (f : forall φ, (φ ∈ Γ) -> A) : list A :=
  in_map_aux Γ f Γ (reflexivity _).


(* This generalises to any type. decidability of equality over this type is necessary for a result in "Type" *)
Lemma in_in_map {A : Type} {HD : forall a b : A, Decision (a = b)}
  Γ (f : forall φ, (φ ∈ Γ) -> A) ψ :
  ψ ∈ (in_map Γ f) -> {ψ0 & {Hin | ψ = f ψ0 Hin}}.
Proof.
unfold in_map.
assert(Hcut : forall Γ' (HΓ' : Γ' ⊆ Γ), ψ ∈ in_map_aux Γ f Γ' HΓ'
  → {ψ0 & {Hin : ψ0 ∈ Γ | ψ = f ψ0 Hin}}); [|apply Hcut].
induction Γ'; simpl; intros HΓ' Hin.
- contradict Hin. auto. now rewrite elem_of_nil.
- match goal with | H : ψ ∈ ?a :: (in_map_aux _ _ _ ?HΓ'') |- _ =>
  case (decide (ψ = a)); [| pose (myHΓ' := HΓ'')] end.
  + intro Heq; subst. exists a. eexists. reflexivity.
  + intro Hneq. apply (IHΓ' myHΓ').
    apply elem_of_cons in Hin. tauto.
Qed.

Local Definition in_subset {Γ : env} {Γ'} (Hi : Γ' ⊆ elements Γ) {ψ0} (Hin : ψ0 ∈ Γ') : ψ0 ∈ Γ.
Proof. apply gmultiset_elem_of_elements,Hi, Hin. Defined.

(* converse *)
(* we require proof irrelevance for the mapped function *)
Lemma in_map_in {A : Type} {HD : forall a b : A, Decision (a = b)}
  {Γ} {f : forall φ, (φ ∈ Γ) -> A} {ψ0} (Hin : ψ0 ∈ Γ):
  {Hin' | f ψ0 Hin' ∈ (in_map Γ f)}.
Proof.
unfold in_map.
assert(Hcut : forall Γ' (HΓ' : Γ' ⊆ Γ) ψ0 (Hin : In ψ0 Γ'),
  {Hin' | f ψ0 Hin' ∈ in_map_aux Γ f Γ' HΓ'}).
- induction Γ'; simpl; intros HΓ' ψ' Hin'; [auto with *|].
  case (decide (ψ' = a)).
  + intro; subst a. eexists. left.
  + intro Hneq. assert (Hin'' : In ψ' Γ') by (destruct Hin'; subst; tauto).
      pose (Hincl := (in_map_aux_obligation_2 Γ (a :: Γ') HΓ' a Γ' eq_refl)).
      destruct (IHΓ' Hincl ψ' Hin'') as [Hin0 Hprop].
      eexists. right. apply Hprop.
- destruct (Hcut Γ (reflexivity Γ) ψ0) as [Hin' Hprop].
  + auto. now apply elem_of_list_In.
  + exists Hin'. exact Hprop.
Qed.

Lemma in_map_empty A f : @in_map A [] f = [].
Proof. auto with *. Qed.

Lemma in_map_ext {A} Δ f g:
  (forall φ H, f φ H = g φ H) -> @in_map A Δ f = in_map Δ g.
Proof.
  intros Heq.
  unfold in_map.
  assert(forall Γ HΓ, in_map_aux Δ f Γ  HΓ = in_map_aux Δ g Γ  HΓ); [|trivial].
  induction Γ; intro HΓ.
  - trivial.
  - simpl. now rewrite Heq, IHΓ.
Qed.

Lemma difference_singleton (Δ: env) φ: φ ∈ Δ -> Δ ≡ ((Δ ∖ {[φ]}) • φ).
Proof.
intro Hin. rewrite (gmultiset_disj_union_difference {[φ]}) at 1. ms.
now apply gmultiset_singleton_subseteq_l.
Qed.

Lemma env_in_add (Δ : env) ϕ φ: φ ∈ (Δ • ϕ) <-> φ = ϕ \/ φ ∈ Δ.
Proof.
rewrite (gmultiset_elem_of_disj_union Δ), gmultiset_elem_of_singleton.
tauto.
Qed.

Lemma equiv_disj_union_compat_r {Δ Δ' Δ'' : env} : Δ ≡ Δ'' -> Δ ⊎ Δ' ≡ Δ'' ⊎ Δ'.
Proof. ms. Qed.

Lemma env_add_comm (Δ : env) φ ϕ : (Δ • φ • ϕ) ≡ (Δ • ϕ • φ).
Proof. ms. Qed.

Lemma in_difference (Δ : env) φ ψ : φ ≠ ψ -> φ ∈ Δ -> φ ∈ Δ ∖ {[ψ]}.
Proof.
intros Hne Hin.
unfold elem_of, gmultiset_elem_of.
rewrite (multiplicity_difference Δ {[ψ]} φ).
assert( HH := multiplicity_singleton_ne φ ψ Hne).
unfold singletonMS, base.singletonMS in HH.
unfold base.singleton, Environments.singleton. ms.
Qed.

Hint Resolve in_difference : multiset.

(* could be used in disj_inv *)
Lemma env_add_inv (Γ Γ' : env) φ ψ:
  φ ≠ ψ ->
  ((Γ • φ) ≡ (Γ' • ψ)) ->
    (Γ' ≡  ((Γ ∖ {[ψ]}) • φ)).
Proof.
intros Hneq Heq. rewrite <- env_replace.
- ms.
- assert(ψ ∈ (Γ • φ)); [rewrite Heq|]; ms.
Qed.

Lemma env_add_inv' (Γ Γ' : env) φ: (Γ • φ) ≡ Γ' -> (Γ ≡  (Γ' ∖ {[φ]})).
Proof. intro Heq. ms. Qed.

Lemma env_equiv_eq (Γ Γ' :env) : Γ =  Γ' -> Γ ≡  Γ'.
Proof. intro; subst; trivial. Qed.

(* reprove the following principles, proved in stdpp for Prop, but
   we need them in Type *)
Lemma gmultiset_choose_or_empty (X : env) : {x | x ∈ X} + {X = ∅}.
Proof.
  destruct (elements X) as [|x l] eqn:HX; [right|left].
  - by apply gmultiset_elements_empty_inv.
  - exists x. rewrite <- (gmultiset_elem_of_elements x X).
    replace (elements X) with (x :: l). left.
Qed.

(* We need this induction principle in type. *)
Lemma gmultiset_rec (P : env → Type) :
  P ∅ → (∀ x X, P X → P ({[+ x +]} ⊎ X)) → ∀ X, P X.
Proof.
  intros Hemp Hinsert X. induction (gmultiset_wf X) as [X _ IH].
  destruct (gmultiset_choose_or_empty X) as [[x Hx]| ->]; auto.
  rewrite (gmultiset_disj_union_difference' x X) by done.
  apply Hinsert, IH; multiset_solver.
Qed.

Lemma difference_include θ θ' (Δ : env) :
  (θ' ∈ Δ) ->
  θ ∈ Δ ∖ {[θ']} -> θ ∈ Δ.
Proof.
intros Hin' Hin.
rewrite gmultiset_disj_union_difference with (X := {[θ']}).
- apply gmultiset_elem_of_disj_union. tauto.
- now apply gmultiset_singleton_subseteq_l.
Qed.

Fixpoint rm x l := match l with
| h :: t => if form_eq_dec x h then t else h :: rm x t
| [] => []
end.

Lemma in_rm l x y: In x (rm y l) -> In x l.
Proof.
induction l; simpl. tauto.
destruct form_eq_dec. tauto. firstorder.
Qed.

Lemma remove_include θ θ' Δ : (θ' ∈ Δ) -> θ ∈ rm θ' Δ -> θ ∈ Δ.
Proof. intros Hin' Hin. eapply elem_of_list_In, in_rm, elem_of_list_In, Hin. Qed.


(* technical lemma : one can constructively find whether an environment contains
   an element satisfying a decidable property *)
Lemma decide_in (P : _ -> Prop) (Γ : env) :
  (forall φ, Decision (P φ)) ->
  {φ | (φ ∈ Γ) /\ P φ} + {forall φ, φ ∈ Γ -> ¬ P φ}.
Proof.
intro HP.
induction Γ using gmultiset_rec.
- right. intros φ Hφ; inversion Hφ.
- destruct IHΓ as [(φ&Hφ) | HF].
  + left. exists φ. ms.
  + case (HP x); intro Hx.
    * left; exists x. ms.
    * right. intros. ms.
Qed.

Lemma union_difference_L (Γ : env) Δ ϕ: ϕ ∈ Γ -> (Γ ⊎ Δ) ∖ {[ϕ]} ≡ Γ ∖{[ϕ]} ⊎ Δ.
Proof. intro Hin. pose (difference_singleton _ _ Hin). ms. Qed.

Lemma union_difference_R (Γ : env) Δ ϕ: ϕ ∈ Δ -> (Γ ⊎ Δ) ∖ {[ϕ]} ≡ Γ ⊎ (Δ ∖{[ϕ]}).
Proof. intro Hin. pose (difference_singleton _ _ Hin). ms. Qed.

Global Instance equiv_assoc : @Assoc env equiv disj_union.
Proof. intros x y z. ms. Qed.

Global Instance proper_difference : Proper ((≡@{env}) ==> eq ==> (≡@{env})) difference.
Proof. intros Γ Γ' Heq Δ Heq'. ms. Qed.

Definition var_not_in_env p (Γ : env):=  (∀ φ0, φ0 ∈ Γ -> ¬ occurs_in p φ0).

(** ** Tactics *)
(* helper tactic split cases given an assumption about belonging to a multiset *)

End GeneralEnvironments.

Global Ltac in_tac :=
repeat
match goal with
| H : ?θ  ∈ {[?θ1; ?θ2]} |- _ => apply gmultiset_elem_of_union in H; destruct H as [H|H]; try subst
| H : ?θ ∈ (?Δ ∖ {[?θ']}) |- _ => apply difference_include in H; trivial
| H : context [?θ  ∈ (?d • ?θ2)] |- _ =>
    rewrite (env_in_add d) in H; destruct H as [H|H]; try subst
| H : context [?θ ∈ {[ ?θ2 ]}] |- _ => rewrite gmultiset_elem_of_singleton in H; subst
end.


Global Hint Immediate equiv_assoc : proof.

Definition open_box {K : Kind} (φ : @form K) : @form K := match φ with
| □ φ => φ
| φ => φ
end.

(* inefficient conversion from multisets to lists and back *)
Definition open_boxes {K : Kind} (Γ : @env K) : @env K :=
  list_to_set_disj (map open_box (elements Γ)).

Notation "⊙ φ" := (open_box φ) (at level 75).
Notation "⊗ Γ" := (open_boxes Γ) (at level 75).

Section Modal.

Context {K : Kind}.

Global Instance proper_open_boxes : Proper ((≡@{env}) ==> (≡@{env})) open_boxes.
Proof. intros Γ Heq Δ Heq'. ms. Qed.

Lemma open_boxes_empty : open_boxes ∅ = ∅.
Proof. auto. Qed.

Lemma open_boxes_disj_union Γ Δ : (open_boxes (Γ ⊎ Δ)) = (open_boxes Γ ⊎ open_boxes Δ).
Proof.
unfold open_boxes. rewrite (gmultiset_elements_disj_union Γ Δ).
rewrite map_app. apply list_to_set_disj_app.
Qed.

Lemma open_boxes_singleton φ : open_boxes {[φ]} = {[⊙ φ]}.
Proof.
unfold open_boxes.
assert (HH := gmultiset_elements_singleton φ).
unfold elements, base.singletonMS, singletonMS, base.singleton, Environments.singleton in *.
rewrite HH. simpl. unfold base.singletonMS, disj_union, empty.
apply gmultiset_disj_union_right_id.
Qed.


Lemma open_boxes_add (Γ : env) φ : (⊗ (Γ • φ)) = (⊗ Γ • ⊙ φ).
Proof.
rewrite open_boxes_disj_union.
unfold open_boxes. f_equal. apply open_boxes_singleton.
Qed.

Local Definition f_inj {K K': Kind} {T : Kind -> Type} (Heq : K = K') (φ : T K) : T K' :=
  eq_rect K T φ K' Heq.

Local Definition env_inj {K K': Kind} (Heq : K = K') (d : list (@form K)) : list (@form K')
:= (eq_rect K (fun K => list (@form K)) d K' Heq).

Lemma elem_of_open_boxes (φ : @form K) Δ : φ ∈ (⊗Δ) ->
  (φ ∈ Δ) \/
  exists (HK : K = Modal), (□ (f_inj HK φ)) ∈ (f_inj HK Δ).
Proof.
intro Hin.
induction Δ as [|θ Δ Hind] using gmultiset_rec.
- auto.
- rewrite open_boxes_disj_union in Hin.
  apply gmultiset_elem_of_disj_union in Hin.
  destruct Hin as [Hθ | HΔ].
  + clear Hind.
    rewrite open_boxes_singleton in Hθ. apply gmultiset_elem_of_singleton in Hθ.
    subst φ. destruct θ; try ms. simpl.
    right. exists eq_refl. ms.
  + destruct (Hind HΔ) as [Hin | [HK Heq]].
    * ms.
    * right. exists HK. ms.
Qed.

Lemma occurs_in_open_boxes x (φ : form) Δ :
  occurs_in x φ -> φ ∈ (⊗Δ) -> exists θ, θ ∈ Δ /\ occurs_in x θ.
Proof.
intros Hx Hφ. apply elem_of_open_boxes in Hφ. destruct Hφ as [Hφ|[HK Hφ]]; eauto.
subst. unfold f_inj in *.
eexists; eauto.
Qed.

Lemma occurs_in_map_open_box x (φ : form) Δ :
  occurs_in x φ -> φ ∈ (map open_box Δ) -> exists θ, θ ∈ Δ /\ occurs_in x θ.
Proof.
intros Hx Hφ. apply elem_of_list_In, in_map_iff in Hφ.
destruct Hφ as [ψ [Hφ Hin]]; subst.
exists ψ. split. now apply elem_of_list_In. dependent destruction ψ; trivial.
Qed.

Lemma open_boxes_remove Γ φ : φ ∈ Γ -> (≡@{env}) (⊗ (Γ ∖ {[φ]})) ((⊗ Γ) ∖ {[⊙ φ]}).
Proof.
intro Hin.
 pose (difference_singleton Γ φ Hin). rewrite e  at 2.
rewrite open_boxes_add. ms.
Qed.

Definition is_box (φ : form) := match φ with
| □ _ => true
| _ => false
end.

Lemma is_not_box_open_box φ : is_box φ = false -> (⊙φ) = φ.
Proof. unfold is_box. dependent destruction φ; simpl; intuition. discriminate. Qed.

Lemma open_boxes_spec' Γ φ :
    {_ : φ ∈ Γ & is_box φ = false}
  + {HK : K = Modal & (□ f_inj HK φ) ∈ f_inj HK Γ} -> φ ∈ open_boxes Γ.
Proof.
intros [[Hin Heq] | [HK Hin]];
unfold open_boxes; apply elem_of_list_to_set_disj, elem_of_list_In, in_map_iff.
- exists φ. apply is_not_box_open_box in Heq. rewrite Heq. split; trivial.
  now apply elem_of_list_In,  gmultiset_elem_of_elements.
- subst. exists (□ φ). simpl. split; trivial. now apply elem_of_list_In,  gmultiset_elem_of_elements.
Qed.

Lemma In_open_boxes (Γ : env) φ : (φ ∈ Γ) -> open_box φ ∈ open_boxes Γ.
Proof.
intro Hin. apply difference_singleton in Hin.
rewrite Hin,  open_boxes_add. auto with *.
Qed.

Global Instance Proper_elements:
  Proper ((≡) ==> (≡ₚ)) ((λ Γ : env, gmultiset_elements Γ)).
Proof.
intros Γ Δ Heq; apply AntiSymm_instance_0; apply gmultiset_elements_submseteq; ms.
Qed.

Lemma elements_open_boxes Γ: elements (⊗ Γ) ≡ₚ map open_box (elements Γ).
Proof.
unfold open_boxes. remember (elements Γ) as l. clear Γ Heql.
induction l as [| a l].
- ms.
- simpl. setoid_rewrite gmultiset_elements_disj_union.
  rewrite IHl. setoid_rewrite gmultiset_elements_singleton. trivial.
Qed.

Lemma list_to_set_disj_env_add Δ v:
  ((list_to_set_disj Δ : env) • v : env) ≡ list_to_set_disj (v :: Δ).
Proof. ms. Qed.

Lemma list_to_set_disj_rm Δ v:
  (list_to_set_disj Δ : env) ∖ {[v]} ≡ list_to_set_disj (rm v Δ).
Proof.
induction Δ as [|φ Δ]; simpl; [ms|].
case form_eq_dec; intro; subst; [ms|].
simpl. rewrite <- IHΔ. case (decide (v ∈ (list_to_set_disj Δ: env))).
- intro. rewrite union_difference_R by assumption. ms.
- intro. rewrite diff_not_in by auto with *. rewrite diff_not_in; auto with *.
Qed.


Lemma gmultiset_elements_list_to_set_disj (l : list form):
  gmultiset_elements(list_to_set_disj l) ≡ₚ l.
Proof.
induction l as [| x l]; [ms|].
rewrite Proper_elements; [|symmetry; apply list_to_set_disj_env_add].
setoid_rewrite elements_env_add; rewrite IHl. trivial.
Qed.

Lemma list_to_set_disj_open_boxes Δ: ((⊗ (list_to_set_disj Δ)) = list_to_set_disj (map open_box Δ)).
Proof. apply list_to_set_disj_perm, Permutation_map', gmultiset_elements_list_to_set_disj. Qed.

End Modal.


Global Hint Resolve In_open_boxes : proof.
Global Hint Unfold open_box : proof.
Global Hint Rewrite (@open_boxes_empty Modal) : proof.
Global Hint Rewrite (@open_boxes_add Modal) : proof.
Global Hint Rewrite (@open_boxes_remove Modal) : proof.
Global Hint Rewrite (@open_boxes_singleton Modal): proof.
Global Hint Resolve open_boxes_spec' : proof.
