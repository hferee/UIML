(* Definition of Kripke frames *)

Require Import Syntax.CML_Syntax.
Import String.

(* In the following, we say forces in the classical case, and satisfies in the intuitionistic one *)
Class ClassicalKripkeModel (W : Type) (R : W -> W -> Prop) : Type :=
  { forces : W -> MPropF -> Prop ;
     kripke_negation : forall w A, forces w (¬A) <-> ~ forces w A;
     kripke_implication: forall w A B, forces w (A --> B) <-> ~ (forces w A) \/ (forces w B);
  }.

Class ClassicalModalKripkeModel W R : Type :=
  {
  classical_modal_kripke_classical : ClassicalKripkeModel W R;
  kripke_modality: forall w A, forces w (Box A) <-> forall u, R w u -> forces u A }.

(* TODO: the satisfaction relation is uniquely determined by its value on propositional variables ; change name *)
Lemma satisfiability_variables W R (M : @ClassicalModalKripkeModel W R) (M' : ClassicalModalKripkeModel W R) :
  let (s, _) := M in (* TODO: better syntax? *)
  let (s, _, _) := s in
  let (s', _) := M' in
  let (s', _, _) := s' in
  (forall p w, s w (Var p) <-> s' w (Var p)) -> (forall φ w, s w φ <-> s' w φ).
Proof. (* TODO: probably only true in the classical case *)
  destruct M as [[s KN KI] KM]. destruct M' as [[s' KN' KI'] KM']. intro Hp.
  induction φ; intro w.
  - trivial.
  - admit. (* Wikipedia seems to miss ⊥ in its formulas! *)
  - rewrite KI, KI', IHφ1, IHφ2. tauto.
  - rewrite KM, KM'. split; intros Hi u Hu; [ rewrite <- IHφ | rewrite IHφ]; apply Hi; trivial.
Admitted.