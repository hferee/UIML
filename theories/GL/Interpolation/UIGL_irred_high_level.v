(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2.1 FREE SOFTWARE LICENSE AGREEMENT        *)
(**************************************************************)

Require Import List Relations Utf8.

Import ListNotations.

#[local] Infix "∈" := (@In _) (at level 70, no associativity).

Definition list_is_nil {X} (l : list X) : { l = [] } + { l ≠ [] }.
Proof. now destruct l; [ left | right ]. Qed.

Section irred_high_level.

  Variables (X : Type) 
            (f : X → list X)
            (f_wf : well_founded (λ u v, u ∈ f v))
            (irred : X → list X)
            (irred_nil : ∀x, f x = [] → irred x = [x])
            (irred_not : ∀x, f x ≠ [] → irred x = flat_map irred (f x))
            .

  Fact irred_max x y : y ∈ irred x → f y = [].
  Proof.
    induction (f_wf x) as [ x _ IHx ] in y.
    destruct (list_is_nil (f x)) as [ H | H ].
    + rewrite irred_nil; auto.
      now intros [ <- | [] ].
    + rewrite irred_not, in_flat_map; auto.
      intros (z & ? & ?); eauto.
  Qed.

  Fact irred_reach x y : y ∈ irred x → clos_refl_trans _  (λ u v, u ∈ f v) y x.
  Proof.
    induction (f_wf x) as [ x _ IHx ] in y.
    destruct (list_is_nil (f x)) as [ H | H ].
    + rewrite irred_nil; auto.
      intros [ <- | [] ]; constructor 2.
    + rewrite irred_not, in_flat_map; auto.
      intros (z & Hz1 & Hz2).
      constructor 3 with z; auto.
      now constructor 1.
  Qed.

  Hint Resolve in_eq : core.

  Theorem irred_high_level_spec x y : y ∈ irred x ↔ f y = [] ∧ clos_refl_trans _  (λ u v, u ∈ f v) y x.
  Proof.
    split.
    + split.
      * now apply irred_max with x.
      * now apply irred_reach.
    + intros (H1 & H2); revert H2 H1.
      rewrite clos_rt_rtn1_iff.
      induction 1 as [ | x z H1 H2 IH2 ]; intros H.
      * rewrite irred_nil; auto.
      * rewrite irred_not, in_flat_map.
        - exists x; auto.
        - now intros e; rewrite e in H1.
  Qed.

  Section provability.

    Variables (P : X → Prop)
              (HP : ∀x, f x ≠ [] → P x ↔ Forall P (f x)).

    Theorem irred_provability x : P x ↔ Forall P (irred x).
    Proof.
      induction (f_wf x) as [ x _ IHx ].
      destruct (list_is_nil (f x)) as [ H | H ].
      + rewrite irred_nil; auto.
        split.
        * repeat (constructor; auto).
        * now inversion 1.
      + rewrite irred_not; auto.
        rewrite Forall_flat_map, HP; auto.
        rewrite !Forall_forall.
        split; firstorder.
    Qed.
 
  End provability.

End irred_high_level.
