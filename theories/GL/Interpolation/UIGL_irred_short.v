(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2.1 FREE SOFTWARE LICENSE AGREEMENT        *)
(**************************************************************)

(** Certification of 

    let rec flatmap f = function
      | []   -> []
      | x::l -> f x ++ flatmap f l

    let rec irred f x =
      match f x with
      | [] -> [x]
      | _  -> flatmap (irred f) (f x)

    by extraction.

  Following a question by Ian Schillito
  Also look at the following PR

   https://github.com/DmxLarchey/Kruskal-Trees/pull/5

*)

(* 
   This is a standalone file, directly compile with

      coqc irred.v 
 *)

Require Import List Utf8 Extraction.
Import ListNotations.

#[local] Infix "∈" := (@In _) (at level 70, no associativity).
#[local] Hint Resolve in_eq in_cons : core.

Definition list_is_nil {X} (l : list X) : { l = [] } + { l ≠ [] }.
Proof. now destruct l; [ left | right ]. Defined.

(** Directly via Fix_F after cleaning up from Braga using
    the domain Dirred := Acc (λ u v, u ∈ f v) directly *)
Section flatmap.

  Variables (X : Type) 
            (F : X → list X → Prop)
            (D : X → Prop)
            (f : ∀x, D x → sig (F x)).

  Implicit Type (l : list X).

  Inductive Gflatmap : list X → list X → Prop :=
    | Gfm_nil            : Gflatmap [] []
    | Gfm_cons {x y l m} : F x y 
                         → Gflatmap l m 
                         → Gflatmap (x::l) (y++m).

  Hint Constructors Gflatmap : core.

  Fact Gflatmap_inv_left l m : 
        Gflatmap l m
      → match l with
        | []   => [] = m
        | x::l => ∃ y m', F x y ∧ Gflatmap l m' ∧ m = y++m'
        end.
  Proof. destruct 1; eauto. Qed.

  Fact Gflatmap_inv_sg_left x m : Gflatmap [x] m → F x m.
  Proof. 
    intros (y & ? & ? & <-%Gflatmap_inv_left & ->)%Gflatmap_inv_left.
    now rewrite app_nil_r.
  Qed.

  Fact Gflatmap_app_inv_left l1 l2 m : 
        Gflatmap (l1++l2) m
      → ∃ m1 m2, Gflatmap l1 m1 ∧ Gflatmap l2 m2 ∧ m = m1++m2.
  Proof. 
    induction l1 as [ | x l1 IH1 ] in m |- *; simpl.
    + exists [], m; auto.
    + intros (y & m' & H1 & (m1 & m2 & H2 & H3 & ->)%IH1 & ->)%Gflatmap_inv_left.
      exists (y++m1), m2; rewrite app_assoc; auto.
  Qed.

  Fixpoint flatmap l : (∀x, x ∈ l → D x) → sig (Gflatmap l).
  Proof.
    refine (match l with 
    | []   => λ _ , exist _ [] Gfm_nil
    | x::l => λ dl, let (y,hy) := f x _       in
                    let (m,hm) := flatmap l _ in
                    exist _ (y++m) (Gfm_cons hy hm)
    end); auto.
  Defined.

  Variables (g : X → list X) (Hg : ∀x, F x (g x)).

  Fact Gflatmap_flat_map l : Gflatmap l (flat_map g l).
  Proof. induction l; simpl; now constructor. Qed.

End flatmap.

Arguments Gflatmap {X} _.
Arguments flatmap {X} _ {D} _ {l}.

Section irred.

  Variables (X : Type) (f : X → list X).

  Implicit Type l : list X.

  Unset Elimination Schemes.

  (** Because of nesting, induction principles are too weak, 
      see below for better ones *)

  Inductive Girred : X → list X → Prop :=
    | Girred_nil {x}   : f x = []
                       → Girred x [x]
    | Girred_not {x l} : f x ≠ []
                       → Gflatmap Girred (f x) l
                       → Girred x l.

  Set Elimination Schemes.

  Fact Girred_inv_nil {x l} : Girred x l → f x = [] → [x] = l.
  Proof. destruct 1 as [ | ? ? Hx ]; intros; trivial; now destruct Hx. Qed.

  Fact Girred_inv_not {x l} : Girred x l → f x ≠ [] → Gflatmap Girred (f x) l.
  Proof. destruct 1; intros G; trivial; now destruct G. Defined.

  Hint Constructors Gflatmap Girred : core.
  Hint Resolve Girred_inv_nil Girred_inv_not : core.

  Section Girred_ind.

    Variables (P : list X → list X → Prop)
              (Q : X → list X → Prop)

              (HP0 : P [] [])
              (HP1 : ∀ x y l m, Girred x y → Q x y → Gflatmap Girred l m → P l m → P (x::l) (y++m))

              (HQ0 : ∀ x, f x = [] → Q x [x])
              (HQ1 : ∀ x m, f x ≠ [] → Gflatmap Girred (f x) m → P (f x) m → Q x m).

    Fixpoint Girred_ind x m (dxm : Girred x m) { struct dxm } : Q x m.
    Proof.
      destruct (list_is_nil (f x)) as [ H | H ].
      + destruct (Girred_inv_nil dxm H); auto.
      + apply HQ1; auto.
        generalize (Girred_inv_not dxm H).
        clear dxm H.
        induction 1; eauto.
    Qed.

  End Girred_ind.

  Lemma Girred_fun : ∀ x l, Girred x l → (λ x l, ∀m, Girred x m → l = m) x l.
  Proof.
    (* the property which is proved for (Gflatmap Girred) cannot be guessed by unification *)
    apply Girred_ind with (P := fun l m1 => ∀m2, Gflatmap Girred l m2 → m1 = m2); eauto.
    + now intros ? ?%Gflatmap_inv_left.
    + intros ? ? ? ? ? ? ? ? ? (y' & m' & ? & ? & ->)%Gflatmap_inv_left; f_equal; eauto.
  Qed.

  (** We build irred packed with conformity to Girred by Fix_F
      induction over Acc (λ u v, u ∈ f v) x directly *)
  Let irred_pwc : ∀ x (dx : Acc (λ u v, u ∈ f v) x), sig (Girred x).
  Proof.
    refine (Fix_F _ (λ x irred_pwc,
      match list_is_nil (f x) with
      | left Hxf  => exist _ [x] _
      | right Hxf => let (m,hm) := flatmap Girred irred_pwc (λ _ h, h) in
                     exist _ m _
      end)); auto.
  Defined.

  (** Now we can instanciate for _ ∈ f _ is well founded 
      and define irred as a total function *)

  Hypothesis hf : well_founded (λ u v, u ∈ f v).

  Definition irred x := proj1_sig (irred_pwc x (hf x)).

  Fact irred_spec x : Girred x (irred x).
  Proof. apply (proj2_sig _). Qed.

  Hint Resolve irred_spec : core.

  (** We conclude with fixpoint equations *)

  Fact irred_nil x : f x = [] → irred x = [x].
  Proof. intros; eapply Girred_fun; eauto. Qed.

  Hint Resolve Gflatmap_flat_map : core.

  Fact irred_not x : f x ≠ [] → irred x = flat_map irred (f x).
  Proof. intros; eapply Girred_fun; eauto. Qed.

End irred.

Arguments Girred {X}.
Arguments irred {X f}.

