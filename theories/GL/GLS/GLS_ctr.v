Require Import List.
Export ListNotations.
Require Import PeanoNat Arith.
Require Import Lia.

Require Import GLS_calcs.
Require Import GLS_inv_ImpR_ImpL.

Set Implicit Arguments.

(* Next are the definitions for contraction of one formula on the left, and
on the right. Note that while the leftmost occurrence of the formula is kept,
if we have exchange for our calculus it amounts to the same to keep the rightmost
formula. *)

Inductive ctr_L (fml : MPropF) : relationT Seq :=
  | ctr_LI Γ0 Γ1 Γ2 Δ : ctr_L fml
        (Γ0 ++ fml :: Γ1 ++ fml :: Γ2, Δ) (Γ0 ++ fml :: Γ1 ++ Γ2, Δ).

Inductive ctr_R (fml : MPropF) : relationT Seq :=
  | ctr_RI Γ Δ0 Δ1 Δ2 : ctr_R fml
        (Γ, Δ0 ++ fml :: Δ1 ++ fml :: Δ2) (Γ, Δ0 ++ fml :: Δ1 ++ Δ2).

(* Some lemmas on the preservation of inapplicability of rules through contraction. *)

Lemma ctr_L_IdP_notapplic : forall s se A,
    (@ctr_L A s se) ->
    ((IdPRule [] s) -> False) ->
    ((IdPRule [] se) -> False).
Proof.
intros s se A ctr. induction ctr. intros RA RAc. apply RA.
inversion RAc. apply app2_find_hole in H. destruct H. destruct s.
- destruct s.
  + destruct p. inversion e0. subst. apply IdPRule_I.
  + destruct p. destruct x.
    * inversion e0. subst. apply IdPRule_I.
    * inversion e0. subst. 
      assert (E: (Γ3 ++ # P :: x) ++ A :: Γ1 ++ A :: Γ2 = Γ3 ++ # P :: x ++ A :: Γ1 ++ A :: Γ2).
      repeat rewrite <- app_assoc. reflexivity. rewrite E. apply IdPRule_I.
- destruct p. destruct x.
  + inversion e0. apply IdPRule_I.
  + inversion e0. subst. apply app2_find_hole in H2. destruct H2. destruct s.
    * destruct s.
      { destruct p. subst.
        assert (E: Γ0 ++ m :: Γ1 ++ m :: # P :: Γ4 = (Γ0 ++ m :: Γ1 ++ [m]) ++ # P :: Γ4).
        repeat rewrite cons_single. repeat rewrite <- app_assoc. reflexivity. rewrite E.
        apply IdPRule_I. }
      { destruct p. subst.
        assert (E: Γ0 ++ m :: Γ1 ++ m :: x0 ++ # P :: Γ4 = (Γ0 ++ m :: Γ1 ++ m :: x0) ++ # P :: Γ4).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
        rewrite E. apply IdPRule_I. }
    * destruct p. destruct x0.
      { simpl in e1. subst.
        assert (E: Γ0 ++ m :: (x ++ []) ++ m :: # P :: Γ4 = (Γ0 ++ m :: x ++ [] ++ [m]) ++ # P :: Γ4).
        repeat rewrite cons_single. repeat rewrite <- app_assoc. reflexivity.
        rewrite E. apply IdPRule_I. }
      { inversion e1. subst.
        assert (E: Γ0 ++ m :: (x ++ # P :: x0) ++ m :: Γ2 = (Γ0 ++ m :: x) ++ # P :: x0 ++ m :: Γ2).
        repeat rewrite <- app_assoc. simpl. reflexivity. rewrite E. apply IdPRule_I. }
Qed.

Lemma ctr_L_IdB_notapplic : forall s se A,
    (@ctr_L A s se) ->
    ((IdBRule [] s) -> False) ->
    ((IdBRule [] se) -> False).
Proof.
intros s se A ctr. induction ctr. intros RA RAc. apply RA.
inversion RAc. apply app2_find_hole in H. destruct H. destruct s.
- destruct s.
  + destruct p. inversion e0. subst. apply IdBRule_I.
  + destruct p. destruct x.
    * inversion e0. subst. apply IdBRule_I.
    * inversion e0. subst. 
      assert (E: (Γ3 ++ Box A0 :: x) ++ A :: Γ1 ++ A :: Γ2 = Γ3 ++ Box A0 :: x ++ A :: Γ1 ++ A :: Γ2).
      repeat rewrite <- app_assoc. reflexivity. rewrite E. apply IdBRule_I.
- destruct p. destruct x.
  + inversion e0. apply IdBRule_I.
  + inversion e0. subst. apply app2_find_hole in H2. destruct H2. destruct s.
    * destruct s.
      { destruct p. subst.
        assert (E: Γ0 ++ m :: Γ1 ++ m :: Box A0 :: Γ4 = (Γ0 ++ m :: Γ1 ++ [m]) ++ Box A0 :: Γ4).
        repeat rewrite cons_single. repeat rewrite <- app_assoc. reflexivity. rewrite E.
        apply IdBRule_I. }
      { destruct p. subst.
        assert (E: Γ0 ++ m :: Γ1 ++ m :: x0 ++ Box A0 :: Γ4 = (Γ0 ++ m :: Γ1 ++ m :: x0) ++ Box A0 :: Γ4).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
        rewrite E. apply IdBRule_I. }
    * destruct p. destruct x0.
      { simpl in e1. subst.
        assert (E: Γ0 ++ m :: (x ++ []) ++ m :: Box A0 :: Γ4 = (Γ0 ++ m :: x ++ [] ++ [m]) ++ Box A0 :: Γ4).
        repeat rewrite cons_single. repeat rewrite <- app_assoc. reflexivity.
        rewrite E. apply IdBRule_I. }
      { inversion e1. subst.
        assert (E: Γ0 ++ m :: (x ++ Box A0 :: x0) ++ m :: Γ2 = (Γ0 ++ m :: x) ++ Box A0 :: x0 ++ m :: Γ2).
        repeat rewrite <- app_assoc. simpl. reflexivity. rewrite E. apply IdBRule_I. }
Qed.

Lemma ctr_L_BotL_notapplic : forall s se A,
    (@ctr_L A s se) ->
    ((BotLRule [] s) -> False) ->
    ((BotLRule [] se) -> False).
Proof.
intros s se A ctr. induction ctr. intros RA RAc. apply RA.
inversion RAc. apply app2_find_hole in H. destruct H. destruct s.
- destruct s.
  + destruct p. inversion e0. subst. apply BotLRule_I.
  + destruct p. destruct x.
    * inversion e0. subst. apply BotLRule_I.
    * inversion e0. subst. 
      assert (E: (Γ3 ++ ⊥ :: x) ++ A :: Γ1 ++ A :: Γ2 = Γ3 ++ ⊥ :: x ++ A :: Γ1 ++ A :: Γ2).
      repeat rewrite <- app_assoc. reflexivity. rewrite E. apply BotLRule_I.
- destruct p. destruct x.
  + inversion e0. apply BotLRule_I.
  + inversion e0. subst. apply app2_find_hole in H2. destruct H2. destruct s.
    * destruct s.
      { destruct p. subst.
        assert (E: Γ0 ++ m :: Γ1 ++ m :: ⊥ :: Γ4 = (Γ0 ++ m :: Γ1 ++ [m]) ++ ⊥ :: Γ4).
        repeat rewrite cons_single. repeat rewrite <- app_assoc. reflexivity. rewrite E.
        apply BotLRule_I. }
      { destruct p. subst.
        assert (E: Γ0 ++ m :: Γ1 ++ m :: x0 ++ ⊥ :: Γ4 = (Γ0 ++ m :: Γ1 ++ m :: x0) ++ ⊥ :: Γ4).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
        rewrite E. apply BotLRule_I. }
    * destruct p. destruct x0.
      { simpl in e1. subst.
        assert (E: Γ0 ++ m :: (x ++ []) ++ m :: ⊥ :: Γ4 = (Γ0 ++ m :: x ++ [] ++ [m]) ++ ⊥ :: Γ4).
        repeat rewrite cons_single. repeat rewrite <- app_assoc. reflexivity.
        rewrite E. apply BotLRule_I. }
      { inversion e1. subst.
        assert (E: Γ0 ++ m :: (x ++ ⊥ :: x0) ++ m :: Γ2 = (Γ0 ++ m :: x) ++ ⊥ :: x0 ++ m :: Γ2).
        repeat rewrite <- app_assoc. simpl. reflexivity. rewrite E. apply BotLRule_I. } 
Qed.

Lemma ctr_R_IdP_notapplic : forall s se A,
    (@ctr_R A s se) ->
    ((IdPRule [] s) -> False) ->
    ((IdPRule [] se) -> False).
Proof.
intros s se A ctr. induction ctr. intros RA RAc. apply RA.
inversion RAc. apply app2_find_hole in H1. destruct H1. destruct s.
- destruct s.
  + destruct p. inversion e0. subst. apply IdPRule_I.
  + destruct p. destruct x.
    * inversion e0. subst. apply IdPRule_I.
    * inversion e0. subst. 
      assert (E: (Δ3 ++ # P :: x) ++ A :: Δ1 ++ A :: Δ2 = Δ3 ++ # P :: x ++ A :: Δ1 ++ A :: Δ2).
      repeat rewrite <- app_assoc. reflexivity. rewrite E. apply IdPRule_I.
- destruct p. destruct x.
  + inversion e0. apply IdPRule_I.
  + inversion e0. subst. apply app2_find_hole in H2. destruct H2. destruct s.
    * destruct s.
      { destruct p. subst.
        assert (E: Δ0 ++ m :: Δ1 ++ m :: # P :: Δ4 = (Δ0 ++ m :: Δ1 ++ [m]) ++ # P :: Δ4).
        repeat rewrite cons_single. repeat rewrite <- app_assoc. reflexivity. rewrite E.
        apply IdPRule_I. }
      { destruct p. subst.
        assert (E: Δ0 ++ m :: Δ1 ++ m :: x0 ++ # P :: Δ4 = (Δ0 ++ m :: Δ1 ++ m :: x0) ++ # P :: Δ4).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
        rewrite E. apply IdPRule_I. }
    * destruct p. destruct x0.
      { simpl in e1. subst.
        assert (E: Δ0 ++ m :: (x ++ []) ++ m :: # P :: Δ4 = (Δ0 ++ m :: x ++ [] ++ [m]) ++ # P :: Δ4).
        repeat rewrite cons_single. repeat rewrite <- app_assoc. reflexivity.
        rewrite E. apply IdPRule_I. }
      { inversion e1. subst.
        assert (E: Δ0 ++ m :: (x ++ # P :: x0) ++ m :: Δ2 = (Δ0 ++ m :: x) ++ # P :: x0 ++ m :: Δ2).
        repeat rewrite <- app_assoc. simpl. reflexivity. rewrite E. apply IdPRule_I. }
Qed.

Lemma ctr_R_IdB_notapplic : forall s se A,
    (@ctr_R A s se) ->
    ((IdBRule [] s) -> False) ->
    ((IdBRule [] se) -> False).
Proof.
intros s se A ctr. induction ctr. intros RA RAc. apply RA.
inversion RAc. apply app2_find_hole in H1. destruct H1. destruct s.
- destruct s.
  + destruct p. inversion e0. subst. apply IdBRule_I.
  + destruct p. destruct x.
    * inversion e0. subst. apply IdBRule_I.
    * inversion e0. subst. 
      assert (E: (Δ3 ++ Box A0 :: x) ++ A :: Δ1 ++ A :: Δ2 = Δ3 ++ Box A0 :: x ++ A :: Δ1 ++ A :: Δ2).
      repeat rewrite <- app_assoc. reflexivity. rewrite E. apply IdBRule_I.
- destruct p. destruct x.
  + inversion e0. apply IdBRule_I.
  + inversion e0. subst. apply app2_find_hole in H2. destruct H2. destruct s.
    * destruct s.
      { destruct p. subst.
        assert (E: Δ0 ++ m :: Δ1 ++ m :: Box A0 :: Δ4 = (Δ0 ++ m :: Δ1 ++ [m]) ++ Box A0 :: Δ4).
        repeat rewrite cons_single. repeat rewrite <- app_assoc. reflexivity. rewrite E.
        apply IdBRule_I. }
      { destruct p. subst.
        assert (E: Δ0 ++ m :: Δ1 ++ m :: x0 ++ Box A0 :: Δ4 = (Δ0 ++ m :: Δ1 ++ m :: x0) ++ Box A0 :: Δ4).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
        rewrite E. apply IdBRule_I. }
    * destruct p. destruct x0.
      { simpl in e1. subst.
        assert (E: Δ0 ++ m :: (x ++ []) ++ m :: Box A0 :: Δ4 = (Δ0 ++ m :: x ++ [] ++ [m]) ++ Box A0 :: Δ4).
        repeat rewrite cons_single. repeat rewrite <- app_assoc. reflexivity.
        rewrite E. apply IdBRule_I. }
      { inversion e1. subst.
        assert (E: Δ0 ++ m :: (x ++ Box A0 :: x0) ++ m :: Δ2 = (Δ0 ++ m :: x) ++ Box A0 :: x0 ++ m :: Δ2).
        repeat rewrite <- app_assoc. simpl. reflexivity. rewrite E. apply IdBRule_I. } 
Qed.

Lemma ctr_R_BotL_notapplic : forall s se A,
    (@ctr_R A s se) ->
    ((BotLRule [] s) -> False) ->
    ((BotLRule [] se) -> False).
Proof.
intros s se A ctr RA RAe. apply RA.
inversion RAe. destruct s. inversion ctr. subst. inversion H3.
subst. apply BotLRule_I.
Qed.

(* The following lemmas make sure that if a rule is applied on a sequent s with
premises ps, then the same rule is applicable on a sequent sc which is a contracted
version of s, with some premises psc that are such that they are either the same premises
(in case the contracted formula was weakened) or contracted versions of ps. *)

Lemma ImpR_app_ctr_L : forall s sc A ps,
  (@ctr_L A s sc) ->
  (ImpRRule [ps] s) ->
  (existsT2 psc, (ImpRRule [psc] sc) * (@ctr_L A ps psc)).
Proof.
intros s sc A ps ctr RA. inversion RA. inversion ctr. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1. destruct s.
- destruct s.
  + destruct p. subst. exists (Γ2 ++ A0 :: A :: Γ3 ++ Γ4, Δ0 ++ B :: Δ1).
    split. apply ImpRRule_I.
    assert (E1: Γ2 ++ A0 :: A :: Γ3 ++ A :: Γ4 = (Γ2 ++ [A0]) ++ A :: Γ3 ++ A :: Γ4).
    repeat rewrite cons_single. repeat rewrite <- app_assoc. reflexivity. rewrite E1.
    assert (E2: Γ2 ++ A0 :: A :: Γ3 ++ Γ4 = (Γ2 ++ [A0]) ++ A :: Γ3 ++ Γ4).
    repeat rewrite cons_single. repeat rewrite <- app_assoc. reflexivity. rewrite E2.
    apply ctr_LI.
  + destruct p. subst. destruct x.
    * simpl in e0. subst. repeat rewrite app_nil_r.
      exists (Γ2 ++ A0 :: A :: Γ3 ++ Γ4, Δ0 ++ B :: Δ1). split. apply ImpRRule_I.
      assert (E1: Γ2 ++ A0 :: A :: Γ3 ++ A :: Γ4 = (Γ2 ++ [A0]) ++ A :: Γ3 ++ A :: Γ4).
      repeat rewrite cons_single. repeat rewrite <- app_assoc. reflexivity. rewrite E1.
      assert (E2: Γ2 ++ A0 :: A :: Γ3 ++ Γ4 = (Γ2 ++ [A0]) ++ A :: Γ3 ++ Γ4).
      repeat rewrite cons_single. repeat rewrite <- app_assoc. reflexivity. rewrite E2.
      apply ctr_LI.
    * inversion e0. subst. apply app2_find_hole in H2. destruct H2. destruct s.
      { destruct s.
        - destruct p. subst. exists ((Γ2 ++ m :: Γ3) ++ A0 :: Γ4, Δ0 ++ B :: Δ1).
          split.
          assert (E: Γ2 ++ m :: Γ3 ++ Γ4 = (Γ2 ++ m :: Γ3) ++ Γ4).
          rewrite <- app_assoc. reflexivity. rewrite E. apply ImpRRule_I.
          assert (E1: (Γ2 ++ m :: Γ3) ++ A0 :: m :: Γ4 = Γ2 ++ m :: (Γ3 ++ [A0]) ++ m :: Γ4).
          repeat rewrite cons_single. repeat rewrite <- app_assoc. reflexivity. rewrite E1.
          assert (E2: (Γ2 ++ m :: Γ3) ++ A0 :: Γ4 = Γ2 ++ m :: (Γ3 ++ [A0]) ++ Γ4).
          repeat rewrite cons_single. repeat rewrite <- app_assoc. reflexivity. rewrite E2.
          apply ctr_LI.
        - destruct p. subst. destruct x0.
          + simpl in e1. subst. repeat rewrite app_nil_r.
            exists ((Γ2 ++ m :: Γ3) ++ A0 :: Γ4, Δ0 ++ B :: Δ1). split.
            assert (E: Γ2 ++ m :: Γ3 ++ Γ4 = (Γ2 ++ m :: Γ3) ++ Γ4).
            rewrite <- app_assoc. reflexivity. rewrite E.
            apply ImpRRule_I.
            assert (E1: (Γ2 ++ m :: Γ3) ++ A0 :: m :: Γ4 = Γ2 ++ m :: (Γ3 ++ [A0]) ++ m :: Γ4).
            repeat rewrite cons_single. repeat rewrite <- app_assoc. reflexivity. rewrite E1.
            assert (E2: (Γ2 ++ m :: Γ3) ++ A0 :: Γ4 = Γ2 ++ m :: (Γ3 ++ [A0]) ++ Γ4).
            repeat rewrite cons_single. repeat rewrite <- app_assoc. reflexivity. rewrite E2.
            apply ctr_LI.
          + inversion e1. subst.
            exists ((Γ2 ++ m0 :: Γ3 ++ x0) ++ A0 :: Γ1, Δ0 ++ B :: Δ1). split.
            assert (E: Γ2 ++ m0 :: Γ3 ++ x0 ++ Γ1 = (Γ2 ++ m0 :: Γ3 ++ x0) ++ Γ1).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite E.
            apply ImpRRule_I.
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. apply ctr_LI. }
      { destruct p. subst. exists ((Γ2 ++ m :: x) ++ A0 :: x0 ++ Γ4,Δ0 ++ B :: Δ1).
        split. assert (E: Γ2 ++ m :: (x ++ x0) ++ Γ4 = (Γ2 ++ m :: x) ++ x0 ++ Γ4).
        repeat rewrite <- app_assoc. reflexivity. rewrite E. apply ImpRRule_I.
        assert (E1: (Γ2 ++ m :: x) ++ A0 :: x0 ++ m :: Γ4 = Γ2 ++ m :: (x ++ A0 :: x0) ++ m :: Γ4).
        repeat rewrite <- app_assoc. reflexivity. rewrite E1.
        assert (E2: (Γ2 ++ m :: x) ++ A0 :: x0 ++ Γ4 = Γ2 ++ m :: (x ++ A0 :: x0) ++ Γ4).
        repeat rewrite cons_single. repeat rewrite <- app_assoc. reflexivity. rewrite E2.
        apply ctr_LI. }
- destruct p. subst. exists (Γ0 ++ A0 :: x ++ A :: Γ3 ++ Γ4, Δ0 ++ B :: Δ1).
  split. rewrite <- app_assoc. apply ImpRRule_I.
  assert (E1: Γ0 ++ A0 :: x ++ A :: Γ3 ++ A :: Γ4 = (Γ0 ++ A0 :: x) ++ A :: Γ3 ++ A :: Γ4).
  repeat rewrite <- app_assoc. reflexivity. rewrite E1.
  assert (E2: Γ0 ++ A0 :: x ++ A :: Γ3 ++ Γ4 = (Γ0 ++ A0 :: x) ++ A :: Γ3 ++ Γ4).
  repeat rewrite cons_single. repeat rewrite <- app_assoc. reflexivity. rewrite E2.
  apply ctr_LI.
Qed.

Lemma ImpL_app_ctr_L : forall s sc A ps1 ps2,
  (@ctr_L A s sc) ->
  (ImpLRule [ps1;ps2] s) ->
  ((existsT2 psc1 psc2, (ImpLRule [psc1;psc2] sc) *
                       (@ctr_L A ps1 psc1) *
                       (@ctr_L A ps2 psc2))
  +
  (existsT2 B C invps11 invps12 invps21 invps22 invpsc11 invpsc22,
                       (A = Imp B C) *
                       (ImpLRule [invps11;invps12] ps1) *
                       (ImpLRule [invps21;invps22] ps2) *
                       (@ctr_R B invps11 invpsc11) *
                       (@ctr_L C invps22 invpsc22) *
                       (ImpLRule [invpsc11;invpsc22] sc))).
Proof.
intros s sc A ps1 ps2 ctr RA. inversion RA. inversion ctr. subst. inversion H.
subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
- inversion e0. subst. right. exists A0. exists B.
  exists (Γ2 ++ Γ3 ++ Γ4, Δ0 ++ A0 :: A0 :: Δ1). exists (Γ2 ++ Γ3 ++ B :: Γ4, Δ0 ++ A0 :: Δ1).
  exists (Γ2 ++ B :: Γ3 ++ Γ4, Δ0 ++ A0 :: Δ1). exists (Γ2 ++ B :: Γ3 ++ B :: Γ4, Δ0 ++ Δ1).
  exists (Γ2 ++ Γ3 ++ Γ4, Δ0 ++ A0 :: Δ1). exists (Γ2 ++ B :: Γ3 ++ Γ4, Δ0 ++ Δ1). repeat split.
  assert (Γ2 ++ Γ3 ++ Γ4 = (Γ2 ++ Γ3) ++ Γ4). rewrite <- app_assoc. reflexivity. rewrite H0.
  clear H0. assert (Γ2 ++ Γ3 ++ B :: Γ4 = (Γ2 ++ Γ3) ++ B :: Γ4). rewrite <- app_assoc. reflexivity.
  rewrite H0. clear H0. assert (Γ2 ++ Γ3 ++ A0 --> B :: Γ4 = (Γ2 ++ Γ3) ++ A0 --> B :: Γ4). rewrite <- app_assoc.
  reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
  assert (Γ2 ++ B :: Γ3 ++ Γ4 = (Γ2 ++ B :: Γ3) ++ Γ4). rewrite <- app_assoc. reflexivity. rewrite H0.
  clear H0. assert (Γ2 ++ B :: Γ3 ++ B :: Γ4 = (Γ2 ++ B :: Γ3) ++ B :: Γ4). rewrite <- app_assoc. reflexivity.
  rewrite H0. clear H0. assert (Γ2 ++ B :: Γ3 ++ A0 --> B :: Γ4 = (Γ2 ++ B :: Γ3) ++ A0 --> B :: Γ4). rewrite <- app_assoc.
  reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
  assert (Δ0 ++ A0 :: A0 :: Δ1 = Δ0 ++ A0 :: [] ++ A0 :: Δ1). reflexivity. rewrite H0. clear H0.
  assert (Δ0 ++ A0 :: Δ1 = Δ0 ++ A0 :: [] ++ Δ1). reflexivity. rewrite H0. clear H0.
  apply ctr_RI.
- destruct x.
  * simpl in e0. inversion e0. subst. right. exists A0. exists B.
    exists (Γ2 ++ Γ3 ++ Γ4, Δ0 ++ A0 :: A0 :: Δ1). exists (Γ2 ++ Γ3 ++ B :: Γ4, Δ0 ++ A0 :: Δ1).
    exists (Γ2 ++ B :: Γ3 ++ Γ4, Δ0 ++ A0 :: Δ1). exists (Γ2 ++ B :: Γ3 ++ B :: Γ4, Δ0 ++ Δ1).
    exists (Γ2 ++ Γ3 ++ Γ4, Δ0 ++ A0 :: Δ1). exists (Γ2 ++ B :: Γ3 ++ Γ4, Δ0 ++ Δ1). repeat split.
    assert (Γ2 ++ Γ3 ++ Γ4 = (Γ2 ++ Γ3) ++ Γ4). repeat rewrite <- app_assoc. reflexivity. rewrite H0.
    clear H0. assert (Γ2 ++ Γ3 ++ B :: Γ4 = (Γ2 ++ Γ3) ++ B :: Γ4). rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. assert ((Γ2 ++ []) ++ Γ3 ++ A0 --> B :: Γ4 = (Γ2 ++ Γ3) ++ A0 --> B :: Γ4).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
    assert (Γ2 ++ B :: Γ3 ++ Γ4 = (Γ2 ++ B :: Γ3) ++ Γ4). rewrite <- app_assoc. reflexivity. rewrite H0.
    clear H0. assert (Γ2 ++ B :: Γ3 ++ B :: Γ4 = (Γ2 ++ B :: Γ3) ++ B :: Γ4). rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. assert ((Γ2 ++ []) ++ B :: Γ3 ++ A0 --> B :: Γ4 = (Γ2 ++ B :: Γ3) ++ A0 --> B :: Γ4).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
    assert (Δ0 ++ A0 :: A0 :: Δ1 = Δ0 ++ A0 :: [] ++ A0 :: Δ1). reflexivity. rewrite H0. clear H0.
    assert (Δ0 ++ A0 :: Δ1 = Δ0 ++ A0 :: [] ++ Δ1). reflexivity. rewrite H0. clear H0.
    apply ctr_RI.
  * inversion e0. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
    + inversion e1. subst. right. exists A0. exists B.
      exists (Γ2 ++ Γ3 ++ Γ4, Δ0 ++ A0 :: A0 :: Δ1). exists (Γ2 ++ B :: Γ3 ++ Γ4, Δ0 ++ A0 :: Δ1).
      exists (Γ2 ++ Γ3 ++ B :: Γ4, Δ0 ++ A0 :: Δ1). exists (Γ2 ++ B :: Γ3 ++ B :: Γ4, Δ0 ++ Δ1).
      exists (Γ2 ++ Γ3 ++ Γ4, Δ0 ++ A0 :: Δ1). exists (Γ2 ++ B :: Γ3 ++ Γ4, Δ0 ++ Δ1). repeat split.
      repeat rewrite <- app_assoc. apply ImpLRule_I. repeat rewrite <- app_assoc. apply ImpLRule_I.
      assert (Δ0 ++ A0 :: A0 :: Δ1 = Δ0 ++ A0 :: [] ++ A0 :: Δ1). reflexivity. rewrite H0. clear H0.
      assert (Δ0 ++ A0 :: Δ1 = Δ0 ++ A0 :: [] ++ Δ1). reflexivity. rewrite H0. clear H0.
      apply ctr_RI.
    + destruct x0.
      { simpl in e1. inversion e1. subst. right. exists A0. exists B.
        exists (Γ2 ++ Γ3 ++ Γ1, Δ0 ++ A0 :: A0 :: Δ1). exists (Γ2 ++ B :: Γ3 ++ Γ1, Δ0 ++ A0 :: Δ1).
        exists (Γ2 ++ Γ3 ++ B :: Γ1, Δ0 ++ A0 :: Δ1). exists (Γ2 ++ B :: Γ3 ++ B :: Γ1, Δ0 ++ Δ1).
        exists (Γ2 ++ Γ3 ++ Γ1, Δ0 ++ A0 :: Δ1). exists (Γ2 ++ B :: Γ3 ++ Γ1, Δ0 ++ Δ1). repeat split.
        repeat rewrite <- app_assoc. simpl. rewrite app_nil_r. apply ImpLRule_I. repeat rewrite <- app_assoc.
        rewrite app_nil_r. apply ImpLRule_I.
        assert (Δ0 ++ A0 :: A0 :: Δ1 = Δ0 ++ A0 :: [] ++ A0 :: Δ1). reflexivity. rewrite H0. clear H0.
        assert (Δ0 ++ A0 :: Δ1 = Δ0 ++ A0 :: [] ++ Δ1). reflexivity. rewrite H0. clear H0.
        apply ctr_RI. }
      { inversion e1. subst. left. exists (Γ2 ++ m0 :: Γ3 ++ x0 ++ Γ1, Δ0 ++ A0 :: Δ1).
        exists (Γ2 ++ m0 :: Γ3 ++ x0 ++ B :: Γ1, Δ0 ++ Δ1). repeat split.
        assert (Γ2 ++ m0 :: Γ3 ++ x0 ++ Γ1 = (Γ2 ++ m0 :: Γ3 ++ x0) ++ Γ1). repeat rewrite <- app_assoc.
        simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert (Γ2 ++ m0 :: Γ3 ++ x0 ++ A0 --> B :: Γ1 = (Γ2 ++ m0 :: Γ3 ++ x0) ++ A0 --> B :: Γ1). repeat rewrite <- app_assoc.
        simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert (Γ2 ++ m0 :: Γ3 ++ x0 ++ B :: Γ1 = (Γ2 ++ m0 :: Γ3 ++ x0) ++ B :: Γ1). repeat rewrite <- app_assoc.
        simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. apply ctr_LI.
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. apply ctr_LI. }
    + destruct x0.
      { simpl in e1. inversion e1. subst. right. exists A0. exists B.
        exists (Γ2 ++ x ++ Γ4, Δ0 ++ A0 :: A0 :: Δ1). exists (Γ2 ++ B :: x ++ Γ4, Δ0 ++ A0 :: Δ1).
        exists (Γ2 ++ x ++ B :: Γ4, Δ0 ++ A0 :: Δ1). exists (Γ2 ++ B :: x ++ B :: Γ4, Δ0 ++ Δ1).
        exists (Γ2 ++ x ++ Γ4, Δ0 ++ A0 :: Δ1). exists (Γ2 ++ B :: x ++ Γ4, Δ0 ++ Δ1). repeat split.
        repeat rewrite <- app_assoc. apply ImpLRule_I. repeat rewrite <- app_assoc. apply ImpLRule_I.
        assert (Δ0 ++ A0 :: A0 :: Δ1 = Δ0 ++ A0 :: [] ++ A0 :: Δ1). reflexivity. rewrite H0. clear H0.
        assert (Δ0 ++ A0 :: Δ1 = Δ0 ++ A0 :: [] ++ Δ1). reflexivity. rewrite H0. clear H0.
        apply ctr_RI. rewrite <- app_assoc. simpl. apply ImpLRule_I. }
      { inversion e1. subst. left. exists (Γ2 ++ m :: x ++ x0 ++ Γ4, Δ0 ++ A0 :: Δ1).
        exists (Γ2 ++ m :: x ++ B :: x0 ++ Γ4, Δ0 ++ Δ1). repeat split.
        assert (Γ2 ++ m :: x ++ x0 ++ Γ4 = (Γ2 ++ m :: x) ++ x0 ++ Γ4). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0.
        assert (Γ2 ++ m :: x ++ B :: x0 ++ Γ4 = (Γ2 ++ m :: x) ++ B :: x0 ++ Γ4). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0.
        assert (Γ2 ++ m :: (x ++ A0 --> B :: x0) ++ Γ4 = (Γ2 ++ m :: x) ++ A0 --> B :: x0 ++ Γ4). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
        assert ((Γ2 ++ m :: x) ++ x0 ++ m :: Γ4 = Γ2 ++ m :: (x ++ x0) ++ m :: Γ4). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0.
        assert (Γ2 ++ m :: x ++ x0 ++ Γ4 = Γ2 ++ m :: (x ++ x0) ++ Γ4). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0. apply ctr_LI.
        assert ((Γ2 ++ m :: x) ++ B :: x0 ++ m :: Γ4 = Γ2 ++ m :: (x ++ B :: x0) ++ m :: Γ4). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0.
        assert (Γ2 ++ m :: x ++ B :: x0 ++ Γ4 = Γ2 ++ m :: (x ++ B :: x0) ++ Γ4). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0. apply ctr_LI. }
- destruct x.
  + simpl in e0. inversion e0. subst. right. exists A0. exists B.
    exists (Γ0 ++ Γ3 ++ Γ4, Δ0 ++ A0 :: A0 :: Δ1). exists (Γ0 ++ Γ3 ++ B :: Γ4, Δ0 ++ A0 :: Δ1).
    exists (Γ0 ++ B :: Γ3 ++ Γ4, Δ0 ++ A0 :: Δ1). exists (Γ0 ++ B :: Γ3 ++ B :: Γ4, Δ0 ++ Δ1).
    exists (Γ0 ++ Γ3 ++ Γ4, Δ0 ++ A0 :: Δ1). exists (Γ0 ++ B :: Γ3 ++ Γ4, Δ0 ++ Δ1) . repeat split.
    assert (Γ0 ++ Γ3 ++ Γ4 = (Γ0 ++ Γ3) ++ Γ4). repeat rewrite <- app_assoc. reflexivity. rewrite H0.
    clear H0. assert (Γ0 ++ Γ3 ++ B :: Γ4 = (Γ0 ++ Γ3) ++ B :: Γ4). rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. assert (Γ0 ++ Γ3 ++ A0 --> B :: Γ4 = (Γ0 ++ Γ3) ++ A0 --> B :: Γ4).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
    assert (Γ0 ++ B :: Γ3 ++ Γ4 = (Γ0 ++ B :: Γ3) ++ Γ4). rewrite <- app_assoc. reflexivity. rewrite H0.
    clear H0. assert (Γ0 ++ B :: Γ3 ++ B :: Γ4 = (Γ0 ++ B :: Γ3) ++ B :: Γ4). rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. assert (Γ0 ++ B :: Γ3 ++ A0 --> B :: Γ4 = (Γ0 ++ B :: Γ3) ++ A0 --> B :: Γ4).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
    assert (Δ0 ++ A0 :: A0 :: Δ1 = Δ0 ++ A0 :: [] ++ A0 :: Δ1). reflexivity. rewrite H0. clear H0.
    assert (Δ0 ++ A0 :: Δ1 = Δ0 ++ A0 :: [] ++ Δ1). reflexivity. rewrite H0. clear H0.
    apply ctr_RI. repeat rewrite <- app_assoc. simpl. apply ImpLRule_I.
  + inversion e0. subst. left. exists (Γ0 ++ x ++ A :: Γ3 ++ Γ4, Δ0 ++ A0 :: Δ1).
    exists (Γ0 ++ B :: x ++ A :: Γ3 ++ Γ4, Δ0 ++ Δ1). repeat split. repeat rewrite <- app_assoc.
    apply ImpLRule_I.
    assert (Γ0 ++ x ++ A :: Γ3 ++ A :: Γ4 = (Γ0 ++ x) ++ A :: Γ3 ++ A :: Γ4). repeat rewrite <- app_assoc.
    reflexivity. rewrite H0. clear H0.
    assert (Γ0 ++ x ++ A :: Γ3 ++ Γ4 = (Γ0 ++ x) ++ A :: Γ3 ++ Γ4). repeat rewrite <- app_assoc.
    reflexivity. rewrite H0. clear H0. apply ctr_LI.
    assert (Γ0 ++ B :: x ++ A :: Γ3 ++ A :: Γ4 = (Γ0 ++ B :: x) ++ A :: Γ3 ++ A :: Γ4). repeat rewrite <- app_assoc.
    reflexivity. rewrite H0. clear H0.
    assert (Γ0 ++ B :: x ++ A :: Γ3 ++ Γ4 = (Γ0 ++ B :: x) ++ A :: Γ3 ++ Γ4). repeat rewrite <- app_assoc.
    reflexivity. rewrite H0. clear H0. apply ctr_LI.
Qed.

Lemma GLR_app_ctr_L : forall s sc A ps,
  (@ctr_L A s sc) ->
  (GLRRule [ps] s) ->
    ((GLRRule [ps] sc) +
     (existsT2 psc1 psc2, (GLRRule [psc2] sc) * (@ctr_L (unBox_formula A) ps psc1) * (@ctr_L A psc1 psc2))).
Proof.
intros s sc A ps ctr RA. inversion RA. inversion ctr. rewrite <- H1 in H2.
inversion H2. subst. apply univ_gen_ext_elem_deep with (l3:=Γ1) (l4:=Γ2 ++ A :: Γ3) (a:=A) in X.
destruct X. 3: reflexivity.
- destruct p. apply univ_gen_ext_elem_deep with (l3:=Γ1 ++ Γ2) (l4:=Γ3) (a:=A) in u. destruct u. destruct p.
3: rewrite <- app_assoc. 3: reflexivity.
  * left. apply GLRRule_I.
    assumption.
    apply univ_gen_ext_add_elem_deep. rewrite app_assoc. assumption. assumption.
  * exfalso. apply f. repeat destruct s. repeat destruct p. subst. apply is_box_is_in_boxed_list with (A:=A) in H0 .
    unfold is_boxedT. destruct H0. exists x1. auto. apply in_or_app. right. apply in_eq.
- repeat destruct s. repeat destruct p. apply univ_gen_ext_elem_deep with (l3:=Γ2) (l4:=Γ3) (a:=A) in u0.
  destruct u0. 3: reflexivity.
  * destruct p. exfalso. subst. apply is_box_is_in_boxed_list with (A:=A) in H0. apply f. unfold is_boxedT.
    destruct H0. exists x1. auto. apply in_or_app. right. apply in_eq.
  * repeat destruct s. repeat destruct p. right. subst.
    exists ((XBoxed_list x) ++ (XBoxed_list [A]) ++ (XBoxed_list x1) ++ A :: (XBoxed_list x2) ++ [Box A0], [A0]).
    exists (XBoxed_list (x ++ A :: x1 ++ x2) ++ [Box A0], [A0]). split.
    + split.
      { apply GLRRule_I.
        intro. intros. apply H0. apply in_app_or in H. destruct H. apply in_or_app. left. assumption.
        inversion H. subst. apply in_or_app. right. apply in_eq. apply in_app_or in H1. destruct H1.
        apply in_or_app. right. apply in_cons. apply in_or_app. left. assumption.
        apply in_or_app. right. apply in_cons. apply in_or_app. right. apply in_cons.
        assumption.
        apply univ_gen_ext_combine. assumption. apply univ_gen_ext_cons. apply univ_gen_ext_combine.
        assumption. assumption. }
      { repeat rewrite cons_single. repeat rewrite XBox_app_distrib. simpl.
        assert (E1: (XBoxed_list x ++ unBox_formula A :: A :: XBoxed_list x1 ++ unBox_formula A :: A :: XBoxed_list x2) ++ [Box A0] =
                     (XBoxed_list x ++ unBox_formula A :: (A :: XBoxed_list x1) ++ unBox_formula A :: (A :: XBoxed_list x2 ++ [Box A0]))).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite E1.
        assert (E2: XBoxed_list x ++ unBox_formula A :: A :: XBoxed_list x1 ++ A :: XBoxed_list x2 ++ [Box A0] =
                    XBoxed_list x ++ unBox_formula A :: (A :: XBoxed_list x1) ++ (A :: XBoxed_list x2 ++ [Box A0])).
        repeat rewrite <- app_assoc. reflexivity. rewrite E2. apply ctr_LI with (Γ2:= A :: XBoxed_list x2 ++ [Box A0]). }
    + simpl. repeat rewrite XBox_app_distrib. simpl. repeat rewrite XBox_app_distrib.
      assert (E1: XBoxed_list x ++ unBox_formula A :: A :: XBoxed_list x1 ++ A :: XBoxed_list x2 ++ [Box A0] =
                  (XBoxed_list x ++ [unBox_formula A]) ++ A :: XBoxed_list x1 ++ A :: XBoxed_list x2 ++ [Box A0]).
      repeat rewrite <- app_assoc. rewrite <- cons_single. reflexivity. rewrite E1.
      assert (E2: (XBoxed_list x ++ unBox_formula A :: A :: XBoxed_list x1 ++ XBoxed_list x2) ++ [Box A0] =
                  (XBoxed_list x ++ [unBox_formula A]) ++ A :: XBoxed_list x1 ++ XBoxed_list x2 ++ [Box A0]).
      repeat rewrite <- app_assoc. rewrite <- cons_single. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite E2.
      apply ctr_LI.
Qed.

Lemma ImpR_app_ctr_R : forall s sc A ps,
  (@ctr_R A s sc) ->
  (ImpRRule [ps] s) ->
  ((existsT2 psc, (ImpRRule [psc] sc) * (@ctr_R A ps psc))
  +
  (existsT2 B C invps invpsc0 invpsc, (A = Imp B C) * (ImpRRule [invps] ps) * (ImpRRule [invpsc] sc) *
                                      (@ctr_L B invps invpsc0) * (@ctr_R C invpsc0 invpsc))).
Proof.
intros s sc A ps ctr RA. inversion RA. inversion ctr. subst.
inversion H. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
- inversion e0. right. exists A0. exists B. exists (Γ0 ++ A0 :: A0 :: Γ1, Δ2 ++ B :: Δ3 ++ B :: Δ4).
  exists (Γ0 ++ A0 :: Γ1, Δ2 ++ B :: Δ3 ++ B :: Δ4). exists (Γ0 ++ A0 :: Γ1, Δ2 ++ B :: Δ3 ++ Δ4).
  repeat split. assert (Δ2 ++ B :: Δ3 ++ B :: Δ4 = (Δ2 ++ B :: Δ3) ++ B :: Δ4). rewrite <- app_assoc. reflexivity.
  rewrite H0. clear H0. assert (Δ2 ++ B :: Δ3 ++ A0 --> B :: Δ4 = (Δ2 ++ B :: Δ3) ++ A0 --> B :: Δ4). rewrite <- app_assoc. reflexivity.
  rewrite H0. clear H0. apply ImpRRule_I.
  assert (Γ0 ++ A0 :: A0 :: Γ1 = Γ0 ++ A0 :: [] ++ A0 :: Γ1). reflexivity. rewrite H0. clear H0.
  assert (Γ0 ++ A0 :: Γ1 = Γ0 ++ A0 :: [] ++ Γ1). reflexivity. rewrite H0. clear H0.
  apply ctr_LI.
- destruct x.
  * simpl in e0. inversion e0. subst. right. exists A0. exists B.
    exists (Γ0 ++ A0 :: A0 :: Γ1, (Δ2 ++ []) ++ B :: Δ3 ++ B :: Δ4).
    exists (Γ0 ++ A0 :: Γ1, (Δ2 ++ []) ++ B :: Δ3 ++ B :: Δ4). exists (Γ0 ++ A0 :: Γ1, (Δ2 ++ []) ++ B :: Δ3 ++ Δ4).
    repeat split. assert ((Δ2 ++ []) ++ B :: Δ3 ++ B :: Δ4 = (Δ2 ++ B :: Δ3) ++ B :: Δ4). repeat rewrite <- app_assoc.
    reflexivity. rewrite H0. clear H0. assert ((Δ2 ++ []) ++ B :: Δ3 ++ A0 --> B :: Δ4 = (Δ2 ++ B :: Δ3) ++ A0 --> B :: Δ4).
    rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    apply ImpRRule_I. repeat rewrite <- app_assoc. simpl. apply ImpRRule_I.
    assert (Γ0 ++ A0 :: A0 :: Γ1 = Γ0 ++ A0 :: [] ++ A0 :: Γ1). reflexivity. rewrite H0. clear H0.
    assert (Γ0 ++ A0 :: Γ1 = Γ0 ++ A0 :: [] ++ Γ1). reflexivity. rewrite H0. clear H0.
    apply ctr_LI.
  * inversion e0. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
    + inversion e1. subst. right. exists A0. exists B.
      exists (Γ0 ++ A0 :: A0 :: Γ1, Δ2 ++ B :: Δ3 ++ B :: Δ4). exists (Γ0 ++ A0 :: Γ1, Δ2 ++ B :: Δ3 ++ B :: Δ4).
      exists (Γ0 ++ A0 :: Γ1, Δ2 ++ B :: Δ3 ++ Δ4). repeat split.
      repeat rewrite <- app_assoc. apply ImpRRule_I.
      assert (Γ0 ++ A0 :: A0 :: Γ1 = Γ0 ++ A0 :: [] ++ A0 :: Γ1). reflexivity. rewrite H0. clear H0.
      assert (Γ0 ++ A0 :: Γ1 = Γ0 ++ A0 :: [] ++ Γ1). reflexivity. rewrite H0. clear H0.
      apply ctr_LI.
    + destruct x0.
      { simpl in e1. inversion e1. subst. right. exists A0. exists B.
        exists (Γ0 ++ A0 :: A0 :: Γ1, Δ2 ++ B :: Δ3 ++ B :: Δ1). exists (Γ0 ++ A0 :: Γ1, Δ2 ++ B :: Δ3 ++ B :: Δ1).
        exists (Γ0 ++ A0 :: Γ1, Δ2 ++ B :: Δ3 ++ Δ1). repeat split.
        repeat rewrite <- app_assoc. simpl. rewrite app_nil_r. apply ImpRRule_I.
        assert (Γ0 ++ A0 :: A0 :: Γ1 = Γ0 ++ A0 :: [] ++ A0 :: Γ1). reflexivity. rewrite H0. clear H0.
        assert (Γ0 ++ A0 :: Γ1 = Γ0 ++ A0 :: [] ++ Γ1). reflexivity. rewrite H0. clear H0.
        apply ctr_LI. }
      { inversion e1. subst. left. exists (Γ0 ++ A0 :: Γ1, Δ2 ++ m0 :: Δ3 ++ x0 ++ B :: Δ1).
        repeat split. assert (Δ2 ++ m0 :: Δ3 ++ x0 ++ B :: Δ1 = (Δ2 ++ m0 :: Δ3 ++ x0) ++ B :: Δ1).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert (Δ2 ++ m0 :: Δ3 ++ x0 ++ A0 --> B :: Δ1 = (Δ2 ++ m0 :: Δ3 ++ x0) ++ A0 --> B :: Δ1). repeat rewrite <- app_assoc.
        simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpRRule_I.
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. apply ctr_RI. }
    + destruct x0.
      { simpl in e1. inversion e1. subst. right. exists A0. exists B.
        exists (Γ0 ++ A0 :: A0 :: Γ1, Δ2 ++ B :: x ++ B :: Δ4). exists (Γ0 ++ A0 :: Γ1, Δ2 ++ B :: x ++ B :: Δ4).
        exists (Γ0 ++ A0 :: Γ1, Δ2 ++ B :: x ++ Δ4). repeat split.
        repeat rewrite <- app_assoc. apply ImpRRule_I. repeat rewrite <- app_assoc. apply ImpRRule_I.
        assert (Γ0 ++ A0 :: A0 :: Γ1 = Γ0 ++ A0 :: [] ++ A0 :: Γ1). reflexivity. rewrite H0. clear H0.
        assert (Γ0 ++ A0 :: Γ1 = Γ0 ++ A0 :: [] ++ Γ1). reflexivity. rewrite H0. clear H0.
        apply ctr_LI. }
      { inversion e1. subst. left. exists (Γ0 ++ A0 :: Γ1, Δ2 ++ m :: x ++ B :: x0 ++ Δ4).
        repeat split.
        assert (Δ2 ++ m :: x ++ B :: x0 ++ Δ4 = (Δ2 ++ m :: x) ++ B :: x0 ++ Δ4). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0.
        assert (Δ2 ++ m :: (x ++ A0 --> B :: x0) ++ Δ4 = (Δ2 ++ m :: x) ++ A0 --> B :: x0 ++ Δ4). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0. apply ImpRRule_I.
        assert ((Δ2 ++ m :: x) ++ B :: x0 ++ m :: Δ4 = Δ2 ++ m :: (x ++ B :: x0) ++ m :: Δ4). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0.
        assert (Δ2 ++ m :: x ++ B :: x0 ++ Δ4 = Δ2 ++ m :: (x ++ B :: x0) ++ Δ4). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0. apply ctr_RI. }
- destruct x.
  + simpl in e0. inversion e0. subst. right. exists A0. exists B.
    exists (Γ0 ++ A0 :: A0 :: Γ1, Δ0 ++ B :: Δ3 ++ B :: Δ4). exists (Γ0 ++ A0 :: Γ1, Δ0 ++ B :: Δ3 ++ B :: Δ4).
    exists (Γ0 ++ A0 :: Γ1, Δ0 ++ B :: Δ3 ++ Δ4). repeat split.
    assert (Δ0 ++ B :: Δ3 ++ A0 --> B :: Δ4 = (Δ0 ++ B :: Δ3) ++ A0 --> B :: Δ4). repeat rewrite <- app_assoc. reflexivity. rewrite H0.
    clear H0. assert (Δ0 ++ B :: Δ3 ++ B :: Δ4 = (Δ0 ++ B :: Δ3) ++ B :: Δ4). rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply ImpRRule_I. repeat rewrite <- app_assoc. simpl. apply ImpRRule_I.
    assert (Γ0 ++ A0 :: A0 :: Γ1 = Γ0 ++ A0 :: [] ++ A0 :: Γ1). reflexivity. rewrite H0. clear H0.
    assert (Γ0 ++ A0 :: Γ1 = Γ0 ++ A0 :: [] ++ Γ1). reflexivity. rewrite H0. clear H0.
    apply ctr_LI.
  + inversion e0. subst. left. exists (Γ0 ++ A0 :: Γ1, Δ0 ++ B :: x ++ A :: Δ3 ++ Δ4).
    repeat split. repeat rewrite <- app_assoc. apply ImpRRule_I.
    assert (Δ0 ++ B :: x ++ A :: Δ3 ++ A :: Δ4 = (Δ0 ++ B :: x) ++ A :: Δ3 ++ A :: Δ4). repeat rewrite <- app_assoc.
    reflexivity. rewrite H0. clear H0.
    assert (Δ0 ++ B :: x ++ A :: Δ3 ++ Δ4 = (Δ0 ++ B :: x) ++ A :: Δ3 ++ Δ4). repeat rewrite <- app_assoc.
    reflexivity. rewrite H0. clear H0. apply ctr_RI.
Qed.

Lemma ImpL_app_ctr_R : forall s sc A ps1 ps2,
  (@ctr_R A s sc) ->
  (ImpLRule [ps1;ps2] s) ->
  (existsT2 psc1 psc2, (ImpLRule [psc1;psc2] sc) * (@ctr_R A ps1 psc1) * (@ctr_R A ps2 psc2)).
Proof.
intros s sc A ps1 ps2 ctr RA. inversion RA. inversion ctr. subst.
inversion H. subst. apply app2_find_hole in H2. destruct H2. destruct s.
- destruct s.
  + destruct p. subst. exists (Γ0 ++ Γ1, Δ2 ++ A0 :: A :: Δ3 ++ Δ4). exists (Γ0 ++ B :: Γ1, Δ2 ++ A :: Δ3 ++ Δ4).
    split. split.
    apply ImpLRule_I.
    assert (E1: Δ2 ++ A0 :: A :: Δ3 ++ A :: Δ4 = (Δ2 ++ [A0]) ++ A :: Δ3 ++ A :: Δ4).
    repeat rewrite <- app_assoc. rewrite cons_single. reflexivity. rewrite E1.
    assert (E2: Δ2 ++ A0 :: A :: Δ3 ++ Δ4 = (Δ2 ++ [A0]) ++ A :: Δ3 ++ Δ4).
    repeat rewrite <- app_assoc. rewrite cons_single. reflexivity. rewrite E2. apply ctr_RI.
    apply ctr_RI.
  + destruct p. destruct x.
    * rewrite app_nil_r in e. rewrite app_nil_l in e0. subst.
      exists (Γ0 ++ Γ1, Δ2 ++ A0 :: A :: Δ3 ++ Δ4). exists (Γ0 ++ B :: Γ1, Δ2 ++ A :: Δ3 ++ Δ4).
      split. split.
      apply ImpLRule_I.
      assert (E1: Δ2 ++ A0 :: A :: Δ3 ++ A :: Δ4 = (Δ2 ++ [A0]) ++ A :: Δ3 ++ A :: Δ4).
      repeat rewrite <- app_assoc. rewrite cons_single. reflexivity. rewrite E1.
      assert (E2: Δ2 ++ A0 :: A :: Δ3 ++ Δ4 = (Δ2 ++ [A0]) ++ A :: Δ3 ++ Δ4).
      repeat rewrite <- app_assoc. rewrite cons_single. reflexivity. rewrite E2. apply ctr_RI.
      apply ctr_RI.
    * inversion e0. subst. apply app2_find_hole in H2. destruct H2. destruct s.
      { destruct s.
        - destruct p. subst. exists  (Γ0 ++ Γ1, (Δ2 ++ m :: Δ3) ++ A0 :: Δ4).
          exists (Γ0 ++ B :: Γ1, (Δ2 ++ m :: Δ3) ++ Δ4). split. split.
          assert (E: Δ2 ++ m :: Δ3 ++ Δ4 = (Δ2 ++ m :: Δ3) ++ Δ4).
          rewrite <- app_assoc. reflexivity. rewrite E.
          apply ImpLRule_I.
          assert (E1: (Δ2 ++ m :: Δ3) ++ A0 :: m :: Δ4 = Δ2 ++ m :: (Δ3 ++ [A0]) ++ m :: Δ4).
          repeat rewrite <- app_assoc. rewrite cons_single. reflexivity. rewrite E1.
          assert (E2: (Δ2 ++ m :: Δ3) ++ A0 :: Δ4 = Δ2 ++ m :: (Δ3 ++ [A0]) ++ Δ4).
          repeat rewrite <- app_assoc. rewrite cons_single. reflexivity. rewrite E2. apply ctr_RI.
          rewrite <- app_assoc. simpl. apply ctr_RI.
        - destruct p. subst. destruct x0.
          + rewrite app_nil_l in e1. rewrite app_nil_r in e0. subst.
            exists (Γ0 ++ Γ1,(Δ2 ++ m :: Δ3) ++ A0 :: Δ4). exists (Γ0 ++ B :: Γ1, (Δ2 ++ m :: Δ3) ++ Δ4).
            split. split.
            assert (E: Δ2 ++ m :: Δ3 ++ Δ4 = (Δ2 ++ m :: Δ3) ++ Δ4).
            rewrite <- app_assoc. reflexivity. rewrite E.
            apply ImpLRule_I.
            assert (E1: (Δ2 ++ m :: Δ3 ++ []) ++ A0 :: m :: Δ4 = Δ2 ++ m :: (Δ3 ++ [A0]) ++ m :: Δ4).
            rewrite app_nil_r. repeat rewrite <- app_assoc. rewrite cons_single. reflexivity. rewrite E1.
            assert (E2: (Δ2 ++ m :: Δ3) ++ A0 :: Δ4 = Δ2 ++ m :: (Δ3 ++ [A0]) ++ Δ4).
            repeat rewrite <- app_assoc. rewrite cons_single. reflexivity. rewrite E2. apply ctr_RI.
            rewrite <- app_assoc. simpl. apply ctr_RI.
          + inversion e1. subst. exists (Γ0 ++ Γ1,(Δ2 ++ m0 :: Δ3 ++ x0) ++ A0 :: Δ1).
            exists (Γ0 ++ B :: Γ1,(Δ2 ++ m0 :: Δ3 ++ x0) ++ Δ1). split. split.
            assert (E: Δ2 ++ m0 :: Δ3 ++ x0 ++ Δ1 = (Δ2 ++ m0 :: Δ3 ++ x0) ++ Δ1).
            rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite E.
            apply ImpLRule_I.
            assert (E1: (Δ2 ++ m0 :: Δ3 ++ m0 :: x0) ++ A0 :: Δ1 = Δ2 ++ m0 :: Δ3 ++ m0 :: x0 ++ A0 :: Δ1).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite E1.
            assert (E2: (Δ2 ++ m0 :: Δ3 ++ x0) ++ A0 :: Δ1 = Δ2 ++ m0 :: Δ3 ++ x0 ++ A0 :: Δ1).
            repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite E2. apply ctr_RI.
            rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. apply ctr_RI. }
      { destruct p. subst. exists (Γ0 ++ Γ1,(Δ2 ++ m :: x) ++ A0 :: x0 ++ Δ4).
        exists (Γ0 ++ B :: Γ1, (Δ2 ++ m :: x) ++ x0 ++ Δ4). split. split.
        assert (E: Δ2 ++ m :: (x ++ x0) ++ Δ4 = (Δ2 ++ m :: x) ++ x0 ++ Δ4).
        rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite E.
        apply ImpLRule_I.
        assert (E1: (Δ2 ++ m :: x) ++ A0 :: x0 ++ m :: Δ4 = Δ2 ++ m :: (x ++ A0 :: x0) ++ m :: Δ4).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite E1.
        assert (E2: (Δ2 ++ m :: x) ++ A0 :: x0 ++ Δ4 = Δ2 ++ m :: (x ++ A0 :: x0) ++ Δ4).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite E2. apply ctr_RI.
        assert (E1: (Δ2 ++ m :: x) ++ x0 ++ Δ4 = Δ2 ++ m :: (x ++ x0) ++ Δ4).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite E1. apply ctr_RI. }
- destruct p. subst. exists (Γ0 ++ Γ1, Δ0 ++ A0 :: x ++ A :: Δ3 ++ Δ4).
  exists (Γ0 ++ B :: Γ1, Δ0 ++ x ++ A :: Δ3 ++ Δ4). split. split.
  rewrite <- app_assoc. apply ImpLRule_I.
  assert (E1: Δ0 ++ A0 :: x ++ A :: Δ3 ++ A :: Δ4 = (Δ0 ++ A0 :: x) ++ A :: Δ3 ++ A :: Δ4).
  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite E1.
  assert (E2: Δ0 ++ A0 :: x ++ A :: Δ3 ++ Δ4 = (Δ0 ++ A0 :: x) ++ A :: Δ3 ++ Δ4).
  repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite E2. apply ctr_RI.
  rewrite app_assoc. apply ctr_RI.
Qed.

Lemma GLR_app_ctr_R : forall s sc A ps,
  (@ctr_R A s sc) -> (GLRRule [ps] s) -> (GLRRule [ps] sc).
Proof.
intros s sc A ps ctr RA. inversion RA. inversion ctr. rewrite <- H1 in H2.
inversion H2. apply app2_find_hole in H6. destruct H6. destruct s0.
  + destruct s0.
    * destruct p. inversion e0. apply GLRRule_I. assumption. assumption.
    * destruct p. subst. destruct x.
      { rewrite app_nil_l in e0. inversion e0. subst. apply GLRRule_I.
        assumption. assumption. }
      { inversion e0. subst. apply app2_find_hole in H3. destruct H3. destruct s.
        - destruct s.
          + destruct p. inversion e1. apply GLRRule_I. assumption. assumption.
          + destruct p. subst. destruct x0.
            * rewrite app_nil_l in e1. inversion e1. subst. apply GLRRule_I. assumption.
              assumption.
            * inversion e1. subst. assert (E: Δ2 ++ m0 :: Δ3 ++ x0 ++ Box A0 :: Δ1 = (Δ2 ++ m0 :: Δ3 ++ x0) ++ Box A0 :: Δ1).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite E. apply GLRRule_I. assumption.
              assumption.
        - destruct p. subst. destruct x0.
          * rewrite app_nil_l in e1. inversion e1. subst. apply GLRRule_I. assumption. assumption.
          * inversion e1. subst. assert (E: Δ2 ++ m :: (x ++ Box A0 :: x0) ++ Δ4 = (Δ2 ++ m :: x) ++ Box A0 :: x0 ++ Δ4).
            repeat rewrite <- app_assoc. reflexivity. rewrite E. apply GLRRule_I. assumption. assumption. }
  + destruct p. subst. destruct x.
    * rewrite app_nil_l in e0. rewrite app_nil_r. inversion e0. subst. apply GLRRule_I. assumption. assumption.
    * inversion e0. rewrite <- app_assoc. simpl. apply GLRRule_I. assumption. assumption.
Qed.

(* Now we can prove that contractions are height-preserving admissible. *)

Theorem GLS_hpadm_ctr_LR : forall (k : nat) s
        (D0 : GLS_prv s),
        k = (derrec_height D0) ->
          (forall sc A, (((@ctr_L A s sc) + (@ctr_R A s sc)) ->
          existsT2 (D1 : GLS_prv sc),
          derrec_height D1 <= k)).
Proof.
induction k as [n IH] using (well_founded_induction_type lt_wf).
intros s D0. remember D0 as D0'. destruct D0.
(* D0 ip a leaf *)
- intros hei sc A ctr. inversion f.
(* D0 is ends with an application of rule *)
- intros hei sc A ctr. destruct ctr as [ctr | ctr].
{ inversion ctr. assert (DersNil: dersrec GLS_rules (fun _ : Seq => False) []).
  apply dersrec_nil. inversion g.
  (* IdP *)
  * inversion H1. rewrite <- H in H5. inversion H5.
    apply app2_find_hole in H7. destruct H7. destruct s.
    + destruct s.
      { destruct p. inversion e0. subst. pose (IdPRule_I P Γ3 (Γ1 ++ Γ2) Δ0 Δ1). apply IdP in i. simpl in i.
        pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
        (ps:=[]) (Γ3 ++ # P :: Γ1 ++ Γ2, Δ0 ++ # P :: Δ1) i DersNil). exists d0. simpl. repeat rewrite dersrec_height_nil.
        left. reflexivity. reflexivity. }
      { destruct p. destruct x.
        - rewrite app_nil_l in e0. inversion e0.
          subst. pose (IdPRule_I P (Γ3 ++ []) (Γ1 ++ Γ2) Δ0 Δ1). apply IdP in i. simpl in i.
          pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
          (ps:=[]) ((Γ3 ++ []) ++ # P :: Γ1 ++ Γ2,Δ0 ++ # P :: Δ1) i DersNil). exists d0. simpl.
          repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity.
        - inversion e0. subst.
          pose (IdPRule_I P Γ3 (x ++ A :: Γ1 ++ Γ2) Δ0 Δ1). apply IdP in i. simpl in i.
          assert (E: Γ3 ++ # P :: x ++ A :: Γ1 ++ Γ2 = (Γ3 ++ # P :: x) ++ A :: Γ1 ++ Γ2). repeat rewrite <- app_assoc. reflexivity.
          rewrite E in i. clear E.
          pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
          (ps:=[]) ((Γ3 ++ # P :: x) ++ A :: Γ1 ++ Γ2,Δ0 ++ # P :: Δ1) i DersNil). exists d0. simpl.
          repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity. }
    + destruct p. destruct x.
      { rewrite app_nil_l in e0. inversion e0. subst.
        pose (IdPRule_I P Γ0 (Γ1 ++ Γ2) Δ0 Δ1). apply IdP in i. simpl in i.
        pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
        (ps:=[]) (Γ0 ++ # P :: Γ1 ++ Γ2, Δ0 ++ # P :: Δ1) i DersNil). exists d0. simpl.
        repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity. }
      { inversion e0. subst. apply app2_find_hole in H9. destruct H9. destruct s.
        - destruct s.
          + destruct p. inversion e1. subst.
            pose (IdPRule_I P Γ0 (Γ1 ++ Γ2) Δ0 Δ1). apply IdP in i. simpl in i.
            pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
            (ps:=[]) (Γ0 ++ # P :: Γ1 ++ Γ2, Δ0 ++ # P :: Δ1) i DersNil). exists d0. simpl.
            repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity.
          + destruct p. destruct x0. 
            * rewrite app_nil_l in e1. inversion e1. subst.
              pose (IdPRule_I P Γ0 (Γ1 ++ Γ4) Δ0 Δ1). apply IdP in i. simpl in i.
              pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
              (ps:=[]) (Γ0 ++ # P :: Γ1 ++ Γ4, Δ0 ++ # P :: Δ1) i DersNil). exists d0. simpl.
              repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity.
            * inversion e1. subst.
              pose (IdPRule_I P (Γ0 ++ m0 :: Γ1 ++ x0) Γ4 Δ0 Δ1). apply IdP in i. simpl in i.
              repeat rewrite <- app_assoc in i. simpl in i. repeat rewrite <- app_assoc in i.
              pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
              (ps:=[]) (Γ0 ++ m0 :: Γ1 ++ x0 ++ # P :: Γ4,Δ0 ++ # P :: Δ1) i DersNil). exists d0. simpl.
              repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity.
        - destruct p. destruct x0.
          + rewrite app_nil_l in e1. inversion e1. subst.
            pose (IdPRule_I P Γ0 ((x ++ []) ++ Γ2) Δ0 Δ1). apply IdP in i. simpl in i.
            pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
            (ps:=[]) (Γ0 ++ # P :: (x ++ []) ++ Γ2, Δ0 ++ # P :: Δ1) i DersNil). exists d0. simpl.
            repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity.
          + inversion e1. subst.
            pose (IdPRule_I P (Γ0 ++ m :: x) (x0 ++ Γ2) Δ0 Δ1). apply IdP in i. simpl in i.
            assert (E:  (Γ0 ++ m :: x) ++ # P :: x0 ++ Γ2 = Γ0 ++ m :: (x ++ # P :: x0) ++ Γ2). repeat rewrite <- app_assoc. reflexivity.
            rewrite E in i. clear E.
            pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
            (ps:=[]) (Γ0 ++ m :: (x ++ # P :: x0) ++ Γ2,Δ0 ++ # P :: Δ1) i DersNil). exists d0. simpl.
            repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity. }
  (* BotL *)
  * inversion H1. rewrite <- H in H5. inversion H5.
    apply app2_find_hole in H7. destruct H7. destruct s.
    + destruct s.
      { destruct p. inversion e0. subst. pose (BotLRule_I Γ3 (Γ1 ++ Γ2) Δ). apply BotL in b.
        pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
        (ps:=[]) (Γ3 ++ ⊥ :: Γ1 ++ Γ2, Δ) b DersNil). exists d0. simpl. repeat rewrite dersrec_height_nil.
        left. reflexivity. reflexivity. }
      { destruct p. destruct x.
        - rewrite app_nil_l in e0. inversion e0.
          subst. pose (BotLRule_I (Γ3 ++ []) (Γ1 ++ Γ2) Δ). apply BotL in b. simpl in b.
          pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
          (ps:=[]) ((Γ3 ++ []) ++ ⊥ :: Γ1 ++ Γ2, Δ) b DersNil). exists d0. simpl.
          repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity.
        - inversion e0. subst.
          pose (BotLRule_I Γ3 (x ++ A :: Γ1 ++ Γ2) Δ). apply BotL in b. simpl in b.
          assert (E: Γ3 ++ ⊥ :: x ++ A :: Γ1 ++ Γ2 = (Γ3 ++ ⊥ :: x) ++ A :: Γ1 ++ Γ2). repeat rewrite <- app_assoc. reflexivity.
          rewrite E in b. clear E.
          pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
          (ps:=[]) ((Γ3 ++ ⊥ :: x) ++ A :: Γ1 ++ Γ2, Δ) b DersNil). exists d0. simpl.
          repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity. }
    + destruct p. destruct x.
      { rewrite app_nil_l in e0. inversion e0. subst.
        pose (BotLRule_I Γ0 (Γ1 ++ Γ2) Δ). apply BotL in b. simpl in b.
        pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
        (ps:=[]) (Γ0 ++ ⊥ :: Γ1 ++ Γ2, Δ) b DersNil). exists d0. simpl.
        repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity. }
      { inversion e0. subst. apply app2_find_hole in H9. destruct H9. destruct s.
        - destruct s.
          + destruct p. inversion e1. subst.
            pose (BotLRule_I Γ0 (Γ1 ++ Γ2) Δ). apply BotL in b. simpl in b.
            pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
            (ps:=[]) (Γ0 ++ ⊥ :: Γ1 ++ Γ2, Δ) b DersNil). exists d0. simpl.
            repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity.
          + destruct p. destruct x0.
            * rewrite app_nil_l in e1. inversion e1. subst.
              pose (BotLRule_I Γ0 (Γ1 ++ Γ4) Δ). apply BotL in b. simpl in b.
              pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
              (ps:=[]) (Γ0 ++ ⊥ :: Γ1 ++ Γ4, Δ) b DersNil). exists d0. simpl.
              repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity.
            * inversion e1. subst.
              pose (BotLRule_I (Γ0 ++ m0 :: Γ1 ++ x0) Γ4 Δ). apply BotL in b. simpl in b.
              repeat rewrite <- app_assoc in b. simpl in b. repeat rewrite <- app_assoc in b.
              pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
              (ps:=[]) (Γ0 ++ m0 :: Γ1 ++ x0 ++ ⊥ :: Γ4, Δ) b DersNil). exists d0. simpl.
              repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity.
        - destruct p. destruct x0.
          + rewrite app_nil_l in e1. inversion e1. subst.
            pose (BotLRule_I Γ0 ((x ++ []) ++ Γ2) Δ). apply BotL in b. simpl in b.
            pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
            (ps:=[]) (Γ0 ++ ⊥ :: (x ++ []) ++ Γ2, Δ) b DersNil). exists d0. simpl.
            repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity.
          + inversion e1. subst.
            pose (BotLRule_I (Γ0 ++ m :: x) (x0 ++ Γ2) Δ). apply BotL in b. simpl in b.
            assert (E:  (Γ0 ++ m :: x) ++ ⊥ :: x0 ++ Γ2 = Γ0 ++ m :: (x ++ ⊥ :: x0) ++ Γ2). repeat rewrite <- app_assoc. reflexivity.
            rewrite E in b. clear E.
            pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
            (ps:=[]) (Γ0 ++ m :: (x ++ ⊥ :: x0) ++ Γ2, Δ) b DersNil). exists d0. simpl.
            repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity. }
  (* ImpR *)
  * inversion H1. subst. inversion H5. subst. pose (ImpR_app_ctr_L ctr H1). destruct s. destruct p.
    apply ImpR in i.
    pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
    (ps:=[x]) (Γ0 ++ A :: Γ1 ++ Γ2, Δ0 ++ A0 --> B :: Δ1) i). subst. simpl.
    remember [(Γ3 ++ A0 :: Γ4, Δ0 ++ B :: Δ1)] as ps'. destruct d. inversion Heqps'.
    inversion Heqps'. subst. simpl. rewrite dersrec_height_nil. simpl in IH.
    rewrite dersrec_height_nil in IH. rewrite Nat.max_0_r. rewrite Nat.max_0_r in IH.
    assert (E: derrec_height d < S (derrec_height d)). auto.
    assert (E1: derrec_height d = derrec_height d). auto.
    assert ((ctr_L A (Γ3 ++ A0 :: Γ4, Δ0 ++ B :: Δ1) x) + (ctr_R A (Γ3 ++ A0 :: Γ4, Δ0 ++ B :: Δ1) x)).
    left. auto.
    pose (IH (derrec_height d) E (Γ3 ++ A0 :: Γ4, Δ0 ++ B :: Δ1) d E1 x A H).
    destruct s.
    pose (dlCons x0 d1). pose (d0 d2). exists d3. simpl. rewrite dersrec_height_nil.
    rewrite Nat.max_0_r. rewrite <- Nat.succ_le_mono. assumption. reflexivity. reflexivity. reflexivity.
  (* ImpL *)
  * inversion H1. subst. inversion H5. subst. pose (ImpL_app_ctr_L ctr H1). destruct s.
    { repeat destruct s. repeat destruct p. apply ImpL in i.
      pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
      (ps:=[x;x0]) (Γ0 ++ A :: Γ1 ++ Γ2, Δ0 ++ Δ1) i). subst. simpl.
      remember [(Γ3 ++ Γ4, Δ0 ++ A0 :: Δ1);(Γ3 ++ B :: Γ4, Δ0 ++ Δ1)] as ps'. destruct d.
      inversion Heqps'. inversion Heqps'. subst.
      remember [(Γ3 ++ B :: Γ4, Δ0 ++ Δ1)] as ps''. destruct d1. inversion Heqps''.
      inversion Heqps''. simpl. subst. rewrite dersrec_height_nil. simpl in IH.
      rewrite dersrec_height_nil in IH. rewrite Nat.max_0_r. rewrite Nat.max_0_r in IH.
      assert (E1: derrec_height d < S (Init.Nat.max (derrec_height d)(derrec_height d1))).
      apply Nat.lt_succ_r. apply Nat.le_max_l.
      assert (E2: derrec_height d = derrec_height d). auto.
      assert ((ctr_L A (Γ3 ++ Γ4, Δ0 ++ A0 :: Δ1) x) + (ctr_R A (Γ3 ++ Γ4, Δ0 ++ A0 :: Δ1) x)).
      auto.
      pose (IH (derrec_height d) E1 (Γ3 ++ Γ4, Δ0 ++ A0 :: Δ1) d E2 x A H).
      destruct s.
      assert (E3: derrec_height d1 < S (Init.Nat.max (derrec_height d)(derrec_height d1))).
      apply Nat.lt_succ_r. apply Nat.le_max_r.
      assert (E4: derrec_height d1 = derrec_height d1). auto.
      assert ((ctr_L A (Γ3 ++ B :: Γ4, Δ0 ++ Δ1) x0) + (ctr_R A (Γ3 ++ B :: Γ4, Δ0 ++ Δ1) x0)).
      auto.
      pose (IH (derrec_height d1) E3 (Γ3 ++ B :: Γ4, Δ0 ++ Δ1) d1 E4 x0 A H2).
      destruct s.
      pose (dlCons x1 (dlCons x2 d2)). pose (d0 d3). exists d4. simpl. rewrite dersrec_height_nil.
      rewrite Nat.max_0_r. rewrite <- Nat.succ_le_mono. apply Nat.max_le_compat.
      assumption. assumption. reflexivity. reflexivity. reflexivity. }
    { simpl. repeat destruct s. repeat destruct p. subst. apply ImpL in i.
      assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
      assert (J1: derrec_height x7 = derrec_height x7). reflexivity.
      pose (ImpR_ImpL_hpinv _ J1). destruct p. clear s. pose (s0 _ _ i1). repeat destruct s.
      clear s0. destruct p. simpl in IH.
      assert (J2: derrec_height x9 < S (dersrec_height d)). lia.
      assert (J3: derrec_height x9 = derrec_height x9). reflexivity.
      assert (J4: (ctr_L x x1 x5) + (ctr_R x x1 x5)). auto.
      pose (IH _ J2 _ _ J3 _ _ J4). destruct s.
      assert (J5: derrec_height x8 = derrec_height x8). reflexivity.
      pose (ImpR_ImpL_hpinv _ J5). destruct p. clear s. pose (s0 _ _ i0). repeat destruct s.
      clear s0. destruct p.
      assert (J6: derrec_height x13 < S (dersrec_height d)). lia.
      assert (J7: derrec_height x13 = derrec_height x13). reflexivity.
      assert (J8: (ctr_L x0 x4 x6) + (ctr_R x0 x4 x6)). auto.
      pose (IH _ J6 _ _ J7 _ _ J8). destruct s. pose (dlCons x14 DersNil). pose (dlCons x11 d0).
      pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
      (ps:=[x5;x6]) (Γ0 ++ x --> x0 :: Γ1 ++ Γ2, Δ0 ++ Δ1) i d1). exists d2. simpl.
      rewrite dersrec_height_nil. lia. reflexivity. }
  (* GLR *)
  * inversion X. rewrite <- H4 in X. pose (GLR_app_ctr_L ctr X). destruct s.
    { apply GLR in g0. pose (derI (rules:=GLS_rules)
      (prems:=fun _ : Seq => False) (ps:=[(XBoxed_list BΓ ++ [Box A0], [A0])]) 
      sc g0). subst. pose (d0 d). exists d1. simpl. reflexivity. }
    { repeat destruct s. repeat destruct p. apply GLR in g0.
      remember [(XBoxed_list BΓ ++ [Box A0], [A0])] as ps'. destruct d. subst. inversion H4.
      rewrite Heqps' in H4. inversion H4. subst. simpl. simpl in IH.
      assert (E1: derrec_height d < S (Init.Nat.max (derrec_height d) (dersrec_height d0))).
      rewrite dersrec_height_nil. rewrite Nat.max_0_r. apply Nat.lt_succ_r. left. reflexivity.
      assert (E2: derrec_height d = derrec_height d). auto.
      assert ((ctr_L (unBox_formula A) (XBoxed_list BΓ ++ [Box A0], [A0]) x) +
      (ctr_R (unBox_formula A) (XBoxed_list BΓ ++ [Box A0], [A0]) x)). auto.
      pose (IH (derrec_height d) E1 ((XBoxed_list BΓ ++ [Box A0], [A0])) d E2 x (unBox_formula A) H).
      destruct s.
      assert (E3: derrec_height x1 < S (Init.Nat.max (derrec_height d) (dersrec_height d0))).
      rewrite dersrec_height_nil. rewrite Nat.max_0_r. apply Nat.lt_succ_r. assumption. reflexivity.
      assert (E4: derrec_height x1 = derrec_height x1). auto.
      assert ((ctr_L A x x0) + (ctr_R A x x0)). auto.
      pose (IH (derrec_height x1) E3 x x1 E4 x0 A H0). destruct s.
      pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
      (ps:=[x0]) (Γ0 ++ A :: Γ1 ++ Γ2, Δ) g0). subst. simpl.
      pose (dlCons x2 d0). pose (d1 d2). exists d3. simpl. rewrite dersrec_height_nil.
      repeat rewrite Nat.max_0_r. rewrite <- Nat.succ_le_mono.
      pose (Nat.le_trans (derrec_height x2) (derrec_height x1) (derrec_height d) l0 l).
      assumption. reflexivity. }}
{ inversion ctr. assert (DersNil: dersrec GLS_rules (fun _ : Seq => False) []).
  apply dersrec_nil. inversion g.
  (* IdP *)
  * inversion H1. rewrite <- H in H5. inversion H5.
    apply app2_find_hole in H8. destruct H8. destruct s.
    + destruct s.
      { destruct p. inversion e0. subst. pose (IdPRule_I P Γ0 Γ1 Δ3 (Δ1 ++ Δ2)). apply IdP in i. simpl in i.
        pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
        (ps:=[]) (Γ0 ++ # P :: Γ1, Δ3 ++ # P :: Δ1 ++ Δ2) i DersNil). exists d0. simpl. repeat rewrite dersrec_height_nil.
        left. reflexivity. reflexivity. }
      { destruct p. destruct x.
        - rewrite app_nil_l in e0. inversion e0.
          subst. pose (IdPRule_I P Γ0 Γ1 (Δ3 ++ []) (Δ1 ++ Δ2)). apply IdP in i. simpl in i.
          pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
          (ps:=[]) (Γ0 ++ # P :: Γ1, (Δ3 ++ []) ++ # P :: Δ1 ++ Δ2) i DersNil). exists d0. simpl.
          repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity.
        - inversion e0. subst.
          pose (IdPRule_I P Γ0 Γ1 Δ3 (x ++ A :: Δ1 ++ Δ2)). apply IdP in i. simpl in i.
          assert (E: Δ3 ++ # P :: x ++ A :: Δ1 ++ Δ2 = (Δ3 ++ # P :: x) ++ A :: Δ1 ++ Δ2). repeat rewrite <- app_assoc. reflexivity.
          rewrite E in i. clear E.
          pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
          (ps:=[]) (Γ0 ++ # P :: Γ1, (Δ3 ++ # P :: x) ++ A :: Δ1 ++ Δ2) i DersNil). exists d0. simpl.
          repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity. }
    + destruct p. destruct x.
      { rewrite app_nil_l in e0. inversion e0. subst.
        pose (IdPRule_I P Γ0 Γ1 Δ0 (Δ1 ++ Δ2)). apply IdP in i. simpl in i.
        pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
        (ps:=[]) (Γ0 ++ # P :: Γ1, Δ0 ++ # P :: Δ1 ++ Δ2) i DersNil). exists d0. simpl.
        repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity. }
      { inversion e0. subst. apply app2_find_hole in H9. destruct H9. destruct s.
        - destruct s.
          + destruct p. inversion e1. subst.
            pose (IdPRule_I P Γ0 Γ1 Δ0 (Δ1 ++ Δ2)). apply IdP in i. simpl in i.
            pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
            (ps:=[]) (Γ0 ++ # P :: Γ1, Δ0 ++ # P :: Δ1 ++ Δ2) i DersNil). exists d0. simpl.
            repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity.
          + destruct p. destruct x0. 
            * rewrite app_nil_l in e1. inversion e1. subst.
              pose (IdPRule_I P Γ0 Γ1 Δ0 (Δ1 ++ Δ4)). apply IdP in i. simpl in i.
              pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
              (ps:=[]) (Γ0 ++ # P :: Γ1, Δ0 ++ # P :: Δ1 ++ Δ4) i DersNil). exists d0. simpl.
              repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity.
            * inversion e1. subst.
              pose (IdPRule_I P Γ0 Γ1 (Δ0 ++ m0 :: Δ1 ++ x0) Δ4). apply IdP in i. simpl in i.
              repeat rewrite <- app_assoc in i. simpl in i. repeat rewrite <- app_assoc in i.
              pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
              (ps:=[]) (Γ0 ++ # P :: Γ1, Δ0 ++ m0 :: Δ1 ++ x0 ++ # P :: Δ4) i DersNil). exists d0. simpl.
              repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity.
        - destruct p. destruct x0.
          + rewrite app_nil_l in e1. inversion e1. subst.
            pose (IdPRule_I P Γ0 Γ1 Δ0 ((x ++ []) ++ Δ2)). apply IdP in i. simpl in i.
            pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
            (ps:=[]) (Γ0 ++ # P :: Γ1, Δ0 ++ # P :: (x ++ []) ++ Δ2) i DersNil). exists d0. simpl.
            repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity.
          + inversion e1. subst.
            pose (IdPRule_I P Γ0 Γ1 (Δ0 ++ m :: x) (x0 ++ Δ2)). apply IdP in i. simpl in i.
            assert (E:  (Δ0 ++ m :: x) ++ # P :: x0 ++ Δ2 = Δ0 ++ m :: (x ++ # P :: x0) ++ Δ2). repeat rewrite <- app_assoc. reflexivity.
            rewrite E in i. clear E.
            pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
            (ps:=[]) (Γ0 ++ # P :: Γ1, Δ0 ++ m :: (x ++ # P :: x0) ++ Δ2) i DersNil). exists d0. simpl.
            repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity. }
  (* BotL *)
  * inversion H1. rewrite <- H in H5. inversion H5.
    pose (BotLRule_I Γ0 Γ1 (Δ0 ++ A :: Δ1 ++ Δ2)). apply BotL in b.
    pose (derI (rules:=GLS_rules)
    (prems:=fun _ : Seq => False)
    (ps:=[]) (Γ0 ++ ⊥ :: Γ1, Δ0 ++ A :: Δ1 ++ Δ2) b DersNil). subst. exists d0. simpl.
    repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity.
  (* ImpR *)
  * inversion H1. subst. inversion H5. subst. pose (ImpR_app_ctr_R ctr H1). destruct s.
    { destruct s. destruct p. apply ImpR in i.
      pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
      (ps:=[x]) (Γ0 ++ Γ1, Δ0 ++ A :: Δ1 ++ Δ2) i). subst. simpl.
      remember [(Γ0 ++ A0 :: Γ1, Δ3 ++ B :: Δ4)] as ps'. destruct d. inversion Heqps'.
      inversion Heqps'. subst. simpl. rewrite dersrec_height_nil. simpl in IH.
      rewrite dersrec_height_nil in IH. rewrite Nat.max_0_r. rewrite Nat.max_0_r in IH.
      assert (E: derrec_height d < S (derrec_height d)). auto.
      assert (E1: derrec_height d = derrec_height d). auto.
      assert ((ctr_L A (Γ0 ++ A0 :: Γ1, Δ3 ++ B :: Δ4) x) + (ctr_R A (Γ0 ++ A0 :: Γ1, Δ3 ++ B :: Δ4) x)).
      auto.
      pose (IH (derrec_height d) E (Γ0 ++ A0 :: Γ1, Δ3 ++ B :: Δ4) d E1 x A H).
      destruct s.
      pose (dlCons x0 d1). pose (d0 d2). exists d3. simpl. rewrite dersrec_height_nil.
      rewrite Nat.max_0_r. rewrite <- Nat.succ_le_mono. assumption. reflexivity. reflexivity. reflexivity. }
    { repeat destruct s. repeat destruct p. subst. apply ImpR in i.
      assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (dersrec_derrec_height d J30). destruct s.
      assert (J1: derrec_height x4 = derrec_height x4). reflexivity.
      pose (ImpR_ImpL_hpinv _ J1). destruct p. clear s0. pose (s _ i0). repeat destruct s0.
      clear s. simpl in IH.
      assert (J2: derrec_height x5 < S (dersrec_height d)). lia.
      assert (J3: derrec_height x5 = derrec_height x5). reflexivity.
      assert (J4: (ctr_L x x1 x2) + (ctr_R x x1 x2)). auto.
      pose (IH _ J2 _ _ J3 _ _ J4). destruct s.
      assert (J5: derrec_height x6 = derrec_height x6). reflexivity.
      assert (J6: derrec_height x6 < S (dersrec_height d)). lia.
      assert (J8: (ctr_L x0 x2 x3) + (ctr_R x0 x2 x3)). auto.
      pose (IH _ J6 _ _ J5 _ _ J8). destruct s. pose (dlCons x7 DersNil).
      pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
      (ps:=[x3]) (Γ0 ++ Γ1, Δ0 ++ x --> x0 :: Δ1 ++ Δ2) i d0). simpl. exists d1. simpl. rewrite dersrec_height_nil.
      lia. reflexivity. }
  (* ImpL *)
  * inversion H1. subst. inversion H5. subst. pose (ImpL_app_ctr_R ctr H1). destruct s.
    repeat destruct s. repeat destruct p. apply ImpL in i.
    pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
    (ps:=[x;x0]) (Γ0 ++ A0 --> B :: Γ1, Δ0 ++ A :: Δ1 ++ Δ2) i). subst. simpl.
    remember [(Γ0 ++ Γ1, Δ3 ++ A0 :: Δ4);(Γ0 ++ B :: Γ1, Δ3 ++ Δ4)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst.
    remember [(Γ0 ++ B :: Γ1, Δ3 ++ Δ4)] as ps''. destruct d1. inversion Heqps''.
    inversion Heqps''. simpl. subst. rewrite dersrec_height_nil. simpl in IH.
    rewrite dersrec_height_nil in IH. rewrite Nat.max_0_r. rewrite Nat.max_0_r in IH.
    assert (E1: derrec_height d < S (Init.Nat.max (derrec_height d)(derrec_height d1))).
    apply Nat.lt_succ_r. apply Nat.le_max_l.
    assert (E2: derrec_height d = derrec_height d). auto.
    assert ((ctr_L A (Γ0 ++ Γ1, Δ3 ++ A0 :: Δ4) x) + (ctr_R A (Γ0 ++ Γ1, Δ3 ++ A0 :: Δ4) x)).
    auto.
    pose (IH (derrec_height d) E1 (Γ0 ++ Γ1, Δ3 ++ A0 :: Δ4) d E2 x A H).
    destruct s.
    assert (E3: derrec_height d1 < S (Init.Nat.max (derrec_height d)(derrec_height d1))).
    apply Nat.lt_succ_r. apply Nat.le_max_r.
    assert (E4: derrec_height d1 = derrec_height d1). auto.
    assert ((ctr_L A (Γ0 ++ B :: Γ1, Δ3 ++ Δ4) x0) + (ctr_R A (Γ0 ++ B :: Γ1, Δ3 ++ Δ4) x0)).
    auto.
    pose (IH (derrec_height d1) E3 (Γ0 ++ B :: Γ1, Δ3 ++ Δ4) d1 E4 x0 A H0).
    destruct s.
    pose (dlCons x1 (dlCons x2 d2)). pose (d0 d3). exists d4. simpl. rewrite dersrec_height_nil.
    rewrite Nat.max_0_r. rewrite <- Nat.succ_le_mono. apply Nat.max_le_compat.
    assumption. assumption. reflexivity. reflexivity. reflexivity.
  (* GLR *)
  * inversion X. rewrite <- H4 in X. pose (GLR_app_ctr_R ctr X).
    apply GLR in g0.
    pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
    (ps:=[(XBoxed_list BΓ ++ [Box A0], [A0])]) sc g0). subst. simpl. pose (d0 d). exists d1.
    simpl. rewrite <- Nat.succ_le_mono. left. }
Qed.

Theorem GLS_hpadm_ctr_L : forall (k : nat) s
        (D0 : GLS_prv s),
        k = (derrec_height D0) ->
          (forall sc A, ((@ctr_L A s sc) ->
          existsT2 (D1 : GLS_prv sc),
          derrec_height D1 <= k)).
Proof.
intros. intros. assert (H1: derrec_height D0 = derrec_height D0). reflexivity.
assert (H3 : (ctr_L A s sc) + (ctr_R A s sc)). auto.
pose (@GLS_hpadm_ctr_LR (derrec_height D0) s
D0 H1 sc A H3). destruct s0. exists x. lia.
Qed.

Theorem GLS_hpadm_ctr_R : forall (k : nat) s
        (D0 : GLS_prv s),
        k = (derrec_height D0) ->
          (forall sc A, ((@ctr_R A s sc) ->
          existsT2 (D1 : GLS_prv sc),
          derrec_height D1 <= k)).
Proof.
intros. intros. assert (H1: derrec_height D0 = derrec_height D0). reflexivity.
assert (H3 : (ctr_L A s sc) + (ctr_R A s sc)). auto.
pose (@GLS_hpadm_ctr_LR (derrec_height D0) s
D0 H1 sc A H3). destruct s0. exists x. lia.
Qed.

(* We can now prove that contraction of lists is also admissible. *)

Theorem GLS_hpadm_list_ctr_L : forall Γ1 (k : nat) Γ0 Γ2 Γ3 Δ
        (D0 : GLS_prv (Γ0 ++ Γ1 ++ Γ2 ++ Γ1 ++ Γ3,Δ)),
        k = (derrec_height D0) ->
          existsT2 (D1 : GLS_prv (Γ0 ++ Γ1 ++ Γ2 ++ Γ3,Δ)),
          derrec_height D1 <= k.
Proof.
induction Γ1.
- intros. exists D0. rewrite H. auto.
- intros. assert (H0: derrec_height D0 = derrec_height D0). reflexivity.
  assert (H1 : ctr_L a (Γ0 ++ (a :: Γ1) ++ Γ2 ++ (a :: Γ1) ++ Γ3, Δ) ((Γ0 ++ [a]) ++ Γ1 ++ Γ2 ++ Γ1 ++ Γ3, Δ)).
  simpl. assert (Γ0 ++ a :: Γ1 ++ Γ2 ++ a :: Γ1 ++ Γ3 = Γ0 ++ a :: (Γ1 ++ Γ2) ++ a :: (Γ1 ++ Γ3)).
  repeat rewrite <- app_assoc. reflexivity. rewrite H1.
  assert ((Γ0 ++ [a]) ++ Γ1 ++ Γ2 ++ Γ1 ++ Γ3 = Γ0 ++ a :: (Γ1 ++ Γ2) ++ Γ1 ++ Γ3). repeat rewrite <- app_assoc.
  reflexivity. rewrite H2. apply ctr_LI.
  assert ((ctr_L a (Γ0 ++ (a :: Γ1) ++ Γ2 ++ (a :: Γ1) ++ Γ3, Δ) ((Γ0 ++ [a]) ++ Γ1 ++ Γ2 ++ Γ1 ++ Γ3, Δ)) +
  (ctr_R a (Γ0 ++ (a :: Γ1) ++ Γ2 ++ (a :: Γ1) ++ Γ3, Δ) ((Γ0 ++ [a]) ++ Γ1 ++ Γ2 ++ Γ1 ++ Γ3, Δ))). auto.
  pose (@GLS_hpadm_ctr_LR (derrec_height D0) (Γ0 ++ (a :: Γ1) ++ Γ2 ++ (a :: Γ1) ++ Γ3, Δ)
  D0 H0 ((Γ0 ++ [a]) ++ Γ1 ++ Γ2 ++ Γ1 ++ Γ3, Δ) a H2). destruct s.
  assert (H3: derrec_height x = derrec_height x). reflexivity.
  pose (IHΓ1 (derrec_height x) (Γ0 ++ [a]) Γ2 Γ3 Δ x H3). destruct s.
  assert (Γ0 ++ (a :: Γ1) ++ Γ2 ++ Γ3 = (Γ0 ++ [a]) ++ Γ1 ++ Γ2 ++ Γ3). repeat rewrite <- app_assoc. auto.
  rewrite H4. exists x0. lia.
Qed.

Theorem GLS_hpadm_list_ctr_R : forall Δ1 (k : nat) Γ Δ0 Δ2 Δ3
        (D0 : GLS_prv (Γ,Δ0 ++ Δ1 ++ Δ2 ++ Δ1 ++ Δ3)),
        k = (derrec_height D0) ->
          existsT2 (D1 : GLS_prv (Γ,Δ0 ++ Δ1 ++ Δ2 ++ Δ3)),
          derrec_height D1 <= k.
Proof.
induction Δ1.
- intros. exists D0. rewrite H. auto.
- intros. assert (H0: derrec_height D0 = derrec_height D0). reflexivity.
  assert (H1 : ctr_R a (Γ, Δ0 ++ (a :: Δ1) ++ Δ2 ++ (a :: Δ1) ++ Δ3) (Γ, (Δ0 ++ [a]) ++ Δ1 ++ Δ2 ++ Δ1 ++ Δ3)).
  simpl. assert (Δ0 ++ a :: Δ1 ++ Δ2 ++ a :: Δ1 ++ Δ3 = Δ0 ++ a :: (Δ1 ++ Δ2) ++ a :: (Δ1 ++ Δ3)).
  repeat rewrite <- app_assoc. reflexivity. rewrite H1.
  assert ((Δ0 ++ [a]) ++ Δ1 ++ Δ2 ++ Δ1 ++ Δ3 = Δ0 ++ a :: (Δ1 ++ Δ2) ++ Δ1 ++ Δ3). repeat rewrite <- app_assoc.
  reflexivity. rewrite H2. apply ctr_RI.
  assert ((ctr_L a (Γ, Δ0 ++ (a :: Δ1) ++ Δ2 ++ (a :: Δ1) ++ Δ3) (Γ, (Δ0 ++ [a]) ++ Δ1 ++ Δ2 ++ Δ1 ++ Δ3)) +
  (ctr_R a (Γ, Δ0 ++ (a :: Δ1) ++ Δ2 ++ (a :: Δ1) ++ Δ3) (Γ, (Δ0 ++ [a]) ++ Δ1 ++ Δ2 ++ Δ1 ++ Δ3))). auto.
  pose (@GLS_hpadm_ctr_LR (derrec_height D0) (Γ, Δ0 ++ (a :: Δ1) ++ Δ2 ++ (a :: Δ1) ++ Δ3)
  D0 H0 (Γ, (Δ0 ++ [a]) ++ Δ1 ++ Δ2 ++ Δ1 ++ Δ3) a H2). destruct s.
  assert (H3: derrec_height x = derrec_height x). reflexivity.
  pose (IHΔ1 (derrec_height x) Γ (Δ0 ++ [a]) Δ2 Δ3 x H3). destruct s.
  assert (Δ0 ++ (a :: Δ1) ++ Δ2 ++ Δ3 = (Δ0 ++ [a]) ++ Δ1 ++ Δ2 ++ Δ3). repeat rewrite <- app_assoc. auto.
  rewrite H4. exists x0. lia.
Qed.



