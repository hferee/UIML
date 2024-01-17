Require Import List.
Export ListNotations.
Require Import Lia.
Require Import PeanoNat.

Require Import KS_calc.
Require Import KS_exch_prelims.

(* The following lemmas make sure that if a rule is applied on a sequent s with
premises ps, then the same rule is applicable on a sequent se which is an exchanged
version of s, with some premises pse that are such that they are exchanged versions
of ps. *)

Lemma ImpR_app_list_exchL : forall s se ps,
  (@list_exch_L s se) ->
  (ImpRRule [ps] s) ->
  (existsT2 pse,
    (ImpRRule [pse] se) *
    (@list_exch_L ps pse)).
Proof.
intros s se ps exch. intro RA. inversion RA. inversion exch. subst.
inversion H. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
- exists (Γ2 ++ A :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6, Δ0 ++ B :: Δ1). split.
  apply ImpRRule_I. assert (Γ2 ++ A :: Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = (Γ2 ++ [A]) ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6).
  rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
  assert (Γ2 ++ A :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ [A]) ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6).
  rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
- apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
  + exists ((Γ2 ++ Γ5) ++ A :: Γ4 ++ Γ3 ++ Γ6, Δ0 ++ B :: Δ1). split.
    assert (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5) ++ Γ4 ++ Γ3 ++ Γ6). rewrite app_assoc.
    reflexivity. rewrite H0. clear H0. apply ImpRRule_I. repeat rewrite <- app_assoc.
    assert (Γ2 ++ Γ3 ++ A :: Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (A :: Γ4) ++ Γ5 ++ Γ6).
    reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ Γ5 ++ A :: Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ (A :: Γ4) ++ Γ3 ++ Γ6).
    reflexivity. rewrite H0. clear H0. apply list_exch_LI.
  + apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
    * exists ((Γ2 ++ Γ5 ++ Γ4) ++ A :: Γ3 ++ Γ6, Δ0 ++ B :: Δ1). split.
      assert (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5 ++ Γ4) ++ Γ3 ++ Γ6). repeat rewrite app_assoc.
      reflexivity. rewrite H0. clear H0. apply ImpRRule_I. repeat rewrite <- app_assoc.
      assert (Γ2 ++ Γ3 ++ Γ4 ++ A :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (Γ4 ++ [A]) ++ Γ5 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      assert (Γ2 ++ Γ5 ++ Γ4 ++ A :: Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ (Γ4 ++ [A]) ++ Γ3 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
    * apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
      { repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ A :: Γ6, Δ0 ++ B :: Δ1).
        split. repeat rewrite app_assoc. apply ImpRRule_I. apply list_exch_LI. }
      { repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x0 ++ A :: Γ1, Δ0 ++ B :: Δ1).
        split. repeat rewrite app_assoc. apply ImpRRule_I. apply list_exch_LI. }
      { repeat rewrite <- app_assoc. exists (Γ2 ++ (x ++ A :: x0) ++ Γ4 ++ Γ3 ++ Γ6, Δ0 ++ B :: Δ1).
        split. assert (Γ2 ++ (x ++ A :: x0) ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ x) ++ A :: x0 ++ Γ4 ++ Γ3 ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert (Γ2 ++ x ++ x0 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ x) ++ x0 ++ Γ4 ++ Γ3 ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        apply ImpRRule_I.
        assert (Γ2 ++ Γ3 ++ Γ4 ++ x ++ A :: x0 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (x ++ A :: x0) ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply list_exch_LI. }
    * repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ (x0 ++ A :: x) ++ Γ3 ++ Γ6, Δ0 ++ B :: Δ1).
      split. assert (Γ2 ++ Γ5 ++ (x0 ++ A :: x) ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5 ++ x0) ++ A :: x ++ Γ3 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      assert (Γ2 ++ Γ5 ++ x0 ++ x ++ Γ3 ++ Γ6 = (Γ2 ++ Γ5 ++ x0) ++ x ++ Γ3 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      apply ImpRRule_I.
      assert (Γ2 ++ Γ3 ++ x0 ++ A :: x ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (x0 ++ A :: x) ++ Γ5 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply list_exch_LI.
  + repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ (x ++ A :: x0) ++ Γ6, Δ0 ++ B :: Δ1).
    split. assert (Γ2 ++ Γ5 ++ Γ4 ++ (x ++ A :: x0) ++ Γ6 = (Γ2 ++ Γ5 ++ Γ4 ++ x) ++ A :: x0 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ Γ5 ++ Γ4 ++ x ++ x0 ++ Γ6 = (Γ2 ++ Γ5 ++ Γ4 ++ x) ++ x0 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    apply ImpRRule_I.
    assert (Γ2 ++ x ++ A :: x0 ++ Γ4 ++ Γ5 ++ Γ6 = Γ2 ++ (x ++ A :: x0) ++ Γ4 ++ Γ5 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply list_exch_LI.
- repeat rewrite <- app_assoc. exists (Γ0 ++ A :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6, Δ0 ++ B :: Δ1).
  split. apply ImpRRule_I.
  assert (Γ0 ++ A :: x ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6 = (Γ0 ++ A :: x) ++ Γ3 ++ Γ4 ++ Γ5 ++ Γ6).
  repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
  assert (Γ0 ++ A :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = (Γ0 ++ A :: x) ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6).
  repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
Qed.


Lemma ImpR_app_list_exchR : forall s se ps,
  (@list_exch_R s se) ->
  (ImpRRule [ps] s) ->
  (existsT2 pse,
    (ImpRRule [pse] se) *
    (@list_exch_R ps pse)).
Proof.
intros s se ps exch. intro RA. inversion RA. inversion exch. subst.
inversion H. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
- destruct Δ3 ; destruct Δ4 ; destruct Δ5 ; simpl ; simpl in e0 ; simpl in exch ; subst ; try inversion e0 ; subst.
  + exists (Γ0 ++ A :: Γ1, Δ2 ++ B :: Δ1). split ; try assumption. apply list_exch_R_id.
  + exists (Γ0 ++ A :: Γ1, Δ2 ++ B :: Δ5 ++ Δ6). split ; try assumption. apply list_exch_R_id.
  + exists (Γ0 ++ A :: Γ1, Δ2 ++ B :: Δ4 ++ Δ6). split ; try assumption. apply list_exch_R_id.
  + exists (Γ0 ++ A :: Γ1, Δ2 ++ (m0 :: Δ5) ++ B :: Δ4 ++ Δ6). split.
    assert (Δ2 ++ (m0 :: Δ5) ++ B :: Δ4 ++ Δ6 = (Δ2 ++ m0 :: Δ5) ++ B :: Δ4 ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Δ2 ++ m0 :: Δ5 ++ A --> B :: Δ4 ++ Δ6 = (Δ2 ++ m0 :: Δ5) ++ A --> B :: Δ4 ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    apply ImpRRule_I. assert (Δ2 ++ B :: Δ4 ++ m0 :: Δ5 ++ Δ6 = Δ2 ++ [] ++ (B :: Δ4) ++ (m0 :: Δ5) ++ Δ6).
    reflexivity. rewrite H0. clear H0.
    assert (Δ2 ++ (m0 :: Δ5) ++ B :: Δ4 ++ Δ6 = Δ2 ++ (m0 :: Δ5) ++ (B :: Δ4) ++ [] ++ Δ6).
    reflexivity. rewrite H0. clear H0. apply list_exch_RI.
  + exists (Γ0 ++ A :: Γ1, Δ2 ++ B :: Δ3 ++ Δ6). split ; try assumption. apply list_exch_R_id.
  + exists (Γ0 ++ A :: Γ1, Δ2 ++ (m0 :: Δ5) ++ B :: Δ3 ++ Δ6). split.
    assert (Δ2 ++ m0 :: Δ5 ++ A --> B :: Δ3 ++ Δ6 = (Δ2 ++ m0 :: Δ5) ++ A --> B :: Δ3 ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Δ2 ++ (m0 :: Δ5) ++ B :: Δ3 ++ Δ6 = (Δ2 ++ m0 :: Δ5) ++ B :: Δ3 ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    apply ImpRRule_I. assert (Δ2 ++ B :: Δ3 ++ m0 :: Δ5 ++ Δ6 = Δ2 ++ (B :: Δ3) ++ [] ++ (m0 :: Δ5) ++ Δ6).
    reflexivity. rewrite H0. clear H0.
    assert (Δ2 ++ (m0 :: Δ5) ++ B :: Δ3 ++ Δ6 = Δ2 ++ (m0 :: Δ5) ++ [] ++ (B :: Δ3) ++ Δ6).
    reflexivity. rewrite H0. clear H0. apply list_exch_RI.
  + exists (Γ0 ++ A :: Γ1, (Δ2 ++ m0 :: Δ4) ++ B :: Δ3 ++ Δ6). split.
    assert (Δ2 ++ m0 :: Δ4 ++ A --> B :: Δ3 ++ Δ6 = (Δ2 ++ m0 :: Δ4) ++ A --> B :: Δ3 ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpRRule_I.
    assert (Δ2 ++ B :: Δ3 ++ m0 :: Δ4 ++ Δ6 = Δ2 ++ (B :: Δ3) ++ [] ++ (m0 :: Δ4) ++ Δ6).
    reflexivity. rewrite H0. clear H0.
    assert ((Δ2 ++ m0 :: Δ4) ++ B :: Δ3 ++ Δ6 = Δ2 ++ (m0 :: Δ4) ++ [] ++ (B :: Δ3) ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI.
  + exists (Γ0 ++ A :: Γ1, (Δ2 ++ m1 :: Δ5 ++ m0 :: Δ4) ++ B :: Δ3 ++ Δ6). split.
    assert (Δ2 ++ m1 :: Δ5 ++ m0 :: Δ4 ++ A --> B :: Δ3 ++ Δ6 = (Δ2 ++ m1 :: Δ5 ++ m0 :: Δ4) ++ A --> B :: Δ3 ++ Δ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpRRule_I.
    assert (Δ2 ++ B :: Δ3 ++ m0 :: Δ4 ++ m1 :: Δ5 ++ Δ6 = Δ2 ++ (B :: Δ3) ++ (m0 :: Δ4) ++ (m1 :: Δ5) ++ Δ6).
    reflexivity. rewrite H0. clear H0.
    assert ((Δ2 ++ m1 :: Δ5 ++ m0 :: Δ4) ++ B :: Δ3 ++ Δ6 = Δ2 ++ (m1 :: Δ5) ++ (m0 :: Δ4) ++ (B :: Δ3) ++ Δ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI.
- apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
  + destruct Δ4 ; destruct Δ5 ; simpl ; simpl in e0 ; simpl in exch ; subst ; try inversion e0 ; subst.
    * rewrite app_assoc. exists (Γ0 ++ A :: Γ1, (Δ2 ++ Δ3) ++ B :: Δ1). split ; try assumption. apply list_exch_R_id.
    * exists (Γ0 ++ A :: Γ1, Δ2 ++ B :: Δ5 ++ Δ3 ++ Δ6). split. apply ImpRRule_I.
      assert ((Δ2 ++ Δ3) ++ B :: Δ5 ++ Δ6 = Δ2 ++ Δ3 ++ [] ++ (B :: Δ5) ++ Δ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert (Δ2 ++ B :: Δ5 ++ Δ3 ++ Δ6 = Δ2 ++ (B :: Δ5) ++ [] ++ Δ3 ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI.
    * exists (Γ0 ++ A :: Γ1, Δ2 ++ B :: Δ4 ++ Δ3 ++ Δ6). split. apply ImpRRule_I.
      assert ((Δ2 ++ Δ3) ++ B :: Δ4 ++ Δ6 = Δ2 ++ Δ3 ++ [] ++ (B :: Δ4) ++ Δ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert (Δ2 ++ B :: Δ4 ++ Δ3 ++ Δ6 = Δ2 ++ (B :: Δ4) ++ [] ++ Δ3 ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI.
    * exists (Γ0 ++ A :: Γ1, (Δ2 ++ m0 :: Δ5) ++ B :: Δ4 ++ Δ3 ++ Δ6). split.
      assert (Δ2 ++ m0 :: Δ5 ++ A --> B :: Δ4 ++ Δ3 ++ Δ6 = (Δ2 ++ m0 :: Δ5) ++ A --> B :: Δ4 ++ Δ3 ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpRRule_I.
      assert ((Δ2 ++ Δ3) ++ B :: Δ4 ++ m0 :: Δ5 ++ Δ6 = Δ2 ++ Δ3 ++ (B :: Δ4) ++ (m0 :: Δ5) ++ Δ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert ((Δ2 ++ m0 :: Δ5) ++ B :: Δ4 ++ Δ3 ++ Δ6 = Δ2 ++ (m0 :: Δ5) ++ (B :: Δ4) ++ Δ3 ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI.
  + apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
    * destruct Δ5 ; simpl ; simpl in e0 ; simpl in exch ; subst ; try inversion e0 ; subst.
      { exists (Γ0 ++ A :: Γ1, (Δ2 ++ Δ4 ++ Δ3) ++ B :: Δ1). split.
        assert (Δ2 ++ Δ4 ++ Δ3 ++ A --> B :: Δ1 = (Δ2 ++ Δ4 ++ Δ3) ++ A --> B :: Δ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpRRule_I.
        assert ((Δ2 ++ Δ3 ++ Δ4) ++ B :: Δ1 = Δ2 ++ Δ3 ++ [] ++ Δ4 ++ B :: Δ1). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0.
        assert ((Δ2 ++ Δ4 ++ Δ3) ++ B :: Δ1 = Δ2 ++ Δ4 ++ [] ++ Δ3 ++ B :: Δ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI. }
      { exists (Γ0 ++ A :: Γ1, Δ2 ++ B :: Δ5 ++ Δ4 ++ Δ3 ++ Δ6). split. apply ImpRRule_I.
        assert ((Δ2 ++ Δ3 ++ Δ4) ++ B :: Δ5 ++ Δ6 = Δ2 ++ Δ3 ++ Δ4 ++ (B :: Δ5) ++ Δ6). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0.
        assert (Δ2 ++ B :: Δ5 ++ Δ4 ++ Δ3 ++ Δ6 = Δ2 ++ (B :: Δ5) ++ Δ4 ++ Δ3 ++ Δ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI. }
    * apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
      { exists (Γ0 ++ A :: Γ1, (Δ2 ++ Δ5 ++ Δ4 ++ Δ3) ++ B :: Δ1). split.
        assert (Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ A --> B :: Δ1 = (Δ2 ++ Δ5 ++ Δ4 ++ Δ3) ++ A --> B :: Δ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpRRule_I.
        repeat rewrite <- app_assoc. apply list_exch_RI. }
      { exists (Γ0 ++ A :: Γ1, (Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ x0) ++ B :: Δ1). split.
        assert (Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ x0 ++ A --> B :: Δ1 = (Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ x0) ++ A --> B :: Δ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpRRule_I.
        repeat rewrite <- app_assoc. apply list_exch_RI. }
      { destruct x0.
        - simpl in e0. subst. rewrite app_nil_r.
          exists (Γ0 ++ A :: Γ1, (Δ2 ++ x ++ Δ4 ++ Δ3) ++ B :: Δ1). split.
          assert (Δ2 ++ x ++ Δ4 ++ Δ3 ++ A --> B :: Δ1 = (Δ2 ++ x ++ Δ4 ++ Δ3) ++ A --> B :: Δ1).
          repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpRRule_I.
          repeat rewrite <- app_assoc. apply list_exch_RI.
        - inversion e0. subst.
          exists (Γ0 ++ A :: Γ1, (Δ2 ++ x) ++ B :: x0 ++ Δ4 ++ Δ3 ++ Δ6). split.
          assert (Δ2 ++ (x ++ A --> B :: x0) ++ Δ4 ++ Δ3 ++ Δ6 = (Δ2 ++ x) ++ A --> B :: x0 ++ Δ4 ++ Δ3 ++ Δ6).
          repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpRRule_I.
          assert ((Δ2 ++ Δ3 ++ Δ4 ++ x) ++ B :: x0 ++ Δ6 = Δ2 ++ Δ3 ++ Δ4 ++ (x ++ B :: x0) ++ Δ6).
          repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
          assert ((Δ2 ++ x) ++ B :: x0 ++ Δ4 ++ Δ3 ++ Δ6 = Δ2 ++ (x ++ B :: x0) ++ Δ4 ++ Δ3 ++ Δ6).
          repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
          apply list_exch_RI. }
    * destruct x ; destruct Δ5 ; simpl ; simpl in e0 ; simpl in exch ; subst ; try inversion e0 ; subst.
      { rewrite app_nil_r. exists (Γ0 ++ A :: Γ1, (Δ2 ++ x0 ++ Δ3) ++ B :: Δ1). split.
        assert (Δ2 ++ x0 ++ Δ3 ++ A --> B :: Δ1 = (Δ2 ++ x0 ++ Δ3) ++ A --> B :: Δ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpRRule_I.
        assert ((Δ2 ++ Δ3 ++ x0) ++ B :: Δ1 = Δ2 ++ Δ3 ++ [] ++ x0 ++ B :: Δ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert ((Δ2 ++ x0 ++ Δ3) ++ B :: Δ1 = Δ2 ++ x0 ++ [] ++ Δ3 ++ B :: Δ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI. }
      { rewrite app_nil_r. exists (Γ0 ++ A :: Γ1, Δ2 ++ B :: Δ5 ++ x0 ++ Δ3 ++ Δ6). split.
        apply ImpRRule_I.
        assert ((Δ2 ++ Δ3 ++ x0) ++ B :: Δ5 ++ Δ6 = Δ2 ++ Δ3 ++ x0 ++ (B :: Δ5) ++ Δ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert (Δ2 ++ B :: Δ5 ++ x0 ++ Δ3 ++ Δ6 = Δ2 ++ (B :: Δ5) ++ x0 ++ Δ3 ++ Δ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI. }
      { exists (Γ0 ++ A :: Γ1, (Δ2 ++ x0) ++ B :: x ++ Δ3 ++ Δ6). split.
        assert (Δ2 ++ (x0 ++ A --> B :: x) ++ Δ3 ++ Δ6 = (Δ2 ++ x0) ++ A --> B :: x ++ Δ3 ++ Δ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpRRule_I.
        assert ((Δ2 ++ Δ3 ++ x0) ++ B :: x ++ Δ6 = Δ2 ++ Δ3 ++ [] ++ (x0 ++ B :: x) ++ Δ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert ((Δ2 ++ x0) ++ B :: x ++ Δ3 ++ Δ6 = Δ2 ++ (x0 ++ B :: x) ++ [] ++ Δ3 ++ Δ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI. }
      { exists (Γ0 ++ A :: Γ1, (Δ2 ++ m0 :: Δ5 ++ x0) ++ B :: x ++ Δ3 ++ Δ6). split.
        assert (Δ2 ++ m0 :: Δ5 ++ (x0 ++ A --> B :: x) ++ Δ3 ++ Δ6 = (Δ2 ++ m0 :: Δ5 ++ x0) ++ A --> B :: x ++ Δ3 ++ Δ6).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0. apply ImpRRule_I.
        assert ((Δ2 ++ Δ3 ++ x0) ++ B :: x ++ m0 :: Δ5 ++ Δ6 = Δ2 ++ Δ3 ++ (x0 ++ B :: x) ++ (m0 :: Δ5) ++ Δ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert ((Δ2 ++ m0 :: Δ5 ++ x0) ++ B :: x ++ Δ3 ++ Δ6 = Δ2 ++ (m0 :: Δ5) ++ (x0 ++ B :: x) ++ Δ3 ++ Δ6).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        apply list_exch_RI. }
  + destruct x0 ; destruct Δ4 ; destruct Δ5 ; simpl ; simpl in e0 ; simpl in exch ; subst ; try inversion e0 ; subst.
    * rewrite app_nil_r. rewrite app_assoc. exists (Γ0 ++ A :: Γ1, (Δ2 ++ x) ++ B :: Δ1). split ; try assumption. apply list_exch_R_id.
    * rewrite app_nil_r. exists (Γ0 ++ A :: Γ1, Δ2 ++ B :: Δ5 ++ x ++ Δ6). split. apply ImpRRule_I.
      assert ((Δ2 ++ x) ++ B :: Δ5 ++ Δ6 = Δ2 ++ x ++ [] ++ (B :: Δ5) ++ Δ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert (Δ2 ++ B :: Δ5 ++ x ++ Δ6 = Δ2 ++ (B :: Δ5) ++ [] ++ x ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI.
    * rewrite app_nil_r. exists (Γ0 ++ A :: Γ1, Δ2 ++ B :: Δ4 ++ x ++ Δ6). split. apply ImpRRule_I.
      assert ((Δ2 ++ x) ++ B :: Δ4 ++ Δ6 = Δ2 ++ x ++ [] ++ (B :: Δ4) ++ Δ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert (Δ2 ++ B :: Δ4 ++ x ++ Δ6 = Δ2 ++ (B :: Δ4) ++ [] ++ x ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI.
    * rewrite app_nil_r. exists (Γ0 ++ A :: Γ1, (Δ2 ++ m0 :: Δ5) ++ B :: Δ4 ++ x ++ Δ6). split.
      assert (Δ2 ++ m0 :: Δ5 ++ A --> B :: Δ4 ++ x ++ Δ6 = (Δ2 ++ m0 :: Δ5) ++ A --> B :: Δ4 ++ x ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpRRule_I.
      assert ((Δ2 ++ x) ++ B :: Δ4 ++ m0 :: Δ5 ++ Δ6 = Δ2 ++ x ++ (B :: Δ4) ++ (m0 :: Δ5) ++ Δ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert ((Δ2 ++ m0 :: Δ5) ++ B :: Δ4 ++ x ++ Δ6 = Δ2 ++ (m0 :: Δ5) ++ (B :: Δ4) ++ x ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI.
    * exists (Γ0 ++ A :: Γ1, (Δ2 ++ x) ++ B :: x0 ++ Δ6). split.
      assert (Δ2 ++ (x ++ A --> B :: x0) ++ Δ6 = (Δ2 ++ x) ++ A --> B :: x0 ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpRRule_I.
      apply list_exch_R_id.
    * exists (Γ0 ++ A :: Γ1, (Δ2 ++ m0 :: Δ5 ++ x) ++ B :: x0 ++ Δ6). split.
      assert (Δ2 ++ m0 :: Δ5 ++ (x ++ A --> B :: x0) ++ Δ6 = (Δ2 ++ m0 :: Δ5 ++ x) ++ A --> B :: x0 ++ Δ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpRRule_I.
      assert ((Δ2 ++ x) ++ B :: x0 ++ m0 :: Δ5 ++ Δ6 = Δ2 ++ [] ++ (x ++ B :: x0) ++ (m0 :: Δ5) ++ Δ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert ((Δ2 ++ m0 :: Δ5 ++ x) ++ B :: x0 ++ Δ6 = Δ2 ++ (m0 :: Δ5) ++ (x ++ B :: x0) ++ [] ++ Δ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
      rewrite H0. clear H0. apply list_exch_RI.
    * exists (Γ0 ++ A :: Γ1, (Δ2 ++ m0 :: Δ4 ++ x) ++ B :: x0 ++ Δ6). split.
      assert (Δ2 ++ m0 :: Δ4 ++ (x ++ A --> B :: x0) ++ Δ6 = (Δ2 ++ m0 :: Δ4 ++ x) ++ A --> B :: x0 ++ Δ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpRRule_I.
      assert ((Δ2 ++ x) ++ B :: x0 ++ m0 :: Δ4 ++ Δ6 = Δ2 ++ [] ++ (x ++ B :: x0) ++ (m0 :: Δ4) ++ Δ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert ((Δ2 ++ m0 :: Δ4 ++ x) ++ B :: x0 ++ Δ6 = Δ2 ++ (m0 :: Δ4) ++ (x ++ B :: x0) ++ [] ++ Δ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
      rewrite H0. clear H0. apply list_exch_RI.
    * exists (Γ0 ++ A :: Γ1, (Δ2 ++ m1 :: Δ5 ++ m0 :: Δ4 ++ x) ++ B :: x0 ++ Δ6). split.
      assert (Δ2 ++ m1 :: Δ5 ++ m0 :: Δ4 ++ (x ++ A --> B :: x0) ++ Δ6 = (Δ2 ++ m1 :: Δ5 ++ m0 :: Δ4 ++ x) ++ A --> B :: x0 ++ Δ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpRRule_I.
      assert ((Δ2 ++ x) ++ B :: x0 ++ m0 :: Δ4 ++ m1 :: Δ5 ++ Δ6 = Δ2 ++ (x ++ B :: x0) ++ (m0 :: Δ4) ++ (m1 :: Δ5) ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      assert ((Δ2 ++ m1 :: Δ5 ++ m0 :: Δ4 ++ x) ++ B :: x0 ++ Δ6 = Δ2 ++ (m1 :: Δ5) ++ (m0 :: Δ4) ++ (x ++ B :: x0) ++ Δ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
      rewrite H0. clear H0. apply list_exch_RI.
- destruct x ; destruct Δ3 ; destruct Δ4 ; destruct Δ5 ; simpl ; simpl in e0 ; simpl in exch ;
  subst ; try inversion e0 ; subst.
  * rewrite app_nil_r. exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1). split ; try assumption.
    apply list_exch_R_id.
  * rewrite app_nil_r. exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ5 ++ Δ6). split ; try assumption.
    apply list_exch_R_id.
  * rewrite app_nil_r. exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ4 ++ Δ6). split ; try assumption.
    apply list_exch_R_id.
  * rewrite app_nil_r. exists (Γ0 ++ A :: Γ1, (Δ0 ++ m0 :: Δ5) ++ B :: Δ4 ++ Δ6). split.
    assert (Δ0 ++ m0 :: Δ5 ++ A --> B :: Δ4 ++ Δ6 = (Δ0 ++ m0 :: Δ5) ++ A --> B :: Δ4 ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpRRule_I.
    assert (Δ0 ++ B :: Δ4 ++ m0 :: Δ5 ++ Δ6 = Δ0 ++ [] ++ (B :: Δ4) ++ (m0 :: Δ5) ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert ((Δ0 ++ m0 :: Δ5) ++ B :: Δ4 ++ Δ6 = Δ0 ++ (m0 :: Δ5) ++ (B :: Δ4) ++ [] ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_RI.
  * rewrite app_nil_r. exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ3 ++ Δ6). split ; try assumption.
    apply list_exch_R_id.
  * rewrite app_nil_r. exists (Γ0 ++ A :: Γ1, (Δ0 ++ m0 :: Δ5) ++ B :: Δ3 ++ Δ6). split.
    assert (Δ0 ++ m0 :: Δ5 ++ A --> B :: Δ3 ++ Δ6 = (Δ0 ++ m0 :: Δ5) ++ A --> B :: Δ3 ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpRRule_I.
    assert (Δ0 ++ B :: Δ3 ++ m0 :: Δ5 ++ Δ6 = Δ0 ++ [] ++ (B :: Δ3) ++ (m0 :: Δ5) ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert ((Δ0 ++ m0 :: Δ5) ++ B :: Δ3 ++ Δ6 = Δ0 ++ (m0 :: Δ5) ++ (B :: Δ3) ++ [] ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_RI.
  * rewrite app_nil_r. exists (Γ0 ++ A :: Γ1, (Δ0 ++ m0 :: Δ4) ++ B :: Δ3 ++ Δ6). split.
    assert (Δ0 ++ m0 :: Δ4 ++ A --> B :: Δ3 ++ Δ6 = (Δ0 ++ m0 :: Δ4) ++ A --> B :: Δ3 ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpRRule_I.
    assert ((Δ0 ++ m0 :: Δ4) ++ B :: Δ3 ++ Δ6 = Δ0 ++ (m0 :: Δ4) ++ (B :: Δ3) ++ [] ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Δ0 ++ B :: Δ3 ++ m0 :: Δ4 ++ Δ6 = Δ0 ++ [] ++ (B :: Δ3) ++ (m0 :: Δ4) ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_RI.
  * rewrite app_nil_r. exists (Γ0 ++ A :: Γ1, (Δ0 ++ m1 :: Δ5 ++ m0 :: Δ4) ++ B :: Δ3 ++ Δ6). split.
    assert (Δ0 ++ m1 :: Δ5 ++ m0 :: Δ4 ++ A --> B :: Δ3 ++ Δ6 = (Δ0 ++ m1 :: Δ5 ++ m0 :: Δ4) ++ A --> B :: Δ3 ++ Δ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpRRule_I.
    assert (Δ0 ++ B :: Δ3 ++ m0 :: Δ4 ++ m1 :: Δ5 ++ Δ6 = Δ0 ++ (B :: Δ3) ++ (m0 :: Δ4) ++ (m1 :: Δ5) ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert ((Δ0 ++ m1 :: Δ5 ++ m0 :: Δ4) ++ B :: Δ3 ++ Δ6 = Δ0 ++ (m1 :: Δ5) ++ (m0 :: Δ4) ++ (B :: Δ3) ++ Δ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_RI.
  * exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: x ++ Δ6). split. repeat rewrite <- app_assoc. apply ImpRRule_I.
    apply list_exch_R_id.
  * exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: x ++ m0 :: Δ5 ++ Δ6). split. repeat rewrite <- app_assoc. apply ImpRRule_I.
    apply list_exch_R_id.
  * exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: x ++ m0 :: Δ4 ++ Δ6). split. repeat rewrite <- app_assoc. apply ImpRRule_I.
    apply list_exch_R_id.
  * exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: x ++ m1 :: Δ5 ++ m0 :: Δ4 ++ Δ6). split.
    repeat rewrite <- app_assoc. apply ImpRRule_I.
    assert (Δ0 ++ B :: x ++ m0 :: Δ4 ++ m1 :: Δ5 ++ Δ6 = (Δ0 ++ B :: x) ++ (m0 :: Δ4) ++ [] ++ (m1 :: Δ5) ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Δ0 ++ B :: x ++ m1 :: Δ5 ++ m0 :: Δ4 ++ Δ6 = (Δ0 ++ B :: x) ++ (m1 :: Δ5) ++ [] ++ (m0 :: Δ4) ++ Δ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_RI.
  * exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: x ++ m0 :: Δ3 ++ Δ6). split. repeat rewrite <- app_assoc. apply ImpRRule_I.
    apply list_exch_R_id.
  * exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: x ++ m1 :: Δ5 ++ m0 :: Δ3 ++ Δ6). split.
    repeat rewrite <- app_assoc. apply ImpRRule_I.
    assert (Δ0 ++ B :: x ++ m0 :: Δ3 ++ m1 :: Δ5 ++ Δ6 = (Δ0 ++ B :: x) ++ (m0 :: Δ3) ++ [] ++ (m1 :: Δ5) ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Δ0 ++ B :: x ++ m1 :: Δ5 ++ m0 :: Δ3 ++ Δ6 = (Δ0 ++ B :: x) ++ (m1 :: Δ5) ++ [] ++ (m0 :: Δ3) ++ Δ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_RI.
  * exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: x ++ m1 :: Δ4 ++ m0 :: Δ3 ++ Δ6). split.
    repeat rewrite <- app_assoc. apply ImpRRule_I.
    assert (Δ0 ++ B :: x ++ m0 :: Δ3 ++ m1 :: Δ4 ++ Δ6 = (Δ0 ++ B :: x) ++ (m0 :: Δ3) ++ [] ++ (m1 :: Δ4) ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Δ0 ++ B :: x ++ m1 :: Δ4 ++ m0 :: Δ3 ++ Δ6 = (Δ0 ++ B :: x) ++ (m1 :: Δ4) ++ [] ++ (m0 :: Δ3) ++ Δ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_RI.
  * exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: x ++ m2 :: Δ5 ++ m1 :: Δ4 ++ m0 :: Δ3 ++ Δ6). split.
    repeat rewrite <- app_assoc. apply ImpRRule_I.
    assert (Δ0 ++ B :: x ++ m0 :: Δ3 ++ m1 :: Δ4 ++ m2 :: Δ5 ++ Δ6 = (Δ0 ++ B :: x) ++ (m0 :: Δ3) ++ (m1 :: Δ4) ++ (m2 :: Δ5) ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Δ0 ++ B :: x ++ m2 :: Δ5 ++ m1 :: Δ4 ++ m0 :: Δ3 ++ Δ6 = (Δ0 ++ B :: x) ++ (m2 :: Δ5) ++ (m1 :: Δ4) ++ (m0 :: Δ3) ++ Δ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_RI.
Qed.
