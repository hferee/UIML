Require Import List.
Export ListNotations.
Require Import Lia.
Require Import PeanoNat.

Require Import KS_calc.
Require Import KS_exch_prelims.

Lemma ImpL_app_list_exchL : forall s se ps1 ps2,
  (@list_exch_L s se) ->
  (ImpLRule [ps1;ps2] s) ->
  (existsT2 pse1 pse2,
    (ImpLRule [pse1;pse2] se) *
    (@list_exch_L ps1 pse1) *
    (@list_exch_L ps2 pse2)).
Proof.
intros s se ps1 ps2 exch. intro RA. inversion RA. inversion exch. subst.
inversion H. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
- destruct Γ3 ; destruct Γ4 ; destruct Γ5 ; simpl ; simpl in e0 ; simpl in exch ; subst ; try inversion e0 ; subst.
  + exists (Γ2 ++ Γ1, Δ0 ++ A :: Δ1). exists (Γ2 ++ B :: Γ1, Δ0 ++ Δ1). split. split ; try assumption.
    apply list_exch_L_id. apply list_exch_L_id.
  + exists (Γ2 ++ Γ5 ++ Γ6, Δ0 ++ A :: Δ1). exists (Γ2 ++ B :: Γ5 ++ Γ6, Δ0 ++ Δ1). split. split ; try assumption.
    apply list_exch_L_id. apply list_exch_L_id.
  + exists (Γ2 ++ Γ4 ++ Γ6, Δ0 ++ A :: Δ1). exists (Γ2 ++ B :: Γ4 ++ Γ6, Δ0 ++ Δ1). split. split ; try assumption.
    apply list_exch_L_id. apply list_exch_L_id.
  + exists (Γ2 ++ (m0 :: Γ5) ++ Γ4 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ2 ++ (m0 :: Γ5) ++ B :: Γ4 ++ Γ6, Δ0 ++ Δ1). split. split.
    assert (Γ2 ++ (m0 :: Γ5) ++ B :: Γ4 ++ Γ6 = (Γ2 ++ m0 :: Γ5) ++ B :: Γ4 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ m0 :: Γ5 ++ A --> B :: Γ4 ++ Γ6 = (Γ2 ++ m0 :: Γ5) ++ A --> B :: Γ4 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ (m0 :: Γ5) ++ Γ4 ++ Γ6 = (Γ2 ++ m0 :: Γ5) ++ Γ4 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    apply ImpLRule_I.
    assert (Γ2 ++ Γ4 ++ m0 :: Γ5 ++ Γ6 = Γ2 ++ [] ++ Γ4 ++ (m0 :: Γ5) ++ Γ6).
    reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ (m0 :: Γ5) ++ Γ4 ++ Γ6 = Γ2 ++ (m0 :: Γ5) ++ Γ4 ++ [] ++ Γ6).
    reflexivity. rewrite H0. clear H0. apply list_exch_LI.
    assert (Γ2 ++ B :: Γ4 ++ m0 :: Γ5 ++ Γ6 = Γ2 ++ [] ++ (B :: Γ4) ++ (m0 :: Γ5) ++ Γ6).
    reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ (m0 :: Γ5) ++ B :: Γ4 ++ Γ6 = Γ2 ++ (m0 :: Γ5) ++ (B :: Γ4) ++ [] ++ Γ6).
    reflexivity. rewrite H0. clear H0. apply list_exch_LI.
  + exists (Γ2 ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1). exists (Γ2 ++ B :: Γ3 ++ Γ6, Δ0 ++ Δ1). split. split ; try assumption.
    apply list_exch_L_id. apply list_exch_L_id.
  + exists (Γ2 ++ (m0 :: Γ5) ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ2 ++ (m0 :: Γ5) ++ B :: Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
    assert (Γ2 ++ m0 :: Γ5 ++ A --> B :: Γ3 ++ Γ6 = (Γ2 ++ m0 :: Γ5) ++ A --> B :: Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ (m0 :: Γ5) ++ B :: Γ3 ++ Γ6 = (Γ2 ++ m0 :: Γ5) ++ B :: Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ (m0 :: Γ5) ++ Γ3 ++ Γ6 = (Γ2 ++ m0 :: Γ5) ++ Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    apply ImpLRule_I.
    assert (Γ2 ++ Γ3 ++ m0 :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ [] ++ (m0 :: Γ5) ++ Γ6).
    reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ (m0 :: Γ5) ++ Γ3 ++ Γ6 = Γ2 ++ (m0 :: Γ5) ++ [] ++ Γ3 ++ Γ6).
    reflexivity. rewrite H0. clear H0. apply list_exch_LI.
    assert (Γ2 ++ B :: Γ3 ++ m0 :: Γ5 ++ Γ6 = Γ2 ++ (B :: Γ3) ++ [] ++ (m0 :: Γ5) ++ Γ6).
    reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ (m0 :: Γ5) ++ B :: Γ3 ++ Γ6 = Γ2 ++ (m0 :: Γ5) ++ [] ++ (B :: Γ3) ++ Γ6).
    reflexivity. rewrite H0. clear H0. apply list_exch_LI.
  + exists (Γ2 ++ m0 :: Γ4 ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ2 ++ m0 :: Γ4 ++ B :: Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
    assert (Γ2 ++ m0 :: Γ4 ++ A --> B :: Γ3 ++ Γ6 = (Γ2 ++ m0 :: Γ4) ++ A --> B :: Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ m0 :: Γ4 ++ B :: Γ3 ++ Γ6 = (Γ2 ++ m0 :: Γ4) ++ B :: Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ m0 :: Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ m0 :: Γ4) ++ Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
    assert (Γ2 ++ Γ3 ++ m0 :: Γ4 ++ Γ6 = Γ2 ++ Γ3 ++ [] ++ (m0 :: Γ4) ++ Γ6).
    reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ m0 :: Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (m0 :: Γ4) ++ [] ++ Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
    assert (Γ2 ++ B :: Γ3 ++ m0 :: Γ4 ++ Γ6 = Γ2 ++ (B :: Γ3) ++ [] ++ (m0 :: Γ4) ++ Γ6).
    reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ m0 :: Γ4 ++ B :: Γ3 ++ Γ6 = Γ2 ++ (m0 :: Γ4) ++ [] ++ (B :: Γ3) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
  + exists (Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ B :: Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
    assert (Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ A --> B :: Γ3 ++ Γ6 = (Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4) ++ A --> B :: Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ B :: Γ3 ++ Γ6 = (Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4) ++ B :: Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4) ++ Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    apply ImpLRule_I.
    assert (Γ2 ++ Γ3 ++ m0 :: Γ4 ++ m1 :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (m0 :: Γ4) ++ (m1 :: Γ5) ++ Γ6).
    reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (m1 :: Γ5) ++ (m0 :: Γ4) ++ Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
    assert (Γ2 ++ B :: Γ3 ++ m0 :: Γ4 ++ m1 :: Γ5 ++ Γ6 = Γ2 ++ (B :: Γ3) ++ (m0 :: Γ4) ++ (m1 :: Γ5) ++ Γ6).
    reflexivity. rewrite H0. clear H0.
    assert (Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ B :: Γ3 ++ Γ6 = Γ2 ++ (m1 :: Γ5) ++ (m0 :: Γ4) ++ (B :: Γ3) ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
- apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
  + destruct Γ4 ; destruct Γ5 ; simpl ; simpl in e0 ; simpl in exch ; subst ; try inversion e0 ; subst.
    * rewrite app_assoc. exists ((Γ2 ++ Γ3) ++ Γ1, Δ0 ++ A :: Δ1).
      exists ((Γ2 ++ Γ3) ++ B :: Γ1, Δ0 ++ Δ1). split. split ; try assumption. apply list_exch_L_id.
      apply list_exch_L_id.
    * exists (Γ2 ++ Γ5 ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
      exists (Γ2 ++ B :: Γ5 ++ Γ3 ++ Γ6, Δ0 ++ Δ1). split. split. apply ImpLRule_I.
      assert ((Γ2 ++ Γ3) ++ Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ [] ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert (Γ2 ++ Γ5 ++ Γ3 ++ Γ6 = Γ2 ++ Γ5 ++ [] ++ Γ3 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
      assert ((Γ2 ++ Γ3) ++ B :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ [] ++ (B :: Γ5) ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert (Γ2 ++ B :: Γ5 ++ Γ3 ++ Γ6 = Γ2 ++ (B :: Γ5) ++ [] ++ Γ3 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
    * exists (Γ2 ++ Γ4 ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
      exists (Γ2 ++ B :: Γ4 ++ Γ3 ++ Γ6, Δ0 ++ Δ1). split. split. apply ImpLRule_I.
      assert ((Γ2 ++ Γ3) ++ Γ4 ++ Γ6 = Γ2 ++ Γ3 ++ [] ++ Γ4 ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert (Γ2 ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ Γ4 ++ [] ++ Γ3 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
      assert ((Γ2 ++ Γ3) ++ B :: Γ4 ++ Γ6 = Γ2 ++ Γ3 ++ [] ++ (B :: Γ4) ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert (Γ2 ++ B :: Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (B :: Γ4) ++ [] ++ Γ3 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
    * exists ((Γ2 ++ m0 :: Γ5) ++ Γ4 ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
      exists ((Γ2 ++ m0 :: Γ5) ++ B :: Γ4 ++ Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
      assert (Γ2 ++ m0 :: Γ5 ++ A --> B :: Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ m0 :: Γ5) ++ A --> B :: Γ4 ++ Γ3 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpLRule_I.
      assert ((Γ2 ++ Γ3) ++ Γ4 ++ m0 :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (m0 :: Γ5) ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert ((Γ2 ++ m0 :: Γ5) ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (m0 :: Γ5) ++ Γ4 ++ Γ3 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
      assert ((Γ2 ++ Γ3) ++ B :: Γ4 ++ m0 :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (B :: Γ4) ++ (m0 :: Γ5) ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert ((Γ2 ++ m0 :: Γ5) ++ B :: Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (m0 :: Γ5) ++ (B :: Γ4) ++ Γ3 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
  + apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
    * destruct Γ5 ; simpl ; simpl in e0 ; simpl in exch ; subst ; try inversion e0 ; subst.
      { exists ((Γ2 ++ Γ4 ++ Γ3) ++ Γ1, Δ0 ++ A :: Δ1).
        exists ((Γ2 ++ Γ4 ++ Γ3) ++ B :: Γ1, Δ0 ++ Δ1). split. split.
        assert (Γ2 ++ Γ4 ++ Γ3 ++ A --> B :: Γ1 = (Γ2 ++ Γ4 ++ Γ3) ++ A --> B :: Γ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpLRule_I.
        assert ((Γ2 ++ Γ3 ++ Γ4) ++ Γ1 = Γ2 ++ Γ3 ++ [] ++ Γ4 ++ Γ1). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0.
        assert ((Γ2 ++ Γ4 ++ Γ3) ++ Γ1 = Γ2 ++ Γ4 ++ [] ++ Γ3 ++ Γ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
        assert ((Γ2 ++ Γ3 ++ Γ4) ++ B :: Γ1 = Γ2 ++ Γ3 ++ [] ++ Γ4 ++ B :: Γ1). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0.
        assert ((Γ2 ++ Γ4 ++ Γ3) ++ B :: Γ1 = Γ2 ++ Γ4 ++ [] ++ Γ3 ++ B :: Γ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI. }
      { exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
        exists (Γ2 ++ B :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6, Δ0 ++ Δ1). split. split. apply ImpLRule_I.
        repeat rewrite <- app_assoc. apply list_exch_LI.
        assert ((Γ2 ++ Γ3 ++ Γ4) ++ B :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (B :: Γ5) ++ Γ6). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0.
        assert (Γ2 ++ B :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (B :: Γ5) ++ Γ4 ++ Γ3 ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI. }
    * apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
      { exists ((Γ2 ++ Γ5 ++ Γ4 ++ Γ3) ++ Γ1, Δ0 ++ A :: Δ1).
        exists ((Γ2 ++ Γ5 ++ Γ4 ++ Γ3) ++ B :: Γ1, Δ0 ++ Δ1). split. split.
        assert (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ A --> B :: Γ1 = (Γ2 ++ Γ5 ++ Γ4 ++ Γ3) ++ A --> B :: Γ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpLRule_I.
        repeat rewrite <- app_assoc. apply list_exch_LI. repeat rewrite <- app_assoc. apply list_exch_LI. }
      { exists ((Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x0) ++ Γ1, Δ0 ++ A :: Δ1).
        exists ((Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x0) ++ B :: Γ1, Δ0 ++ Δ1). split. split.
        assert (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x0 ++ A --> B :: Γ1 = (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x0) ++ A --> B :: Γ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpLRule_I.
        repeat rewrite <- app_assoc. apply list_exch_LI. repeat rewrite <- app_assoc. apply list_exch_LI. }
      { destruct x0.
        - simpl in e0. subst. rewrite app_nil_r.
          exists ((Γ2 ++ x ++ Γ4 ++ Γ3) ++ Γ1, Δ0 ++ A :: Δ1).
          exists ((Γ2 ++ x ++ Γ4 ++ Γ3) ++ B :: Γ1, Δ0 ++ Δ1). split. split.
          assert (Γ2 ++ x ++ Γ4 ++ Γ3 ++ A --> B :: Γ1 = (Γ2 ++ x ++ Γ4 ++ Γ3) ++ A --> B :: Γ1).
          repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
          repeat rewrite <- app_assoc. apply list_exch_LI. repeat rewrite <- app_assoc. apply list_exch_LI.
        - inversion e0. subst.
          exists ((Γ2 ++ x) ++ x0 ++ Γ4 ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
          exists ((Γ2 ++ x) ++ B :: x0 ++ Γ4 ++ Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
          assert (Γ2 ++ (x ++ A --> B :: x0) ++ Γ4 ++ Γ3 ++ Γ6 = (Γ2 ++ x) ++ A --> B :: x0 ++ Γ4 ++ Γ3 ++ Γ6).
          repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
          assert ((Γ2 ++ Γ3 ++ Γ4 ++ x) ++ x0 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (x ++ x0) ++ Γ6).
          repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
          assert ((Γ2 ++ x) ++ x0 ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (x ++ x0) ++ Γ4 ++ Γ3 ++ Γ6).
          repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
          apply list_exch_LI.
          assert ((Γ2 ++ Γ3 ++ Γ4 ++ x) ++ B :: x0 ++ Γ6 = Γ2 ++ Γ3 ++ Γ4 ++ (x ++ B :: x0) ++ Γ6).
          repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
          assert ((Γ2 ++ x) ++ B :: x0 ++ Γ4 ++ Γ3 ++ Γ6 = Γ2 ++ (x ++ B :: x0) ++ Γ4 ++ Γ3 ++ Γ6).
          repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
          apply list_exch_LI. }
    * destruct x ; destruct Γ5 ; simpl ; simpl in e0 ; simpl in exch ; subst ; try inversion e0 ; subst.
      { rewrite app_nil_r. exists ((Γ2 ++ x0 ++ Γ3) ++ Γ1, Δ0 ++ A :: Δ1).
        exists ((Γ2 ++ x0 ++ Γ3) ++ B :: Γ1, Δ0 ++ Δ1). split. split.
        assert (Γ2 ++ x0 ++ Γ3 ++ A --> B :: Γ1 = (Γ2 ++ x0 ++ Γ3) ++ A --> B :: Γ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
        assert ((Γ2 ++ Γ3 ++ x0) ++ Γ1 = Γ2 ++ Γ3 ++ [] ++ x0 ++ Γ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert ((Γ2 ++ x0 ++ Γ3) ++ Γ1 = Γ2 ++ x0 ++ [] ++ Γ3 ++ Γ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
        assert ((Γ2 ++ Γ3 ++ x0) ++ B :: Γ1 = Γ2 ++ Γ3 ++ [] ++ x0 ++ B :: Γ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert ((Γ2 ++ x0 ++ Γ3) ++ B :: Γ1 = Γ2 ++ x0 ++ [] ++ Γ3 ++ B :: Γ1).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI. }
      { rewrite app_nil_r. exists (Γ2 ++ Γ5 ++ x0 ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
        exists (Γ2 ++ B :: Γ5 ++ x0 ++ Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
        apply ImpLRule_I. repeat rewrite <- app_assoc. apply list_exch_LI.
        assert ((Γ2 ++ Γ3 ++ x0) ++ B :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ x0 ++ (B :: Γ5) ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert (Γ2 ++ B :: Γ5 ++ x0 ++ Γ3 ++ Γ6 = Γ2 ++ (B :: Γ5) ++ x0 ++ Γ3 ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI. }
      { exists ((Γ2 ++ x0) ++ x ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
        exists ((Γ2 ++ x0) ++ B :: x ++ Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
        assert (Γ2 ++ (x0 ++ A --> B :: x) ++ Γ3 ++ Γ6 = (Γ2 ++ x0) ++ A --> B :: x ++ Γ3 ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
        assert ((Γ2 ++ Γ3 ++ x0) ++ x ++ Γ6 = Γ2 ++ Γ3 ++ [] ++ (x0 ++ x) ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert ((Γ2 ++ x0) ++ x ++ Γ3 ++ Γ6 = Γ2 ++ (x0 ++ x) ++ [] ++ Γ3 ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
        assert ((Γ2 ++ Γ3 ++ x0) ++ B :: x ++ Γ6 = Γ2 ++ Γ3 ++ [] ++ (x0 ++ B :: x) ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert ((Γ2 ++ x0) ++ B :: x ++ Γ3 ++ Γ6 = Γ2 ++ (x0 ++ B :: x) ++ [] ++ Γ3 ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI. }
      { exists ((Γ2 ++ m0 :: Γ5 ++ x0) ++ x ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
        exists ((Γ2 ++ m0 :: Γ5 ++ x0) ++ B :: x ++ Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
        assert (Γ2 ++ m0 :: Γ5 ++ (x0 ++ A --> B :: x) ++ Γ3 ++ Γ6 = (Γ2 ++ m0 :: Γ5 ++ x0) ++ A --> B :: x ++ Γ3 ++ Γ6).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
        assert ((Γ2 ++ Γ3 ++ x0) ++ x ++ m0 :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (x0 ++ x) ++ (m0 :: Γ5) ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert ((Γ2 ++ m0 :: Γ5 ++ x0) ++ x ++ Γ3 ++ Γ6 = Γ2 ++ (m0 :: Γ5) ++ (x0 ++ x) ++ Γ3 ++ Γ6).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        apply list_exch_LI.
        assert ((Γ2 ++ Γ3 ++ x0) ++ B :: x ++ m0 :: Γ5 ++ Γ6 = Γ2 ++ Γ3 ++ (x0 ++ B :: x) ++ (m0 :: Γ5) ++ Γ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert ((Γ2 ++ m0 :: Γ5 ++ x0) ++ B :: x ++ Γ3 ++ Γ6 = Γ2 ++ (m0 :: Γ5) ++ (x0 ++ B :: x) ++ Γ3 ++ Γ6).
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        apply list_exch_LI. }
  + destruct x0 ; destruct Γ4 ; destruct Γ5 ; simpl ; simpl in e0 ; simpl in exch ; subst ; try inversion e0 ; subst.
    * rewrite app_nil_r. rewrite app_assoc. exists ((Γ2 ++ x) ++ Γ1, Δ0 ++ A :: Δ1).
      exists ((Γ2 ++ x) ++ B :: Γ1, Δ0 ++ Δ1). split. split ; try assumption. apply list_exch_L_id. apply list_exch_L_id.
    * rewrite app_nil_r. exists (Γ2 ++ Γ5 ++ x ++ Γ6, Δ0 ++ A :: Δ1).
      exists (Γ2 ++ B :: Γ5 ++ x ++ Γ6, Δ0 ++ Δ1). split. split. apply ImpLRule_I.
      assert ((Γ2 ++ x) ++ Γ5 ++ Γ6 = Γ2 ++ x ++ [] ++ Γ5 ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert (Γ2 ++ Γ5 ++ x ++ Γ6 = Γ2 ++ Γ5 ++ [] ++ x ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
      assert ((Γ2 ++ x) ++ B :: Γ5 ++ Γ6 = Γ2 ++ x ++ [] ++ (B :: Γ5) ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert (Γ2 ++ B :: Γ5 ++ x ++ Γ6 = Γ2 ++ (B :: Γ5) ++ [] ++ x ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
    * rewrite app_nil_r. exists (Γ2 ++ Γ4 ++ x ++ Γ6, Δ0 ++ A :: Δ1).
      exists (Γ2 ++ B :: Γ4 ++ x ++ Γ6, Δ0 ++ Δ1). split. split. apply ImpLRule_I.
      assert ((Γ2 ++ x) ++ Γ4 ++ Γ6 = Γ2 ++ x ++ [] ++ Γ4 ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert (Γ2 ++ Γ4 ++ x ++ Γ6 = Γ2 ++ Γ4 ++ [] ++ x ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
      assert ((Γ2 ++ x) ++ B :: Γ4 ++ Γ6 = Γ2 ++ x ++ [] ++ (B :: Γ4) ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert (Γ2 ++ B :: Γ4 ++ x ++ Γ6 = Γ2 ++ (B :: Γ4) ++ [] ++ x ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
    * rewrite app_nil_r. exists ((Γ2 ++ m0 :: Γ5) ++ Γ4 ++ x ++ Γ6, Δ0 ++ A :: Δ1).
      exists ((Γ2 ++ m0 :: Γ5) ++ B :: Γ4 ++ x ++ Γ6, Δ0 ++ Δ1). split. split.
      assert (Γ2 ++ m0 :: Γ5 ++ A --> B :: Γ4 ++ x ++ Γ6 = (Γ2 ++ m0 :: Γ5) ++ A --> B :: Γ4 ++ x ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpLRule_I.
      assert ((Γ2 ++ x) ++ Γ4 ++ m0 :: Γ5 ++ Γ6 = Γ2 ++ x ++ Γ4 ++ (m0 :: Γ5) ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert ((Γ2 ++ m0 :: Γ5) ++ Γ4 ++ x ++ Γ6 = Γ2 ++ (m0 :: Γ5) ++ Γ4 ++ x ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
      assert ((Γ2 ++ x) ++ B :: Γ4 ++ m0 :: Γ5 ++ Γ6 = Γ2 ++ x ++ (B :: Γ4) ++ (m0 :: Γ5) ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert ((Γ2 ++ m0 :: Γ5) ++ B :: Γ4 ++ x ++ Γ6 = Γ2 ++ (m0 :: Γ5) ++ (B :: Γ4) ++ x ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_LI.
    * exists ((Γ2 ++ x) ++ x0 ++ Γ6, Δ0 ++ A :: Δ1).
      exists ((Γ2 ++ x) ++ B :: x0 ++ Γ6, Δ0 ++ Δ1). split. split.
      assert (Γ2 ++ (x ++ A --> B :: x0) ++ Γ6 = (Γ2 ++ x) ++ A --> B :: x0 ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpLRule_I.
      apply list_exch_L_id. apply list_exch_L_id.
    * exists ((Γ2 ++ m0 :: Γ5 ++ x) ++ x0 ++ Γ6, Δ0 ++ A :: Δ1).
      exists ((Γ2 ++ m0 :: Γ5 ++ x) ++ B :: x0 ++ Γ6, Δ0 ++ Δ1). split. split.
      assert (Γ2 ++ m0 :: Γ5 ++ (x ++ A --> B :: x0) ++ Γ6 = (Γ2 ++ m0 :: Γ5 ++ x) ++ A --> B :: x0 ++ Γ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpLRule_I.
      assert ((Γ2 ++ x) ++ x0 ++ m0 :: Γ5 ++ Γ6 = Γ2 ++ [] ++ (x ++ x0) ++ (m0 :: Γ5) ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert ((Γ2 ++ m0 :: Γ5 ++ x) ++ x0 ++ Γ6 = Γ2 ++ (m0 :: Γ5) ++ (x ++ x0) ++ [] ++ Γ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
      rewrite H0. clear H0. apply list_exch_LI.
      assert ((Γ2 ++ x) ++ B :: x0 ++ m0 :: Γ5 ++ Γ6 = Γ2 ++ [] ++ (x ++ B :: x0) ++ (m0 :: Γ5) ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert ((Γ2 ++ m0 :: Γ5 ++ x) ++ B :: x0 ++ Γ6 = Γ2 ++ (m0 :: Γ5) ++ (x ++ B :: x0) ++ [] ++ Γ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
      rewrite H0. clear H0. apply list_exch_LI.
    * exists ((Γ2 ++ m0 :: Γ4 ++ x) ++ x0 ++ Γ6, Δ0 ++ A :: Δ1).
      exists ((Γ2 ++ m0 :: Γ4 ++ x) ++ B :: x0 ++ Γ6, Δ0 ++ Δ1). split. split.
      assert (Γ2 ++ m0 :: Γ4 ++ (x ++ A --> B :: x0) ++ Γ6 = (Γ2 ++ m0 :: Γ4 ++ x) ++ A --> B :: x0 ++ Γ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpLRule_I.
      assert ((Γ2 ++ x) ++ x0 ++ m0 :: Γ4 ++ Γ6 = Γ2 ++ [] ++ (x ++ x0) ++ (m0 :: Γ4) ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert ((Γ2 ++ m0 :: Γ4 ++ x) ++ x0 ++ Γ6 = Γ2 ++ (m0 :: Γ4) ++ (x ++ x0) ++ [] ++ Γ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
      rewrite H0. clear H0. apply list_exch_LI.
      assert ((Γ2 ++ x) ++ B :: x0 ++ m0 :: Γ4 ++ Γ6 = Γ2 ++ [] ++ (x ++ B :: x0) ++ (m0 :: Γ4) ++ Γ6). repeat rewrite <- app_assoc.
      reflexivity. rewrite H0. clear H0.
      assert ((Γ2 ++ m0 :: Γ4 ++ x) ++ B :: x0 ++ Γ6 = Γ2 ++ (m0 :: Γ4) ++ (x ++ B :: x0) ++ [] ++ Γ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
      rewrite H0. clear H0. apply list_exch_LI.
    * exists ((Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ x) ++ x0 ++ Γ6, Δ0 ++ A :: Δ1).
      exists ((Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ x) ++ B :: x0 ++ Γ6, Δ0 ++ Δ1). split. split.
      assert (Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ (x ++ A --> B :: x0) ++ Γ6 = (Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ x) ++ A --> B :: x0 ++ Γ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpLRule_I.
      assert ((Γ2 ++ x) ++ x0 ++ m0 :: Γ4 ++ m1 :: Γ5 ++ Γ6 = Γ2 ++ (x ++ x0) ++ (m0 :: Γ4) ++ (m1 :: Γ5) ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      assert ((Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ x) ++ x0 ++ Γ6 = Γ2 ++ (m1 :: Γ5) ++ (m0 :: Γ4) ++ (x ++ x0) ++ Γ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
      rewrite H0. clear H0. apply list_exch_LI.
      assert ((Γ2 ++ x) ++ B :: x0 ++ m0 :: Γ4 ++ m1 :: Γ5 ++ Γ6 = Γ2 ++ (x ++ B :: x0) ++ (m0 :: Γ4) ++ (m1 :: Γ5) ++ Γ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      assert ((Γ2 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ x) ++ B :: x0 ++ Γ6 = Γ2 ++ (m1 :: Γ5) ++ (m0 :: Γ4) ++ (x ++ B :: x0) ++ Γ6).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
      rewrite H0. clear H0. apply list_exch_LI.
- destruct x ; destruct Γ3 ; destruct Γ4 ; destruct Γ5 ; simpl ; simpl in e0 ; simpl in exch ;
  subst ; try inversion e0 ; subst.
  * rewrite app_nil_r. exists (Γ0 ++ Γ1, Δ0 ++ A :: Δ1).
    exists (Γ0 ++ B :: Γ1, Δ0 ++ Δ1). split. split ; try assumption.
    apply list_exch_L_id. apply list_exch_L_id.
  * rewrite app_nil_r. exists (Γ0 ++ Γ5 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ0 ++ B :: Γ5 ++ Γ6, Δ0 ++ Δ1). split. split ; try assumption.
    apply list_exch_L_id. apply list_exch_L_id.
  * rewrite app_nil_r. exists (Γ0 ++ Γ4 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ0 ++ B :: Γ4 ++ Γ6, Δ0 ++ Δ1). split. split ; try assumption.
    apply list_exch_L_id. apply list_exch_L_id.
  * rewrite app_nil_r. exists ((Γ0 ++ m0 :: Γ5) ++ Γ4 ++ Γ6, Δ0 ++ A :: Δ1).
    exists ((Γ0 ++ m0 :: Γ5) ++ B :: Γ4 ++ Γ6, Δ0 ++ Δ1). split. split.
    assert (Γ0 ++ m0 :: Γ5 ++ A --> B :: Γ4 ++ Γ6 = (Γ0 ++ m0 :: Γ5) ++ A --> B :: Γ4 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpLRule_I.
    assert (Γ0 ++ Γ4 ++ m0 :: Γ5 ++ Γ6 = Γ0 ++ [] ++ Γ4 ++ (m0 :: Γ5) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert ((Γ0 ++ m0 :: Γ5) ++ Γ4 ++ Γ6 = Γ0 ++ (m0 :: Γ5) ++ Γ4 ++ [] ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
    assert (Γ0 ++ B :: Γ4 ++ m0 :: Γ5 ++ Γ6 = Γ0 ++ [] ++ (B :: Γ4) ++ (m0 :: Γ5) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert ((Γ0 ++ m0 :: Γ5) ++ B :: Γ4 ++ Γ6 = Γ0 ++ (m0 :: Γ5) ++ (B :: Γ4) ++ [] ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
  * rewrite app_nil_r. exists (Γ0 ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ0 ++ B :: Γ3 ++ Γ6, Δ0 ++ Δ1). split.  split ; try assumption.
    apply list_exch_L_id. apply list_exch_L_id.
  * rewrite app_nil_r. exists ((Γ0 ++ m0 :: Γ5) ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
    exists ((Γ0 ++ m0 :: Γ5) ++ B :: Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
    assert (Γ0 ++ m0 :: Γ5 ++ A --> B :: Γ3 ++ Γ6 = (Γ0 ++ m0 :: Γ5) ++ A --> B :: Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpLRule_I.
    assert (Γ0 ++ Γ3 ++ m0 :: Γ5 ++ Γ6 = Γ0 ++ [] ++ Γ3 ++ (m0 :: Γ5) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert ((Γ0 ++ m0 :: Γ5) ++ Γ3 ++ Γ6 = Γ0 ++ (m0 :: Γ5) ++ Γ3 ++ [] ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
    assert (Γ0 ++ B :: Γ3 ++ m0 :: Γ5 ++ Γ6 = Γ0 ++ [] ++ (B :: Γ3) ++ (m0 :: Γ5) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert ((Γ0 ++ m0 :: Γ5) ++ B :: Γ3 ++ Γ6 = Γ0 ++ (m0 :: Γ5) ++ (B :: Γ3) ++ [] ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
  * rewrite app_nil_r. exists ((Γ0 ++ m0 :: Γ4) ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
    exists ((Γ0 ++ m0 :: Γ4) ++ B :: Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
    assert (Γ0 ++ m0 :: Γ4 ++ A --> B :: Γ3 ++ Γ6 = (Γ0 ++ m0 :: Γ4) ++ A --> B :: Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpLRule_I.
    assert ((Γ0 ++ m0 :: Γ4) ++ Γ3 ++ Γ6 = Γ0 ++ (m0 :: Γ4) ++ Γ3 ++ [] ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ0 ++ Γ3 ++ m0 :: Γ4 ++ Γ6 = Γ0 ++ [] ++ Γ3 ++ (m0 :: Γ4) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
    assert ((Γ0 ++ m0 :: Γ4) ++ B :: Γ3 ++ Γ6 = Γ0 ++ (m0 :: Γ4) ++ (B :: Γ3) ++ [] ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ0 ++ B :: Γ3 ++ m0 :: Γ4 ++ Γ6 = Γ0 ++ [] ++ (B :: Γ3) ++ (m0 :: Γ4) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
  * rewrite app_nil_r. exists ((Γ0 ++ m1 :: Γ5 ++ m0 :: Γ4) ++ Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
    exists ((Γ0 ++ m1 :: Γ5 ++ m0 :: Γ4) ++ B :: Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
    assert (Γ0 ++ m1 :: Γ5 ++ m0 :: Γ4 ++ A --> B :: Γ3 ++ Γ6 = (Γ0 ++ m1 :: Γ5 ++ m0 :: Γ4) ++ A --> B :: Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply ImpLRule_I.
    assert (Γ0 ++ Γ3 ++ m0 :: Γ4 ++ m1 :: Γ5 ++ Γ6 = Γ0 ++ Γ3 ++ (m0 :: Γ4) ++ (m1 :: Γ5) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert ((Γ0 ++ m1 :: Γ5 ++ m0 :: Γ4) ++ Γ3 ++ Γ6 = Γ0 ++ (m1 :: Γ5) ++ (m0 :: Γ4) ++ Γ3 ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
    assert (Γ0 ++ B :: Γ3 ++ m0 :: Γ4 ++ m1 :: Γ5 ++ Γ6 = Γ0 ++ (B :: Γ3) ++ (m0 :: Γ4) ++ (m1 :: Γ5) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert ((Γ0 ++ m1 :: Γ5 ++ m0 :: Γ4) ++ B :: Γ3 ++ Γ6 = Γ0 ++ (m1 :: Γ5) ++ (m0 :: Γ4) ++ (B :: Γ3) ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
  * exists (Γ0 ++ x ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ0 ++ B :: x ++ Γ6, Δ0 ++ Δ1). split. split. repeat rewrite <- app_assoc. apply ImpLRule_I.
    apply list_exch_L_id. apply list_exch_L_id.
  * exists (Γ0 ++ x ++ m0 :: Γ5 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ0 ++ B :: x ++ m0 :: Γ5 ++ Γ6, Δ0 ++ Δ1). split. split. repeat rewrite <- app_assoc. apply ImpLRule_I.
    apply list_exch_L_id. apply list_exch_L_id.
  * exists (Γ0 ++ x ++ m0 :: Γ4 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ0 ++ B :: x ++ m0 :: Γ4 ++ Γ6, Δ0 ++ Δ1). split. split. repeat rewrite <- app_assoc. apply ImpLRule_I.
    apply list_exch_L_id. apply list_exch_L_id.
  * exists (Γ0 ++ x ++ m1 :: Γ5 ++ m0 :: Γ4 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ0 ++ B :: x ++ m1 :: Γ5 ++ m0 :: Γ4 ++ Γ6, Δ0 ++ Δ1). split. split.
    repeat rewrite <- app_assoc. apply ImpLRule_I.
    assert (Γ0 ++ x ++ m0 :: Γ4 ++ m1 :: Γ5 ++ Γ6 = (Γ0 ++ x) ++ (m0 :: Γ4) ++ [] ++ (m1 :: Γ5) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ0 ++ x ++ m1 :: Γ5 ++ m0 :: Γ4 ++ Γ6 = (Γ0 ++ x) ++ (m1 :: Γ5) ++ [] ++ (m0 :: Γ4) ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
    assert (Γ0 ++ B :: x ++ m0 :: Γ4 ++ m1 :: Γ5 ++ Γ6 = (Γ0 ++ B :: x) ++ (m0 :: Γ4) ++ [] ++ (m1 :: Γ5) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ0 ++ B :: x ++ m1 :: Γ5 ++ m0 :: Γ4 ++ Γ6 = (Γ0 ++ B :: x) ++ (m1 :: Γ5) ++ [] ++ (m0 :: Γ4) ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
  * exists (Γ0 ++ x ++ m0 :: Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ0 ++ B :: x ++ m0 :: Γ3 ++ Γ6, Δ0 ++ Δ1). split. split. repeat rewrite <- app_assoc. apply ImpLRule_I.
    apply list_exch_L_id. apply list_exch_L_id.
  * exists (Γ0 ++ x ++ m1 :: Γ5 ++ m0 :: Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ0 ++ B :: x ++ m1 :: Γ5 ++ m0 :: Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
    repeat rewrite <- app_assoc. apply ImpLRule_I.
    assert (Γ0 ++ x ++ m0 :: Γ3 ++ m1 :: Γ5 ++ Γ6 = (Γ0 ++ x) ++ (m0 :: Γ3) ++ [] ++ (m1 :: Γ5) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ0 ++ x ++ m1 :: Γ5 ++ m0 :: Γ3 ++ Γ6 = (Γ0 ++ x) ++ (m1 :: Γ5) ++ [] ++ (m0 :: Γ3) ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
    assert (Γ0 ++ B :: x ++ m0 :: Γ3 ++ m1 :: Γ5 ++ Γ6 = (Γ0 ++ B :: x) ++ (m0 :: Γ3) ++ [] ++ (m1 :: Γ5) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ0 ++ B :: x ++ m1 :: Γ5 ++ m0 :: Γ3 ++ Γ6 = (Γ0 ++ B :: x) ++ (m1 :: Γ5) ++ [] ++ (m0 :: Γ3) ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
  * exists (Γ0 ++ x ++ m1 :: Γ4 ++ m0 :: Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ0 ++ B :: x ++ m1 :: Γ4 ++ m0 :: Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
    repeat rewrite <- app_assoc. apply ImpLRule_I.
    assert (Γ0 ++ x ++ m0 :: Γ3 ++ m1 :: Γ4 ++ Γ6 = (Γ0 ++ x) ++ (m0 :: Γ3) ++ [] ++ (m1 :: Γ4) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ0 ++ x ++ m1 :: Γ4 ++ m0 :: Γ3 ++ Γ6 = (Γ0 ++ x) ++ (m1 :: Γ4) ++ [] ++ (m0 :: Γ3) ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
    assert (Γ0 ++ B :: x ++ m0 :: Γ3 ++ m1 :: Γ4 ++ Γ6 = (Γ0 ++ B :: x) ++ (m0 :: Γ3) ++ [] ++ (m1 :: Γ4) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ0 ++ B :: x ++ m1 :: Γ4 ++ m0 :: Γ3 ++ Γ6 = (Γ0 ++ B :: x) ++ (m1 :: Γ4) ++ [] ++ (m0 :: Γ3) ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
  * exists (Γ0 ++ x ++ m2 :: Γ5 ++ m1 :: Γ4 ++ m0 :: Γ3 ++ Γ6, Δ0 ++ A :: Δ1).
    exists (Γ0 ++ B :: x ++ m2 :: Γ5 ++ m1 :: Γ4 ++ m0 :: Γ3 ++ Γ6, Δ0 ++ Δ1). split. split.
    repeat rewrite <- app_assoc. apply ImpLRule_I.
    assert (Γ0 ++ x ++ m0 :: Γ3 ++ m1 :: Γ4 ++ m2 :: Γ5 ++ Γ6 = (Γ0 ++ x) ++ (m0 :: Γ3) ++ (m1 :: Γ4) ++ (m2 :: Γ5) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ0 ++ x ++ m2 :: Γ5 ++ m1 :: Γ4 ++ m0 :: Γ3 ++ Γ6 = (Γ0 ++ x) ++ (m2 :: Γ5) ++ (m1 :: Γ4) ++ (m0 :: Γ3) ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
    assert (Γ0 ++ B :: x ++ m0 :: Γ3 ++ m1 :: Γ4 ++ m2 :: Γ5 ++ Γ6 = (Γ0 ++ B :: x) ++ (m0 :: Γ3) ++ (m1 :: Γ4) ++ (m2 :: Γ5) ++ Γ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Γ0 ++ B :: x ++ m2 :: Γ5 ++ m1 :: Γ4 ++ m0 :: Γ3 ++ Γ6 = (Γ0 ++ B :: x) ++ (m2 :: Γ5) ++ (m1 :: Γ4) ++ (m0 :: Γ3) ++ Γ6).
    repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
    rewrite H0. clear H0. apply list_exch_LI.
Qed.

Lemma ImpL_app_list_exchR : forall s se ps1 ps2,
  (@list_exch_R s se) ->
  (ImpLRule [ps1;ps2] s) ->
  (existsT2 pse1 pse2,
    (ImpLRule [pse1;pse2] se) *
    (@list_exch_R ps1 pse1) *
    (@list_exch_R ps2 pse2)).
Proof.
intros s se ps1 ps2 exch. intro RA. inversion RA. inversion exch. subst.
inversion H. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
- exists (Γ0 ++ Γ1, Δ2 ++ A :: Δ5 ++ Δ4 ++ Δ3 ++ Δ6).
  exists (Γ0 ++ B :: Γ1, Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6). split. split. apply ImpLRule_I.
  assert (Δ2 ++ A :: Δ3 ++ Δ4 ++ Δ5 ++ Δ6 = (Δ2 ++ [A]) ++ Δ3 ++ Δ4 ++ Δ5 ++ Δ6).
  rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
  assert (Δ2 ++ A :: Δ5 ++ Δ4 ++ Δ3 ++ Δ6 = (Δ2 ++ [A]) ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6).
  rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI.
  apply list_exch_RI.
- apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
  + exists (Γ0 ++ Γ1, (Δ2 ++ Δ5) ++ A :: Δ4 ++ Δ3 ++ Δ6).
    exists (Γ0 ++ B :: Γ1, Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6).
    split. split.
    assert (Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6 = (Δ2 ++ Δ5) ++ Δ4 ++ Δ3 ++ Δ6). rewrite app_assoc.
    reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
    repeat rewrite <- app_assoc.
    assert (Δ2 ++ Δ3 ++ A :: Δ4 ++ Δ5 ++ Δ6 = Δ2 ++ Δ3 ++ (A :: Δ4) ++ Δ5 ++ Δ6).
    reflexivity. rewrite H0. clear H0.
    assert (Δ2 ++ Δ5 ++ A :: Δ4 ++ Δ3 ++ Δ6 = Δ2 ++ Δ5 ++ (A :: Δ4) ++ Δ3 ++ Δ6).
    reflexivity. rewrite H0. clear H0. apply list_exch_RI. apply list_exch_RI.
  + apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
    * exists (Γ0 ++ Γ1, (Δ2 ++ Δ5 ++ Δ4) ++ A :: Δ3 ++ Δ6).
      exists (Γ0 ++ B :: Γ1, Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6). split. split.
      assert (Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6 = (Δ2 ++ Δ5 ++ Δ4) ++ Δ3 ++ Δ6). repeat rewrite app_assoc.
      reflexivity. rewrite H0. clear H0. apply ImpLRule_I. repeat rewrite <- app_assoc.
      assert (Δ2 ++ Δ3 ++ Δ4 ++ A :: Δ5 ++ Δ6 = Δ2 ++ Δ3 ++ (Δ4 ++ [A]) ++ Δ5 ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      assert (Δ2 ++ Δ5 ++ Δ4 ++ A :: Δ3 ++ Δ6 = Δ2 ++ Δ5 ++ (Δ4 ++ [A]) ++ Δ3 ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI. apply list_exch_RI.
    * apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
      { repeat rewrite <- app_assoc. exists (Γ0 ++ Γ1, Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ A :: Δ6).
        exists (Γ0 ++ B :: Γ1, Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6).
        split. split. repeat rewrite app_assoc. apply ImpLRule_I. apply list_exch_RI.
        apply list_exch_RI. }
      { repeat rewrite <- app_assoc. exists (Γ0 ++ Γ1, Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ x0 ++ A :: Δ1).
        exists (Γ0 ++ B :: Γ1, Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ x0 ++ Δ1). split. split. repeat rewrite app_assoc.
        apply ImpLRule_I. apply list_exch_RI. apply list_exch_RI. }
      { repeat rewrite <- app_assoc. exists (Γ0 ++ Γ1, Δ2 ++ (x ++ A :: x0) ++ Δ4 ++ Δ3 ++ Δ6).
        exists (Γ0 ++ B :: Γ1, Δ2 ++ x ++ x0 ++ Δ4 ++ Δ3 ++ Δ6). split. split.
        assert (Δ2 ++ (x ++ A :: x0) ++ Δ4 ++ Δ3 ++ Δ6 = (Δ2 ++ x) ++ A :: x0 ++ Δ4 ++ Δ3 ++ Δ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert (Δ2 ++ x ++ x0 ++ Δ4 ++ Δ3 ++ Δ6 = (Δ2 ++ x) ++ x0 ++ Δ4 ++ Δ3 ++ Δ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        apply ImpLRule_I.
        assert (Δ2 ++ Δ3 ++ Δ4 ++ x ++ A :: x0 ++ Δ6 = Δ2 ++ Δ3 ++ Δ4 ++ (x ++ A :: x0) ++ Δ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply list_exch_RI.
        assert (Δ2 ++ Δ3 ++ Δ4 ++ x ++ x0 ++ Δ6 = Δ2 ++ Δ3 ++ Δ4 ++ (x ++ x0) ++ Δ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert (Δ2 ++ x ++ x0 ++ Δ4 ++ Δ3 ++ Δ6 = Δ2 ++ (x ++ x0) ++ Δ4 ++ Δ3 ++ Δ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply list_exch_RI. }
    * repeat rewrite <- app_assoc. exists (Γ0 ++ Γ1, Δ2 ++ Δ5 ++ (x0 ++ A :: x) ++ Δ3 ++ Δ6).
      exists (Γ0 ++ B :: Γ1, Δ2 ++ Δ5 ++ (x0 ++ x) ++ Δ3 ++ Δ6). split. split.
      assert (Δ2 ++ Δ5 ++ (x0 ++ A :: x) ++ Δ3 ++ Δ6 = (Δ2 ++ Δ5 ++ x0) ++ A :: x ++ Δ3 ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      assert (Δ2 ++ Δ5 ++ x0 ++ x ++ Δ3 ++ Δ6 = (Δ2 ++ Δ5 ++ x0) ++ x ++ Δ3 ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      assert (Δ2 ++ Δ5 ++ (x0 ++ x) ++ Δ3 ++ Δ6 = (Δ2 ++ Δ5 ++ x0) ++ x ++ Δ3 ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      apply ImpLRule_I.
      assert (Δ2 ++ Δ3 ++ x0 ++ A :: x ++ Δ5 ++ Δ6 = Δ2 ++ Δ3 ++ (x0 ++ A :: x) ++ Δ5 ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply list_exch_RI.
      assert (Δ2 ++ Δ3 ++ x0 ++ x ++ Δ5 ++ Δ6 = Δ2 ++ Δ3 ++ (x0 ++ x) ++ Δ5 ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply list_exch_RI.
  + repeat rewrite <- app_assoc. exists (Γ0 ++ Γ1, Δ2 ++ Δ5 ++ Δ4 ++ (x ++ A :: x0) ++ Δ6).
    exists (Γ0 ++ B :: Γ1, Δ2 ++ Δ5 ++ Δ4 ++ (x ++ x0) ++ Δ6). split. split.
    assert (Δ2 ++ Δ5 ++ Δ4 ++ (x ++ A :: x0) ++ Δ6 = (Δ2 ++ Δ5 ++ Δ4 ++ x) ++ A :: x0 ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Δ2 ++ Δ5 ++ Δ4 ++ x ++ x0 ++ Δ6 = (Δ2 ++ Δ5 ++ Δ4 ++ x) ++ x0 ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    assert (Δ2 ++ Δ5 ++ Δ4 ++ (x ++ x0) ++ Δ6 = (Δ2 ++ Δ5 ++ Δ4 ++ x) ++ x0 ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
    apply ImpLRule_I.
    assert (Δ2 ++ x ++ A :: x0 ++ Δ4 ++ Δ5 ++ Δ6 = Δ2 ++ (x ++ A :: x0) ++ Δ4 ++ Δ5 ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply list_exch_RI.
    assert (Δ2 ++ x ++ x0 ++ Δ4 ++ Δ5 ++ Δ6 = Δ2 ++ (x ++ x0) ++ Δ4 ++ Δ5 ++ Δ6).
    repeat rewrite <- app_assoc. reflexivity. rewrite H0. apply list_exch_RI.
- repeat rewrite <- app_assoc. exists (Γ0 ++ Γ1, Δ0 ++ A :: x ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6).
  exists (Γ0 ++ B :: Γ1, Δ0 ++ x ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6). split. split. apply ImpLRule_I.
  assert (Δ0 ++ A :: x ++ Δ3 ++ Δ4 ++ Δ5 ++ Δ6 = (Δ0 ++ A :: x) ++ Δ3 ++ Δ4 ++ Δ5 ++ Δ6).
  repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
  assert (Δ0 ++ A :: x ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6 = (Δ0 ++ A :: x) ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6).
  repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI.
  assert (Δ0 ++ x ++ Δ3 ++ Δ4 ++ Δ5 ++ Δ6 = (Δ0 ++ x) ++ Δ3 ++ Δ4 ++ Δ5 ++ Δ6).
  repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
  assert (Δ0 ++ x ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6 = (Δ0 ++ x) ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6).
  repeat rewrite <- app_assoc. reflexivity. rewrite H0. clear H0. apply list_exch_RI.
Qed.
