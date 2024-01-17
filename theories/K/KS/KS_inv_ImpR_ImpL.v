Require Import List.
Export ListNotations.
Require Import Lia.
Require Import PeanoNat.

Require Import KS_calc.
Require Import KS_exch.
Require Import KS_wkn.
Require Import KS_dec.


Lemma remove_rest_gen_ext : forall l A, rest_gen_ext [A] (remove eq_dec_form A l) l.
Proof.
induction l ; intros.
- simpl. apply univ_gen_ext_nil.
- simpl. destruct (eq_dec_form A a).
  * subst. apply univ_gen_ext_extra. apply InT_eq. apply IHl.
  * apply univ_gen_ext_cons. apply IHl.
Qed.

Theorem derrec_height_False_ge_1 : forall s, forall (D : KS_prv s), 1 <= derrec_height D.
Proof.
intros s D.
induction D.
- destruct p.
- simpl. lia.
Qed.

Lemma rest_nobox_gen_ext_trans : forall (A B : MPropF) l0 l1 l2, ((In (Imp A B) l0) -> False) ->
                                                    (nobox_gen_ext l0 l1) ->
                                                    (rest_gen_ext [Imp A B] l2 l1) ->
                                                    (nobox_gen_ext l0 l2).
Proof.
intros A B l0 l1 l2 H1 H2. generalize dependent l2.
induction H2.
- intros. inversion X. apply univ_gen_ext_nil.
- intros. inversion X.
  * subst. apply univ_gen_ext_cons. apply IHuniv_gen_ext. intro. apply H1.
    apply in_cons. assumption. assumption.
  * subst. inversion H3. subst. exfalso. apply H1. apply in_eq.
    inversion H0.
- intros. inversion X.
  * subst. apply univ_gen_ext_extra. assumption. apply IHuniv_gen_ext ; assumption.
  * subst. apply IHuniv_gen_ext ; assumption.
Qed.

(* We prove the height-preserving invertibility of ImpR and ImpL below. *)

Theorem ImpR_ImpL_hpinv : forall (k : nat) concl
        (D0 : KS_prv concl),
        k = (derrec_height D0) ->
          ((forall prem, ((ImpRRule [prem] concl) ->
          existsT2 (D1 : KS_prv prem),
          derrec_height D1 <= k))) *
          ((forall prem1 prem2, ((ImpLRule [prem1; prem2] concl) ->
          existsT2 (D1 : KS_prv prem1)
                   (D2 : KS_prv prem2),
          (derrec_height D1 <= k) * (derrec_height D2 <= k)))).
Proof.
assert (DersNilF: dersrec (KS_rules) (fun _ : Seq => False) []).
apply dersrec_nil.
(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall (concl : Seq)
  (D0 : derrec (KS_rules) (fun _ : Seq => False) concl),
x = derrec_height D0 ->
((forall prem, ((ImpRRule [prem] concl) ->
          existsT2 (D1 : KS_prv prem),
          derrec_height D1 <= x))) *
          ((forall prem1 prem2, ((ImpLRule [prem1; prem2] concl) ->
          existsT2 (D1 : KS_prv prem1)
                   (D2 : KS_prv prem2),
          (derrec_height D1 <= x) * (derrec_height D2 <= x)))))).
apply p. intros n IH. clear p.
(* Now we do the actual proof-theoretical work. *)
intros s D0. remember D0 as D0'. destruct D0.
(* D0 is a leaf *)
- destruct f.
(* D0 is ends with an application of rule *)
- intros hei. split.
{ intros prem RA. inversion RA. subst.
  inversion k ; subst.
  (* IdP *)
  * inversion H. subst. assert (InT # P (Γ0 ++ Γ1)).
    rewrite <- H2. apply InT_or_app. right. apply InT_eq. assert (InT # P (Γ0 ++ A :: Γ1)).
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right.
    apply InT_cons. assumption. apply InT_split in H1. destruct H1. destruct s. rewrite e.
    assert (InT # P (Δ0 ++ B :: Δ1)). assert (InT # P (Δ2 ++ # P :: Δ3)).
    apply InT_or_app. right. apply InT_eq. rewrite H3 in H1. apply InT_app_or in H1.
    destruct H1. apply InT_or_app. auto. inversion i. inversion H4. apply InT_or_app. right.
    apply InT_cons. assumption. apply InT_split in H1. destruct H1. destruct s.
    rewrite e0. assert (IdPRule [] (x ++ # P :: x0, x1 ++ # P :: x2)).
    apply IdPRule_I. apply IdP in H1.
    pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x ++ # P :: x0, x1 ++ # P :: x2) H1 DersNilF). exists d0.
    simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* BotL *)
  * inversion H. subst. assert (InT (Bot) (Γ0 ++ Γ1)).
    rewrite <- H2. apply InT_or_app. right. apply InT_eq. assert (InT (Bot) (Γ0 ++ A :: Γ1)).
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right.
    apply InT_cons. assumption. apply InT_split in H1. destruct H1. destruct s. rewrite e.
    assert (BotLRule [] (x ++ Bot :: x0, Δ0 ++ B :: Δ1)).
    apply BotLRule_I. apply BotL in H1.
    pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x ++ Bot :: x0, Δ0 ++ B :: Δ1) H1 DersNilF). exists d0.
    simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* ImpR *)
  * inversion H. subst. apply app2_find_hole in H3. destruct H3. repeat destruct s ; destruct p ; subst.
    + inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (J1: list_exch_L (Γ2 ++ A0 :: Γ3, Δ2 ++ B0 :: Δ3) (A0 :: Γ0 ++ Γ1, Δ2 ++ B0 :: Δ3)).
      assert (Γ2 ++ A0 :: Γ3 = [] ++ [] ++ Γ2 ++ [A0] ++ Γ3). reflexivity.
      rewrite H0. clear H0.
      assert (A0 :: Γ0 ++ Γ1 = [] ++ [A0] ++ Γ2 ++ [] ++ Γ3). simpl. rewrite H2. reflexivity.
      rewrite H0. clear H0. apply list_exch_LI.
      assert (J20: derrec_height x0 = derrec_height x0). reflexivity.
      pose (KS_hpadm_list_exch_L0 _ _ x0 J20 _ J1). destruct s.
      assert (J2: list_exch_L (A0 :: Γ0 ++ Γ1, Δ2 ++ B0 :: Δ3) (Γ0 ++ A0 :: Γ1, Δ2 ++ B0 :: Δ3)).
      assert ((A0 :: Γ0 ++ Γ1, Δ2 ++ B0 :: Δ3) = ([] ++ [A0] ++ Γ0 ++ [] ++ Γ1, Δ2 ++ B0 :: Δ3)).
      reflexivity. assert ((Γ0 ++ A0 :: Γ1, Δ2 ++ B0 :: Δ3) = ([] ++ [] ++ Γ0 ++ [A0] ++ Γ1, Δ2 ++ B0 :: Δ3)).
      reflexivity. rewrite H1. rewrite H0. clear H1. clear H0. apply list_exch_LI.
      assert (J21: derrec_height x1 = derrec_height x1). reflexivity.
      pose (KS_hpadm_list_exch_L0 _ _ x1 J21 _ J2). destruct s. exists x2.
      simpl. lia.
    + destruct x.
      { simpl in e0. inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (J1: list_exch_L (Γ2 ++ A :: Γ3, Δ2 ++ B :: Δ1) (A :: Γ0 ++ Γ1, Δ2 ++ B :: Δ1)).
        assert (Γ2 ++ A :: Γ3 = [] ++ [] ++ Γ2 ++ [A] ++ Γ3). reflexivity.
        rewrite H0. clear H0.
        assert (A :: Γ0 ++ Γ1 = [] ++ [A] ++ Γ2 ++ [] ++ Γ3). simpl. rewrite H2. reflexivity.
        rewrite H0. clear H0. apply list_exch_LI.
        assert (J20: derrec_height x = derrec_height x). reflexivity.
        pose (KS_hpadm_list_exch_L0 _ _ x J20 _ J1). destruct s.
        assert (J2: list_exch_L (A :: Γ0 ++ Γ1, Δ2 ++ B :: Δ1) (Γ0 ++ A :: Γ1, (Δ2 ++ []) ++ B :: Δ1)).
        assert ((A :: Γ0 ++ Γ1, Δ2 ++ B :: Δ1) = ([] ++ [A] ++ Γ0 ++ [] ++ Γ1, Δ2 ++ B :: Δ1)).
        reflexivity. assert ((Γ0 ++ A :: Γ1, (Δ2 ++ []) ++ B :: Δ1) = ([] ++ [] ++ Γ0 ++ [A] ++ Γ1, Δ2 ++ B :: Δ1)).
        rewrite app_nil_r. reflexivity. rewrite H1. rewrite H0. clear H1. clear H0. apply list_exch_LI.
        assert (J21: derrec_height x0 = derrec_height x0). reflexivity.
        pose (KS_hpadm_list_exch_L0 _ _ x0 J21 _ J2). destruct s. exists x1.
        simpl. lia. }
      { inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (J1: list_exch_L (Γ2 ++ A0 :: Γ3, Δ2 ++ B0 :: x ++ A --> B :: Δ1) (A0 :: Γ0 ++ Γ1, Δ2 ++ B0 :: x ++ A --> B :: Δ1)).
        assert (Γ2 ++ A0 :: Γ3 = [] ++ [] ++ Γ2 ++ [A0] ++ Γ3). reflexivity.
        rewrite H0. clear H0.
        assert (A0 :: Γ0 ++ Γ1 = [] ++ [A0] ++ Γ2 ++ [] ++ Γ3). simpl. rewrite H2. reflexivity.
        rewrite H0. clear H0. apply list_exch_LI.
        assert (J20: derrec_height x0 = derrec_height x0). reflexivity.
        pose (KS_hpadm_list_exch_L0 _ _ x0 J20 _ J1). destruct s. simpl in IH. simpl.
        assert (J2: derrec_height x1 < S (dersrec_height d)). lia.
        assert (J3: derrec_height x1 = derrec_height x1). reflexivity.
        assert (J4: ImpRRule [(A0 :: Γ0 ++ A :: Γ1, Δ2 ++ B0 :: x ++ B :: Δ1)] (A0 :: Γ0 ++ Γ1, Δ2 ++ B0 :: x ++ A --> B :: Δ1)).
        assert (A0 :: Γ0 ++ A :: Γ1 = (A0 :: Γ0) ++ A :: Γ1). reflexivity. rewrite H0. clear H0.
        assert (A0 :: Γ0 ++ Γ1 = (A0 :: Γ0) ++ Γ1). reflexivity. rewrite H0. clear H0.
        assert (Δ2 ++ B0 :: x ++ B :: Δ1 = (Δ2 ++ B0 :: x) ++ B :: Δ1). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0.
        assert (Δ2 ++ B0 :: x ++ A --> B :: Δ1 = (Δ2 ++ B0 :: x) ++ A --> B :: Δ1). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0. apply ImpRRule_I.
        pose (IH _ J2 _ _ J3). destruct p. pose (s _ J4). clear s0. destruct s1. clear s.
        assert (existsT2 (x3 : derrec KS_rules (fun _ : Seq => False)
        (Γ0 ++ A :: Γ1, (Δ2 ++ A0 --> B0 :: x) ++ B :: Δ1)), derrec_height x3 <= S (dersrec_height d)).
        assert (ImpRRule [(A0 :: Γ0 ++ A :: Γ1, Δ2 ++ B0 :: x ++ B :: Δ1)] (Γ0 ++ A :: Γ1, (Δ2 ++ A0 --> B0 :: x) ++ B :: Δ1)).
        assert (A0 :: Γ0 ++ A :: Γ1 = [] ++ A0 :: Γ0 ++ A :: Γ1). reflexivity. rewrite H0. clear H0.
        assert (Γ0 ++ A :: Γ1 = [] ++ Γ0 ++ A :: Γ1). reflexivity. rewrite H0. clear H0. repeat rewrite <- app_assoc.
        apply ImpRRule_I. apply ImpR in H0 ; try intro ; try apply f0 ; try auto ; try assumption.
        pose (dlCons x2 DersNilF).
        pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
        (ps:=[(A0 :: Γ0 ++ A :: Γ1, Δ2 ++ B0 :: x ++ B :: Δ1)]) (Γ0 ++ A :: Γ1, (Δ2 ++ A0 --> B0 :: x) ++ B :: Δ1) H0 d0).
        exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
        destruct X. exists x3. lia. }
    + destruct x.
      { simpl in e0. inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (J1: list_exch_L (Γ2 ++ A0 :: Γ3, (Δ0 ++ []) ++ B0 :: Δ3) (A0 :: Γ0 ++ Γ1, Δ0 ++ B0 :: Δ3)).
        rewrite app_nil_r.
        assert (Γ2 ++ A0 :: Γ3 = [] ++ [] ++ Γ2 ++ [A0] ++ Γ3). reflexivity.
        rewrite H0. clear H0.
        assert (A0 :: Γ0 ++ Γ1 = [] ++ [A0] ++ Γ2 ++ [] ++ Γ3). simpl. rewrite H2. reflexivity.
        rewrite H0. clear H0. apply list_exch_LI.
        assert (J20: derrec_height x = derrec_height x). reflexivity.
        pose (KS_hpadm_list_exch_L0 _ _ x J20 _ J1). destruct s.
        assert (J2: list_exch_L (A0 :: Γ0 ++ Γ1, Δ0 ++ B0 :: Δ3) (Γ0 ++ A0 :: Γ1, Δ0 ++ B0 :: Δ3)).
        assert ((A0 :: Γ0 ++ Γ1, Δ0 ++ B0 :: Δ3) = ([] ++ [A0] ++ Γ0 ++ [] ++ Γ1, Δ0 ++ B0 :: Δ3)).
        reflexivity. assert ((Γ0 ++ A0 :: Γ1, Δ0 ++ B0 :: Δ3) = ([] ++ [] ++ Γ0 ++ [A0] ++ Γ1, Δ0 ++ B0 :: Δ3)).
        reflexivity. rewrite H1. rewrite H0. clear H1. clear H0. apply list_exch_LI.
        assert (J21: derrec_height x0 = derrec_height x0). reflexivity.
        pose (KS_hpadm_list_exch_L0 _ _ x0 J21 _ J2). destruct s. exists x1.
        simpl. lia. }
      { inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s. simpl.
        assert (J1: list_exch_L (Γ2 ++ A0 :: Γ3, (Δ0 ++ A --> B :: x) ++ B0 :: Δ3) (A0 :: Γ0 ++ Γ1, Δ0 ++ A --> B :: x ++ B0 :: Δ3)).
        repeat rewrite <- app_assoc.
        assert (Γ2 ++ A0 :: Γ3 = [] ++ [] ++ Γ2 ++ [A0] ++ Γ3). reflexivity.
        rewrite H0. clear H0.
        assert (A0 :: Γ0 ++ Γ1 = [] ++ [A0] ++ Γ2 ++ [] ++ Γ3). simpl. rewrite H2. reflexivity.
        rewrite H0. clear H0. apply list_exch_LI.
        assert (J20: derrec_height x0 = derrec_height x0). reflexivity.
        pose (KS_hpadm_list_exch_L0 _ _ x0 J20 _ J1). destruct s. simpl in IH. simpl.
        assert (J2: derrec_height x1 < S (dersrec_height d)). lia.
        assert (J3: derrec_height x1 = derrec_height x1). reflexivity.
        assert (J4: ImpRRule [(A0 :: Γ0 ++ A :: Γ1, Δ0 ++ B :: x ++ B0 :: Δ3)] (A0 :: Γ0 ++ Γ1, Δ0 ++ A --> B :: x ++ B0 :: Δ3)).
        assert (A0 :: Γ0 ++ A :: Γ1 = (A0 :: Γ0) ++ A :: Γ1). reflexivity. rewrite H0. clear H0.
        assert (A0 :: Γ0 ++ Γ1 = (A0 :: Γ0) ++ Γ1). reflexivity. rewrite H0. clear H0.
        apply ImpRRule_I.
        pose (IH _ J2 _ _ J3). destruct p. pose (s _ J4). clear s0. destruct s1. clear s.
        assert (ImpRRule [(A0 :: Γ0 ++ A :: Γ1, Δ0 ++ B :: x ++ B0 :: Δ3)] (Γ0 ++ A :: Γ1, Δ0 ++ B :: x ++ A0 --> B0 :: Δ3)).
        assert (A0 :: Γ0 ++ A :: Γ1 = [] ++ A0 :: Γ0 ++ A :: Γ1). reflexivity. rewrite H0. clear H0.
        assert (Γ0 ++ A :: Γ1 = [] ++ Γ0 ++ A :: Γ1). reflexivity. rewrite H0. clear H0. repeat rewrite <- app_assoc.
        assert (Δ0 ++ B :: x ++ B0 :: Δ3 = (Δ0 ++ B :: x) ++ B0 :: Δ3). rewrite <- app_assoc. reflexivity.
        rewrite H0. clear H0.
        assert (Δ0 ++ B :: x ++ A0 --> B0 :: Δ3 = (Δ0 ++ B :: x) ++ A0 --> B0 :: Δ3). rewrite <- app_assoc. reflexivity.
        rewrite H0. clear H0.
        apply ImpRRule_I. apply ImpR in H0 ; try intro ; try apply f0 ; try auto ; try assumption.
        pose (dlCons x2 DersNilF).
        pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
        (ps:=[(A0 :: Γ0 ++ A :: Γ1, Δ0 ++ B :: x ++ B0 :: Δ3)]) (Γ0 ++ A :: Γ1, Δ0 ++ B :: x ++ A0 --> B0 :: Δ3) H0 d0).
        exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity. }
  (* ImpL *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J1: ImpRRule [(A :: Γ2 ++ B0 :: Γ3, Δ0 ++ B :: Δ1)] (Γ2 ++ B0 :: Γ3, Δ2 ++ Δ3)).
    rewrite H3. assert (A :: Γ2 ++ B0 :: Γ3 = [] ++ A :: Γ2 ++ B0 :: Γ3). reflexivity.
    rewrite H0. clear H0. assert (Γ2 ++ B0 :: Γ3 = [] ++ Γ2 ++ B0 :: Γ3). reflexivity.
    rewrite H0. clear H0. apply ImpRRule_I. simpl in IH.
    assert (J2: derrec_height x0 < S (dersrec_height d)). lia.
    assert (J3: derrec_height x0 = derrec_height x0). reflexivity.
    pose (IH _ J2 _ _ J3). destruct p. clear s0. pose (s _ J1). destruct s0. clear s.
    assert (J7: list_exch_R (Γ2 ++ Γ3, Δ2 ++ A0 :: Δ3) (Γ2 ++ Γ3, A0 :: Δ0 ++ A --> B :: Δ1)).
    rewrite <- H3. assert (Δ2 ++ A0 :: Δ3 = [] ++ [] ++ Δ2 ++ [A0] ++ Δ3). reflexivity.
    rewrite H0. clear H0. assert (A0 :: Δ2 ++ Δ3 = [] ++ [A0] ++ Δ2 ++ [] ++ Δ3). reflexivity.
    rewrite H0. clear H0. apply list_exch_RI.
    assert (J8: derrec_height x = derrec_height x). reflexivity.
    pose (KS_hpadm_list_exch_R0 _ _ x J8 _ J7). destruct s.
    assert (J4: ImpRRule [(A :: Γ2 ++ Γ3, A0 :: Δ0 ++ B :: Δ1)] (Γ2 ++ Γ3, A0 :: Δ0 ++ A --> B :: Δ1)).
    assert (A :: Γ2 ++ Γ3 = [] ++ A :: Γ2 ++ Γ3). reflexivity.
    rewrite H0. clear H0. assert ((Γ2 ++ Γ3, A0 :: Δ0 ++ A --> B :: Δ1) = ([] ++ Γ2 ++ Γ3, A0 :: Δ0 ++ A --> B :: Δ1)). reflexivity.
    rewrite H0. clear H0. assert (A0 :: Δ0 ++ B :: Δ1 = (A0 :: Δ0) ++ B :: Δ1). reflexivity.
    rewrite H0. clear H0. assert (A0 :: Δ0 ++ A --> B :: Δ1 = (A0 :: Δ0) ++ A --> B :: Δ1). reflexivity.
    rewrite H0. clear H0. apply ImpRRule_I. simpl in IH.
    assert (J5: derrec_height x2 < S (dersrec_height d)). lia.
    assert (J6: derrec_height x2 = derrec_height x2). reflexivity.
    pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s _ J4). destruct s0. clear s.
    assert (ImpLRule [(A :: Γ2 ++ Γ3, A0 :: Δ0 ++ B :: Δ1); (A :: Γ2 ++ B0 :: Γ3, Δ0 ++ B :: Δ1)]
    (A :: Γ2 ++ A0 --> B0 :: Γ3, Δ0 ++ B :: Δ1)).
    assert (A :: Γ2 ++ Γ3 = (A :: Γ2) ++ Γ3). reflexivity. rewrite H0. clear H0.
    assert (A :: Γ2 ++ B0 :: Γ3 = (A :: Γ2) ++ B0 :: Γ3). reflexivity. rewrite H0. clear H0.
    assert (A :: Γ2 ++ A0 --> B0 :: Γ3 = (A :: Γ2) ++ A0 --> B0 :: Γ3). reflexivity. rewrite H0. clear H0.
    assert (Δ0 ++ B :: Δ1 = [] ++ Δ0 ++ B :: Δ1). reflexivity. rewrite H0. clear H0.
    assert (A0 :: [] ++ Δ0 ++ B :: Δ1 = [] ++ A0 :: Δ0 ++ B :: Δ1). reflexivity. rewrite H0. clear H0.
    apply ImpLRule_I. pose (dlCons x1 DersNilF). pose (dlCons x3 d0).
    apply ImpL in H0.
    pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
    (ps:=[(A :: Γ2 ++ Γ3, A0 :: Δ0 ++ B :: Δ1); (A :: Γ2 ++ B0 :: Γ3, Δ0 ++ B :: Δ1)])
    (A :: Γ2 ++ A0 --> B0 :: Γ3, Δ0 ++ B :: Δ1) H0 d1).
    assert (J40: list_exch_L (A :: Γ2 ++ A0 --> B0 :: Γ3, Δ0 ++ B :: Δ1) (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)).
    rewrite H2. assert (A :: Γ0 ++ Γ1 = [] ++ [A] ++ Γ0 ++ [] ++ Γ1). reflexivity. rewrite H1. clear H1.
    assert (Γ0 ++ A :: Γ1 = [] ++ [] ++ Γ0 ++ [A] ++ Γ1). reflexivity. rewrite H1. clear H1.
    apply list_exch_LI.
    assert (J41: derrec_height d2 = derrec_height d2). reflexivity.
    pose (KS_hpadm_list_exch_L0 _ _ d2 J41 _ J40). destruct s. exists x4. simpl in J41.
    simpl in l2. rewrite dersrec_height_nil in l2. lia. reflexivity.
  (* KR *)
  * inversion X. subst.
    assert (KRRule [(unboxed_list BΓ , [A0])] (Γ0 ++ Γ1, Δ0 ++ Δ1)).
    assert (In (Box A0) (Δ0 ++ Δ1)).
    assert (InT (Box A0) (Δ2 ++ Box A0 :: Δ3)). apply InT_or_app. right. apply InT_eq.
    rewrite H2 in H. apply InT_app_or in H. apply in_or_app. destruct H. apply InT_In in i. auto.
    inversion i. inversion H0. apply InT_In in H0. auto.
    apply in_splitT in H. destruct H. destruct s. rewrite e. apply KRRule_I ; try assumption.
    simpl. simpl in IH.
    apply KR in X1.
    assert (dersrec_height d = dersrec_height d). reflexivity.
    pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
    (ps:=[(unboxed_list BΓ, [A0])]) (Γ0 ++ Γ1, Δ0 ++ Δ1) X1 d).
    assert (J1: wkn_L A (Γ0 ++ Γ1, Δ0 ++ Δ1) (Γ0 ++ A :: Γ1, Δ0 ++ Δ1)).
    apply wkn_LI.
    assert (J2: derrec_height d0 = derrec_height d0). reflexivity.
    pose (KS_wkn_L _ _ d0 J2 _ _ J1). destruct s.
    assert (J3: wkn_R B (Γ0 ++ A :: Γ1, Δ0 ++ Δ1) (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)).
    apply wkn_RI.
    assert (J4: derrec_height x = derrec_height x). reflexivity.
    pose (KS_wkn_R _ _ x J4 _ _ J3). destruct s. exists x0.
    pose (Nat.le_trans _ _ _ l0 l). simpl in l1. assumption. }
{ intros prem1 prem2 RA. inversion RA. subst.
  inversion k ; subst.
  (* IdP *)
  * inversion H. subst. assert (InT # P (Γ0 ++ Γ1)). assert (InT # P (Γ2 ++ # P :: Γ3)).
    apply InT_or_app. right. apply InT_eq. rewrite H2 in H0. apply InT_or_app.
    apply InT_app_or in H0. destruct H0. auto. inversion i. inversion H1.
    auto. assert (InT # P (Γ0 ++ B :: Γ1)).
    apply InT_app_or in H0. apply InT_or_app. destruct H0. auto. right. apply InT_cons.
    assumption. apply InT_split in H1. destruct H1. destruct s. apply InT_split in H0. destruct H0.
    destruct s. rewrite e0. rewrite e. assert (In # P (Δ0 ++ A :: Δ1)). assert (In # P (Δ0 ++ Δ1)).
    rewrite <- H3. apply in_or_app. right. apply in_eq. apply in_app_or in H0. apply in_or_app.
    destruct H0. auto. right. apply in_cons. assumption. apply in_splitT in H0. destruct H0.
    destruct s. rewrite e1.
    assert (IdPRule [] (x1 ++ # P :: x2, x3 ++ # P :: x4)).
    apply IdPRule_I. apply IdP in H0.
    pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x1 ++ # P :: x2, x3 ++ # P :: x4) H0 DersNilF). exists d0.
    assert (IdPRule [] (x ++ # P :: x0, Δ0 ++ Δ1)). rewrite <- H3.
    apply IdPRule_I. apply IdP in H1.
    pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x ++ # P :: x0, Δ0 ++ Δ1) H1 DersNilF). exists d1.
    simpl. rewrite dersrec_height_nil. split ; lia. reflexivity.
  (* BotL *)
  * inversion H. subst. assert (InT (Bot) (Γ0 ++ Γ1)). assert (InT (Bot) (Γ2 ++ (Bot) :: Γ3)).
    apply InT_or_app. right. apply InT_eq. rewrite H2 in H0. apply InT_app_or in H0.
    apply InT_or_app. destruct H0. auto. inversion i. inversion H1. auto. assert (InT (Bot) (Γ0 ++ B :: Γ1)).
    apply InT_app_or in H0. apply InT_or_app. destruct H0. auto. right. apply InT_cons.
    assumption. apply InT_split in H0. destruct H0. destruct s. apply InT_split in H1. destruct H1.
    destruct s. rewrite e0. rewrite e.
    assert (BotLRule [] (x ++ Bot :: x0, Δ0 ++ A :: Δ1)).
    apply BotLRule_I. apply BotL in H0.
    pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x ++ Bot :: x0, Δ0 ++ A :: Δ1) H0 DersNilF). exists d0.
    assert (BotLRule [] (x1 ++ Bot :: x2, Δ0 ++ Δ1)).
    apply BotLRule_I. apply BotL in H1.
    pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x1 ++ Bot :: x2, Δ0 ++ Δ1) H1 DersNilF). exists d1.
    simpl. rewrite dersrec_height_nil. split ; lia. reflexivity.
  (* ImpR *)
  * inversion H. subst. simpl in IH.
    assert (J0: (dersrec_height d) = (dersrec_height d)). reflexivity.
    pose (dersrec_derrec_height d J0). destruct s.
    apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
    + assert (ImpLRule [(Γ2 ++ A0 :: Γ1, A :: Δ2 ++ B0 :: Δ3) ; (Γ2 ++ A0 :: B :: Γ1, Δ2 ++ B0 :: Δ3)]
      (Γ2 ++ A0 :: A --> B :: Γ1, Δ2 ++ B0 :: Δ3)). assert (Γ2 ++ A0 :: Γ1 = (Γ2 ++ [A0]) ++ Γ1).
      rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      assert (Γ2 ++ A0 :: B :: Γ1 = (Γ2 ++ [A0]) ++ B :: Γ1). rewrite <- app_assoc. reflexivity.
      rewrite H0. clear H0. assert (Γ2 ++ A0 :: A --> B :: Γ1 = (Γ2 ++ [A0]) ++ A --> B :: Γ1). rewrite <- app_assoc. reflexivity.
      rewrite H0. clear H0. assert (Δ2 ++ B0 :: Δ3 = [] ++ Δ2 ++ B0 :: Δ3).
      reflexivity. rewrite H0. clear H0. assert (A :: [] ++ Δ2 ++ B0 :: Δ3 = [] ++ A :: Δ2 ++ B0 :: Δ3).
      reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
      assert (J1: derrec_height x  < S (dersrec_height d)). lia.
      assert (J2: derrec_height x = derrec_height x). reflexivity.
      pose (IH (derrec_height x) J1 _ x J2). destruct p. clear s.
      pose (s0 _ _ H0). repeat destruct s. clear s0. destruct p.
      assert (ImpRRule [(Γ2 ++ A0 :: Γ1, A :: Δ2 ++ B0 :: Δ3)] (Γ2 ++ Γ1, A :: Δ0 ++ Δ1)).
      rewrite <- H3. assert (A :: Δ2 ++ B0 :: Δ3 = (A :: Δ2) ++ B0 :: Δ3). reflexivity.
      rewrite H1. clear H1. assert (A :: Δ2 ++ A0 --> B0 :: Δ3 = (A :: Δ2) ++ A0 --> B0 :: Δ3). reflexivity.
      rewrite H1. clear H1. apply ImpRRule_I.
      assert (existsT2 (x3: derrec KS_rules (fun _ : Seq => False)
      (Γ2 ++ Γ1, A :: Δ0 ++ Δ1)), derrec_height x3 <= S (dersrec_height d)).
      apply ImpR in H1.
      pose (dlCons x1 DersNilF). pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ A0 :: Γ1, A :: Δ2 ++ B0 :: Δ3)]) (Γ2 ++ Γ1, A :: Δ0 ++ Δ1) H1 d0).
      exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
      destruct X.
      assert (J3: derrec_height x3 = derrec_height x3). reflexivity.
      assert (J4: list_exch_R (Γ2 ++ Γ1, A :: Δ0 ++ Δ1) (Γ2 ++ Γ1, Δ0 ++ A :: Δ1)).
      assert (A :: Δ0 ++ Δ1 = [] ++ [A] ++ Δ0 ++ [] ++ Δ1). reflexivity. rewrite H2. clear H2.
      assert (Δ0 ++ A :: Δ1 = [] ++ [] ++ Δ0 ++ [A] ++ Δ1). reflexivity. rewrite H2. clear H2.
      apply list_exch_RI. pose (KS_hpadm_list_exch_R0 _ _ x3 J3 _ J4). destruct s. exists x4.
      assert (ImpRRule [(Γ2 ++ A0 :: B :: Γ1, Δ2 ++ B0 :: Δ3)] (Γ2 ++ B :: Γ1, Δ0 ++ Δ1)).
      rewrite <- H3. apply ImpRRule_I.
      assert (existsT2 (x3: derrec KS_rules (fun _ : Seq => False)
      (Γ2 ++ B :: Γ1, Δ0 ++ Δ1)), derrec_height x3 <= S (dersrec_height d)).
      apply ImpR in H2.
      pose (dlCons x2 DersNilF). pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ A0 :: B :: Γ1, Δ2 ++ B0 :: Δ3)]) (Γ2 ++ B :: Γ1, Δ0 ++ Δ1) H2 d0).
      exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
      destruct X. exists x5. simpl. split. lia. lia.
    + assert (ImpLRule [(Γ2 ++ A0 :: x0 ++ Γ1, A :: Δ2 ++ B0 :: Δ3) ; (Γ2 ++ A0 :: x0 ++ B :: Γ1, Δ2 ++ B0 :: Δ3)]
      (Γ2 ++ A0 :: x0 ++ A --> B :: Γ1, Δ2 ++ B0 :: Δ3)). assert (Γ2 ++ A0 :: x0 ++ Γ1 = (Γ2 ++ A0 :: x0) ++ Γ1).
      rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      assert (Γ2 ++ A0 :: x0 ++ B :: Γ1 = (Γ2 ++ A0 :: x0) ++ B :: Γ1). rewrite <- app_assoc. reflexivity.
      rewrite H0. clear H0. assert (Γ2 ++ A0 :: x0 ++ A --> B :: Γ1 = (Γ2 ++ A0 :: x0) ++ A --> B :: Γ1). rewrite <- app_assoc. reflexivity.
      rewrite H0. clear H0. assert (Δ2 ++ B0 :: Δ3 = [] ++ Δ2 ++ B0 :: Δ3).
      reflexivity. rewrite H0. clear H0. assert (A :: [] ++ Δ2 ++ B0 :: Δ3 = [] ++ A :: Δ2 ++ B0 :: Δ3).
      reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
      assert (J1: derrec_height x  < S (dersrec_height d)). lia.
      assert (J2: derrec_height x = derrec_height x). reflexivity.
      pose (IH (derrec_height x) J1 _ x J2). destruct p. clear s.
      pose (s0 _ _ H0). repeat destruct s. clear s0. destruct p.
      assert (ImpRRule [(Γ2 ++ A0 :: x0 ++ Γ1, A :: Δ2 ++ B0 :: Δ3)] ((Γ2 ++ x0) ++ Γ1, A :: Δ0 ++ Δ1)).
      rewrite <- H3. assert (A :: Δ2 ++ B0 :: Δ3 = (A :: Δ2) ++ B0 :: Δ3). reflexivity.
      rewrite H1. clear H1. assert (A :: Δ2 ++ A0 --> B0 :: Δ3 = (A :: Δ2) ++ A0 --> B0 :: Δ3). reflexivity.
      rewrite H1. clear H1. rewrite <- app_assoc. apply ImpRRule_I.
      assert (existsT2 (x3: derrec KS_rules (fun _ : Seq => False)
      ((Γ2 ++ x0) ++ Γ1, A :: Δ0 ++ Δ1)), derrec_height x3 <= S (dersrec_height d)).
      apply ImpR in H1.
      pose (dlCons x1 DersNilF). pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ A0 :: x0 ++ Γ1, A :: Δ2 ++ B0 :: Δ3)]) ((Γ2 ++ x0) ++ Γ1, A :: Δ0 ++ Δ1) H1 d0).
      exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
      destruct X.
      assert (J3: derrec_height x3 = derrec_height x3). reflexivity.
      assert (J4: list_exch_R ((Γ2 ++ x0) ++ Γ1, A :: Δ0 ++ Δ1) ((Γ2 ++ x0) ++ Γ1, Δ0 ++ A :: Δ1)).
      assert (A :: Δ0 ++ Δ1 = [] ++ [A] ++ Δ0 ++ [] ++ Δ1). reflexivity. rewrite H2. clear H2.
      assert (Δ0 ++ A :: Δ1 = [] ++ [] ++ Δ0 ++ [A] ++ Δ1). reflexivity. rewrite H2. clear H2.
      apply list_exch_RI. pose (KS_hpadm_list_exch_R0 _ _ x3 J3 _ J4). destruct s. exists x4.
      assert (ImpRRule [(Γ2 ++ A0 :: x0 ++ B :: Γ1, Δ2 ++ B0 :: Δ3)] ((Γ2 ++ x0) ++ B :: Γ1, Δ0 ++ Δ1)).
      rewrite <- H3. rewrite <- app_assoc. apply ImpRRule_I.
      assert (existsT2 (x3: derrec KS_rules (fun _ : Seq => False)
      ((Γ2 ++ x0) ++ B :: Γ1, Δ0 ++ Δ1)), derrec_height x3 <= S (dersrec_height d)).
      apply ImpR in H2.
      pose (dlCons x2 DersNilF). pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ A0 :: x0 ++ B :: Γ1, Δ2 ++ B0 :: Δ3)]) ((Γ2 ++ x0) ++ B :: Γ1, Δ0 ++ Δ1) H2 d0).
      exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
      destruct X. exists x5. simpl. split. lia. lia.
    + destruct x0.
      { simpl in e1. subst. assert (ImpLRule [(Γ0 ++ A0 :: Γ1, A :: Δ2 ++ B0 :: Δ3) ; (Γ0 ++ A0 :: B :: Γ1, Δ2 ++ B0 :: Δ3)]
        ((Γ0 ++ []) ++ A0 :: A --> B :: Γ1, Δ2 ++ B0 :: Δ3)). rewrite app_nil_r. assert (Γ0 ++ A0 :: Γ1 = (Γ0 ++ [A0]) ++ Γ1).
        rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert (Γ0 ++ A0 :: B :: Γ1 = (Γ0 ++ [A0]) ++ B :: Γ1). rewrite <- app_assoc. reflexivity.
        rewrite H0. clear H0. assert (Γ0 ++ A0 :: A --> B :: Γ1 = (Γ0 ++ [A0]) ++ A --> B :: Γ1). rewrite <- app_assoc. reflexivity.
        rewrite H0. clear H0. assert (Δ2 ++ B0 :: Δ3 = [] ++ Δ2 ++ B0 :: Δ3).
        reflexivity. rewrite H0. clear H0. assert (A :: [] ++ Δ2 ++ B0 :: Δ3 = [] ++ A :: Δ2 ++ B0 :: Δ3).
        reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
        assert (J1: derrec_height x  < S (dersrec_height d)). lia.
        assert (J2: derrec_height x = derrec_height x). reflexivity.
        pose (IH (derrec_height x) J1 _ x J2). destruct p. clear s.
        pose (s0 _ _ H0). repeat destruct s. clear s0. destruct p.
        assert (ImpRRule [(Γ0 ++ A0 :: Γ1, A :: Δ2 ++ B0 :: Δ3)] (Γ0 ++ Γ1, A :: Δ0 ++ Δ1)).
        rewrite <- H3. assert (A :: Δ2 ++ B0 :: Δ3 = (A :: Δ2) ++ B0 :: Δ3). reflexivity.
        rewrite H1. clear H1. assert (A :: Δ2 ++ A0 --> B0 :: Δ3 = (A :: Δ2) ++ A0 --> B0 :: Δ3). reflexivity.
        rewrite H1. clear H1. apply ImpRRule_I.
        assert (existsT2 (x3: derrec KS_rules (fun _ : Seq => False)
        (Γ0 ++ Γ1, A :: Δ0 ++ Δ1)), derrec_height x3 <= S (dersrec_height d)).
        apply ImpR in H1.
        pose (dlCons x0 DersNilF). pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ0 ++ A0 :: Γ1, A :: Δ2 ++ B0 :: Δ3)]) (Γ0 ++ Γ1, A :: Δ0 ++ Δ1) H1 d0).
        exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
        destruct X.
        assert (J3: derrec_height x2 = derrec_height x2). reflexivity.
        assert (J4: list_exch_R (Γ0 ++ Γ1, A :: Δ0 ++ Δ1) (Γ0 ++ Γ1, Δ0 ++ A :: Δ1)).
        assert (A :: Δ0 ++ Δ1 = [] ++ [A] ++ Δ0 ++ [] ++ Δ1). reflexivity. rewrite H2. clear H2.
        assert (Δ0 ++ A :: Δ1 = [] ++ [] ++ Δ0 ++ [A] ++ Δ1). reflexivity. rewrite H2. clear H2.
        apply list_exch_RI. pose (KS_hpadm_list_exch_R0 _ _ x2 J3 _ J4). destruct s. exists x3.
        assert (ImpRRule [(Γ0 ++ A0 :: B :: Γ1, Δ2 ++ B0 :: Δ3)] (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)).
        rewrite <- H3. apply ImpRRule_I.
        assert (existsT2 (x3: derrec KS_rules (fun _ : Seq => False)
        (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)), derrec_height x3 <= S (dersrec_height d)).
        apply ImpR in H2.
        pose (dlCons x1 DersNilF). pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ0 ++ A0 :: B :: Γ1, Δ2 ++ B0 :: Δ3)]) (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) H2 d0).
        exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
        destruct X. exists x4. simpl. split. lia. lia. }
        { inversion e1. subst. assert (ImpLRule [(Γ0 ++ x0 ++ A0 :: Γ3, A :: Δ2 ++ B0 :: Δ3) ; (Γ0 ++ B :: x0 ++ A0 :: Γ3, Δ2 ++ B0 :: Δ3)]
          ((Γ0 ++ A --> B :: x0) ++ A0 :: Γ3, Δ2 ++ B0 :: Δ3)). rewrite <- app_assoc.
          assert (Δ2 ++ B0 :: Δ3 = [] ++ Δ2 ++ B0 :: Δ3). reflexivity. rewrite H0. clear H0.
          assert (A :: [] ++ Δ2 ++ B0 :: Δ3 = [] ++ A :: Δ2 ++ B0 :: Δ3). reflexivity. rewrite H0.
          clear H0. apply ImpLRule_I.
          assert (J1: derrec_height x  < S (dersrec_height d)). lia.
          assert (J2: derrec_height x = derrec_height x). reflexivity.
          pose (IH (derrec_height x) J1 _ x J2). destruct p. clear s.
          pose (s0 _ _ H0). repeat destruct s. clear s0. destruct p.
          assert (ImpRRule [(Γ0 ++ x0 ++ A0 :: Γ3, A :: Δ2 ++ B0 :: Δ3)] (Γ0 ++ x0 ++ Γ3, A :: Δ0 ++ Δ1)).
          rewrite <- H3. assert (A :: Δ2 ++ B0 :: Δ3 = (A :: Δ2) ++ B0 :: Δ3). reflexivity.
          rewrite H1. clear H1. assert (A :: Δ2 ++ A0 --> B0 :: Δ3 = (A :: Δ2) ++ A0 --> B0 :: Δ3). reflexivity.
          rewrite H1. clear H1. assert (Γ0 ++ x0 ++ A0 :: Γ3 = (Γ0 ++ x0) ++ A0 :: Γ3). rewrite <- app_assoc.
          reflexivity. rewrite H1. clear H1. assert (Γ0 ++ x0 ++ Γ3 = (Γ0 ++ x0) ++ Γ3). rewrite <- app_assoc.
          reflexivity. rewrite H1. clear H1. apply ImpRRule_I.
          assert (existsT2 (x3: derrec KS_rules (fun _ : Seq => False)
          (Γ0 ++ x0 ++ Γ3, A :: Δ0 ++ Δ1)), derrec_height x3 <= S (dersrec_height d)).
          apply ImpR in H1.
          pose (dlCons x1 DersNilF). pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
          (ps:=[(Γ0 ++ x0 ++ A0 :: Γ3, A :: Δ2 ++ B0 :: Δ3)]) (Γ0 ++ x0 ++ Γ3, A :: Δ0 ++ Δ1) H1 d0).
          exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
          destruct X.
          assert (J3: derrec_height x3 = derrec_height x3). reflexivity.
          assert (J4: list_exch_R (Γ0 ++ x0 ++ Γ3, A :: Δ0 ++ Δ1) (Γ0 ++ x0 ++ Γ3, Δ0 ++ A :: Δ1)).
          assert (A :: Δ0 ++ Δ1 = [] ++ [A] ++ Δ0 ++ [] ++ Δ1). reflexivity. rewrite H2. clear H2.
          assert (Δ0 ++ A :: Δ1 = [] ++ [] ++ Δ0 ++ [A] ++ Δ1). reflexivity. rewrite H2. clear H2.
          apply list_exch_RI. pose (KS_hpadm_list_exch_R0 _ _ x3 J3 _ J4). destruct s. exists x4.
          assert (ImpRRule [(Γ0 ++ B :: x0 ++ A0 :: Γ3, Δ2 ++ B0 :: Δ3)] (Γ0 ++ B :: x0 ++ Γ3, Δ0 ++ Δ1)).
          rewrite <- H3. assert (Γ0 ++ B :: x0 ++ A0 :: Γ3 = (Γ0 ++ B :: x0) ++ A0 :: Γ3). rewrite <- app_assoc.
          reflexivity. rewrite H2. clear H2. assert (Γ0 ++ B :: x0 ++ Γ3 = (Γ0 ++ B :: x0) ++ Γ3). rewrite <- app_assoc.
          reflexivity. rewrite H2. clear H2. apply ImpRRule_I.
          assert (existsT2 (x3: derrec KS_rules (fun _ : Seq => False)
          (Γ0 ++ B :: x0 ++ Γ3, Δ0 ++ Δ1)), derrec_height x3 <= S (dersrec_height d)).
          apply ImpR in H2.
          pose (dlCons x2 DersNilF). pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
          (ps:=[(Γ0 ++ B :: x0 ++ A0 :: Γ3, Δ2 ++ B0 :: Δ3)]) (Γ0 ++ B :: x0 ++ Γ3, Δ0 ++ Δ1) H2 d0).
          exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
          destruct X. exists x5. simpl. split. lia. lia. }
  (* ImpL *)
  * inversion H. subst.
    apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
    + inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
      assert (J1: list_exch_R (Γ2 ++ Γ3, Δ2 ++ A0 :: Δ3) (Γ2 ++ Γ3, A0 :: Δ0 ++ Δ1)).
      assert (Δ2 ++ A0 :: Δ3 = [] ++ [] ++ Δ2 ++ [A0] ++ Δ3). reflexivity.
      rewrite H0. clear H0.
      assert (A0 :: Δ0 ++ Δ1 = [] ++ [A0] ++ Δ2 ++ [] ++ Δ3). simpl. rewrite H3. reflexivity.
      rewrite H0. clear H0. apply list_exch_RI.
      assert (J20: derrec_height x0 = derrec_height x0). reflexivity.
      pose (KS_hpadm_list_exch_R0 _ _ x0 J20 _ J1). destruct s.
      assert (J2: list_exch_R (Γ2 ++ Γ3, A0 :: Δ0 ++ Δ1) (Γ2 ++ Γ3, Δ0 ++ A0 :: Δ1)).
      assert (A0 :: Δ0 ++ Δ1 = [] ++ [A0] ++ Δ0 ++ [] ++ Δ1).
      reflexivity. assert (Δ0 ++ A0 :: Δ1 = [] ++ [] ++ Δ0 ++ [A0] ++ Δ1).
      reflexivity. rewrite H1. rewrite H0. clear H1. clear H0. apply list_exch_RI.
      assert (J21: derrec_height x2 = derrec_height x2). reflexivity.
      pose (KS_hpadm_list_exch_R0 _ _ x2 J21 _ J2). destruct s. exists x3.
      assert (existsT2 (x4: derrec KS_rules (fun _ : Seq => False) (Γ2 ++ B0 :: Γ3, Δ0 ++ Δ1)),
      derrec_height x4 = derrec_height x1). rewrite <- H3. exists x1. reflexivity. destruct X. exists x4. split.
       simpl. lia. simpl. lia.
    + destruct x.
      { simpl in e0. inversion e0. simpl. rewrite app_nil_r. subst.
        assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
        assert (J1: list_exch_R (Γ2 ++ Γ1, Δ2 ++ A :: Δ3) (Γ2 ++ Γ1, A :: Δ0 ++ Δ1)).
        assert (Δ2 ++ A :: Δ3 = [] ++ [] ++ Δ2 ++ [A] ++ Δ3). reflexivity.
        rewrite H0. clear H0.
        assert (A :: Δ0 ++ Δ1 = [] ++ [A] ++ Δ2 ++ [] ++ Δ3). simpl. rewrite H3. reflexivity.
        rewrite H0. clear H0. apply list_exch_RI.
        assert (J20: derrec_height x = derrec_height x). reflexivity.
        pose (KS_hpadm_list_exch_R0 _ _ x J20 _ J1). destruct s.
        assert (J2: list_exch_R (Γ2 ++ Γ1, A :: Δ0 ++ Δ1) (Γ2 ++ Γ1, Δ0 ++ A :: Δ1)).
        assert (A :: Δ0 ++ Δ1 = [] ++ [A] ++ Δ0 ++ [] ++ Δ1).
        reflexivity. assert (Δ0 ++ A :: Δ1 = [] ++ [] ++ Δ0 ++ [A] ++ Δ1).
        reflexivity. rewrite H1. rewrite H0. clear H1. clear H0. apply list_exch_RI.
        assert (J21: derrec_height x1 = derrec_height x1). reflexivity.
        pose (KS_hpadm_list_exch_R0 _ _ x1 J21 _ J2). destruct s. exists x2.
        assert (existsT2 (x3: derrec KS_rules (fun _ : Seq => False) (Γ2 ++ B :: Γ1, Δ0 ++ Δ1)),
        derrec_height x3 = derrec_height x0). rewrite <- H3. exists x0. reflexivity. destruct X. exists x3. split.
        simpl. lia. simpl. lia. }
      { inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
        assert (J1: list_exch_R (Γ2 ++ x ++ A --> B :: Γ1, Δ2 ++ A0 :: Δ3) (Γ2 ++ x ++ A --> B :: Γ1, A0 :: Δ0 ++ Δ1)).
        assert (Δ2 ++ A0 :: Δ3 = [] ++ [] ++ Δ2 ++ [A0] ++ Δ3). reflexivity.
        rewrite H0. clear H0.
        assert (A0 :: Δ0 ++ Δ1 = [] ++ [A0] ++ Δ2 ++ [] ++ Δ3). simpl. rewrite H3. reflexivity.
        rewrite H0. clear H0. apply list_exch_RI.
        assert (J20: derrec_height x0 = derrec_height x0). reflexivity.
        pose (KS_hpadm_list_exch_R0 _ _ x0 J20 _ J1). destruct s. simpl in IH. simpl.
        assert (J2: derrec_height x2 < S (dersrec_height d)). lia.
        assert (J3: derrec_height x2 = derrec_height x2). reflexivity.
        assert (J4: ImpLRule [(Γ2 ++ x ++ Γ1, A0 :: Δ0 ++ A :: Δ1); (Γ2 ++ x ++ B :: Γ1, A0 :: Δ0 ++ Δ1)]
        (Γ2 ++ x ++ A --> B :: Γ1, A0 :: Δ0 ++ Δ1)).
        assert (A0 :: Δ0 ++ A :: Δ1 = (A0 :: Δ0) ++ A :: Δ1). reflexivity. rewrite H0. clear H0.
        assert (A0 :: Δ0 ++ Δ1 = (A0 :: Δ0) ++ Δ1). reflexivity. rewrite H0. clear H0.
        assert (Γ2 ++ x ++ B :: Γ1 = (Γ2 ++ x) ++ B :: Γ1). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0.
        assert (Γ2 ++ x ++ A --> B :: Γ1 = (Γ2 ++ x) ++ A --> B :: Γ1). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0.
        assert (Γ2 ++ x ++ Γ1 = (Γ2 ++ x) ++ Γ1). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
        pose (IH _ J2 _ _ J3). destruct p. pose (s0 _ _ J4). clear s. destruct s1. clear s0. destruct s.
        destruct p.
        assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
        assert (J7: ImpLRule [(Γ2 ++ B0 :: x ++ Γ1, Δ0 ++ A :: Δ1); (Γ2 ++ B0 :: x ++ B :: Γ1, Δ0 ++ Δ1)]
        (Γ2 ++ B0 :: x ++ A --> B :: Γ1, Δ2 ++ Δ3)). rewrite H3.
        assert (Γ2 ++ B0 :: x ++ Γ1 = (Γ2 ++ B0 :: x) ++ Γ1). rewrite <- app_assoc. reflexivity.
        rewrite H0. clear H0.
        assert (Γ2 ++ B0 :: x ++ B :: Γ1 = (Γ2 ++ B0 :: x) ++ B :: Γ1). rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0.
        assert (Γ2 ++ B0 :: x ++ A --> B :: Γ1 = (Γ2 ++ B0 :: x) ++ A --> B :: Γ1). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
        pose (IH _ J5 _ _ J6). destruct p. pose (s0 _ _ J7). clear s. destruct s1. clear s0. destruct s.
        destruct p.
        assert (existsT2 (x7 : derrec KS_rules (fun _ : Seq => False)
        ((Γ2 ++ A0 --> B0 :: x) ++ Γ1, Δ0 ++ A :: Δ1)), derrec_height x7 <= S (dersrec_height d)).
        assert (ImpLRule [(Γ2 ++ x ++ Γ1, A0 :: Δ0 ++ A :: Δ1); (Γ2 ++ B0 :: x ++ Γ1, Δ0 ++ A :: Δ1)]
        ((Γ2 ++ A0 --> B0 :: x) ++ Γ1, Δ0 ++ A :: Δ1)). rewrite <- app_assoc.
        assert (A0 :: Δ0 ++ A :: Δ1 = [] ++ A0 :: Δ0 ++ A :: Δ1). reflexivity. rewrite H0. clear H0.
        assert (Δ0 ++ A :: Δ1 = [] ++ Δ0 ++ A :: Δ1). reflexivity. rewrite H0. clear H0. repeat rewrite <- app_assoc.
        apply ImpLRule_I. apply ImpL in H0.
        pose (dlCons x5 DersNilF). pose (dlCons x3 d0).
        pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ x ++ Γ1, A0 :: Δ0 ++ A :: Δ1); (Γ2 ++ B0 :: x ++ Γ1, Δ0 ++ A :: Δ1)])
        ((Γ2 ++ A0 --> B0 :: x) ++ Γ1, Δ0 ++ A :: Δ1) H0 d1).
        exists d2. simpl. rewrite dersrec_height_nil. lia. reflexivity.
        destruct X. exists x7.
        assert (existsT2 (x8 : derrec KS_rules (fun _ : Seq => False)
        ((Γ2 ++ A0 --> B0 :: x) ++ B :: Γ1, Δ0 ++ Δ1)), derrec_height x8 <= S (dersrec_height d)).
        assert (ImpLRule [(Γ2 ++ x ++ B :: Γ1, A0 :: Δ0 ++ Δ1); (Γ2 ++ B0 :: x ++ B :: Γ1, Δ0 ++ Δ1)]
        ((Γ2 ++ A0 --> B0 :: x) ++ B :: Γ1, Δ0 ++ Δ1)). rewrite <- app_assoc.
        assert (Δ0 ++ Δ1 = [] ++ Δ0 ++ Δ1). reflexivity. rewrite H0. clear H0.
        assert (A0 :: [] ++ Δ0 ++ Δ1 = [] ++ A0 :: Δ0 ++ Δ1). reflexivity. rewrite H0. clear H0.
        apply ImpLRule_I. apply ImpL in H0.
        pose (dlCons x6 DersNilF). pose (dlCons x4 d0).
        pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ x ++ B :: Γ1, A0 :: Δ0 ++ Δ1); (Γ2 ++ B0 :: x ++ B :: Γ1, Δ0 ++ Δ1)])
        ((Γ2 ++ A0 --> B0 :: x) ++ B :: Γ1, Δ0 ++ Δ1) H0 d1).
        exists d2. simpl. rewrite dersrec_height_nil. lia. reflexivity.
        destruct X. exists x8. split. lia. lia. }
    + destruct x.
      { simpl in e0. inversion e0. simpl. subst.
        assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
        assert (J1: list_exch_R ((Γ0 ++ []) ++ Γ3, Δ2 ++ A0 :: Δ3) (Γ0 ++ Γ3, A0 :: Δ0 ++ Δ1)).
        rewrite app_nil_r.
        assert (Δ2 ++ A0 :: Δ3 = [] ++ [] ++ Δ2 ++ [A0] ++ Δ3). reflexivity.
        rewrite H0. clear H0.
        assert (A0 :: Δ0 ++ Δ1 = [] ++ [A0] ++ Δ2 ++ [] ++ Δ3). simpl. rewrite H3. reflexivity.
        rewrite H0. clear H0. apply list_exch_RI.
        assert (J20: derrec_height x = derrec_height x). reflexivity.
        pose (KS_hpadm_list_exch_R0 _ _ x J20 _ J1). destruct s.
        assert (J2: list_exch_R (Γ0 ++ Γ3, A0 :: Δ0 ++ Δ1) (Γ0 ++ Γ3, Δ0 ++ A0 :: Δ1)).
        assert (A0 :: Δ0 ++ Δ1 = [] ++ [A0] ++ Δ0 ++ [] ++ Δ1).
        reflexivity. assert (Δ0 ++ A0 :: Δ1 = [] ++ [] ++ Δ0 ++ [A0] ++ Δ1).
        reflexivity. rewrite H1. rewrite H0. clear H1. clear H0. apply list_exch_RI.
        assert (J21: derrec_height x1 = derrec_height x1). reflexivity.
        pose (KS_hpadm_list_exch_R0 _ _ x1 J21 _ J2). destruct s. exists x2.
        assert (existsT2 (x3: derrec KS_rules (fun _ : Seq => False) (Γ0 ++ B0 :: Γ3, Δ0 ++ Δ1)),
        derrec_height x3 = derrec_height x0). rewrite <- H3.
        assert (Γ0 ++ B0 :: Γ3 = (Γ0 ++ []) ++ B0 :: Γ3). rewrite app_nil_r. reflexivity.
        rewrite H0. exists x0. reflexivity. destruct X. exists x3. split.
        simpl. lia. simpl. lia. }
      { inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
        assert (J1: list_exch_R ((Γ0 ++ A --> B :: x) ++ Γ3, Δ2 ++ A0 :: Δ3) (Γ0 ++ A --> B :: x ++ Γ3, A0 :: Δ0 ++ Δ1)).
        assert (Δ2 ++ A0 :: Δ3 = [] ++ [] ++ Δ2 ++ [A0] ++ Δ3). reflexivity.
        rewrite H0. clear H0. rewrite <- app_assoc.
        assert (A0 :: Δ0 ++ Δ1 = [] ++ [A0] ++ Δ2 ++ [] ++ Δ3). simpl. rewrite H3. reflexivity.
        rewrite H0. clear H0. apply list_exch_RI.
        assert (J20: derrec_height x0 = derrec_height x0). reflexivity.
        pose (KS_hpadm_list_exch_R0 _ _ x0 J20 _ J1). destruct s. simpl in IH. simpl.
        assert (J2: derrec_height x2 < S (dersrec_height d)). lia.
        assert (J3: derrec_height x2 = derrec_height x2). reflexivity.
        assert (J4: ImpLRule [(Γ0 ++ x ++ Γ3, A0 :: Δ0 ++ A :: Δ1); (Γ0 ++ B :: x ++ Γ3, A0 :: Δ0 ++ Δ1)]
        (Γ0 ++ A --> B :: x ++ Γ3, A0 :: Δ0 ++ Δ1)).
        assert (A0 :: Δ0 ++ A :: Δ1 = (A0 :: Δ0) ++ A :: Δ1). reflexivity. rewrite H0. clear H0.
        assert (A0 :: Δ0 ++ Δ1 = (A0 :: Δ0) ++ Δ1). reflexivity. rewrite H0. clear H0.
        apply ImpLRule_I.
        pose (IH _ J2 _ _ J3). destruct p. pose (s0 _ _ J4). clear s. destruct s1. clear s0. destruct s.
        destruct p.
        assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
        assert (J7: ImpLRule [(Γ0 ++ x ++ B0 :: Γ3, Δ0 ++ A :: Δ1); (Γ0 ++ B :: x ++ B0 :: Γ3, Δ0 ++ Δ1)]
        ((Γ0 ++ A --> B :: x) ++ B0 :: Γ3, Δ2 ++ Δ3)). rewrite H3. rewrite <- app_assoc.
        apply ImpLRule_I.  pose (IH _ J5 _ _ J6). destruct p. pose (s0 _ _ J7). clear s.
        destruct s1. clear s0. destruct s. destruct p.
        assert (existsT2 (x7 : derrec KS_rules (fun _ : Seq => False)
        (Γ0 ++ x ++ A0 --> B0 :: Γ3, Δ0 ++ A :: Δ1)), derrec_height x7 <= S (dersrec_height d)).
        assert (ImpLRule [(Γ0 ++ x ++ Γ3, A0 :: Δ0 ++ A :: Δ1); (Γ0 ++ x ++ B0 :: Γ3, Δ0 ++ A :: Δ1)]
        (Γ0 ++ x ++ A0 --> B0 :: Γ3, Δ0 ++ A :: Δ1)).
        assert (A0 :: Δ0 ++ A :: Δ1 = [] ++ A0 :: Δ0 ++ A :: Δ1). reflexivity. rewrite H0. clear H0.
        assert (Δ0 ++ A :: Δ1 = [] ++ Δ0 ++ A :: Δ1). reflexivity. rewrite H0. clear H0.
        assert (Γ0 ++ x ++ Γ3 = (Γ0 ++ x) ++ Γ3). rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert (Γ0 ++ x ++ B0 :: Γ3 = (Γ0 ++ x) ++ B0 :: Γ3). rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert (Γ0 ++ x ++ A0 --> B0 :: Γ3 = (Γ0 ++ x) ++ A0 --> B0 :: Γ3). rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        apply ImpLRule_I. apply ImpL in H0.
        pose (dlCons x5 DersNilF). pose (dlCons x3 d0).
        pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ0 ++ x ++ Γ3, A0 :: Δ0 ++ A :: Δ1); (Γ0 ++ x ++ B0 :: Γ3, Δ0 ++ A :: Δ1)])
        (Γ0 ++ x ++ A0 --> B0 :: Γ3, Δ0 ++ A :: Δ1) H0 d1).
        exists d2. simpl. rewrite dersrec_height_nil. lia. reflexivity.
        destruct X. exists x7.
        assert (existsT2 (x8 : derrec KS_rules (fun _ : Seq => False)
        (Γ0 ++ B :: x ++ A0 --> B0 :: Γ3, Δ0 ++ Δ1)), derrec_height x8 <= S (dersrec_height d)).
        assert (ImpLRule [(Γ0 ++ B :: x ++ Γ3, A0 :: Δ0 ++ Δ1); (Γ0 ++ B :: x ++ B0 :: Γ3, Δ0 ++ Δ1)]
        (Γ0 ++ B :: x ++ A0 --> B0 :: Γ3, Δ0 ++ Δ1)).
        assert (Δ0 ++ Δ1 = [] ++ Δ0 ++ Δ1). reflexivity. rewrite H0. clear H0.
        assert (A0 :: [] ++ Δ0 ++ Δ1 = [] ++ A0 :: Δ0 ++ Δ1). reflexivity. rewrite H0. clear H0.
        assert (Γ0 ++ B :: x ++ Γ3 = (Γ0 ++ B :: x) ++ Γ3). rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert (Γ0 ++ B :: x ++ B0 :: Γ3 = (Γ0 ++ B :: x) ++ B0 :: Γ3). rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert (Γ0 ++ B :: x ++ A0 --> B0 :: Γ3 = (Γ0 ++ B :: x) ++ A0 --> B0 :: Γ3). rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        apply ImpLRule_I. apply ImpL in H0.
        pose (dlCons x6 DersNilF). pose (dlCons x4 d0).
        pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ0 ++ B :: x ++ Γ3, A0 :: Δ0 ++ Δ1); (Γ0 ++ B :: x ++ B0 :: Γ3, Δ0 ++ Δ1)])
        (Γ0 ++ B :: x ++ A0 --> B0 :: Γ3, Δ0 ++ Δ1) H0 d1).
        exists d2. simpl. rewrite dersrec_height_nil. lia. reflexivity.
        destruct X. exists x8. split. lia. lia. }
  (* KR *)
  * inversion X. subst. pose (univ_gen_ext_splitR _ _ X0). repeat destruct s. repeat destruct p. subst.
    assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec_height d J0). destruct s.
    assert (KRRule [(unboxed_list (x ++ x0), [A0])] (Γ0 ++ Γ1, Δ0 ++ Δ1)).
    rewrite <- H2. apply KRRule_I ; try assumption. apply univ_gen_ext_combine.
    assumption. apply univ_gen_ext_not_In_delete with (a:=A --> B). intro.
    assert (In (A --> B) (x ++ x0)). apply in_or_app. auto. apply H1 in H0. destruct H0.
    inversion H0. assumption.
    assert (existsT2 (D : derrec KS_rules (fun _ : Seq => False) (Γ0 ++ Γ1, Δ0 ++ Δ1)),
    derrec_height D <= S (dersrec_height d)).
    apply KR in X1.
    pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
    (ps:=[(unboxed_list (x ++ x0), [A0])]) (Γ0 ++ Γ1, Δ0 ++ Δ1) X1 d).
    exists d0. simpl. lia.
    destruct X2.
    assert (J1: derrec_height x2 = derrec_height x2). reflexivity.
    assert (J2: wkn_L B (Γ0 ++ Γ1, Δ0 ++ Δ1) (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)). apply wkn_LI.
    pose (KS_wkn_L _ _ x2 J1 _ _ J2). destruct s.
    assert (J3: wkn_R A (Γ0 ++ Γ1, Δ0 ++ Δ1) (Γ0 ++ Γ1, Δ0 ++ A :: Δ1)). apply wkn_RI.
    pose (KS_wkn_R _ _ x2 J1 _ _ J3). destruct s. exists x4. exists x3. simpl.
    split ; lia. }
Qed.


Theorem ImpR_inv : forall concl prem, (KS_prv concl) ->
                                      (ImpRRule [prem] concl) ->
                                      (KS_prv prem).
Proof.
intros.
assert (J1: derrec_height X = derrec_height X). reflexivity.
pose (ImpR_ImpL_hpinv _ _ X J1). destruct p. pose (s _ H). destruct s1. assumption.
Qed.

Theorem ImpL_inv : forall concl prem1 prem2, (KS_prv concl) ->
                                      (ImpLRule [prem1;prem2] concl) ->
                                      (KS_prv prem1) *
                                      (KS_prv prem2).
Proof.
intros.
assert (J1: derrec_height X = derrec_height X). reflexivity.
pose (ImpR_ImpL_hpinv _ _ X J1). destruct p. pose (s0 _ _ H). repeat destruct s1. auto.
Qed.