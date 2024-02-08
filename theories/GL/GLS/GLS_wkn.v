Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import GLS_calcs.
Require Import GLS_dec.

Set Implicit Arguments.

(* We define the relations which take care of the notion of weakening. *)

Inductive wkn_L (fml : MPropF) : relationT Seq :=
  | wkn_LI Γ0 Γ1 Δ : wkn_L fml
        (Γ0 ++ Γ1, Δ) (Γ0 ++ fml :: Γ1, Δ).

Inductive wkn_R (fml : MPropF) : relationT Seq :=
  | wkn_RI Γ Δ0 Δ1 : wkn_R fml
        (Γ, Δ0 ++ Δ1) (Γ, Δ0 ++ fml :: Δ1).

(* Some lemmas on the preservation of inapplicability of BotL through weakening. *)

Lemma wkn_R_BotL_notapplic : forall s sw A,
    (@wkn_R A s sw) ->
    ((BotLRule [] s) -> False) ->
    ((BotLRule [] sw) -> False).
Proof.
intros s sw A wkn RA RAw. apply RA.
inversion RAw. destruct s. inversion wkn. subst. inversion H3.
subst. apply BotLRule_I.
Qed.

(* The following lemmas make sure that if a rule is applied on a sequent s with
premises ps, then the same rule is applicable on a sequent sw which is a weakened
version of s, with some premises psw that are such that they are either the same premises
(in case the weakened formula is weakened in the rule) or weakened versions of ps. *)

Lemma ImpR_app_wkn_L : forall s sw A ps,
  (@wkn_L A s sw) ->
  (ImpRRule [ps] s) ->
  (existsT2 psw, (ImpRRule [psw] sw) * (@wkn_L A ps psw)).
Proof.
intros s sw A ps wkn RA. inversion RA. inversion wkn. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- exists (Γ2 ++ A0 :: A :: Γ3, Δ0 ++ B :: Δ1). repeat split ; try assumption.
  rewrite cons_single. rewrite cons_single with (v:=A0). rewrite app_assoc. rewrite app_assoc with (l:=Γ2).
  apply wkn_LI.
- exists ((Γ2 ++ A :: x) ++ A0 :: Γ1, Δ0 ++ B :: Δ1). split.
  * assert (Γ2 ++ A :: x ++ Γ1 = (Γ2 ++ A :: x) ++ Γ1). rewrite <- app_assoc. reflexivity.
    rewrite H0. apply ImpRRule_I ; assumption.
  * repeat rewrite <- app_assoc. apply wkn_LI.
- exists (Γ0 ++ A0 :: x ++ A :: Γ3, Δ0 ++ B :: Δ1). split.
  * repeat rewrite <- app_assoc. apply ImpRRule_I ; assumption.
  * rewrite cons_single. rewrite cons_single with (v:=A0). rewrite app_assoc. rewrite app_assoc with (l:=Γ0).
    rewrite app_assoc. rewrite app_assoc with (l:=(Γ0 ++ [A0])). apply wkn_LI.
Qed.

Lemma ImpL_app_wkn_L : forall s sw A ps1 ps2,
  (@wkn_L A s sw) ->
  (ImpLRule [ps1;ps2] s) ->
  (existsT2 psw1 psw2, (ImpLRule [psw1;psw2] sw) *
                                                  (@wkn_L A ps1 psw1) *
                                                  (@wkn_L A ps2 psw2)).
Proof.
intros s sw A ps1 ps2 wkn RA. inversion RA. inversion wkn. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1. repeat destruct s ; destruct p ; subst.
  - exists (Γ2 ++ A :: Γ1, Δ0 ++ A0 :: Δ1). exists (Γ2 ++ A :: B :: Γ1, Δ0 ++ Δ1).
    split. split. assert (E1: Γ2 ++ A :: Γ1 = (Γ2 ++ [A]) ++ Γ1). rewrite <- app_assoc.
    simpl. auto. rewrite E1. assert (E2 : Γ2 ++ A :: B :: Γ1 = (Γ2 ++ [A]) ++ B :: Γ1).
    rewrite <- app_assoc. simpl. auto. rewrite E2. assert (E3 : Γ2 ++ A :: A0 --> B :: Γ1 = (Γ2 ++ [A]) ++ A0 --> B :: Γ1).
    rewrite <- app_assoc. simpl. auto. rewrite E3. apply ImpLRule_I.
    apply wkn_LI. apply wkn_LI.
  - exists (Γ2 ++ A :: x ++ Γ1, Δ0 ++ A0 :: Δ1). exists (Γ2 ++ A :: x ++ B :: Γ1, Δ0 ++ Δ1).
    split. split. assert (E1: Γ2 ++ A :: x ++ Γ1 = (Γ2 ++ [A] ++ x) ++ Γ1). rewrite <- app_assoc.
    simpl. auto. rewrite E1. assert (E2 : Γ2 ++ A :: x ++ B :: Γ1 = (Γ2 ++ [A] ++ x) ++ B :: Γ1).
    rewrite <- app_assoc. simpl. auto. rewrite E2.
    assert (E3 : Γ2 ++ A :: x ++ A0 --> B :: Γ1 = (Γ2 ++ [A] ++ x) ++ A0 --> B :: Γ1).
    rewrite <- app_assoc. simpl. auto. rewrite E3. apply ImpLRule_I.
    repeat rewrite <- app_assoc. apply wkn_LI. repeat rewrite <- app_assoc. apply wkn_LI.
  - destruct x ; subst ; repeat rewrite app_nil_r.
    + simpl in e0. subst. exists (Γ0 ++ A :: Γ1, Δ0 ++ A0 :: Δ1). exists (Γ0 ++ A :: B :: Γ1, Δ0 ++ Δ1) .
      split. split. assert (E1: Γ0 ++ A :: Γ1 = (Γ0 ++ [A]) ++ Γ1). rewrite <- app_assoc.
      simpl. auto. rewrite E1. assert (E2 : Γ0 ++ A :: B :: Γ1 = (Γ0 ++ [A]) ++ B :: Γ1).
      rewrite <- app_assoc. simpl. auto. rewrite E2.
      assert (E3 : Γ0 ++ A :: A0 --> B :: Γ1 = (Γ0 ++ [A]) ++ A0 --> B :: Γ1).
      rewrite <- app_assoc. simpl. auto. rewrite E3. apply ImpLRule_I.
      repeat rewrite <- app_assoc. apply wkn_LI. repeat rewrite <- app_assoc. apply wkn_LI.
    + inversion e0. subst. exists (Γ0 ++ x ++ A :: Γ3, Δ0 ++ A0 :: Δ1).
      exists (Γ0 ++ B :: x ++ A :: Γ3, Δ0 ++ Δ1). split. split.
      repeat rewrite <- app_assoc. apply ImpLRule_I.
      assert (Γ0 ++ x ++ Γ3 = (Γ0 ++ x) ++ Γ3). rewrite <- app_assoc. reflexivity.
      rewrite H0. assert (Γ0 ++ x ++ A :: Γ3 = (Γ0 ++ x) ++ A :: Γ3). rewrite <- app_assoc. reflexivity.
      rewrite H1. apply wkn_LI.
      assert (Γ0 ++ B :: x ++ Γ3 = (Γ0 ++ B :: x) ++ Γ3). rewrite <- app_assoc. reflexivity.
      rewrite H0. assert (Γ0 ++ B :: x ++ A :: Γ3 = (Γ0 ++ B :: x) ++ A :: Γ3). rewrite <- app_assoc. reflexivity.
      rewrite H1. apply wkn_LI.
Qed.

Lemma GLR_app_wkn_L : forall s sw A ps,
  (@wkn_L A s sw) ->
  (GLRRule [ps] s) ->
  ((GLRRule [ps] sw) +
   (existsT2 psw1 psw2, (GLRRule [psw2] sw) * (@wkn_L (unBox_formula A) ps psw1) * (@wkn_L A psw1 psw2))).
Proof.
intros s sw A ps wkn RA. inversion RA. inversion wkn. rewrite <- H1 in H2.
inversion H2. subst. destruct (dec_is_boxedT A).
  * right. apply univ_gen_ext_splitR in X. destruct X. destruct s. repeat destruct p.
    subst. exists (((XBoxed_list x) ++ (unBox_formula A) :: (XBoxed_list x0)) ++ [Box A0], [A0]).
    exists (XBoxed_list (x ++ A :: x0) ++ [Box A0], [A0]). split. split.
    + apply GLRRule_I. intro. intros. apply in_app_or in H. destruct H. apply H0. apply in_or_app. auto.
      inversion H. subst. assumption. apply H0. apply in_or_app. auto. apply univ_gen_ext_combine.
      assumption. apply univ_gen_ext_cons. assumption.
    + rewrite XBox_app_distrib. repeat rewrite <- app_assoc. apply wkn_LI.
    + rewrite XBox_app_distrib. simpl.
      assert (E1: (XBoxed_list x ++ unBox_formula A :: XBoxed_list x0) ++ [Box A0] =
      (XBoxed_list x ++ [unBox_formula A]) ++ XBoxed_list x0 ++ [Box A0]). repeat rewrite <- app_assoc.
      simpl. reflexivity. rewrite E1.
      assert (E2: (XBoxed_list x ++ unBox_formula A :: A :: XBoxed_list x0) ++ [Box A0] =
      (XBoxed_list x ++ [unBox_formula A]) ++ A :: XBoxed_list x0 ++ [Box A0]). repeat rewrite <- app_assoc.
      simpl. reflexivity. rewrite E2.
      apply wkn_LI.
  * left. apply GLRRule_I.
    + assumption.
    + apply univ_gen_ext_splitR in X. destruct X. destruct s. repeat destruct p.
      subst. apply univ_gen_ext_combine. assumption. apply univ_gen_ext_extra. assumption.
      assumption.
Qed.

Lemma ImpR_app_wkn_R : forall s sw A ps,
  (@wkn_R A s sw) ->
  (ImpRRule [ps] s) ->
  ((existsT2 psw, (ImpRRule [psw] sw) * (@wkn_R A ps psw))).
Proof.
intros s sw A ps wkn RA. inversion RA. inversion wkn. subst. inversion H.
subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
  - exists (Γ0 ++ A0 :: Γ1, Δ2 ++ A :: B :: Δ1). split.
    assert (E1: Δ2 ++ A :: B :: Δ1 = (Δ2 ++ [A]) ++ B :: Δ1). rewrite <- app_assoc.
    simpl. auto. rewrite E1. assert (E3 : Δ2 ++ A :: A0 --> B :: Δ1 = (Δ2 ++ [A]) ++ A0 --> B :: Δ1).
    rewrite <- app_assoc. simpl. auto. rewrite E3. apply ImpRRule_I.
    apply wkn_RI.
  - exists (Γ0 ++ A0 :: Γ1, Δ2 ++ A :: x ++ B :: Δ1).
    split. assert (E1: Δ2 ++ A :: x  ++ B :: Δ1 = (Δ2 ++ [A] ++ x) ++ B :: Δ1). rewrite <- app_assoc.
    simpl. auto. rewrite E1. assert (E2 : Δ2 ++ A :: x ++ A0 --> B :: Δ1 = (Δ2 ++ [A] ++ x) ++ A0 --> B :: Δ1).
    rewrite <- app_assoc. simpl. auto. rewrite E2. apply ImpRRule_I.
    repeat rewrite <- app_assoc. apply wkn_RI.
  - destruct x ; subst ; repeat rewrite app_nil_r.
    + simpl in e0. subst. exists (Γ0 ++ A0 :: Γ1, Δ0 ++ A :: B :: Δ1).
      split. assert (E1: Δ0 ++ A :: B :: Δ1 = (Δ0 ++ [A]) ++ B :: Δ1). rewrite <- app_assoc.
      simpl. auto. rewrite E1.
      assert (E3 : Δ0 ++ A :: A0 --> B :: Δ1 = (Δ0 ++ [A]) ++ A0 --> B :: Δ1).
      rewrite <- app_assoc. simpl. auto. rewrite E3. apply ImpRRule_I.
      repeat rewrite <- app_assoc. apply wkn_RI.
    + inversion e0. subst. exists (Γ0 ++ A0 :: Γ1, Δ0 ++ B :: x ++ A :: Δ3).
      split. repeat rewrite <- app_assoc. apply ImpRRule_I.
      assert (Δ0 ++ B :: x ++ Δ3 = (Δ0 ++ B :: x) ++ Δ3). rewrite <- app_assoc. reflexivity.
      rewrite H0. assert (Δ0 ++ B :: x ++ A :: Δ3 = (Δ0 ++ B :: x) ++ A :: Δ3). rewrite <- app_assoc. reflexivity.
      rewrite H1. apply wkn_RI.
Qed.

Lemma ImpL_app_wkn_R : forall s sw A ps1 ps2,
  (@wkn_R A s sw) ->
  (ImpLRule [ps1;ps2] s) ->
  (existsT2 psw1 psw2, (ImpLRule [psw1;psw2] sw) * (@wkn_R A ps1 psw1) *
                                                   (@wkn_R A ps2 psw2)).
Proof.
intros s sw A ps1 ps2 wkn RA. inversion RA. inversion wkn. subst.
inversion H. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s.
- destruct p. subst. exists (Γ0 ++ Γ1, Δ2 ++ A0 :: A :: Δ3).
  exists (Γ0 ++ B :: Γ1, Δ2 ++ A :: Δ3). repeat split.
  assert (E1: Δ2 ++ A0 :: A :: Δ3 = (Δ2 ++ [A0]) ++ A :: Δ3).
  repeat rewrite <- app_assoc. simpl. reflexivity. rewrite E1.
  assert (E2: Δ2 ++ A0 :: Δ3 = (Δ2 ++ [A0]) ++ Δ3).
  repeat rewrite <- app_assoc. simpl. reflexivity. rewrite E2. apply wkn_RI.
- destruct p. subst. exists (Γ0 ++ Γ1, (Δ2 ++ A :: x) ++ A0 :: Δ1). exists (Γ0 ++ B :: Γ1, (Δ2 ++ A :: x) ++ Δ1).
  split. split.
  * assert (E: Δ2 ++ A :: x ++ Δ1 = (Δ2 ++ A :: x) ++ Δ1). rewrite <- app_assoc. simpl. reflexivity.
    rewrite E. apply ImpLRule_I ; assumption.
  * repeat rewrite <- app_assoc. simpl. apply wkn_RI.
  * repeat rewrite <- app_assoc. simpl. apply wkn_RI.
- destruct p. subst. exists  (Γ0 ++ Γ1, Δ0 ++ A0 :: x ++ A :: Δ3).
  exists (Γ0 ++ B :: Γ1, Δ0 ++ x ++ A :: Δ3). repeat split.
  * rewrite <- app_assoc. apply ImpLRule_I ; assumption.
  * assert (E1: Δ0 ++ A0 :: x ++ Δ3 = (Δ0 ++ A0 :: x) ++ Δ3). rewrite <- app_assoc. simpl. reflexivity.
    rewrite E1.
    assert (E2: Δ0 ++ A0 :: x ++ A :: Δ3 = (Δ0 ++ A0 :: x) ++ A :: Δ3). rewrite <- app_assoc. simpl. reflexivity.
    rewrite E2. apply wkn_RI.
  * rewrite app_assoc with (l:=Δ0). apply wkn_RI.
Qed.

Lemma GLR_app_wkn_R : forall s sw A ps,
  (@wkn_R A s sw) ->
  (GLRRule [ps] s) ->
  (GLRRule [ps] sw).
Proof.
intros s sw A ps wkn RA. inversion RA. inversion wkn. rewrite <- H1 in H2.
inversion H2. apply app2_find_hole in H6. destruct H6. repeat destruct s0.
- destruct p. subst. assert (Δ2 ++ A :: Box A0 :: Δ1 = (Δ2 ++ [A]) ++ Box A0 :: Δ1).
  rewrite <- app_assoc. simpl. reflexivity. rewrite H. apply GLRRule_I ; assumption.
- destruct p. subst. assert (E: Δ2 ++ A :: x ++ Box A0 :: Δ1 = (Δ2 ++ A :: x) ++ Box A0 :: Δ1).
  repeat rewrite <- app_assoc. simpl. reflexivity. rewrite E.
  apply GLRRule_I ; assumption.
- destruct p. subst. destruct x.
  + rewrite app_nil_r. rewrite app_nil_l in e0. subst. assert (Δ0 ++ A :: Box A0 :: Δ1 = (Δ0 ++ [A]) ++ Box A0 :: Δ1).
    rewrite <- app_assoc. reflexivity. rewrite H. apply GLRRule_I ; assumption.
  + inversion e0. subst. rewrite <- app_assoc. simpl. apply GLRRule_I ; assumption.
Qed.

(* Now we can prove that weakening is height-preserving admissible. *)

Theorem GLS_wkn_L : forall (k : nat) s
        (D0 : GLS_prv s),
        k = (derrec_height D0) ->
          (forall sw A, ((@wkn_L A s sw) ->
          existsT2 (D1 : GLS_prv sw),
          derrec_height D1 <= k)).
Proof.
(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall (s : Seq)
  (D0 : derrec GLS_rules (fun _ : Seq => False) s),
x = derrec_height D0 ->
(forall sw A,
wkn_L A s sw ->
(existsT2
  D1 : derrec GLS_rules
         (fun _ : Seq => False) sw,
  derrec_height D1 <= x)))).
apply s. intros n IH. clear s.
(* Now we do the actual proof-theoretical work. *)
intros s0 D0. remember D0 as D0'. destruct D0.
(* D0 is a leaf *)
- intros hei sw A wkn. inversion f.
(* D0 ends with an application of rule *)
- intros hei sw A wkn. inversion wkn. inversion g.
  (* IdP *)
  * inversion H1. rewrite <- H in H5. inversion H5. apply app2_find_hole in H7.
    destruct H7. assert (DersNil: dersrec GLS_rules (fun _ : Seq => False) []).
    apply dersrec_nil.
    destruct s.
    + destruct s.
      { destruct p. inversion e0. subst. pose (IdPRule_I P (Γ2 ++ [A]) Γ3 Δ0 Δ1). apply IdP in i. rewrite <- app_assoc in i.
        simpl in i. pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
        (ps:=[]) (Γ2 ++ A :: # P :: Γ3, Δ0 ++ # P :: Δ1) i DersNil). exists d0. simpl. repeat rewrite dersrec_height_nil.
        left. reflexivity. reflexivity. }
      { destruct p. destruct x.
        - rewrite app_nil_l in e0. inversion e0. subst.
          pose (IdPRule_I P ((Γ2 ++ []) ++ [A]) Γ3 Δ0 Δ1). apply IdP in i. rewrite <- app_assoc in i. simpl in i.
          pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
          (ps:=[]) ((Γ2 ++ []) ++ A :: # P :: Γ3, Δ0 ++ # P :: Δ1) i DersNil). exists d0. simpl. repeat rewrite dersrec_height_nil.
          left. reflexivity. reflexivity.
        - inversion e0. subst.
          pose (IdPRule_I P Γ2 (x ++ A :: Γ1) Δ0 Δ1). apply IdP in i.
          assert (E0 : Γ2 ++ # P :: x ++ A :: Γ1 = (Γ2 ++ # P :: x) ++ A :: Γ1). rewrite <- app_assoc. reflexivity.
          rewrite E0 in i.
          pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
          (ps:=[]) ((Γ2 ++ # P :: x) ++ A :: Γ1, Δ0 ++ # P :: Δ1) i DersNil).
          exists d0. simpl. repeat rewrite dersrec_height_nil.
          left. reflexivity. reflexivity. }
    + destruct p. subst. pose (IdPRule_I P (Γ0 ++ A :: x) Γ3 Δ0 Δ1). apply IdP in i. rewrite <- app_assoc in i. simpl in i.
      pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
      (ps:=[]) (Γ0 ++ A :: x ++ # P :: Γ3, Δ0 ++ # P :: Δ1) i DersNil).
      exists d0. simpl. repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity.
  (* BotL *)
  * inversion H1. rewrite <- H in H5. inversion H5.
    assert (DersNil: dersrec GLS_rules (fun _ : Seq => False) []).
    apply dersrec_nil.
    apply app2_find_hole in H7. destruct H7. destruct s.
    + destruct s.
      { destruct p. inversion e0. subst.
        pose (BotLRule_I (Γ2 ++ [A]) Γ3 Δ). apply BotL in b. rewrite <- app_assoc in b. simpl in b.
        pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
        (ps:=[]) (Γ2 ++ A :: ⊥ :: Γ3, Δ) b DersNil). exists d0. simpl. repeat rewrite dersrec_height_nil.
        left. reflexivity. reflexivity. }
      { destruct p. destruct x.
        - rewrite app_nil_l in e0. inversion e0. subst.
          pose (BotLRule_I ((Γ2 ++ []) ++ [A]) Γ3 Δ). apply BotL in b. rewrite <- app_assoc in b. simpl in b.
          pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
          (ps:=[]) ((Γ2 ++ []) ++ A :: ⊥ :: Γ3, Δ) b DersNil). exists d0. simpl. repeat rewrite dersrec_height_nil.
          left. reflexivity. reflexivity.
        - inversion e0. subst.
          pose (BotLRule_I Γ2 (x ++ A :: Γ1) Δ). apply BotL in b.
          assert (E0: Γ2 ++ ⊥ :: x ++ A :: Γ1 = (Γ2 ++ ⊥ :: x) ++ A :: Γ1). rewrite <- app_assoc. reflexivity.
          rewrite E0 in b.
          pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
          (ps:=[]) ((Γ2 ++ ⊥ :: x) ++ A :: Γ1, Δ) b DersNil).
          exists d0. simpl. repeat rewrite dersrec_height_nil.
          left. reflexivity. reflexivity. }
    + destruct p. subst. pose (BotLRule_I (Γ0 ++ A :: x) Γ3 Δ). apply BotL in b.
      assert (E0 : (Γ0 ++ A :: x) ++ ⊥ :: Γ3 = Γ0 ++ A :: x ++ ⊥ :: Γ3).
      rewrite <- app_assoc. reflexivity. rewrite E0 in b.
      pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
      (ps:=[]) (Γ0 ++ A :: x ++ ⊥ :: Γ3, Δ) b DersNil). exists d0. simpl.
      repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity.
  (* ImpR *)
  * assert (DersNil: dersrec GLS_rules (fun _ : Seq => False) []).
    apply dersrec_nil.
    inversion H1. subst. inversion H5. subst. pose (ImpR_app_wkn_L wkn H1). destruct s.
    repeat destruct p. remember [(Γ2 ++ A0 :: Γ3, Δ0 ++ B :: Δ1)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst.
    assert (E: derrec_height d < S (derrec_height d)). auto.
    assert (E1: derrec_height d = derrec_height d). auto. simpl in IH.
    rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Nat.max_0_r in IH.
    pose (IH (derrec_height d) E (Γ2 ++ A0 :: Γ3, Δ0 ++ B :: Δ1) d
    E1 x A w).
    destruct s. pose (dlCons x0 d0). apply ImpR in i.
    pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
    (ps:=[x]) (Γ0 ++ A :: Γ1, Δ0 ++ A0 --> B :: Δ1) i).
    pose (d2 d1). exists d3.
    simpl. repeat rewrite dersrec_height_nil. repeat rewrite Nat.max_0_r.
    rewrite <- Nat.succ_le_mono. assumption. reflexivity.
  (* ImpL *)
  * inversion H1. subst. inversion H5. subst. pose (ImpL_app_wkn_L wkn H1). repeat destruct s.
    repeat destruct p. apply ImpL in i.
    pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
    (ps:=[x;x0]) (Γ0 ++ A :: Γ1, Δ0 ++ Δ1) i). subst. simpl.
    remember [(Γ2 ++ Γ3, Δ0 ++ A0 :: Δ1); (Γ2 ++ B :: Γ3, Δ0 ++ Δ1)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst.
    remember [(Γ2 ++ B :: Γ3, Δ0 ++ Δ1)] as ps''. destruct d1. inversion Heqps''.
    inversion Heqps''. simpl. subst. rewrite dersrec_height_nil. simpl in IH.
    rewrite dersrec_height_nil in IH. rewrite Nat.max_0_r. rewrite Nat.max_0_r in IH.
    assert (E1: derrec_height d < S (Init.Nat.max (derrec_height d)(derrec_height d1))).
    apply Nat.lt_succ_r. apply Nat.le_max_l.
    assert (E2: derrec_height d = derrec_height d). auto.
    pose (IH (derrec_height d) E1 (Γ2 ++ Γ3, Δ0 ++ A0 :: Δ1) d E2 x A w0).
    destruct s.
    assert (E3: derrec_height d1 < S (Init.Nat.max (derrec_height d)(derrec_height d1))).
    apply Nat.lt_succ_r. apply Nat.le_max_r.
    assert (E4: derrec_height d1 = derrec_height d1). auto.
    pose (IH (derrec_height d1) E3 (Γ2 ++ B :: Γ3, Δ0 ++ Δ1) d1 E4 x0 A w).
    destruct s.
    pose (dlCons x1 (dlCons x2 d2)). subst. pose (d0 d3). exists d4. simpl. rewrite dersrec_height_nil.
    rewrite Nat.max_0_r. rewrite <- Nat.succ_le_mono. apply Nat.max_le_compat.
    assumption. assumption. reflexivity. reflexivity. reflexivity.
  (* GLR *)
  * inversion X. rewrite <- H4 in X. subst. pose (GLR_app_wkn_L wkn X). destruct s.
    { apply GLR in g0. subst. pose (derI (rules:=GLS_rules)
      (prems:=fun _ : Seq => False) (ps:=[(XBoxed_list BΓ ++ [Box A0], [A0])])
      (Γ0 ++ A :: Γ1, Δ) g0). subst. pose (d0 d). exists d1. simpl. reflexivity. }
    { repeat destruct s. repeat destruct p. apply GLR in g0.
      remember [(XBoxed_list BΓ ++ [Box A0], [A0])] as ps'. destruct d. inversion Heqps'. subst.
      inversion Heqps'. subst. simpl. simpl in IH.
      assert (E1: derrec_height d < S (Init.Nat.max (derrec_height d) (dersrec_height d0))).
      rewrite dersrec_height_nil. rewrite Nat.max_0_r. apply Nat.lt_succ_r. left. reflexivity.
      assert (E2: derrec_height d = derrec_height d). auto.
      pose (IH (derrec_height d) E1 ((XBoxed_list BΓ ++ [Box A0], [A0])) d E2 x (unBox_formula A) w0).
      destruct s.
      assert (E3: derrec_height x1 < S (Init.Nat.max (derrec_height d) (dersrec_height d0))).
      rewrite dersrec_height_nil. rewrite Nat.max_0_r. apply Nat.lt_succ_r. assumption. reflexivity.
      assert (E4: derrec_height x1 = derrec_height x1). auto.
      pose (IH (derrec_height x1) E3 x x1 E4 x0 A w). destruct s.
      pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
      (ps:=[x0]) (Γ0 ++ A :: Γ1, Δ) g0). subst. simpl.
      pose (dlCons x2 d0). pose (d1 d2). exists d3. simpl. rewrite dersrec_height_nil.
      repeat rewrite Nat.max_0_r. rewrite <- Nat.succ_le_mono.
      pose (Nat.le_trans (derrec_height x2) (derrec_height x1) (derrec_height d) l0 l).
      assumption. reflexivity. }
Qed.

Theorem GLS_prv_wkn_L : forall s, GLS_prv s ->
          (forall sw A, (@wkn_L A s sw) -> GLS_prv sw).
Proof.
intros.
assert (J0: derrec_height X = derrec_height X). auto.
pose (GLS_wkn_L _ J0 H). destruct s0. auto.
Qed.

Theorem GLS_wkn_R : forall (k : nat) s
        (D0 : GLS_prv s),
        k = (derrec_height D0) ->
          (forall sw A, ((@wkn_R A s sw) ->
          existsT2 (D1 : GLS_prv sw),
          derrec_height D1 <= k)).
Proof.
(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall (s : Seq)
  (D0 : derrec GLS_rules (fun _ : Seq => False) s),
x = derrec_height D0 ->
(forall sw A,
wkn_R A s sw ->
(existsT2
  D1 : derrec GLS_rules
         (fun _ : Seq => False) sw,
  derrec_height D1 <= x)))).
apply s. intros n IH. clear s.
(* Now we do the actual proof-theoretical work. *)
intros s0 D0. remember D0 as D0'. destruct D0.
(* D0 is a leaf *)
- intros hei sw A wkn. inversion f.
(* D0 ends with an application of rule *)
- intros hei sw A wkn. inversion wkn. inversion g.
  (* IdP *)
  * inversion H1. rewrite <- H in H5. inversion H5. apply app2_find_hole in H8.
    destruct H8. assert (DersNil: dersrec GLS_rules (fun _ : Seq => False) []).
    apply dersrec_nil.
    repeat destruct s.
    + destruct p. inversion e0. subst. pose (IdPRule_I P Γ0 Γ1 (Δ2 ++ [A]) Δ3). apply IdP in i. rewrite <- app_assoc in i. simpl in i.
      pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
      (ps:=[]) (Γ0 ++ # P :: Γ1, Δ2 ++ A :: # P :: Δ3) i DersNil). exists d0. simpl. repeat rewrite dersrec_height_nil.
      left. reflexivity. reflexivity.
    + destruct p. destruct x.
      { rewrite app_nil_l in e0. inversion e0. subst.
        pose (IdPRule_I P Γ0 Γ1 ((Δ2 ++ []) ++ [A]) Δ3). apply IdP in i. rewrite <- app_assoc in i. simpl in i.
        pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
        (ps:=[]) (Γ0 ++ # P :: Γ1, (Δ2 ++ []) ++ A :: # P :: Δ3) i DersNil). exists d0. simpl. repeat rewrite dersrec_height_nil.
        left. reflexivity. reflexivity. }
      { inversion e0. subst.
        pose (IdPRule_I P Γ0 Γ1 Δ2 (x ++ A :: Δ1)). apply IdP in i.
        assert (E0: Δ2 ++ # P :: x ++ A :: Δ1 = (Δ2 ++ # P :: x) ++ A :: Δ1). rewrite <- app_assoc. reflexivity.
        rewrite E0 in i.
        pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
        (ps:=[]) (Γ0 ++ # P :: Γ1, (Δ2 ++ # P :: x) ++ A :: Δ1) i DersNil).
        exists d0. simpl. repeat rewrite dersrec_height_nil.
        left. reflexivity. reflexivity. }
    + destruct p. subst. pose (IdPRule_I P Γ0 Γ1 (Δ0 ++ A :: x) Δ3). apply IdP in i. rewrite <- app_assoc in i. simpl in i.
      pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
      (ps:=[]) (Γ0 ++ # P :: Γ1, Δ0 ++ A :: x ++ # P :: Δ3) i DersNil).
      exists d0. simpl. repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity.
  (* BotL *)
  * inversion H1. rewrite <- H in H5. inversion H5.
    assert (DersNil: dersrec GLS_rules (fun _ : Seq => False) []).
    apply dersrec_nil.
    pose (BotLRule_I Γ0 Γ1 (Δ0 ++ A :: Δ1)). apply BotL in b.
    pose (derI (rules:=GLS_rules)
    (prems:=fun _ : Seq => False)
    (ps:=[]) (Γ0 ++ ⊥ :: Γ1, Δ0 ++ A :: Δ1) b DersNil). subst. exists d0. simpl.
    repeat rewrite dersrec_height_nil. left. reflexivity. reflexivity.
  (* ImpR *)
  * inversion H1. subst. inversion H5. subst. pose (ImpR_app_wkn_R wkn H1). destruct s.
    destruct p. apply ImpR in i.
    pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
    (ps:=[x]) (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) i). subst. simpl.
    remember [(Γ0 ++ A0 :: Γ1, Δ2 ++ B :: Δ3)] as ps'. destruct d. inversion Heqps'.
    inversion Heqps'. subst. simpl. rewrite dersrec_height_nil. simpl in IH.
    rewrite dersrec_height_nil in IH. rewrite Nat.max_0_r. rewrite Nat.max_0_r in IH.
    assert (E: derrec_height d < S (derrec_height d)). auto.
    assert (E1: derrec_height d = derrec_height d). auto.
    pose (IH (derrec_height d) E (Γ0 ++ A0 :: Γ1, Δ2 ++ B :: Δ3) d E1 x A w).
    destruct s.
    pose (dlCons x0 d1). pose (d0 d2). exists d3. simpl. rewrite dersrec_height_nil.
    rewrite Nat.max_0_r. rewrite <- Nat.succ_le_mono. assumption. reflexivity. reflexivity. reflexivity.
  (* ImpL *)
  * inversion H1. subst. inversion H5. subst. pose (ImpL_app_wkn_R wkn H1). repeat destruct s.
    repeat destruct p. apply ImpL in i.
    pose (derI (rules:=GLS_rules) (prems:=fun _ : Seq => False)
    (ps:=[x;x0]) (Γ0 ++ A0 --> B :: Γ1, Δ0 ++ A :: Δ1) i). subst. simpl.
    remember [(Γ0 ++ Γ1, Δ2 ++ A0 :: Δ3); (Γ0 ++ B :: Γ1, Δ2 ++ Δ3)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst.
    remember [(Γ0 ++ B :: Γ1, Δ2 ++ Δ3)] as ps''. destruct d1. inversion Heqps''.
    inversion Heqps''. simpl. subst. rewrite dersrec_height_nil. simpl in IH.
    rewrite dersrec_height_nil in IH. rewrite Nat.max_0_r. rewrite Nat.max_0_r in IH.
    assert (E1: derrec_height d < S (Init.Nat.max (derrec_height d)(derrec_height d1))).
    apply Nat.lt_succ_r. apply Nat.le_max_l.
    assert (E2: derrec_height d = derrec_height d). auto.
    pose (IH (derrec_height d) E1 (Γ0 ++ Γ1, Δ2 ++ A0 :: Δ3) d E2 x A w0).
    destruct s.
    assert (E3: derrec_height d1 < S (Init.Nat.max (derrec_height d)(derrec_height d1))).
    apply Nat.lt_succ_r. apply Nat.le_max_r.
    assert (E4: derrec_height d1 = derrec_height d1). auto.
    pose (IH (derrec_height d1) E3 (Γ0 ++ B :: Γ1, Δ2 ++ Δ3) d1 E4 x0 A w).
    destruct s.
    pose (dlCons x1 (dlCons x2 d2)). subst. pose (d0 d3). exists d4. simpl. rewrite dersrec_height_nil.
    rewrite Nat.max_0_r. rewrite <- Nat.succ_le_mono. apply Nat.max_le_compat.
    assumption. assumption. reflexivity. reflexivity. reflexivity.
  (* GLR *)
  * inversion X. rewrite <- H4 in X. pose (GLR_app_wkn_R wkn X).
    apply GLR in g0. pose (derI (rules:=GLS_rules)
    (prems:=fun _ : Seq => False) (ps:=[(XBoxed_list BΓ ++ [Box A0], [A0])]) 
    sw g0). subst. pose (d0 d). exists d1. simpl. reflexivity.
Qed.

Theorem GLS_prv_wkn_R : forall s, GLS_prv s ->
          (forall sw A, (@wkn_R A s sw) -> GLS_prv sw).
Proof.
intros.
assert (J0: derrec_height X = derrec_height X). auto.
pose (GLS_wkn_R _ J0 H). destruct s0. auto.
Qed.


Theorem GLS_list_wkn_R : forall (k : nat) Γ Δ0 Δ1
        (D0 : GLS_prv (Γ,Δ0 ++ Δ1)),
        k = (derrec_height D0) ->
          (forall l, existsT2 (D1 : GLS_prv (Γ,Δ0 ++ l ++ Δ1)),
           derrec_height D1 <= k).
Proof.
intros. induction l.
- simpl. exists D0. lia.
- simpl. destruct IHl.
  assert (E: derrec_height x = derrec_height x). reflexivity.
  assert (H0: wkn_R a (Γ, Δ0 ++ l ++ Δ1) (Γ, Δ0 ++ a :: l ++ Δ1)). apply wkn_RI.
  pose (@GLS_wkn_R (derrec_height x) (Γ, Δ0 ++ l ++ Δ1) x E (Γ, Δ0 ++ a :: l ++ Δ1) a H0).
  destruct s. exists x0. lia.
Qed.

Theorem GLS_prv_list_wkn_R : forall Γ Δ0 Δ1,
        GLS_prv (Γ,Δ0 ++ Δ1) -> forall l, GLS_prv (Γ,Δ0 ++ l ++ Δ1).
Proof.
intros.
assert (J0: derrec_height X = derrec_height X). auto.
pose (@GLS_list_wkn_R _ _ _ _ X J0 l). destruct s. auto.
Qed.

Theorem GLS_list_wkn_L : forall (k : nat) Γ0 Γ1 Δ
        (D0 : GLS_prv (Γ0 ++ Γ1,Δ)),
        k = (derrec_height D0) ->
          (forall l, existsT2 (D1 : GLS_prv (Γ0 ++ l ++ Γ1,Δ)),
          derrec_height D1 <= k).
Proof.
intros. induction l.
- simpl. exists D0. lia.
- simpl. destruct IHl.
  assert (E: derrec_height x = derrec_height x). reflexivity.
  assert (H0: wkn_L a (Γ0 ++ l ++ Γ1, Δ) (Γ0 ++ a :: l ++ Γ1, Δ)). apply wkn_LI.
  pose (@GLS_wkn_L (derrec_height x) (Γ0 ++ l ++ Γ1, Δ) x E (Γ0 ++ a :: l ++ Γ1, Δ) a H0).
  destruct s. exists x0. lia.
Qed.

Theorem GLS_prv_list_wkn_L : forall Γ0 Γ1 Δ,
        GLS_prv (Γ0 ++ Γ1,Δ) -> forall l, GLS_prv (Γ0 ++ l ++ Γ1,Δ).
Proof.
intros.
assert (J0: derrec_height X = derrec_height X). auto.
pose (@GLS_list_wkn_L _ _ _ _ X J0 l). destruct s. auto.
Qed.

Theorem GLS_XBoxed_list_wkn_L : forall (k : nat) Γ1 Γ0 Γ2 Δ
        (D0 : GLS_prv (Γ0 ++ Γ1 ++ Γ2,Δ)),
        k = (derrec_height D0) ->
          (existsT2 (D1 : GLS_prv (Γ0 ++ (XBoxed_list Γ1) ++ Γ2,Δ)),
           derrec_height D1 <= k).
Proof.
induction Γ1.
- intros. simpl. simpl in D0. exists D0. rewrite H. left.
- intros. simpl. assert (Γ0 ++ (a :: Γ1) ++ Γ2 = (Γ0 ++ [a]) ++ Γ1 ++ Γ2). rewrite <- app_assoc. reflexivity.
  pose (@IHΓ1 (Γ0 ++ [a]) Γ2 Δ). repeat rewrite <- H0 in s.
  pose (s D0 H). destruct s0. clear s.
  assert (wkn_L (unBox_formula a) ((Γ0 ++ [a]) ++ XBoxed_list Γ1 ++ Γ2, Δ) (Γ0 ++ unBox_formula a :: a :: XBoxed_list Γ1 ++ Γ2, Δ)).
  assert ((Γ0 ++ [a]) ++ XBoxed_list Γ1 ++ Γ2 = Γ0 ++ a :: XBoxed_list Γ1 ++ Γ2). rewrite <- app_assoc. reflexivity. rewrite H1.
  apply wkn_LI.
  assert (derrec_height x = derrec_height x). reflexivity.
  pose (GLS_wkn_L x H2 H1). destruct s. exists x0. lia.
Qed.
