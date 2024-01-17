Require Import List.
Export ListNotations.
Require Import Lia.
Require Import PeanoNat.

Require Import KS_calc.
Require Export KS_exch_prelims.
Require Export KS_exch_ImpR.
Require Export KS_exch_ImpL.
Require Export KS_exch_KR.

(* We can now prove the admissibility of list_exchange on the left. *)

Theorem KS_adm_list_exch_L : forall s,
        (KS_prv s) ->
        (forall se, (@list_exch_L s se) ->
        (KS_prv se)).
Proof.
intros s D. apply derrec_all_rect with 
(Q:= fun x => forall (se : Seq),
list_exch_L x se ->
derrec KS_rules  (fun _ : Seq => False)
  se)
in D.
- exact D.
- intros concl F. inversion F.
- intros ps concl rule. induction rule.
  (* IdP *)
  * intros ders IH se exch. inversion i. apply derI with (ps:=[]).
    apply IdP.
    + assert (Permstose: existsT2 eΓ0 eΓ1, se = (eΓ0 ++ # P :: eΓ1, Δ0 ++ # P :: Δ1)).
      { pose (list_exch_L_permLR _ _ exch). subst. destruct s0 with (Γ0:=Γ0) (Γ1:=Γ1) (Δ0:=Δ0) (Δ1:=Δ1)
      (C:=# P) (D:=# P). auto. exists x. assumption. }
      destruct Permstose. repeat destruct s0. subst. apply IdPRule_I.
    + apply dersrec_all in ders. apply dersrec_all. subst. assumption.
  (* BotL *)
  * intros ders IH se exch. apply derI with (ps:=ps).
    + apply BotL. inversion b. symmetry in H0.
      assert (Permstose: existsT2 eΓ0 eΓ1, se = ((eΓ0 ++ Bot :: eΓ1), Δ)).
      { apply list_exch_L_permL with (s:=c) (Γ0:=Γ0) (Γ1:=Γ1) (Δ:=Δ). assumption.
        assumption. }
      destruct Permstose. destruct s0. subst. apply BotLRule_I.
    + apply dersrec_all in ders. apply dersrec_all. assumption.
  (* ImpR *)
  * intros ders IH se exch. inversion i. subst. pose (ImpR_app_list_exchL _ _ _ exch i).
    destruct s0. destruct p. apply derI with (ps:=[x]).
    + apply ImpR. assumption.
    + apply dersrec_all. apply dersrec_all in ders. inversion i0.
      inversion i. apply ForallT_inv in IH. apply ForallT_cons.
      { apply IH. subst. assumption. }
      { apply ForallT_nil. }
  (* ImpL *)
  * intros ders IH se exch. inversion i. subst. pose (ImpL_app_list_exchL _ _ _ _ exch i).
    destruct s0. destruct s0. destruct p. destruct p. apply derI with (ps:=[x;x0]).
    + apply ImpL. assumption.
    + apply dersrec_all. apply dersrec_all in ders. inversion i0.
      inversion i. apply ForallT_cons_inv in IH. destruct IH.
      apply ForallT_inv in f. apply ForallT_cons.
      { apply d. subst. assumption. }
      { apply ForallT_cons. apply f. subst. assumption. apply ForallT_nil. }
  (* KR *)
  * intros ders IH se exch. inversion k. subst. pose (KR_app_list_exchL _ _ _ exch k).
    destruct s0. destruct p. apply derI with (ps:=[x]).
    + apply KR. assumption.
    + apply dersrec_all. apply dersrec_all in ders. inversion k0.
      inversion k. apply ForallT_inv in IH. apply ForallT_cons.
      { apply IH. subst. assumption. }
      { apply ForallT_nil. }
Qed.

Theorem KS_adm_list_exch_R : forall s,
        (KS_prv s) ->
        (forall se, (@list_exch_R s se) ->
        (KS_prv se)).
Proof.
intros s D. apply derrec_all_rect with
(Q:= fun x => forall (se : Seq),
list_exch_R x se ->
derrec KS_rules  (fun _ : Seq => False)
  se)
in D.
- exact D.
- intros concl F. inversion F.
- intros ps concl rule. induction rule.
  (* IdP *)
  * intros ders IH se exch. inversion i. apply derI with (ps:=[]).
    apply IdP.
    + assert (Permstose: existsT2 eΔ0 eΔ1, se = (Γ0 ++ # P :: Γ1, eΔ0 ++ # P :: eΔ1)).
      { pose (list_exch_R_permLR _ _ exch). subst. destruct s0 with (Γ0:=Γ0) (Γ1:=Γ1) (Δ0:=Δ0) (Δ1:=Δ1)
      (C:=# P) (D:=# P). auto. exists x. assumption. }
      destruct Permstose. repeat destruct s0. subst. apply IdPRule_I.
    + apply dersrec_all in ders. apply dersrec_all. subst. assumption.
  (* BotL *)
  * intros ders IH se exch. apply derI with (ps:=ps).
    + apply BotL. inversion b. symmetry in H0.
      assert (Permstose: existsT2 eΔ, se = ((Γ0 ++ Bot :: Γ1), eΔ)).
      { apply list_exch_R_permL with (s:=c) (Γ0:=Γ0) (Γ1:=Γ1) (Δ:=Δ). assumption.
        assumption. }
      destruct Permstose. subst. apply BotLRule_I.
    + apply dersrec_all in ders. apply dersrec_all. assumption.
  (* ImpR *)
  * intros ders IH se exch. inversion i. subst. pose (ImpR_app_list_exchR _ _ _ exch i).
    destruct s0. destruct p. apply derI with (ps:=[x]).
    + apply ImpR. assumption.
    + apply dersrec_all. apply dersrec_all in ders. inversion i0.
      inversion i. apply ForallT_inv in IH. apply ForallT_cons.
      { apply IH. subst. assumption. }
      { apply ForallT_nil. }
  (* ImpL *)
  * intros ders IH se exch. inversion i. subst. pose (ImpL_app_list_exchR _ _ _ _ exch i).
    destruct s0. destruct s0. destruct p. destruct p. apply derI with (ps:=[x;x0]).
    + apply ImpL. assumption.
    + apply dersrec_all. apply dersrec_all in ders. inversion i0.
      inversion i. apply ForallT_cons_inv in IH. destruct IH.
      apply ForallT_inv in f. apply ForallT_cons.
      { apply d. subst. assumption. }
      { apply ForallT_cons. apply f. subst. assumption. apply ForallT_nil. }
  (* KR *)
  * intros ders IH se exch. inversion k. subst. pose (KR_app_list_exchR _ _ _ exch k).
    destruct s0. destruct p. apply derI with (ps:=[x]).
    + apply KR. assumption.
    + apply dersrec_all. apply dersrec_all in ders. inversion k0.
      inversion k. apply ForallT_inv in IH. apply ForallT_cons.
      { apply IH. subst. assumption. }
      { apply ForallT_nil. }
Qed.

(* Now we can turn to the derivability of list_exchange. *)

Inductive Closure {X: Type} (F : X -> Type) (P : X -> X -> Type) : X -> Type :=
  | InitClo : forall x, F x -> Closure F P x
  | IndClo : forall x y,  Closure F P y -> (P y x) -> Closure F P x.

Inductive ExcClosure (hyps : Seq -> Type) : Seq -> Type :=
  | InitLExch : forall x, Closure hyps list_exch_L x -> ExcClosure hyps x
  | InitRExch : forall x, Closure hyps list_exch_R x -> ExcClosure hyps x
  | IndLExch : forall x y, ExcClosure hyps x -> list_exch_L x y -> ExcClosure hyps y
  | IndRExch : forall x y, ExcClosure hyps x -> list_exch_R x y -> ExcClosure hyps y.

Theorem KS_der_list_exch_L : forall hyps s,
        (derrec KS_rules hyps s) ->
        (forall se, (@list_exch_L s se) ->
        (derrec KS_rules (ExcClosure hyps) se)).
Proof.
intros hyps s D. apply derrec_all_rect with
(Q:= fun x => forall (se : Seq),
list_exch_L x se ->
derrec KS_rules  (ExcClosure hyps) se) in D.
- exact D.
- intros concl H1 se exch. apply dpI. apply InitLExch. apply IndClo with (y:=concl).
  apply InitClo. assumption. assumption.
- intros ps concl rule. induction rule.
  (* IdP *)
  * intros ders IH se exch. inversion i. apply derI with (ps:=[]).
    apply IdP.
    + assert (Permstose: existsT2 eΓ0 eΓ1, se = (eΓ0 ++ # P :: eΓ1, Δ0 ++ # P :: Δ1)).
      { pose (list_exch_L_permLR _ _ exch). subst. destruct s0 with (Γ0:=Γ0) (Γ1:=Γ1) (Δ0:=Δ0) (Δ1:=Δ1)
      (C:=# P) (D:=# P). auto. exists x. assumption. }
      destruct Permstose. repeat destruct s0. subst. apply IdPRule_I.
    + apply dersrec_all in ders. apply dersrec_nil.
  (* BotL *)
  * intros ders IH se exch. apply derI with (ps:=ps).
    + apply BotL. inversion b. symmetry in H0.
      assert (Permstose: existsT2 eΓ0 eΓ1, se = ((eΓ0 ++ Bot :: eΓ1), Δ)).
      { apply list_exch_L_permL with (s:=c) (Γ0:=Γ0) (Γ1:=Γ1) (Δ:=Δ). assumption.
        assumption. }
      destruct Permstose. repeat destruct s0. subst. apply BotLRule_I.
    + apply dersrec_all in ders. inversion b. apply dersrec_nil.
  (* ImpR *)
  * intros ders IH se exch. inversion i. subst. pose (ImpR_app_list_exchL _ _ _ exch i).
    destruct s0. destruct p. apply derI with (ps:=[x]).
    + apply ImpR. assumption.
    + apply dersrec_all. apply dersrec_all in ders. inversion i0.
      inversion i. apply ForallT_inv in IH. apply ForallT_cons.
      { apply IH. subst. assumption. }
      { apply ForallT_nil. }
  (* ImpL *)
  * intros ders IH se exch. inversion i. subst. pose (ImpL_app_list_exchL _ _ _ _ exch i).
    destruct s0. destruct s0. destruct p. destruct p. apply derI with (ps:=[x;x0]).
    + apply ImpL. assumption.
    + apply dersrec_all. apply dersrec_all in ders. inversion i0.
      inversion i. apply ForallT_cons_inv in IH. destruct IH.
      apply ForallT_inv in f. apply ForallT_cons.
      { apply d. subst. assumption. }
      { apply ForallT_cons. apply f. subst. assumption. apply ForallT_nil. }
  (* KR *)
  * intros ders IH se exch. inversion k. subst. pose (KR_app_list_exchL _ _ _ exch k).
    destruct s0. destruct p. apply derI with (ps:=[x]).
    + apply KR. assumption.
    + apply dersrec_all. apply dersrec_all in ders. inversion k0.
      inversion k. apply ForallT_inv in IH. apply ForallT_cons.
      { apply IH. subst. assumption. }
      { apply ForallT_nil. }
Qed.

Theorem KS_der_list_exch_R : forall hyps s,
        (derrec KS_rules hyps s) ->
        (forall se, (@list_exch_R s se) ->
        (derrec KS_rules (ExcClosure hyps) se)).
Proof.
intros hyps s D. apply derrec_all_rect with
(Q:= fun x => forall (se : Seq),
list_exch_R x se ->
derrec KS_rules  (ExcClosure hyps) se) in D.
- exact D.
- intros concl H1 se exch. apply dpI. apply InitRExch. apply IndClo with (y:=concl).
  apply InitClo. assumption. assumption.
- intros ps concl rule. induction rule.
  (* IdP *)
  * intros ders IH se exch. inversion i. apply derI with (ps:=[]).
    apply IdP.
    + assert (Permstose: existsT2 eΔ0 eΔ1, se = (Γ0 ++ # P :: Γ1, eΔ0 ++ # P :: eΔ1)).
      { pose (list_exch_R_permLR _ _ exch). subst. destruct s0 with (Γ0:=Γ0) (Γ1:=Γ1) (Δ0:=Δ0) (Δ1:=Δ1)
      (C:=# P) (D:=# P). auto. exists x. assumption. }
      destruct Permstose. repeat destruct s0. subst. apply IdPRule_I.
    + apply dersrec_all in ders. apply dersrec_nil.
  (* BotL *)
  * intros ders IH se exch. apply derI with (ps:=ps).
    + apply BotL. inversion b. symmetry in H0.
      assert (Permstose: existsT2 eΔ, se = ((Γ0 ++ Bot :: Γ1), eΔ)).
      { apply list_exch_R_permL with (s:=c) (Γ0:=Γ0) (Γ1:=Γ1) (Δ:=Δ). assumption.
        assumption. }
      destruct Permstose. subst. apply BotLRule_I.
    + apply dersrec_all in ders. inversion b. apply dersrec_nil.
  (* ImpR *)
  * intros ders IH se exch. inversion i. subst. pose (ImpR_app_list_exchR _ _ _ exch i).
    destruct s0. destruct p. apply derI with (ps:=[x]).
    + apply ImpR. assumption.
    + apply dersrec_all. apply dersrec_all in ders. inversion i0.
      inversion i. apply ForallT_inv in IH. apply ForallT_cons.
      { apply IH. subst. assumption. }
      { apply ForallT_nil. }
  (* ImpL *)
  * intros ders IH se exch. inversion i. subst. pose (ImpL_app_list_exchR _ _ _ _ exch i).
    destruct s0. destruct s0. destruct p. destruct p. apply derI with (ps:=[x;x0]).
    + apply ImpL. assumption.
    + apply dersrec_all. apply dersrec_all in ders. inversion i0.
      inversion i. apply ForallT_cons_inv in IH. destruct IH.
      apply ForallT_inv in f. apply ForallT_cons.
      { apply d. subst. assumption. }
      { apply ForallT_cons. apply f. subst. assumption. apply ForallT_nil. }
  (* KR *)
  * intros ders IH se exch. inversion k. subst. pose (KR_app_list_exchR _ _ _ exch k).
    destruct s0. destruct p. apply derI with (ps:=[x]).
    + apply KR. assumption.
    + apply dersrec_all. apply dersrec_all in ders. inversion k0.
      inversion k. apply ForallT_inv in IH. apply ForallT_cons.
      { apply IH. subst. assumption. }
      { apply ForallT_nil. }
Qed.

(* In fact, we can prove that exchange is height-preserving admissible. *)

Theorem KS_hpadm_list_exch_R0 : forall (k : nat) s
                                  (D0: KS_prv s),
        k = (derrec_height D0) ->
        (forall se, (list_exch_R s se) ->
        (existsT2 (D1 : KS_prv se),
          derrec_height D1 <=k)).
Proof.
(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall (s : Seq)
  (D0 : derrec KS_rules  (fun _ : Seq => False) s),
x = derrec_height D0 ->
(forall se,
(list_exch_R s se) ->
(existsT2
  D1 : derrec KS_rules 
         (fun _ : Seq => False) se,
  derrec_height D1 <= x)))).
apply s. intros n IH. clear s.
(* Now we do the actual proof-theoretical work. *)
intros s0 D0. remember D0 as D0'. destruct D0.
(* D0 ip a leaf *)
- inversion f.
(* D0 is ends with an application of rule *)
- intros hei se exch. inversion exch.
  assert (DersNil: dersrec KS_rules  (fun _ : Seq => False) []).
  apply dersrec_nil. inversion k.
  (* IdP *)
  * inversion H1. subst. inversion H5. subst. simpl.
    assert (In # P (Δ0 ++ Δ3 ++ Δ2 ++ Δ1 ++ Δ4)). assert (In # P (Δ0 ++ Δ1 ++ Δ2 ++ Δ3 ++ Δ4)).
    rewrite <- H2. apply in_or_app. right. apply in_eq. apply in_app_or in H. apply in_or_app.
    destruct H. auto. apply in_app_or in H. right. apply in_or_app. destruct H. right. apply in_or_app.
    right. apply in_or_app. auto. apply in_app_or in H. destruct H. right. apply in_or_app. auto.
    apply in_app_or in H. destruct H. auto. right. apply in_or_app. right. apply in_or_app. auto.
    apply in_splitT in H. destruct H. destruct s. rewrite e.
    assert (IdPRule [] (Γ0 ++ # P :: Γ1, x ++ # P :: x0)). apply IdPRule_I. apply IdP in H.
    pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (Γ0 ++ # P :: Γ1, x ++ # P :: x0) H DersNil). exists d0. simpl. rewrite dersrec_height_nil.
    lia. reflexivity.
  (* BotL *)
  * inversion H1. subst. inversion H5. subst. simpl.
    assert (BotLRule [] (Γ0 ++ Bot :: Γ1, Δ0 ++ Δ3 ++ Δ2 ++ Δ1 ++ Δ4)). apply BotLRule_I. apply BotL in H.
    pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (Γ0 ++ Bot :: Γ1, Δ0 ++ Δ3 ++ Δ2 ++ Δ1 ++ Δ4) H DersNil). exists d0. simpl. rewrite dersrec_height_nil.
    lia. reflexivity.
  (* ImpR *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (ImpR_app_list_exchR _ _ _ exch H1). destruct s. destruct p.
    apply ImpR in i. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec_height d J0). destruct s.
    assert (E: derrec_height x0 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x0 = derrec_height x0). auto.
    pose (IH (derrec_height x0) E (Γ0 ++ A :: Γ1, Δ5 ++ B :: Δ6) x0 E1 x l).
    destruct s. pose (dlCons x1 DersNil).
    pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
    (ps:=[x]) (Γ0 ++ Γ1, Δ0 ++ Δ3 ++ Δ2 ++ Δ1 ++ Δ4) i d0). exists d1. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* ImpL *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (ImpL_app_list_exchR _ _ _ _ exch H1). repeat destruct s. repeat destruct p.
    apply ImpL in i. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec2_height d J0). repeat destruct s.
    assert (E: derrec_height x1 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x1 = derrec_height x1). auto.
    pose (IH (derrec_height x1) E (Γ0 ++ Γ1, Δ5 ++ A :: Δ6) x1 E1 x l0).
    destruct s.
    assert (E2: derrec_height x2 < S (dersrec_height d)). lia.
    assert (E3: derrec_height x2 = derrec_height x2). auto.
    pose (IH (derrec_height x2) E2 (Γ0 ++ B :: Γ1, Δ5 ++ Δ6) x2 E3 x0 l).
    destruct s. pose (dlCons x4 DersNil). pose (dlCons x3 d0).
    pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
    (ps:=[x; x0]) (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ3 ++ Δ2 ++ Δ1 ++ Δ4) i d1). exists d2. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* KR *)
  * inversion X. subst. inversion H5. subst. simpl. simpl in IH.
    pose (KR_app_list_exchR _ _ _ exch X). destruct s. destruct p.
    apply KR in k0. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec_height d J0). destruct s.
    assert (E: derrec_height x0 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x0 = derrec_height x0). auto.
    pose (IH (derrec_height x0) E (unboxed_list BΓ, [A]) x0 E1 x l).
    destruct s. pose (dlCons x1 DersNil).
    pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
    (ps:=[x]) (Γ, Δ0 ++ Δ3 ++ Δ2 ++ Δ1 ++ Δ4) k0 d0). exists d1. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
Qed.

Theorem KS_hpadm_list_exch_L0 : forall (k : nat) s
                                  (D0: KS_prv s),
        k = (derrec_height D0) ->
        (forall se, (list_exch_L s se) ->
        (existsT2 (D1 : KS_prv se),
          derrec_height D1 <=k)).
Proof.
(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall (s : Seq)
  (D0 : derrec KS_rules  (fun _ : Seq => False) s),
x = derrec_height D0 ->
(forall se,
(list_exch_L s se) ->
(existsT2
  D1 : derrec KS_rules 
         (fun _ : Seq => False) se,
  derrec_height D1 <= x)))).
apply s. intros n IH. clear s.
(* Now we do the actual proof-theoretical work. *)
intros s0 D0. remember D0 as D0'. destruct D0.
(* D0 ip a leaf *)
- inversion f.
(* D0 is ends with an application of rule *)
- intros hei se exch. inversion exch.
  assert (DersNil: dersrec KS_rules  (fun _ : Seq => False) []).
  apply dersrec_nil. inversion k.
  (* IdP *)
  * inversion H1. subst. inversion H5. subst. simpl.
    assert (In # P (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4)). assert (In # P (Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4)).
    rewrite <- H0. apply in_or_app. right. apply in_eq. apply in_app_or in H. apply in_or_app.
    destruct H. auto. apply in_app_or in H. right. apply in_or_app. destruct H. right. apply in_or_app.
    right. apply in_or_app. auto. apply in_app_or in H. destruct H. right. apply in_or_app. auto.
    apply in_app_or in H. destruct H. auto. right. apply in_or_app. right. apply in_or_app. auto.
    apply in_splitT in H. destruct H. destruct s. rewrite e.
    assert (IdPRule [] (x ++ # P :: x0, Δ0 ++ # P :: Δ1)). apply IdPRule_I. apply IdP in H.
    pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x ++ # P :: x0, Δ0 ++ # P :: Δ1) H DersNil). exists d0. simpl. rewrite dersrec_height_nil.
    lia. reflexivity.
  (* BotL *)
  * inversion H1. subst. inversion H5. subst. simpl.
    assert (In (Bot) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4)). assert (In (Bot) (Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4)).
    rewrite <- H0. apply in_or_app. right. apply in_eq. apply in_app_or in H. apply in_or_app.
    destruct H. auto. apply in_app_or in H. right. apply in_or_app. destruct H. right. apply in_or_app.
    right. apply in_or_app. auto. apply in_app_or in H. destruct H. right. apply in_or_app. auto.
    apply in_app_or in H. destruct H. auto. right. apply in_or_app. right. apply in_or_app. auto.
    apply in_splitT in H. destruct H. destruct s. rewrite e.
    assert (BotLRule [] (x ++ Bot :: x0, Δ)). apply BotLRule_I. apply BotL in H.
    pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x ++ Bot :: x0, Δ) H DersNil). exists d0. simpl. rewrite dersrec_height_nil.
    lia. reflexivity.
  (* ImpR *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (ImpR_app_list_exchL _ _ _ exch H1). destruct s. destruct p.
    apply ImpR in i. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec_height d J0). destruct s.
    assert (E: derrec_height x0 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x0 = derrec_height x0). auto.
    pose (IH (derrec_height x0) E (Γ5 ++ A :: Γ6, Δ0 ++ B :: Δ1) x0 E1 x l).
    destruct s. pose (dlCons x1 DersNil).
    pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
    (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, Δ0 ++ A --> B :: Δ1) i d0). exists d1. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* ImpL *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (ImpL_app_list_exchL _ _ _ _ exch H1). repeat destruct s. repeat destruct p.
    apply ImpL in i. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec2_height d J0). repeat destruct s.
    assert (E: derrec_height x1 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x1 = derrec_height x1). auto.
    pose (IH (derrec_height x1) E (Γ5 ++ Γ6, Δ0 ++ A :: Δ1) x1 E1 x l0).
    destruct s.
    assert (E2: derrec_height x2 < S (dersrec_height d)). lia.
    assert (E3: derrec_height x2 = derrec_height x2). auto.
    pose (IH (derrec_height x2) E2 (Γ5 ++ B :: Γ6, Δ0 ++ Δ1) x2 E3 x0 l).
    destruct s. pose (dlCons x4 DersNil). pose (dlCons x3 d0).
    pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
    (ps:=[x; x0]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, Δ0 ++ Δ1) i d1). exists d2. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* KR *)
  * inversion X. subst. inversion H5. subst. simpl. simpl in IH.
    pose (KR_app_list_exchL _ _ _ exch X). destruct s. destruct p.
    apply KR in k0. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec_height d J0). destruct s.
    assert (E: derrec_height x0 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x0 = derrec_height x0). auto.
    pose (IH (derrec_height x0) E (unboxed_list BΓ, [A]) x0 E1 x l).
    destruct s. pose (dlCons x1 DersNil).
    pose (derI (rules:=KS_rules) (prems:=fun _ : Seq => False)
    (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, Δ0 ++ Box A :: Δ1) k0 d0). exists d1. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
Qed.

Theorem KS_hpadm_list_exch_L : forall s (D0: KS_prv s),
        (forall se, (list_exch_L s se) ->
        (existsT2 (D1 : KS_prv se),
          derrec_height D1 <= derrec_height D0)).
Proof.
intros.
pose (@KS_hpadm_list_exch_L0 (derrec_height D0) _ D0).
apply s0 ; auto.
Qed.

Theorem KS_hpadm_list_exch_R : forall s (D0: KS_prv s),
        (forall se, (list_exch_R s se) ->
        (existsT2 (D1 : KS_prv se),
          derrec_height D1 <= derrec_height D0)).
Proof.
intros.
pose (@KS_hpadm_list_exch_R0 (derrec_height D0) _ D0).
apply s0 ; auto.
Qed.

Theorem KS_adm_list_exch_LR : forall s (D0: KS_prv s),
        (forall se, ((list_exch_L s se) -> (KS_prv se)) *
                        ((list_exch_R s se) -> (KS_prv se))).
Proof.
intros. assert (J1: derrec_height D0 = derrec_height D0). auto. split ; intro.
- pose (@KS_hpadm_list_exch_L0 (derrec_height D0) s D0 J1 se H). destruct s0 ; auto.
- pose (@KS_hpadm_list_exch_R0 (derrec_height D0) s D0 J1 se H). destruct s0 ; auto.
Qed.


