Require Import List.
Export ListNotations.
Require Import Lia.
Require Import PeanoNat.

Require Import KS_calc.
Require Import KS_dec.
Require Import KS_termination_measure.
Require Export KS_termination_prelims.
Require Export KS_termination_init.
Require Export KS_termination_ImpR.
Require Export KS_termination_ImpL.
Require Export KS_termination_KR.

(* Now that we have the list of all premises of a sequent via all rules, we can combine
   them all to obtain the list of all potential premises via the KS calculus. *)

Lemma finite_premises_of_S : forall (s : Seq), existsT2 listprems,
              (forall prems, ((KS_rules prems s) -> (InT prems listprems)) *
                             ((InT prems listprems) -> (KS_rules prems s))).
Proof.
intro s.
destruct (dec_KS_rules s).
- exists []. intros. split. intro. exfalso. apply f. exists prems. assumption.
  intro. inversion H. 
- pose (finite_IdP_premises_of_S s). destruct s1.
  pose (finite_BotL_premises_of_S s). destruct s1.
  pose (finite_ImpR_premises_of_S s). destruct s1.
  pose (finite_ImpL_premises_of_S s). destruct s1.
  pose (finite_KR_premises_of_S s). destruct s1.
  exists (x ++ x0 ++ x1 ++ x2 ++ x3).
  split.
  * intro RA. inversion RA.
    { inversion H. subst. pose (p []). destruct p4. apply InT_or_app. auto. }
    { inversion H. subst. pose (p0 []). destruct p4. apply InT_or_app. right. apply InT_or_app. auto. }
    { inversion H. subst. pose (p1 [(Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)]). destruct p4.
      apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. left. auto. }
    { inversion H. subst. pose (p2 [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]).
      destruct p4. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. right.
      apply InT_or_app. left. auto. }
    { inversion X. subst. pose (p3 [(unboxed_list BΓ, [A])]).
      destruct p4. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app.
      right. apply InT_or_app. auto. }
  * intro. apply InT_app_or in H. destruct H.
    { apply p in i. apply IdP ; try intro ; try apply f ; try auto ; try assumption. }
    { apply InT_app_or in i. destruct i.
      - apply p0 in i. apply BotL ; try intro ; try apply f ; try auto ; try assumption.
      - apply InT_app_or in i. destruct i.
        + apply p1 in i. apply ImpR ; try intro ; try apply f ; try auto ; try assumption.
        + apply InT_app_or in i. destruct i.
          * apply p2 in i. apply ImpL ; try intro ; try apply f ; try auto ; try assumption.
          * apply p3 in i. apply KR ; try intro ; try apply f ; try auto ; try assumption. }
Qed.

(* The next definitions "flattens" a list of lists of premises to a list of premises.*)

Definition list_of_premises (s : Seq) : list Seq :=
         flatten_list (proj1_sigT2 (finite_premises_of_S s)).

Lemma InT_list_of_premises_exists_prems : forall s prem, InT prem (list_of_premises s) ->
            existsT2 prems, (InT prem prems) * (KS_rules prems s).
Proof.
intros s prem X. unfold list_of_premises in X.
apply InT_flatten_list_InT_elem in X. destruct X. destruct p.
exists x. split. auto.
destruct (finite_premises_of_S s). pose (p x). destruct p0. apply k. assumption.
Qed.

Lemma exists_prems_InT_list_of_premises : forall s prem,
            (existsT2 prems, (InT prem prems) * (KS_rules prems s)) ->
            InT prem (list_of_premises s).
Proof.
intros. destruct X. destruct p. unfold list_of_premises. destruct (finite_premises_of_S s).
pose (p x). destruct p0. apply InT_trans_flatten_list with (bs:=x). assumption. simpl. apply i0.
assumption.
Qed.

Lemma find_the_max_mhd : forall concl l
      (Prem_mhd : forall prems : list Seq, KS_rules prems concl ->
                  forall prem : Seq, InT prem prems ->
                  existsT2 Dprem : derrec KS_rules (fun _ : Seq => True) prem,
                  is_mhd Dprem)
      (H1 : forall prem : Seq, InT prem l -> InT prem (list_of_premises concl))
      (H2 : forall (prem : Seq) (J : InT prem l), InT prem (proj1_sigT2
            (InT_list_of_premises_exists_prems concl _ (H1 prem J))))
      (H3 : forall (prem : Seq) (J : InT prem l), KS_rules (proj1_sigT2
            (InT_list_of_premises_exists_prems concl _ (H1 prem J))) concl)
      (NotNil: l <> nil),

existsT2 prem, existsT2 (J0: InT prem l), forall prem' (J1: InT prem' l),
       (derrec_height (proj1_sigT2 (Prem_mhd
        (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1 prem' J1)))
        (H3 prem' J1)
        prem'
        (H2 prem' J1))))
       <=
       (derrec_height (proj1_sigT2 (Prem_mhd
        (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1 prem J0)))
        (H3 prem J0)
        prem
        (H2 prem J0)))).
Proof.
induction l ; intros.
- exfalso. apply NotNil. reflexivity.
- clear NotNil. destruct l as [ | r l].
  * exists a. assert (InT a [a]). apply InT_eq. exists H. intros. inversion J1. subst.
    destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1 prem' H))) (H3 prem' H) prem' (H2 prem' H)).
    destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1 prem' J1))) (H3 prem' J1) prem' (H2 prem' J1)).
    simpl. auto. inversion H4.
  * assert (H1' : forall prem : Seq, InT prem (r :: l) -> InT prem (list_of_premises concl)).
    { intros. apply H1. apply InT_cons. assumption. }
    assert (Prem_mhd' : forall prems : list Seq, KS_rules prems concl -> forall prem : Seq,
                        InT prem prems -> existsT2 Dprem : derrec KS_rules (fun _ : Seq => True)
                        prem, is_mhd Dprem).
    { intros. apply Prem_mhd with (prems:= prems) ; try assumption. }
    assert (H2' : forall (prem : Seq) (J : InT prem (r :: l)), InT prem (proj1_sigT2
                  (InT_list_of_premises_exists_prems concl _ (H1' prem J)))).
    { intros. assert (InT prem (a :: r :: l)). apply InT_cons. assumption. pose (H2 _ H).
      destruct (InT_list_of_premises_exists_prems concl _ (H1' prem J)).
      simpl. destruct p. assumption. }
    assert (H3' : forall (prem : Seq) (J : InT prem (r :: l)), KS_rules
                (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1' prem J))) concl).
    { intros. destruct (InT_list_of_premises_exists_prems concl _ (H1' prem J)). simpl. destruct p.
      assumption. }
    assert (r :: l <> []). intro. inversion H.
    pose (IHl Prem_mhd' H1' H2' H3' H). destruct s. destruct s.
    (* I have a max in r :: l: so I simply need to compare it with a. *)
    assert (J2: InT a (a :: r :: l)). apply InT_eq.
    assert (J3: InT x (a :: r :: l)). apply InT_cons. assumption.
    (* The next assert decides on le between mhd of a and mhd of x. *)
    pose (dec_le
      (derrec_height (proj1_sigT2 (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1 a J2)))
      (H3 a J2) a (H2 a J2))))
      (derrec_height
       (proj1_sigT2
          (Prem_mhd' (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1' x x0))) 
             (H3' x x0) x (H2' x x0))))).
    destruct s.
    + exists x. exists J3. intros. inversion J1. subst.
      destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1 prem' J1))) 
      (H3 prem' J1) prem' (H2 prem' J1)). simpl.
      destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1 prem' J2))) 
      (H3 prem' J2) prem' (H2 prem' J2)). simpl in l1. unfold is_mhd in i0.
      pose (i0 x1).
      destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1 x J3))) (H3 x J3) x (H2 x J3)).
      simpl.
      destruct (Prem_mhd' (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1' x x0))) 
      (H3' x x0) x (H2' x x0)). simpl in l1.
      unfold is_mhd in i1. pose (i1 x4). lia.
      destruct (Prem_mhd' (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1' x x0)))
      (H3' x x0) x (H2' x x0)). simpl in l0.
      destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1 x J3))) (H3 x J3) x (H2 x J3)).
      simpl.
      destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1 prem' J1)))). simpl.
      assert (derrec_height
     (proj1_sigT2
        (Prem_mhd' (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1' prem' H4)))
           (H3' prem' H4) prem' (H2' prem' H4))) <= derrec_height x1).
      apply (l0 prem' H4). subst.
      unfold is_mhd in i0. pose (i0 x1).
      destruct (Prem_mhd' (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1' prem' H4)))
           (H3' prem' H4) prem' (H2' prem' H4)). simpl in H6. unfold is_mhd in i2. pose (i2 x3). lia.
    + exists a. exists J2. intros. apply le_False_lt in f.
      inversion J1.
      { subst. destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1 prem' J1))) 
        (H3 prem' J1) prem' (H2 prem' J1)). simpl.
        destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1 prem' J2))) 
        (H3 prem' J2) prem' (H2 prem' J2)).
        simpl. unfold is_mhd in i0. pose (i0 x1). lia. }
      { subst.
        destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1 a J2))) (H3 a J2) a (H2 a J2)).
        simpl.
        destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1 prem' J1))) 
        (H3 prem' J1) prem' (H2 prem' J1)). simpl.
        destruct (Prem_mhd' (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1' x x0))) 
             (H3' x x0) x (H2' x x0)). simpl in l0.
        assert (derrec_height
       (proj1_sigT2
          (Prem_mhd' (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1' prem' H4)))
             (H3' prem' H4) prem' (H2' prem' H4))) <= derrec_height x3). apply l0.
       destruct (Prem_mhd' (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1' prem' H4)))
             (H3' prem' H4) prem' (H2' prem' H4)). simpl in H0. simpl in f. unfold is_mhd in i2.
       pose (i2 x2). lia. }
Qed.

Lemma term_IH_help : forall concl,
     (existsT2 prems, (KS_rules prems concl) * (prems <> [])) ->
     (forall prems, KS_rules prems concl -> (forall prem, InT prem prems -> (existsT2 Dprem, @is_mhd prem Dprem)))
      ->
     (existsT2 Maxprems Maxprem DMaxprem, (KS_rules Maxprems concl) * (@is_mhd Maxprem DMaxprem) * (InT Maxprem Maxprems) *
        (forall prems prem (Dprem : KS_drv prem), KS_rules prems concl -> InT prem prems ->
            derrec_height Dprem <= derrec_height DMaxprem)).
Proof.
intros concl FAH Prem_mhd.
pose (list_of_premises concl).
assert (H1: forall prem, InT prem l -> InT prem (list_of_premises concl)).
intros. auto.
assert (H2: forall prem (J: InT prem l), InT prem (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1 prem J)))).
intros. destruct (InT_list_of_premises_exists_prems concl _ (H1 prem J)). destruct p. auto.
assert (H3: forall prem (J: InT prem l),
KS_rules (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1 prem J))) concl).
intros. destruct (InT_list_of_premises_exists_prems concl _ (H1 prem J)). destruct p. auto.
assert (H4: forall prem (J: InT prem l), is_mhd (proj1_sigT2 (Prem_mhd
        (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1 prem J)))
        (H3 prem J)
        prem
        (H2 prem J)))).
intros. intro. destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1 prem J)))
(H3 prem J) prem (H2 prem J)). auto.
assert (l <> []). intro. destruct FAH. destruct p. destruct k.
- inversion i. subst. auto.
- inversion b. subst. auto.
- inversion i. subst. pose (@exists_prems_InT_list_of_premises (Γ0 ++ Γ1, Δ0 ++ A --> B :: Δ1) (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)).
  assert (InT (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) (list_of_premises (Γ0 ++ Γ1, Δ0 ++ A --> B :: Δ1))). apply i0.
  exists [(Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)]. split. apply InT_eq. apply ImpR ; assumption.
  assert (InT (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) l). auto. rewrite H in H5. inversion H5.
- inversion i. subst. pose (@exists_prems_InT_list_of_premises (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1) (Γ0 ++ Γ1, Δ0 ++ A :: Δ1)).
  assert (InT (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) (list_of_premises (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1))). apply i0.
  exists [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]. split. apply InT_eq. apply ImpL ; assumption.
  assert (InT (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) l). auto. rewrite H in H5. inversion H5.
- inversion k. subst. pose (@exists_prems_InT_list_of_premises (Γ0, Δ0 ++ Box A :: Δ1) (unboxed_list BΓ, [A])).
  assert (InT (unboxed_list BΓ, [A]) (list_of_premises (Γ0, Δ0 ++ Box A :: Δ1))). apply i.
  exists [(unboxed_list BΓ, [A])]. split. apply InT_eq. apply KR ; assumption.
  assert (InT (unboxed_list BΓ, [A]) l). auto. rewrite H in H6. inversion H6.

- pose (find_the_max_mhd _ _ Prem_mhd H1 H2 H3 H).
  destruct s. destruct s. exists (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1 x x0))).
  exists x. exists (proj1_sigT2 (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1 x x0)))
  (H3 x x0) x (H2 x x0))). repeat split ; try apply H3 ; try apply H4 ; try apply H2.
  intros prems prem Dprem RA IsPrem.
  assert (J3: InT prem l).
  pose (@exists_prems_InT_list_of_premises concl prem). apply i. exists prems. auto.
  assert (E1: derrec_height Dprem <= derrec_height (proj1_sigT2 (Prem_mhd (proj1_sigT2
  (InT_list_of_premises_exists_prems concl _ (H1 prem J3))) (H3 prem J3) prem (H2 prem J3)))).
  destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1 prem J3)))
  (H3 prem J3) prem (H2 prem J3)). auto.
  assert (E2: derrec_height (proj1_sigT2 (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl
  _ (H1 prem J3))) (H3 prem J3) prem (H2 prem J3))) <=
  derrec_height (proj1_sigT2 (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl _ (H1 x x0)))
  (H3 x x0) x (H2 x x0)))). apply l0. lia.
Qed.

Lemma in_drs_concl_in_allT W rules prems ps (cn : W) (drs : dersrec rules prems ps)
  (dtn : derrec rules prems cn) : in_dersrec dtn drs -> InT cn ps.
Proof.
intro ind. induction ind. apply InT_eq.
apply InT_cons. assumption.
Qed.

Lemma dec_non_nil_prems: forall (concl : Seq), ((existsT2 prems, (KS_rules prems concl) * (prems <> []))) +
                                       ((existsT2 prems, (KS_rules prems concl) * (prems <> [])) -> False).
Proof.
intros. destruct (dec_KR_rule concl).
  + destruct s. left. exists [x]. split. apply KR in k ; auto. intro. inversion H.
  + destruct (dec_ImpR_rule concl).
    * destruct s. left. exists [x]. split. apply ImpR in i. assumption. intro. inversion H.
    * destruct (dec_ImpL_rule concl).
      { destruct s. destruct s. left. exists [x; x0]. split. apply ImpL in i. assumption.
        intro. inversion H. }
      { right. intro. destruct X. destruct p. inversion k.
        - subst. inversion H. auto.
        - subst. inversion H. auto.
        - subst. inversion H. subst. apply f0. exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1). assumption.
        - subst. inversion H. subst. apply f1. exists (Γ0 ++ Γ1, Δ0 ++ A :: Δ1).
          exists (Γ0 ++ B :: Γ1, Δ0 ++ Δ1). assumption.
        - subst. inversion X. subst. apply f. exists (unboxed_list BΓ, [A]). assumption. }
Qed.

(* The next theorem claims that every sequent s has a derivation DMax of maximal height. *)

Theorem KS_termin_base : forall n s, (n = measure s) ->
   existsT2 (DMax : KS_drv s), (@is_mhd s DMax).
Proof.
(* Setting up the strong inductions on each. *)
pose (strong_inductionT (fun (x:nat) => forall (s : Seq),
(x = measure s) ->
(existsT2 DMax : derrec KS_rules
(fun _ : Seq => True) s, is_mhd DMax))).
apply s. intros n IH. clear s.

(* Now we can do the pen and paper proof. *)
assert (dersrecnil: dersrec KS_rules (fun _ => True) nil).
apply dersrec_nil.
intros. pose (dec_KS_rules s). destruct s0.
- assert (forall ps : list Seq, KS_rules ps s -> False).
  intros. apply f. exists ps. assumption. pose (@no_KS_rule_applic s H0).
  pose (dpI KS_rules (fun _ : Seq => True) s I).
  exists d. unfold is_mhd. intros. simpl. pose (e D1). rewrite e0. auto.
- assert (forall prems, KS_rules prems s -> (forall prem, InT prem prems ->
  (existsT2 Dprem, @is_mhd prem Dprem))).
  { simpl. intros prems X prem X0. inversion X.
    - inversion H0. subst. exfalso. inversion X0.
    - inversion H0. subst. exfalso. inversion X0.
    - inversion H0. subst. inversion X0. 2: inversion H1. subst.
      assert (J0: measure (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) < measure (Γ0 ++ Γ1, Δ0 ++ A --> B :: Δ1)).
      unfold measure. simpl.
      repeat rewrite size_LF_dist_app. simpl. lia.
      pose (IH (measure (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)) J0 (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)).
      apply s. reflexivity.
    - inversion H0. subst. inversion X0 ; subst.
     + assert (J0: measure (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) < measure (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)).
        unfold measure. simpl. repeat rewrite size_LF_dist_app. simpl. lia.
        pose (IH (measure (Γ0 ++ Γ1, Δ0 ++ A :: Δ1)) J0 (Γ0 ++ Γ1, Δ0 ++ A :: Δ1)).
        apply s. reflexivity.
     + inversion H1. subst.
        assert (J0: measure (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) < measure (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)).
        unfold measure. simpl. repeat rewrite size_LF_dist_app. simpl. lia.
        pose (IH (measure (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)) J0 (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)).
        apply s. reflexivity. inversion H2.
    - inversion X1. subst. inversion X0. 2: inversion H0. subst.
      assert (J0: measure (unboxed_list BΓ, [A]) < measure (Γ0, Δ0 ++ Box A :: Δ1)).
      unfold measure. simpl. repeat rewrite size_LF_dist_app. simpl.
      pose (size_nobox_gen_ext _ _ X2). pose (size_unboxed BΓ). lia.
      pose (IH (measure (unboxed_list BΓ, [A])) J0 (unboxed_list BΓ, [A])).
      apply s. reflexivity. }
    destruct (dec_non_nil_prems s).
    + pose (@term_IH_help s s1 X). repeat destruct s2. destruct p. destruct p. destruct p.
      inversion k.
      (* Use PIH and SIH here, depending on the rule applied *)
      * inversion H0. subst. inversion i.
      * inversion H0. subst. inversion i.
      * subst. inversion H0. subst. assert (E: x0 = (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)).
        inversion i. auto. inversion H1. subst.
        pose (dlCons x1 dersrecnil).
        pose (@derI _ _ (fun _ : Seq => True) [(Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)] (Γ0 ++ Γ1, Δ0 ++ A --> B :: Δ1) k d).
        exists d0. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil). rewrite Nat.max_0_r.
        destruct D1.
        { simpl. lia. }
        { simpl.
          assert (forall p (d : derrec KS_rules (fun _ : Seq => True) p),
          in_dersrec d d1 -> derrec_height d <= (derrec_height x1)). intros.
          pose (@in_drs_concl_in_allT _ _ _ _ _ _ _ X0). subst. pose (l ps p d2 k0 i1). assumption.
          pose (dersrec_height_le H). lia. }
        { reflexivity. }
      * subst. inversion H0. subst. inversion i.
        { subst. pose (dpI KS_rules (fun _ : Seq => True) (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) I).
          pose (dlCons d dersrecnil). pose (dlCons x1 d0).
          pose (@derI _ _ (fun _ : Seq => True) [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]
          (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1) k d1).
          exists d2. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil). rewrite Nat.max_0_r.
          destruct D1.
          { simpl. lia. }
          { simpl.
            assert (forall p (d : derrec KS_rules (fun _ : Seq => True) p),
            in_dersrec d d3 -> derrec_height d <= (derrec_height x1)). intros.
            pose (@in_drs_concl_in_allT _ _ _ _ _ _ _ X0). subst. pose (l ps p d4 k0 i1). assumption.
            pose (dersrec_height_le H). lia. }
          { reflexivity. } }
        { inversion H1. subst. pose (dpI KS_rules (fun _ : Seq => True) (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) I).
          pose (dlCons x1 dersrecnil). pose (dlCons d d0).
          pose (@derI _ _ (fun _ : Seq => True) [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]
          (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1) k d1).
          exists d2. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil). rewrite Nat.max_0_r.
          destruct D1.
          { simpl. lia. }
          { simpl.
            assert (forall p (d : derrec KS_rules (fun _ : Seq => True) p),
            in_dersrec d d3 -> derrec_height d <= (derrec_height x1)). intros.
            pose (@in_drs_concl_in_allT _ _ _ _ _ _ _ X0). subst. pose (l ps p d4 k0 i1). assumption.
            pose (dersrec_height_le H). lia. }
          { reflexivity. }
          inversion H4. }
      * subst. inversion X0. subst. assert (E: x0 = (unboxed_list BΓ, [A])).
        inversion i. subst. auto. inversion H1. subst.
        pose (dlCons x1 dersrecnil).
        pose (@derI _ _ (fun _ : Seq => True) [(unboxed_list BΓ, [A])] (Γ0, Δ0 ++ Box A :: Δ1) k d).
        exists d0. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil). rewrite Nat.max_0_r.
        destruct D1.
        { simpl. lia. }
        { simpl.
          assert (forall p (d : derrec KS_rules (fun _ : Seq => True) p),
          in_dersrec d d1 -> derrec_height d <= (derrec_height x1)). intros.
          pose (@in_drs_concl_in_allT _ _ _ _ _ _ _ X2). subst. pose (l ps p d2 k0 i1). assumption.
          pose (dersrec_height_le H0). lia. }
        { reflexivity. }
    + destruct s0. inversion k.
      * inversion H0. subst. pose (@derI _ _ (fun _ : Seq => True) [] (Γ0 ++ # P :: Γ1, Δ0 ++ # P :: Δ1) k dersrecnil).
        exists d. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil).
        destruct D1.
        { simpl. lia. }
        { simpl. destruct k0.
          - inversion i. subst. rewrite dersrec_height_nil with (ds:=d0). lia. reflexivity.
          - inversion b. subst. rewrite dersrec_height_nil with (ds:=d0). lia. reflexivity.
          - inversion i. subst. exfalso. apply f. exists [(Γ2 ++ A :: Γ3, Δ2 ++ B :: Δ3)]. split.
            apply ImpR in i. assumption. intro. inversion H.
          - inversion i. subst. exfalso. apply f. exists [(Γ2 ++ Γ3, Δ2 ++ A :: Δ3); (Γ2 ++ B :: Γ3, Δ2 ++ Δ3)]. split.
            apply ImpL in i. assumption. intro. inversion H.
          - inversion k0. subst. exfalso. apply f. exists [(unboxed_list BΓ, [A])]. split.
            apply KR in k0. assumption. intro. inversion H1. }
        { reflexivity. }
      * inversion H0. subst. pose (@derI _ _ (fun _ : Seq => True) [] (Γ0 ++ Bot :: Γ1, Δ) k dersrecnil).
        exists d. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil).
        destruct D1.
        { simpl. lia. }
        { simpl. destruct k0.
          - inversion i. subst. rewrite dersrec_height_nil with (ds:=d0). lia. reflexivity.
          - inversion b. subst. rewrite dersrec_height_nil with (ds:=d0). lia. reflexivity.
          - inversion i. subst. exfalso. apply f. exists [(Γ2 ++ A :: Γ3, Δ0 ++ B :: Δ1)]. split.
            apply ImpR in i. assumption. intro. inversion H.
          - inversion i. subst. exfalso. apply f. exists [(Γ2 ++ Γ3, Δ0 ++ A :: Δ1); (Γ2 ++ B :: Γ3, Δ0 ++ Δ1)]. split.
            apply ImpL in i. assumption. intro. inversion H.
          - inversion k0. subst. exfalso. apply f. exists [(unboxed_list BΓ, [A])]. split.
            apply KR in k0. assumption. intro. inversion H1. }
        { reflexivity. }
      * inversion H0. subst. exfalso. apply f. exists [(Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)]. split. assumption. intro.
        inversion H.
      * inversion H0. subst. exfalso. apply f. exists [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]. split. assumption. intro.
        inversion H.
      * inversion X0. subst. exfalso. apply f. exists [(unboxed_list BΓ, [A])]. split. assumption. intro.
        inversion H.
Qed.


Theorem KS_termin : forall s, existsT2 (DMax : KS_drv s), (@is_mhd s DMax).
Proof.
intro s. pose (@KS_termin_base (measure s)). apply s0 ; reflexivity.
Qed.

Theorem KS_termin1 : forall (s : Seq), exists (DMax : KS_drv s), (is_mhd DMax).
Proof.
intro s.
assert (J1: measure s = measure s). reflexivity.
pose (@KS_termin_base (measure s) s J1).
destruct s0. exists x. assumption.
Qed.

Theorem KS_termin2 : forall s, exists (DMax : KS_drv s), (is_mhd DMax).
Proof.
intro s.
assert (J1: measure s = measure s). reflexivity.
pose (@KS_termin_base (measure s) s J1 ).
destruct s0. exists x. assumption.
Qed.

Theorem KS_termin3 : forall (s : Seq), existsT2 (DMax : KS_drv s), (is_mhd DMax).
Proof.
intro s. pose (@KS_termin_base (measure s)). apply s0 ; reflexivity.
Qed.

(* Now we can prove that the maximal height of derivations (mhd) for sequents
   decreases upwards in the applicability of the proofs. In other words, if a sequent s is the
   conclusion of an instance of a rule R of KS with premises in ps, then for any element s0 of
   ps we have that (mhd s0) < (mhd s).

   To do so we first define mhd.*)

Definition mhd (s: Seq) : nat := derrec_height (proj1_sigT2 (KS_termin s)).

Lemma KS_termin_der_is_mhd : forall s, (@is_mhd s (proj1_sigT2 (@KS_termin s))).
Proof.
intro s. destruct KS_termin. auto.
Qed.

Theorem RA_mhd_decreases : forall prems concl, (KS_rules prems concl) ->
                             (forall prem, (In prem prems) -> (mhd prem) < (mhd concl)).
Proof.
intros. inversion X.
- inversion H0. subst. inversion H.
- inversion H0. subst. inversion H.
- inversion H0. subst. inversion H.
  * subst. apply le_False_lt. intro.
    pose (d:= proj1_sigT2 (KS_termin (Γ0 ++ Γ1, Δ0 ++ A --> B :: Δ1))).
    pose (d0:=proj1_sigT2 (KS_termin (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1))).
    assert (dersrecnil: dersrec KS_rules (fun _ => True) nil).
    apply dersrec_nil. pose (dlCons d0 dersrecnil).
    pose (@derI _ _ (fun _ : Seq => True) [(Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)] (Γ0 ++ Γ1, Δ0 ++ A --> B :: Δ1) X d1).
    assert (E1: derrec_height d0 = mhd (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)).
    unfold mhd. auto.
    assert (E2: derrec_height d = mhd (Γ0 ++ Γ1, Δ0 ++ A --> B :: Δ1)).
    unfold mhd. auto.
    assert (@is_mhd (Γ0 ++ Γ1, Δ0 ++ A --> B :: Δ1) d). apply KS_termin_der_is_mhd.
    unfold is_mhd in H2. pose (H2 d2). simpl in l. rewrite dersrec_height_nil in l. rewrite Nat.max_0_r in l.
    lia. reflexivity.
  * inversion H1.
- inversion H0. subst. inversion H.
    * subst. apply le_False_lt. intro.
      pose (d:=proj1_sigT2 (KS_termin (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1))).
      pose (d0:=proj1_sigT2 (KS_termin (Γ0 ++ Γ1, Δ0 ++ A :: Δ1))).
      assert (dersrecnil: dersrec KS_rules (fun _ => True) nil).
      apply dersrec_nil.
      pose (dpI KS_rules (fun _ : Seq => True) (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) I).
      pose (dlCons d1 dersrecnil). pose (dlCons d0 d2).
      pose (@derI _ _ (fun _ : Seq => True) [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]
      (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1) X d3).
      assert (E1: derrec_height d0 = mhd (Γ0 ++ Γ1, Δ0 ++ A :: Δ1)).
      unfold mhd. auto.
      assert (E2: derrec_height d = mhd (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)).
      unfold mhd. auto.
      assert (@is_mhd (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1) d). apply KS_termin_der_is_mhd.
      unfold is_mhd in H2. pose (H2 d4). simpl in l. rewrite dersrec_height_nil in l. rewrite Nat.max_0_r in l.
      lia. reflexivity.
    * inversion H1. subst. apply le_False_lt. intro.
      pose (d:=proj1_sigT2 (KS_termin (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1))).
      pose (d0:=proj1_sigT2 (KS_termin (Γ0 ++ B :: Γ1, Δ0 ++ Δ1))).
      assert (dersrecnil: dersrec KS_rules (fun _ => True) nil).
      apply dersrec_nil.
      pose (dpI KS_rules (fun _ : Seq => True) (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) I).
      pose (dlCons d0 dersrecnil). pose (dlCons d1 d2).
      pose (@derI _ _ (fun _ : Seq => True) [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]
      (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1) X d3).
      assert (E1: derrec_height d0 = mhd (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)).
      unfold mhd. auto.
      assert (E2: derrec_height d = mhd (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)).
      unfold mhd. auto.
      assert (@is_mhd (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1) d). apply KS_termin_der_is_mhd.
      unfold is_mhd in H3. pose (H3 d4). simpl in l. rewrite dersrec_height_nil in l. rewrite Nat.max_0_r in l.
      simpl in l. lia. reflexivity. inversion H2.
- inversion X0. subst. inversion H.
  * subst. apply le_False_lt. intro.
    pose (d:=proj1_sigT2 (KS_termin (Γ0, Δ0 ++ Box A :: Δ1))).
    pose (d0:=proj1_sigT2 (KS_termin (unboxed_list BΓ, [A]))).
    assert (dersrecnil: dersrec KS_rules (fun _ => True) nil).
    apply dersrec_nil. pose (dlCons d0 dersrecnil).
    pose (@derI _ _ (fun _ : Seq => True) [(unboxed_list BΓ, [A])] (Γ0, Δ0 ++ Box A :: Δ1) X d1).
    assert (E1: derrec_height d0 = mhd (unboxed_list BΓ, [A])).
    unfold mhd. auto.
    assert (E2: derrec_height d = mhd (Γ0, Δ0 ++ Box A :: Δ1)).
    unfold mhd. auto.
    assert (@is_mhd (Γ0, Δ0 ++ Box A :: Δ1) d). apply KS_termin_der_is_mhd.
    unfold is_mhd in H1. pose (H1 d2). simpl in l. rewrite dersrec_height_nil in l. rewrite Nat.max_0_r in l.
    lia. reflexivity.
  * inversion H0.
Qed.

