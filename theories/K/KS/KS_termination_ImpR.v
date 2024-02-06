Require Import List.
Export ListNotations.
Require Import Lia.
Require Import PeanoNat.

Require Import KS_calc.
Require Import KS_dec.
Require Import KS_termination_measure.
Require Import KS_termination_prelims.

(* Now we can prove that a sequent has only finitely many potential premises via the ImpR rules.

   The next definition simply takes a list of formulae l and a sequent s. It outputs a list of sequents.
   These sequents are generated when there is an implication (Imp A B) encountered in l. With such an
   implication, the function will stack the list of all insertions of A on the left of s and of B on
   the right of s (roughly: in fact you need to destroy all such implications on the right to get an ImpRRule
   premise), and then continues computing on the rest of l. *)

Fixpoint prems_Imp_R (l : list ((MPropF) * nat)) (s : Seq) : list Seq :=
match l with
  | nil => nil
  | (C, n) :: t => match n with
                    | 0 => prems_Imp_R t s
                    | S m => match C with
                                | Imp A B => (listInsertsR_Seqs (fst s)
                                               ((fst (nth_split m (remove_nth (S m) C (snd s)))) ++
                                               B :: (snd (nth_split m (remove_nth (S m) C (snd s)))))
                                               A)
                                             ++ (prems_Imp_R t s)
                                | _ => prems_Imp_R t s
                                end
                   end
end.

Lemma In_pos_top_imps_0_False : forall l (A : MPropF), In (A, 0) (pos_top_imps l) -> False.
Proof.
- induction l.
  * intros. inversion H.
  * intros. simpl in H. destruct a.
    + simpl in H. apply In_InT_pair in H. apply InT_map_iff in H. destruct H.
      destruct p. destruct x. inversion e.
    + simpl in H. apply In_InT_pair in H. apply InT_map_iff in H. destruct H.
      destruct p. destruct x. inversion e.
    + simpl in H. destruct H. inversion H. apply In_InT_pair in H. apply InT_map_iff in H. destruct H.
      destruct p. destruct x. inversion e.
    + simpl in H. apply In_InT_pair in H. apply InT_map_iff in H. destruct H.
      destruct p. destruct x. inversion e.
Qed.

Lemma In_pos_top_imps_imp : forall l (A : MPropF) n, In (A, n) (pos_top_imps l) -> (existsT2 C D, A = Imp C D).
Proof.
induction l ; intros.
- simpl in H. inversion H.
- simpl in H. destruct a ; try apply IHl in H. apply In_InT_pair in H. apply InT_map_iff in H. destruct H.
  destruct p. inversion e. destruct x. subst. apply InT_In in i. apply IHl in i. assumption.
  apply In_InT_pair in H. apply InT_map_iff in H. destruct H.
  destruct p. inversion e. destruct x. subst. apply InT_In in i. apply IHl in i. assumption.
  apply In_InT_pair in H. inversion H. subst. inversion H1. exists a1. exists a2. reflexivity.
  subst. apply InT_map_iff in H1. destruct H1. destruct p. destruct x. simpl in e. inversion e.
  subst. apply InT_In in i. apply IHl in i. assumption.
  apply In_InT_pair in H. apply InT_map_iff in H. destruct H.
  destruct p. inversion e. destruct x. subst. apply InT_In in i. apply IHl in i. assumption.
Qed.

Lemma In_pos_top_imps_In_l : forall l (A : MPropF) n, In (A, n) (pos_top_imps l) -> In A l.
Proof.
induction l.
- intros. simpl in H. destruct H.
- intros. simpl in H. destruct a.
  * apply in_cons. apply In_InT_pair in H. apply InT_map_iff in H. destruct H.
    destruct p. destruct x. inversion e. subst. apply InT_In in i. apply IHl in i.
    assumption.
  * apply in_cons. apply In_InT_pair in H. apply InT_map_iff in H. destruct H.
    destruct p. destruct x. inversion e. subst. apply InT_In in i. apply IHl in i.
    assumption.
  * inversion H.
    + inversion H0. subst. apply in_eq.
    + apply in_cons. apply In_InT_pair in H0. apply InT_map_iff in H0. destruct H0.
      destruct p. destruct x. inversion e. subst. apply InT_In in i. apply IHl in i.
      assumption.
  *  apply In_InT_pair in H. apply InT_map_iff in H. destruct H.
    destruct p. destruct x. inversion e. subst. apply InT_In in i. apply IHl in i.
    apply in_cons. assumption.
Qed.

Lemma In_pos_top_imps_split_l : forall l (A : MPropF) n, In (A, S n) (pos_top_imps l) -> 
          existsT2 l0 l1, (l = l0 ++ A :: l1) /\
                          (length l0 = n) /\
                          (l0 = fst (nth_split n (remove_nth (S n) A l))) /\
                          (l1 = snd (nth_split n (remove_nth (S n) A l))).
Proof.
induction l.
- intros. simpl. exfalso. simpl in H. destruct H.
- intros. simpl in H. destruct a.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H as ([m n1] & e & i).
    simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_imps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). destruct s as (x & x0 & e2 & e3 & e1 & e0).
    subst. exists (# n0 :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (# n0 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
    # n0 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (# n0 :: x))). simpl. reflexivity.
    rewrite H0. assert ((# n0 :: x ++ A :: x0) = ((# n0 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (# n0 :: x) x0). simpl (length (# n0 :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (# n0 :: x))). simpl. reflexivity.
    rewrite H. assert ((# n0 :: x ++ A :: x0) = ((# n0 :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (# n0 :: x) x0). simpl (length (# n0 :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H as ([m n1] & e & i).
    simpl in e. inversion e. subst. destruct n.
    -- exfalso. apply InT_In in i. apply In_pos_top_imps_0_False in i. assumption.
      -- apply InT_In in i. pose (IHl A n i). destruct s as (x & x0 & e2 & e3 & e1 & e0).
      subst. exists (Bot :: x). exists x0. repeat split.
      rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
      assert (fst (Bot :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      Bot :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (Bot :: x))). simpl. reflexivity.
    rewrite H0. assert ((Bot :: x ++ A :: x0) = ((Bot :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (Bot :: x) x0). simpl (length (Bot :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (Bot :: x))). simpl. reflexivity.
    rewrite H. assert ((Bot :: x ++ A :: x0) = ((Bot :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (Bot :: x) x0). simpl (length (Bot :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. inversion H.
    + inversion H1. subst. exists []. exists l. repeat split. simpl.
      destruct (eq_dec_form (a1 --> a2) (a1 --> a2)). reflexivity. exfalso. auto.
    + subst. apply InT_map_iff in H1. destruct H1 as ([m n1] & e & i).
        simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_imps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). destruct s as (x & x0 & e2 & e3 & e1 & e0).
        subst. exists (a1 --> a2 :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst (a1 --> a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        a1 --> a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length (a1 --> a2 :: x))). simpl. reflexivity.
        rewrite H1. assert ((a1 --> a2 :: x ++ A :: x0) = ((a1 --> a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H2. clear H2. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL (a1 --> a2 :: x) x0). simpl (length (a1 --> a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length (a1 --> a2 :: x))). simpl. reflexivity.
        rewrite H0. assert ((a1 --> a2 :: x ++ A :: x0) = ((a1 --> a2 :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idR (a1 --> a2 :: x) x0). simpl (length (a1 --> a2 :: x)) in e2.
        rewrite <- e2. reflexivity.
        * apply In_InT_pair in H. apply InT_map_iff in H. destruct H as ([m n1] & e & i).
         simpl in e. inversion e. subst. destruct n. exfalso.
        apply InT_In in i. apply In_pos_top_imps_0_False in i. assumption.
        apply InT_In in i. pose (IHl A n i). destruct s  as (x & x0 & e2 & e3 & e1 & e0).
        subst. exists (Box a :: x). exists x0. repeat split.
        rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
        assert (fst (Box a :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
        Box a :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
        assert (S (S (length x)) = S (length (Box a :: x))). simpl. reflexivity.
        rewrite H0. assert ((Box a :: x ++ A :: x0) = ((Box a :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
        pose (nth_split_idL (Box a :: x) x0). simpl (length (Box a :: x)) in e2.
        rewrite <- e2. reflexivity.
        rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
        assert (S (S (length x)) = S (length (Box a :: x))). simpl. reflexivity.
        rewrite H. assert ((Box a :: x ++ A :: x0) = ((Box a :: x) ++ A :: x0)). simpl. reflexivity.
        rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
        pose (nth_split_idR (Box a :: x) x0). simpl (length (Box a :: x)) in e2.
        rewrite <- e2. reflexivity.
Qed.

Lemma In_l_imp_In_pos_top_imps : forall l (A B : MPropF), In (Imp A B) l ->
                                    existsT2 n, In ((Imp A B), n) (pos_top_imps l).
Proof.
induction l.
- intros. simpl in H. destruct H.
- intros. apply In_InT in H. inversion H.
  * subst. exists 1. simpl. left. reflexivity.
  * destruct a.
    + subst. apply InT_In in H1. apply IHl in H1. destruct H1. exists (S x). simpl.
      apply InT_In. apply InT_map_iff. exists (A --> B, x). simpl. split ; auto.
      apply In_InT_pair. assumption.
    + subst. apply InT_In in H1. apply IHl in H1. destruct H1. exists (S x). simpl.
      apply InT_In. apply InT_map_iff. exists (A --> B, x). simpl. split ; auto.
      apply In_InT_pair. assumption.
    + subst. apply InT_In in H1. apply IHl in H1. destruct H1. exists (S x). simpl.
      right. apply InT_In. apply InT_map_iff. exists (A --> B, x). simpl. split ; auto.
      apply In_InT_pair. assumption.
    + subst. apply InT_In in H1. apply IHl in H1. destruct H1. exists (S x). simpl.
      apply InT_In. apply InT_map_iff. exists (A --> B, x). simpl. split ; auto.
      apply In_InT_pair. assumption.
Qed.

Lemma Good_pos_in_pos_top_imps : forall A B Δ0 Δ1,
              In (A --> B, S (length Δ0)) (pos_top_imps (Δ0 ++ A --> B :: Δ1)).
Proof.
induction Δ0.
- intros. simpl. auto.
- intros. destruct a.
  * simpl. apply InT_In. apply InT_map_iff. exists (A --> B, S (length Δ0)).
    split. simpl. reflexivity. apply In_InT_pair. apply IHΔ0.
  * simpl. apply InT_In. apply InT_map_iff. exists (A --> B, S (length Δ0)).
    split. simpl. reflexivity. apply In_InT_pair. apply IHΔ0.
  * simpl. right. apply InT_In. apply InT_map_iff. exists (A --> B, S (length Δ0)).
    split. simpl. reflexivity. apply In_InT_pair. apply IHΔ0.
  * simpl. apply InT_In. apply InT_map_iff. exists (A --> B, S (length Δ0)).
    split. simpl. reflexivity. apply In_InT_pair. apply IHΔ0.
Qed.

(* From there we can show that given a specific (Imp A B) on the right of a sequent S,
   there is only finitely many premises via ImpR applied on this implication. But we
   need to do it for all implications on the right of this sequent. *)

Lemma ImpR_help01 : forall prem s l, InT prem (prems_Imp_R l s) ->
                  (existsT2 n A B Γ0 Γ1 Δ0 Δ1,
                        (In ((Imp A B), S n) l) /\
                        (prem = (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)) /\
                        (Γ0 ++ Γ1 = fst s) /\
                        (Δ0 = (fst (nth_split n (remove_nth (S n) (Imp A B) (snd s))))) /\
                        (Δ1 = (snd (nth_split n (remove_nth (S n) (Imp A B) (snd s)))))).
Proof.
intros prem s. destruct s. destruct prem. induction l3 ; intros X.
- simpl in X. inversion X.
- destruct a as [m n]. destruct m.
  * simpl in X. destruct n.
    + pose (IHl3 X). destruct s as (x & x0 & x1 & x2 & x3 & x4 & x5 & p).
        decompose record p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. repeat split ; try auto. apply in_cons. tauto.
    + pose (IHl3 X). destruct s as (x & x0 & x1 & x2 & x3 & x4 & x5 & p). decompose record p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. repeat split ; try tauto. apply in_cons. tauto.
  * simpl in X. destruct n.
    + pose (IHl3 X). destruct s as (x & x0 & x1 & x2 & x3 & x4 & x5 & p). decompose record p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. repeat split ; try tauto. apply in_cons. tauto.
    + pose (IHl3 X). destruct s as (x & x0 & x1 & x2 & x3 & x4 & x5 & p). decompose record p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. repeat split ; try tauto. apply in_cons. tauto.
  * destruct n.
    + pose (IHl3 X). destruct s as (x & x0 & x1 & x2 & x3 & x4 & x5 & p). decompose record p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. repeat split ; try tauto. apply in_cons. tauto.
    + apply InT_app_or in X. destruct X.
      { simpl (fst (l, l0)) in i. simpl (snd (l, l0)) in i.
        unfold listInsertsR_Seqs in i. apply InT_map_iff in i. destruct i.
        destruct p. subst. unfold listInserts in i. apply InT_map_iff in i. destruct i.
        destruct p. destruct x0. subst. destruct (list_of_splits l). simpl in i. exists n.
        exists m1. exists m2. exists l4. exists l5. simpl (snd (l, l0)).
        simpl (fst (l, l0)).
        exists (fst (nth_split n (remove_nth (S n) (m1 --> m2) l0))).
        exists (snd (nth_split n (remove_nth (S n) (m1 --> m2) l0))).
        repeat split ; try auto. apply in_eq. rewrite i0. apply InT_In. assumption. }
      { pose (IHl3 i). destruct s as (x & x0 & x1 & x2 & x3 & x4 & x5 & p). decompose record p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. repeat split ; try tauto. apply in_cons. tauto. }
  * simpl in X. destruct n.
    + pose (IHl3 X). destruct s as (x & x0 & x1 & x2 & x3 & x4 & x5 & p). decompose record p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. repeat split ; try tauto. apply in_cons. tauto.
    + pose (IHl3 X). destruct s as (x & x0 & x1 & x2 & x3 & x4 & x5 & p). decompose record p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. repeat split ; try tauto. apply in_cons. tauto.
Qed.

Lemma ImpR_help1 : forall prem s, InT prem (prems_Imp_R (pos_top_imps (snd s)) s) -> ImpRRule [prem] s.
Proof.
intros prem s X. pose (ImpR_help01 _ _ _ X). destruct s0. destruct s.
destruct s0. destruct s as (B & Γ0 & Γ1 & Δ0 & Δ1 & i & e2 & e3 & e4 & e5).
subst. simpl in i, e3. subst.
simpl (snd (_, _)) in *.
apply In_pos_top_imps_split_l in i. destruct i. destruct s as (x2 & H1 & H2 & H3 & H4).
subst.
rewrite <- H4. rewrite effective_remove_nth. rewrite <- nth_split_idL.
apply ImpRRule_I.
Qed.

Lemma ImpR_help002 : forall Γ0 Γ1 Δ0 Δ1 A B,
           InT (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) (listInsertsR_Seqs (Γ0 ++ Γ1) (Δ0 ++ B :: Δ1) A).
Proof.
intros. unfold listInsertsR_Seqs. apply InT_map_iff. exists (Γ0 ++ A :: Γ1). split.
reflexivity. unfold listInserts. apply InT_map_iff. exists (Γ0, Γ1). simpl. split.
reflexivity. destruct (list_of_splits (Γ0 ++ Γ1)). simpl. pose (i Γ0 Γ1).
apply In_InT_seqs. apply i0. reflexivity.
Qed.

Lemma ImpR_help02 : forall Γ0 Γ1 Δ0 Δ1 A B l n,
                                ImpRRule [(Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)] (Γ0 ++ Γ1, Δ0 ++ (Imp A B) :: Δ1) ->
                                (length Δ0 = n) ->
                                (In ((Imp A B), S n) l) ->
                                InT (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) (prems_Imp_R l (Γ0 ++ Γ1, Δ0 ++ (Imp A B) :: Δ1)).
Proof.
induction l ; intros.
- inversion H1.
- destruct a. destruct m.
  * apply In_InT_pair in H1. inversion H1. subst. inversion H3. subst. apply InT_In in H3.
    assert (J1: length Δ0 = length Δ0). reflexivity.
    pose (IHl _ H J1 H3). simpl. destruct n0. assumption. assumption.
  * apply In_InT_pair in H1. inversion H1. subst. inversion H3. subst. apply InT_In in H3.
    assert (J1: length Δ0 = length Δ0). reflexivity.
    pose (IHl _ H J1 H3). simpl. destruct n0. assumption. assumption.
  * apply In_InT_pair in H1. inversion H1.
    + subst. inversion H3. subst. destruct Δ0.
      { simpl. pose (ImpR_help002 Γ0 Γ1 [] Δ1 A B). simpl in i. destruct (eq_dec_form (A --> B) (A --> B)).
        apply InT_or_app. auto. exfalso. auto. }
      { unfold prems_Imp_R. apply InT_or_app. left.
        assert ((remove_nth (S (length (m :: Δ0))) (A --> B) (snd (Γ0 ++ Γ1, (m :: Δ0) ++ A --> B :: Δ1))) =
        (m :: Δ0) ++ Δ1). simpl (snd (Γ0 ++ Γ1, (m :: Δ0) ++ A --> B :: Δ1)).
        pose (effective_remove_nth (A --> B) (m :: Δ0) Δ1). assumption.
        rewrite H0.
        assert (fst (nth_split (length (m :: Δ0)) ((m :: Δ0) ++ Δ1)) = (m :: Δ0) /\
        snd (nth_split (length (m :: Δ0)) ((m :: Δ0) ++ Δ1)) = Δ1). apply nth_split_length_id.
        reflexivity. destruct H2. rewrite H2. rewrite H4. apply ImpR_help002. }
    + subst. assert (J1: (length Δ0) = (length Δ0)). reflexivity. apply InT_In in H3.
      pose (IHl (length Δ0) H J1 H3). simpl. destruct n0. assumption. apply InT_or_app. auto.
  * apply In_InT_pair in H1. inversion H1. subst. inversion H3. subst. apply InT_In in H3.
    assert (J1: length Δ0 = length Δ0). reflexivity.
    pose (IHl _ H J1 H3). simpl. destruct n0. assumption. assumption.
Qed.

Lemma ImpR_help2 : forall prem s, ImpRRule [prem] s -> InT prem (prems_Imp_R (pos_top_imps (snd s)) s).
Proof.
intros. inversion H. subst. simpl.
pose (@ImpR_help02 Γ0 Γ1 Δ0 Δ1 A B (pos_top_imps (Δ0 ++ A --> B :: Δ1)) (length Δ0)). apply i ; try assumption.
reflexivity. apply Good_pos_in_pos_top_imps.
Qed.

Lemma finite_ImpR_premises_of_S : forall (s : Seq), existsT2 listImpRprems,
              (forall prems, ((ImpRRule prems s) -> (InT prems listImpRprems)) *
                             ((InT prems listImpRprems) -> (ImpRRule prems s))).
Proof.
intro s. destruct s.
exists (map (fun y => [y]) (prems_Imp_R (pos_top_imps l0) (l,l0))).
intros. split ; intro.
- inversion H. subst. apply InT_map_iff.
  exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1). split. reflexivity.
  pose (@ImpR_help2 (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) (Γ0 ++ Γ1, Δ0 ++ A --> B :: Δ1)). simpl in i. apply i.
  assumption.
- apply InT_map_iff in H. destruct H. destruct p. subst. apply ImpR_help1. simpl. assumption.
Qed.