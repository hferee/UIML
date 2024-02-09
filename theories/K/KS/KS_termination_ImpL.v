Require Import List.
Export ListNotations.
Require Import Lia.
Require Import PeanoNat.

Require Import KS_calc.
Require Import KS_dec.
Require Import KS_termination_measure.
Require Import KS_termination_prelims.
Require Import KS_termination_ImpR.



(* Then, we turn to the case of the ImpL rule. *)

Fixpoint prems_Imp_L (l : list ((MPropF) * nat)) (s : Seq) : list (list Seq) :=
match l with
  | nil => nil
  | (C, n) :: t => match n with
      | 0 => prems_Imp_L t s
      | S m => match C with
           | Imp A B => flatten_list
                        (map (fun y => map (fun z => [z; y])
                        (listInsertsL_Seqs ((fst (nth_split m (remove_nth (S m) C (fst s)))) ++
                        (snd (nth_split m (remove_nth (S m) C (fst s))))) (snd s) A))
                        [(((fst (nth_split m (remove_nth (S m) C (fst s)))) ++
                        B :: (snd (nth_split m (remove_nth (S m) C (fst s))))), (snd s))])
                        ++ (prems_Imp_L t s)
           | _ => prems_Imp_L t s
           end
      end
end.

Lemma ImpL_help002 : forall Γ0 Γ1 Δ0 Δ1 A B,
           InT [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]
               (flatten_list (map (fun y : list MPropF * list MPropF => map
               (fun z : list MPropF * list MPropF => [y; z]) [(Γ0 ++ B :: Γ1, Δ0 ++ Δ1)])
               (listInsertsL_Seqs (Γ0 ++ Γ1) (Δ0 ++ Δ1) A)))
              .
Proof.
intros.
pose (@InT_trans_flatten_list _ (map (fun y : list MPropF * list MPropF => map
(fun z : list MPropF * list MPropF => [y; z]) [(Γ0 ++ B :: Γ1, Δ0 ++ Δ1)])
(listInsertsL_Seqs (Γ0 ++ Γ1) (Δ0 ++ Δ1) A))
(map (fun z : list MPropF * list MPropF => [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); z])
[(Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]) [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]).
apply i ; clear i.
- pose (InT_map_iff (fun z : list MPropF * list MPropF => [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); z]) [(Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]
  [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]).
  destruct p. clear s. apply i. exists (Γ0 ++ B :: Γ1, Δ0 ++ Δ1). split. reflexivity. apply InT_eq.
- pose (InT_map_iff (fun y : list MPropF * list MPropF =>
  map (fun z : list MPropF * list MPropF => [y; z]) [(Γ0 ++ B :: Γ1, Δ0 ++ Δ1)])
  (listInsertsL_Seqs (Γ0 ++ Γ1) (Δ0 ++ Δ1) A) (map (fun z : list MPropF * list MPropF => [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); z])
  [(Γ0 ++ B :: Γ1, Δ0 ++ Δ1)])).
  destruct p. apply i. clear i. clear s. exists (Γ0 ++ Γ1, Δ0 ++ A :: Δ1). split. reflexivity.
  unfold listInsertsL_Seqs.
  pose (InT_map_iff (fun y : list MPropF => (Γ0 ++ Γ1, y)) (listInserts (Δ0 ++ Δ1) A) (Γ0 ++ Γ1, Δ0 ++ A :: Δ1)).
  destruct p. apply i. clear s. clear i. exists (Δ0 ++ A :: Δ1). split. reflexivity.
  unfold listInserts.
  pose (InT_map_iff (fun y : list MPropF * list MPropF => fst y ++ A :: snd y)
  (proj1_sigT2 (list_of_splits (Δ0 ++ Δ1))) (Δ0 ++ A :: Δ1)). destruct p. clear s.
  apply i. clear i. exists (Δ0,Δ1). simpl. split. reflexivity. destruct (list_of_splits (Δ0 ++ Δ1)).
  simpl. pose (i Δ0 Δ1). apply In_InT_seqs. rewrite <- i0. reflexivity.
Qed.

Lemma ImpL_help02 : forall Γ0 Γ1 Δ0 Δ1 A B l n,
            ImpLRule [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)] (Γ0 ++ (Imp A B) :: Γ1, Δ0 ++ Δ1) ->
            (length Γ0 = n) ->
            (In ((Imp A B), S n) l) ->
            InT [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)] (prems_Imp_L l (Γ0 ++ (Imp A B) :: Γ1, Δ0 ++ Δ1)).
Proof.
induction l ; intros.
- inversion H1.
- destruct a. destruct m.
  * subst. apply In_InT_pair in H1. inversion H1. subst. inversion H2. subst. apply InT_In in H2.
    assert (J1: length Γ0 = length Γ0). reflexivity.
    pose (IHl _ H J1 H2). simpl. destruct n0. assumption. assumption.
  * subst. apply In_InT_pair in H1. inversion H1. subst. inversion H2. subst. apply InT_In in H2.
    assert (J1: length Γ0 = length Γ0). reflexivity.
    pose (IHl _ H J1 H2). simpl. destruct n0. assumption. assumption.
  * apply In_InT_pair in H1. inversion H1.
    + subst. inversion H3. subst.
      pose (ImpL_help002 Γ0 Γ1 Δ0 Δ1 A B). simpl in i.
      apply InT_or_app. left.
      apply InT_trans_flatten_list with (bs:=(flatten_list
      (map (fun y : list MPropF * list MPropF => [[y; (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]])
         (listInsertsL_Seqs (Γ0 ++ Γ1) (Δ0 ++ Δ1) A)))). assumption. apply InT_map_iff.
      exists (Γ0 ++ B :: Γ1, Δ0 ++ Δ1). split.
      destruct (eq_dec_form (A --> B) (A --> B)).
      apply InT_flatten_list_InT_elem in i. destruct i. destruct p.
      assert ((listInsertsL_Seqs (fst
      (nth_split (length Γ0) (remove_nth (S (length Γ0)) (A --> B) (fst (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)))) ++
      snd
      (nth_split (length Γ0) (remove_nth (S (length Γ0)) (A --> B) (fst (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)))))
      (snd (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)) A) = (listInsertsL_Seqs (Γ0 ++ Γ1) (Δ0 ++ Δ1) A)).
      simpl (snd (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)).
      simpl (fst (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)). repeat rewrite effective_remove_nth.
      assert (length Γ0 = length Γ0). reflexivity.
      pose (@nth_split_length_id Γ0 Γ1 (length Γ0) H0). destruct a. rewrite H2. rewrite H4.
      reflexivity. rewrite H0.
      apply redundant_flatten_list. exfalso. auto.
      destruct (eq_dec_form (A --> B) (A --> B)). simpl (snd (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)).
      simpl (fst (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)). repeat rewrite effective_remove_nth.
      assert (length Γ0 = length Γ0). reflexivity.
      pose (@nth_split_length_id Γ0 Γ1 (length Γ0) H0). destruct a. rewrite H2. rewrite H4.
      apply InT_eq. exfalso. auto.
    + subst. assert (J1: (length Γ0) = (length Γ0)). reflexivity. apply InT_In in H3.
      pose (IHl (length Γ0) H J1 H3). simpl. destruct n0. assumption. apply InT_or_app. auto.
  * subst. apply In_InT_pair in H1. inversion H1. subst. inversion H2. subst. apply InT_In in H2.
    assert (J1: length Γ0 = length Γ0). reflexivity.
    pose (IHl _ H J1 H2). simpl. destruct n0. assumption. assumption.
Qed.

Lemma ImpL_help2 : forall prem1 prem2 s, ImpLRule [prem1; prem2] s ->
                      InT [prem1; prem2] (prems_Imp_L (pos_top_imps (fst s)) s).
Proof.
intros. inversion H. subst. simpl.
pose (@ImpL_help02 Γ0 Γ1 Δ0 Δ1 A B (pos_top_imps (Γ0 ++ (Imp A B) :: Γ1)) (length Γ0)). apply i ; try assumption.
reflexivity. apply Good_pos_in_pos_top_imps.
Qed.

Lemma ImpL_help01 : forall prems s l, InT prems (prems_Imp_L l s) ->
                  (existsT2 n prem1 prem2 A B Γ0 Γ1 Δ0 Δ1,
                        (prems = [prem1; prem2]) /\
                        (In ((Imp A B), S n) l) /\
                        (prem1 = (Γ0 ++ Γ1, Δ0 ++ A :: Δ1)) /\
                        (prem2 = (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)) /\
                        (Δ0 ++ Δ1 = snd s) /\
                        (Γ0 = (fst (nth_split n (remove_nth (S n) (Imp A B) (fst s))))) /\
                        (Γ1 = (snd (nth_split n (remove_nth (S n) (Imp A B) (fst s)))))).
Proof.
intros prems s. destruct s. induction l1 ; intros X.
- simpl in X. inversion X.
- simpl (fst (l, l0)). destruct a as [m n]. destruct m as [n0| | |].
  * simpl in X. destruct n.
    + pose (s := IHl1 X). repeat destruct s. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. exists x6. exists x7.
      repeat split ; try tauto. apply in_cons. tauto.
    + pose (s := IHl1 X). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. exists x6. exists x7.
      repeat split ; try tauto. apply in_cons. tauto.
  * simpl in X. destruct n.
    + pose (s := IHl1 X). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. exists x6. exists x7.
      repeat split ; try tauto. apply in_cons. tauto.
    + pose (s := IHl1 X). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. exists x6. exists x7.
      repeat split ; try tauto. apply in_cons. tauto.
  * destruct n.
    + pose (s := IHl1 X). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. exists x6. exists x7.
      repeat split ; try tauto. apply in_cons. tauto.
    + apply InT_app_or in X. destruct X.
      { simpl (fst (l, l0)) in i. simpl (snd (l, l0)) in i.
        apply InT_flatten_list_InT_elem in i. destruct i. destruct p.
        apply InT_map_iff in i0. destruct i0. destruct p.
        inversion i0. subst. apply InT_map_iff in i. destruct i.
        destruct p. unfold listInsertsL_Seqs in i. apply InT_map_iff in i.
        destruct i. destruct p. subst. unfold listInserts in i. apply InT_map_iff in i. destruct i.
        destruct p. destruct x. subst. destruct (list_of_splits l0). simpl in i. exists n.
        simpl (fst (l2, l3)). simpl (snd (l2, l3)).
        exists (fst (nth_split n (remove_nth (S n) (m1 --> m2) l)) ++
        snd (nth_split n (remove_nth (S n) (m1 --> m2) l)), l2 ++ m1 :: l3).
        exists (fst
          (nth_split n
             match n with
             | 0 =>
                 match l with
                 | [] => []
                 | B0 :: tl => if eq_dec_form (m1 --> m2) B0 then tl else B0 :: tl
                 end
             | S _ => match l with
                      | [] => []
                      | B0 :: tl => B0 :: remove_nth n (m1 --> m2) tl
                      end
             end) ++
        m2
        :: snd
             (nth_split n
                match n with
                | 0 =>
                    match l with
                    | [] => []
                    | B0 :: tl => if eq_dec_form (m1 --> m2) B0 then tl else B0 :: tl
                    end
                | S _ => match l with
                         | [] => []
                         | B0 :: tl => B0 :: remove_nth n (m1 --> m2) tl
                         end
                end), l0).
        exists m1. exists m2. exists (fst (nth_split n (remove_nth (S n) (m1 --> m2) l))).
        exists (snd (nth_split n (remove_nth (S n) (m1 --> m2) l))).
        exists l2. exists l3. simpl (snd (l, l0)). simpl (fst (l, l0)).
        repeat split ; try auto. apply in_eq. simpl. assert (l2 ++ l3 = l0). rewrite i1. apply InT_In.
        assumption. rewrite <- H. reflexivity. rewrite i1. apply InT_In. assumption. subst. inversion H0. }
      { pose (IHl1 i). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
        exists x2. exists x3. exists x4. exists x5. exists x6. exists x7.
        repeat split ; try tauto. apply in_cons. tauto. }
  * simpl in X. destruct n.
    + pose (IHl1 X). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. exists x6. exists x7.
      repeat split ; try tauto. apply in_cons. tauto.
    + pose (IHl1 X). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. exists x6. exists x7.
      repeat split ; try tauto. apply in_cons. tauto.
Qed.

Lemma ImpL_help1 : forall prems s, InT prems (prems_Imp_L (pos_top_imps (fst s)) s) ->
                                         ImpLRule prems s.
Proof.
intros prem s X. pose (s0 := @ImpL_help01 _ _ _ X). destruct s0 as (n&Hn&A&B&Γ0&Γ1&Δ0& Δ1&e1&Heq&i&p). destruct s as (l&l0). simpl in X.
intuition. subst.
apply In_pos_top_imps_split_l in i.
simpl (fst (l, l0)). simpl in H0. subst.
 simpl (fst (l, Δ1 ++ e1)) in X.
destruct i as (l0&l1&Heq1 & Hlen & Heq2 & Heq3).
subst.
simpl (fst (l, Δ1 ++ e1)) in Heq1.
simpl (fst (l, Δ1 ++ e1)) in Heq2.
remember (fst (nth_split (length l0) (remove_nth (S (length l0)) (B --> Γ0) l))) as Γ0'.
remember (snd (nth_split (length l0) (remove_nth (S (length l0)) (B --> Γ0) l))) as Γ1'.
rewrite Heq1, Heq2.
apply ImpLRule_I.
Qed.


Lemma finite_ImpL_premises_of_S : forall (s : Seq), existsT2 listImpLprems,
              (forall prems, ((ImpLRule prems s) -> (InT prems listImpLprems)) *
                             ((InT prems listImpLprems) -> (ImpLRule prems s))).
Proof.
intros. destruct s.
exists (prems_Imp_L (pos_top_imps l) (l,l0)).
intros. split ; intro.
- inversion H. subst.
  pose (@ImpL_help2 (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)). apply i.
  assumption.
- pose (@ImpL_help1 prems (l, l0)). apply i. assumption.
Qed.


