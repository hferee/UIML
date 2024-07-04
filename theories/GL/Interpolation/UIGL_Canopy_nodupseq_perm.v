Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import general_export.

Require Import GLS_export.

Require Import UIGL_Def_measure.
Require Import UIGL_Canopy.
Require Import UIGL_irred_short.
Require Import UIGL_braga.
Require Import UIGL_LexSeq.
Require Import UIGL_PermutationT.
Require Import UIGL_PermutationTS.
Require Import UIGL_nodupseq.
Require Import UIGL_Canopy_ImpR.
Require Import UIGL_Canopy_ImpL.

Lemma nodup_length : forall l0 l1, length (nodup eq_dec_form l0) <= length (nodup eq_dec_form (l1 ++ l0)).
Proof.
intros l0 l1. revert l0. induction l1 ; intros ; simpl ; auto.
destruct (in_dec eq_dec_form a (l1 ++ l0)).
- apply in_app_or in i. destruct i ; auto.
- simpl. pose (IHl1 l0). lia.
Qed.

Lemma repeat_n_imp_subformLF: forall (n : nat) A, n_imp_subformLF (repeat A n) = (mult n (n_imp_subformF A)).
Proof.
induction n ; simpl ; intros ; auto.
Qed.

Lemma replace_n_imp_subformLF: forall l A B,
    plus (mult (S (n_imp_subformF A)) (count_occ eq_dec_form l (A --> B))) (n_imp_subformLF (replace (A --> B) B l)) = n_imp_subformLF l.
Proof.
induction l ; simpl ; intros ; auto. lia.
destruct (eq_dec_form a (A --> B)) ; subst ; simpl. destruct (eq_dec_form (A --> B) (A --> B)) ; simpl. pose (IHl A B). lia.
exfalso ; apply n ; auto. destruct (eq_dec_form (A --> B) a) ; simpl. subst. exfalso ; apply n ; auto.
pose (IHl A B). lia.
Qed.

Lemma repeat_S : forall n (A: MPropF)A, 0 < n -> (A :: (@repeat MPropF A (Init.Nat.pred n))) = repeat A n.
Proof.
induction n ; simpl ; intros ; auto. inversion H.
Qed.

Lemma Permutation_replace_repeat : forall l A B, Permutation (replace A B l) ((repeat B (count_occ eq_dec_form l A)) ++ remove eq_dec_form A l).
Proof.
induction l ; intros ; simpl ; auto. destruct (eq_dec_form A a) ; subst. destruct (eq_dec_form a a) ; subst.
pose (IHl a B). simpl. apply perm_skip ; auto. exfalso ; apply n ; auto.
destruct (eq_dec_form a A) ; subst ; simpl. exfalso ; apply n ; auto.
pose (IHl a B). apply Permutation_cons_app ; auto.
Qed.

Lemma Permutation_repeat_extract : forall n l0 l1 l2 A B,
  (0 < n) ->
  ((count_occ eq_dec_form l0 A) = n) ->
  (In A (l1 ++ B :: l2) -> False) ->
  Permutation (remove eq_dec_form A l0) (l1 ++ l2) ->
  Permutation (repeat B n ++ remove eq_dec_form A l0) ((repeat B (Init.Nat.pred n)) ++ l1 ++ B :: l2).
Proof.
induction n ; simpl ; auto.
- intros. inversion H.
- induction l0 ; simpl ; intros ; auto. exfalso ; lia.
  destruct (eq_dec_form a A) ; subst.
  + destruct (eq_dec_form A A) ; subst. inversion H0 ; subst.
     apply perm_trans with (l':=(B :: repeat B (count_occ eq_dec_form l0 A) ++ l1 ++ l2)). apply perm_skip.
     apply Permutation_app ; auto. pose (@Permutation_middle _ (repeat B (count_occ eq_dec_form l0 A) ++ l1) l2 B).
     repeat rewrite <- app_assoc in p ; simpl in p. auto.
     apply perm_trans with (l':=(B :: repeat B n ++ l1 ++ l2)). apply perm_skip.
     apply Permutation_app ; auto. pose (@Permutation_middle _ (repeat B n ++ l1) l2 B).
     repeat rewrite <- app_assoc in p ; simpl in p. auto.
  + destruct (eq_dec_form A a) ; subst. exfalso ; apply n0 ; auto.
     apply perm_trans with (l':=(B :: repeat B n ++ l1 ++ l2)). apply perm_skip.
     apply Permutation_app ; auto. pose (@Permutation_middle _ (repeat B n ++ l1) l2 B).
     repeat rewrite <- app_assoc in p ; simpl in p. auto.
Qed.

Lemma Permutation_remove : forall l0 l1 A, Permutation l0 l1 -> Permutation (remove eq_dec_form A l0) (remove eq_dec_form A l1).
Proof.
induction 1 ; simpl ; auto.
- destruct (eq_dec_form A x) ; subst ; auto.
- destruct (eq_dec_form A y) ; subst ; auto. destruct (eq_dec_form A x) ; subst ; auto.
  apply perm_swap.
- apply (perm_trans IHPermutation1 IHPermutation2).
Qed.

Lemma count_occ_n_imp_subformLF : forall l A, count_occ eq_dec_form l A * n_imp_subformF A <= n_imp_subformLF l.
Proof.
induction l ; simpl ; auto.
intros. destruct (eq_dec_form a A) ; subst ; auto. pose (IHl A). lia.
pose (IHl A) ; lia.
Qed.

Lemma remove_n_imp_subformLF : forall l A,
        n_imp_subformLF (remove eq_dec_form A l) = minus (n_imp_subformLF l) (mult (count_occ eq_dec_form l A) (n_imp_subformF A)).
Proof.
induction l ; simpl ; auto ; intros.
destruct (eq_dec_form A a) ; subst ; auto. destruct (eq_dec_form a a) ; subst ; auto.
assert (n_imp_subformLF (remove eq_dec_form a l) = n_imp_subformLF l - count_occ eq_dec_form l a * n_imp_subformF a).
apply IHl. destruct (count_occ eq_dec_form l a) ; lia. exfalso ; auto.
destruct (eq_dec_form a A). exfalso ; auto.
pose (IHl A). simpl. rewrite e.
assert (count_occ eq_dec_form l A * n_imp_subformF A <= n_imp_subformLF l). apply count_occ_n_imp_subformLF.
lia.
Qed.

Lemma remove_n_imp_subformLF_decomp : forall l A,
        n_imp_subformLF l = plus (n_imp_subformLF (remove eq_dec_form A l)) (mult (count_occ eq_dec_form l A) (n_imp_subformF A)).
Proof.
induction l ; simpl ; intros ; auto.
destruct (eq_dec_form A a) ; subst ; auto. destruct (eq_dec_form a a) ; subst ; auto. pose (IHl a).
lia. exfalso ; auto. simpl. destruct (eq_dec_form a A). exfalso ; auto. simpl. pose (IHl A). lia.
Qed.

Lemma Permutation_replace : forall l0 l1 A B, Permutation l0 l1 -> Permutation (replace A B l0) (replace A B l1).
Proof. intros. apply Permutation_map. assumption. Qed.

Lemma Canopy_nodupseq_perm_gen : forall s0 s1 leaf1,
        (existsT2 l0 l1, (PermutationTS s0 (l0 ++ fst s1, l1 ++ snd s1)) * (incl l0 (fst s1)) * (incl l1 (snd s1))) ->
        (InT leaf1 (Canopy s1)) ->
        (existsT2 leaf0, InT leaf0 (Canopy s0) * (PermutationTS (nodupseq leaf0) (nodupseq leaf1))).
Proof.
  intros s ; induction on s as IH with measure (n_imp_subformS s).
  intros s1 leaf1 perm InClos. destruct perm. destruct s0. destruct p. destruct p.
  pose (fold_Canopy _ _ InClos). destruct s0 ; subst ; auto.
  - exists s. split ; auto. apply Canopy_critical in InClos. apply critical_Seq_InT_Canopy.
    apply PermutationTS_sym in p. apply (PermutationTS_critic _ _ p). intros A HA ; simpl in HA.
    apply InClos. apply in_or_app. apply in_app_or in HA ; destruct HA. 1-2: apply in_app_or in H ; destruct H ; auto.
    split ; apply Permutation_PermutationT ; destruct p ; apply Permutation_PermutationT in p,p0 ; simpl in p,p0 ; unfold nodupseq ; simpl.
    apply perm_trans with (l':=(nodup eq_dec_form (x ++ fst s1))).
    apply Permutation_PermutationT ; apply PermutationT_nodupseq ; apply Permutation_PermutationT ; auto.
    apply (@NoDup_Permutation_bis _ (nodup eq_dec_form (x ++ fst s1)) (nodup eq_dec_form (fst s1))). apply NoDup_nodup.
    apply nodup_length. intros A HA. apply nodup_In. apply (nodup_In) in HA. apply in_app_or in HA ; destruct HA ; auto.
    apply perm_trans with (l':=(nodup eq_dec_form (x0 ++ snd s1))).
    apply Permutation_PermutationT ; apply PermutationT_nodupseq ; apply Permutation_PermutationT ; auto.
    apply (@NoDup_Permutation_bis _ (nodup eq_dec_form (x0 ++ snd s1)) (nodup eq_dec_form (snd s1))). apply NoDup_nodup.
    apply nodup_length. intros A HA. apply nodup_In. apply (nodup_In) in HA. apply in_app_or in HA ; destruct HA ; auto.
  - destruct s0. destruct p0. unfold inv_prems in i1. apply InT_flatten_list_InT_elem in i1. destruct i1.
    destruct p0. destruct (finite_ImpRules_premises_of_S s1). simpl in i3.
    apply p0 in i3. destruct i3 ; inversion i3 ; subst.
    (* x0 is obtained via ImpR. *)
    + inversion i1 ; subst. 2: inversion H0. simpl in *.
       assert (InT (A --> B) (snd s)). apply In_InT. destruct p. apply Permutation_PermutationT in p1 ; simpl in p1.
       apply Permutation_in with (l:=(x0 ++ Δ0 ++ A --> B :: Δ1)). apply Permutation_sym ; auto.
       apply in_or_app ; right ; apply in_or_app ; right ; simpl ; auto. apply InT_split in H. destruct H. destruct s0.
       destruct s ; simpl in * ; rewrite e in * ; clear e. inversion p ; simpl in *.
       destruct (In_dec x0 (A --> B)).
       * destruct (In_dec (Δ0 ++ Δ1) (A --> B)).
         -- assert (J1: n_imp_subformS (A :: l, x1 ++ B :: x2) < n_imp_subformS (l, x1 ++ A --> B :: x2)).
            unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl. lia.
            pose (IH _ J1 (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) leaf1). simpl in s. destruct s ; simpl ; auto.
            exists x. clear p0. exists x0. repeat split ; auto ; simpl. apply Permutation_PermutationT.
            apply perm_trans with (l':=(A :: x ++ Γ0 ++ Γ1)). apply perm_skip. apply Permutation_PermutationT ; auto.
            pose (Permutation_middle (x ++ Γ0) Γ1 A). repeat rewrite <- app_assoc in p0 ; simpl in p0 ; auto. apply Permutation_PermutationT.
            apply perm_trans with (l':=(B :: x0 ++ Δ0 ++ Δ1)). apply perm_trans with (l':=(B :: x1 ++ x2)) ; auto.
            2: apply perm_skip. apply Permutation_sym ; apply Permutation_cons_app ; apply Permutation_refl. apply Permutation_PermutationT in H0.
            epose (@Permutation_cons_app_inv _ _ (x0 ++ Δ0) Δ1 (A --> B)). repeat rewrite <- app_assoc in p0 ; simpl in p0. apply p0.
            apply perm_trans with (l':=(x1 ++ A --> B :: x2)) ; auto. apply Permutation_cons_app ; apply Permutation_refl.
            epose (@Permutation_cons_app _ _ (x0 ++ Δ0) Δ1 B). repeat rewrite <- app_assoc in p0 ; simpl in p0. apply p0 ; apply Permutation_refl.
            intros C HC. apply in_or_app. apply i0 in HC. simpl. apply in_app_or in HC ; destruct HC ; auto.
            intros C HC. apply in_or_app ; simpl. pose (i _ HC). apply in_app_or in i6 ; destruct i6 ; auto. inversion H1 ; subst ; auto.
            apply in_app_or in i5 ; destruct i5 ; auto.
            destruct p1. exists x4 ; split ; auto. eapply ImpRule_Canopy. left. apply (ImpRRule_I A B [] l x1 x2).
            simpl. apply InT_eq. auto.
         -- assert (J1: n_imp_subformS (repeat A (count_occ eq_dec_form (x1 ++ A --> B :: x2) (A --> B)) ++ l, replace (A --> B) B (x1 ++ A --> B :: x2)) < n_imp_subformS (l, x1 ++ A --> B :: x2)).
            unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl. rewrite repeat_n_imp_subformLF.
            pose (replace_n_imp_subformLF (x1 ++ A --> B :: x2) A B). repeat rewrite n_imp_subformLF_dist_app in e ; simpl in e. rewrite <- e.
            assert (0 < count_occ eq_dec_form (x1 ++ A --> B :: x2) (A --> B)). apply count_occ_In. apply in_or_app ; right ; simpl ; auto. lia.
            pose (IH _ J1 (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) leaf1). simpl in s. destruct s ; simpl ; auto.
            exists (repeat A (pred (count_occ eq_dec_form (x1 ++ A --> B :: x2) (A --> B))) ++ x). clear p0.
            exists (repeat B (pred (count_occ eq_dec_form (x1 ++ A --> B :: x2) (A --> B))) ++ (remove eq_dec_form (A --> B) x0)).
            repeat split ; auto ; simpl. apply Permutation_PermutationT. repeat rewrite <- app_assoc.
            apply perm_trans with (l':=(repeat A (count_occ eq_dec_form (x1 ++ A --> B :: x2) (A --> B)) ++ x ++ Γ0 ++ Γ1)).
            apply Permutation_app_head. apply Permutation_PermutationT ; auto.
            apply perm_trans with (l':=(A :: repeat A (Init.Nat.pred (count_occ eq_dec_form (x1 ++ A --> B :: x2) (A --> B))) ++ x ++ Γ0 ++ Γ1)).
            assert (A :: repeat A (Init.Nat.pred (count_occ eq_dec_form (x1 ++ A --> B :: x2) (A --> B))) = repeat A (count_occ eq_dec_form (x1 ++ A --> B :: x2) (A --> B))).
            apply repeat_S ; auto. apply count_occ_In. apply in_or_app ; right ; simpl ; auto.
            rewrite <- H1. simpl. apply perm_skip. apply Permutation_app_head. apply Permutation_refl.
            epose (@Permutation_cons_app _ _ (repeat A (Init.Nat.pred (count_occ eq_dec_form (x1 ++ A --> B :: x2) (A --> B))) ++ x ++ Γ0) Γ1 A).
            repeat rewrite <- app_assoc in p0 ; apply p0 ; clear p0. apply Permutation_refl.
            apply Permutation_PermutationT. pose (Permutation_replace_repeat (x1 ++ A --> B :: x2) (A --> B) B).
            apply perm_trans with (l':=(repeat B (count_occ eq_dec_form (x1 ++ A --> B :: x2) (A --> B)) ++ remove eq_dec_form (A --> B) (x1 ++ A --> B :: x2))) ; auto.
            assert (J20: 0 < count_occ eq_dec_form (x1 ++ A --> B :: x2) (A --> B)). apply count_occ_In. apply in_or_app ; right ; simpl ; auto.
            assert (J21: (In (A --> B) ((remove eq_dec_form (A --> B) x0 ++ Δ0) ++ B :: Δ1) -> False)).
            intros. apply in_app_or in H1 ; destruct H1. apply in_app_or in H1 ; destruct H1. apply remove_not_in_anymore in H1 ; auto.
            apply n ; apply in_or_app ; auto. inversion H1. assert (size B = size (A --> B)). rewrite <- H2 ; auto. simpl in H3 ; lia.
            apply n ; apply in_or_app ; auto. assert (J43: count_occ eq_dec_form (x1 ++ A --> B :: x2) (A --> B) = count_occ eq_dec_form (x1 ++ A --> B :: x2) (A --> B)) ; auto.
            pose (Permutation_repeat_extract _ (x1 ++ A --> B :: x2) _ _ (A --> B) B J20 J43 J21).
            repeat rewrite <- app_assoc ; simpl. repeat rewrite <- app_assoc in p1 ; simpl in p1. apply p1 ; clear p1.
            assert ((remove eq_dec_form (A --> B) x0 ++ Δ0 ++ Δ1) = (remove eq_dec_form (A --> B) (x0 ++ Δ0 ++ A --> B :: Δ1))).
            repeat rewrite remove_app. simpl. destruct (eq_dec_form (A --> B) (A --> B)). pose (notin_remove eq_dec_form Δ0).
            pose (notin_remove eq_dec_form Δ1). rewrite e0. rewrite e1 ; auto. 1-2: intro ; apply n ; apply in_or_app ; auto.
            exfalso ; apply n0 ; auto. rewrite H1. apply Permutation_remove ; apply Permutation_PermutationT in H0 ; auto.
            intros C HC. apply in_or_app. apply in_app_or in HC ; destruct HC. right. simpl. apply repeat_spec in H1 ; auto.
            apply i0 in H1. simpl. apply in_app_or in H1 ; destruct H1 ; auto.
            intros C HC. apply in_or_app ; simpl. apply in_app_or in HC ; destruct HC. right. apply repeat_spec in H1 ; auto.
            apply in_remove in H1. destruct H1. pose (i _ H1). apply in_app_or in i5 ; destruct i5 ; auto. inversion H3 ; subst ; auto.
            exfalso ; auto.
            destruct p1. exists x4 ; split ; auto. apply (mult_ImpR _ _ A B) ; auto.
       * assert (J1: n_imp_subformS (A :: l, x1 ++ B :: x2) < n_imp_subformS (l, x1 ++ A --> B :: x2)).
         unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl. lia.
         pose (IH _ J1 (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) leaf1). simpl in s. destruct s ; simpl ; auto.
         exists x. clear p0. exists x0. repeat split ; auto ; simpl. apply Permutation_PermutationT.
         apply perm_trans with (l':=(A :: x ++ Γ0 ++ Γ1)). apply perm_skip. apply Permutation_PermutationT ; auto.
         pose (Permutation_middle (x ++ Γ0) Γ1 A). repeat rewrite <- app_assoc in p0 ; simpl in p0 ; auto. apply Permutation_PermutationT.
         apply perm_trans with (l':=(B :: x0 ++ Δ0 ++ Δ1)). apply perm_trans with (l':=(B :: x1 ++ x2)) ; auto.
         2: apply perm_skip. apply Permutation_sym ; apply Permutation_cons_app ; apply Permutation_refl. apply Permutation_PermutationT in H0.
         epose (@Permutation_cons_app_inv _ _ (x0 ++ Δ0) Δ1 (A --> B)). repeat rewrite <- app_assoc in p0 ; simpl in p0. apply p0.
         apply perm_trans with (l':=(x1 ++ A --> B :: x2)) ; auto. apply Permutation_cons_app ; apply Permutation_refl.
         epose (@Permutation_cons_app _ _ (x0 ++ Δ0) Δ1 B). repeat rewrite <- app_assoc in p0 ; simpl in p0. apply p0 ; apply Permutation_refl.
         intros C HC. apply in_or_app. apply i0 in HC. simpl. apply in_app_or in HC ; destruct HC ; auto.
         intros C HC. apply in_or_app ; simpl. pose (i _ HC). apply in_app_or in i4 ; destruct i4 ; auto. inversion H1 ; subst ; auto.
         exfalso ; auto.
         destruct p1. exists x4 ; split ; auto. eapply ImpRule_Canopy. left. apply (ImpRRule_I A B [] l x1 x2).
         simpl. apply InT_eq. auto.
    (* x0 is obtained via ImpL. *)
    + subst. inversion p. simpl in *.
       assert (InT (A --> B) (fst s)). apply In_InT. apply Permutation_PermutationT in H.
       apply Permutation_in with (l:=(x ++ Γ0 ++ A --> B :: Γ1)). apply Permutation_sym ; auto.
       apply in_or_app ; right ; apply in_or_app ; right ; simpl ; auto. apply InT_split in H1. destruct H1. destruct s0.
       destruct s ; simpl in * ; rewrite e in * ; clear e. inversion i1 ; subst. 2: inversion H2 ; subst ; simpl in *. 3: inversion H3.
     (* Left premise. *)
     { destruct (In_dec x (A --> B)).
       * destruct (In_dec (Γ0 ++ Γ1) (A --> B)).
         -- assert (J1: n_imp_subformS (x2 ++ x4, A :: l0) < n_imp_subformS (x2 ++ A --> B :: x4, l0)).
            unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
            pose (IH _ J1 (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) leaf1). simpl in s. destruct s ; simpl ; auto.
            exists x. clear p0. exists x0. repeat split ; auto ; simpl. 1-2: apply Permutation_PermutationT.
            pose (@Permutation_app_inv _ x2 x4 (x ++ Γ0) Γ1 (A --> B)). repeat rewrite <- app_assoc in p0.
            apply p0 ; apply Permutation_PermutationT ; auto.
            apply perm_trans with (l':=(A :: x0 ++ Δ0 ++ Δ1)). apply perm_skip. apply Permutation_PermutationT ; auto.
            pose (Permutation_middle (x0 ++ Δ0) Δ1 A). repeat rewrite <- app_assoc in p0 ; simpl in p0 ; auto.
            intros C HC. apply in_or_app ; simpl. pose (i0 _ HC). apply in_app_or in i6 ; destruct i6 ; auto. inversion H1 ; subst ; auto.
            apply in_app_or in i5 ; destruct i5 ; auto.
            intros C HC. apply in_or_app. apply i in HC. simpl. apply in_app_or in HC ; destruct HC ; auto.
            destruct p1. exists x1 ; split ; auto. eapply ImpRule_Canopy. right. apply (ImpLRule_I A B x2 x4 [] l0).
            simpl. apply InT_eq. auto.
         -- assert (J1: n_imp_subformS (remove eq_dec_form (A --> B) (x2 ++ x4), repeat A (count_occ eq_dec_form (x2 ++ A --> B :: x4) (A --> B)) ++ l0) < n_imp_subformS (x2 ++ A --> B :: x4, l0)).
            unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl. rewrite repeat_n_imp_subformLF.
            assert (0 < count_occ eq_dec_form (x2 ++ A --> B :: x4) (A --> B)). apply count_occ_In. apply in_or_app ; right ; simpl ; auto.
            pose (remove_n_imp_subformLF_decomp (x2 ++ A --> B :: x4) (A --> B)). rewrite n_imp_subformLF_dist_app in e ; simpl in e.
            assert (n_imp_subformLF (remove eq_dec_form (A --> B) (x2 ++ x4)) + (count_occ eq_dec_form (x2 ++ A --> B :: x4) (A --> B) * n_imp_subformF A + n_imp_subformLF l0) <
            n_imp_subformLF l0 +  (n_imp_subformLF x2 + S (n_imp_subformF A + n_imp_subformF B + n_imp_subformLF x4))).
            rewrite e. repeat rewrite remove_app. simpl. destruct (eq_dec_form (A --> B) (A --> B)). lia. exfalso ; apply n0 ; auto. lia.
            pose (IH _ J1 (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) leaf1). simpl in s. destruct s ; simpl ; auto.
            exists (remove eq_dec_form (A --> B) x). clear p0.
            exists (repeat A (pred (count_occ eq_dec_form (x2 ++ A --> B :: x4) (A --> B))) ++ x0).
            repeat split ; auto ; simpl. 1-2: apply Permutation_PermutationT.
            pose (Permutation_remove (x2 ++ x4) (x ++ Γ0 ++ Γ1) (A --> B)).
            assert (remove eq_dec_form (A --> B) x ++ Γ0 ++ Γ1 = remove eq_dec_form (A --> B) (x ++ Γ0 ++ Γ1)).
            repeat rewrite remove_app. pose (notin_remove eq_dec_form Γ0). pose (notin_remove eq_dec_form Γ1).
            rewrite e. rewrite e0 ; auto. 1-2: intro ; apply n ; apply in_or_app ; auto. rewrite H1. apply p0.
            epose (Permutation_app_inv x2 x4 (x ++ Γ0) Γ1 (A --> B)). repeat rewrite <- app_assoc in p1. apply p1 ; apply Permutation_PermutationT ; auto.
            apply perm_trans with (l':=((A :: repeat A (Init.Nat.pred (count_occ eq_dec_form (x2 ++ A --> B :: x4) (A --> B))) ++ x0) ++ Δ0 ++ Δ1)).
            assert (A :: repeat A (Init.Nat.pred (count_occ eq_dec_form (x2 ++ A --> B :: x4) (A --> B))) = repeat A (count_occ eq_dec_form (x2 ++ A --> B :: x4) (A --> B))).
            remember (count_occ eq_dec_form (x2 ++ A --> B :: x4) (A --> B)) as n' ; destruct n' ; auto ; simpl. exfalso. symmetry in Heqn' ; apply count_occ_not_In in Heqn'.
            apply Heqn'. apply in_or_app ; simpl ; auto. rewrite <- H1. simpl. apply perm_skip. repeat rewrite <- app_assoc ; simpl.
            apply Permutation_app_head ; apply Permutation_PermutationT ; auto.
            epose (@Permutation_cons_app _ ((repeat A (Init.Nat.pred (count_occ eq_dec_form (x2 ++ A --> B :: x4) (A --> B))) ++ x0) ++ Δ0 ++ Δ1)
            (repeat A (Init.Nat.pred (count_occ eq_dec_form (x2 ++ A --> B :: x4) (A --> B))) ++ x0 ++ Δ0) Δ1 A).
            simpl ; repeat rewrite <- app_assoc ; simpl in p0 ; repeat rewrite <- app_assoc in p0. apply p0 ; clear p0. apply Permutation_refl.
            intros C HC. apply in_or_app. apply in_remove in HC. destruct HC. apply i0 in H1. apply in_app_or in H1 ; destruct H1 ; auto.
            inversion H1 ; [ exfalso ; subst ; apply H2 ; auto | auto].
            intros C HC. apply in_or_app ; simpl. apply in_app_or in HC ; destruct HC. right. apply repeat_spec in H1 ; auto.
            pose (i _ H1). apply in_app_or in i5 ; destruct i5 ; auto.
            destruct p1. exists x1 ; split ; auto. apply (mult_ImpL_L _ _ A B) ; simpl ; auto.
            assert (remove eq_dec_form (A --> B) (x2 ++ A --> B :: x4) = remove eq_dec_form (A --> B) (x2 ++ x4)).
            repeat rewrite remove_app. simpl. destruct (eq_dec_form (A --> B) (A --> B)) ; auto. exfalso ; auto. rewrite H1 ; auto.
       * assert (J1: n_imp_subformS (x2 ++ x4, A :: l0) < n_imp_subformS (x2 ++ A --> B :: x4, l0)).
         unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl. lia.
         pose (IH _ J1 (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) leaf1). simpl in s. destruct s ; simpl ; auto.
        exists x. clear p0. exists x0. repeat split ; auto ; simpl. 1-2: apply Permutation_PermutationT.
        pose (@Permutation_app_inv _ x2 x4 (x ++ Γ0) Γ1 (A --> B)). repeat rewrite <- app_assoc in p0.
        apply p0 ; apply Permutation_PermutationT ; auto.
        apply perm_trans with (l':=(A :: x0 ++ Δ0 ++ Δ1)). apply perm_skip. apply Permutation_PermutationT ; auto.
        pose (Permutation_middle (x0 ++ Δ0) Δ1 A). repeat rewrite <- app_assoc in p0 ; simpl in p0 ; auto.
        intros C HC. apply in_or_app ; simpl. pose (i0 _ HC). apply in_app_or in i4 ; destruct i4 ; auto. inversion H1 ; subst ; auto.
        exfalso ; auto.
        intros C HC. apply in_or_app. apply i in HC. simpl. apply in_app_or in HC ; destruct HC ; auto.
        destruct p1. exists x1 ; split ; auto. eapply ImpRule_Canopy. right. apply (ImpLRule_I A B x2 x4 [] l0).
        simpl. apply InT_eq. auto. }
     (* Right premise. *)
     { destruct (In_dec x (A --> B)).
       * destruct (In_dec (Γ0 ++ Γ1) (A --> B)).
         -- assert (J1: n_imp_subformS (x2 ++ B :: x4, l0) < n_imp_subformS (x2 ++ A --> B :: x4, l0)).
            unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
            pose (IH _ J1 (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) leaf1). simpl in s. destruct s ; simpl ; auto.
            exists x. clear p0. exists x0. repeat split ; auto ; simpl. apply Permutation_PermutationT.
            pose (@Permutation_app_inv _ x2 x4 (x ++ Γ0) Γ1 (A --> B)). repeat rewrite <- app_assoc in p0.
            pose (Permutation_elt x2 x4 (x ++ Γ0) Γ1 B). repeat rewrite <- app_assoc in p1. apply p1.
            apply p0. apply Permutation_PermutationT ; auto.
            intros C HC. apply in_or_app ; simpl. pose (i0 _ HC). apply in_app_or in i6 ; destruct i6 ; auto. inversion H1 ; subst ; auto.
            apply in_app_or in i5 ; destruct i5 ; auto.
            destruct p1. exists x1 ; split ; auto. eapply ImpRule_Canopy. right. apply (ImpLRule_I A B x2 x4 [] l0).
            simpl. apply InT_cons ; apply InT_eq. auto.
         -- assert (J1: n_imp_subformS (replace (A --> B) B (x2 ++ A --> B :: x4), l0) < n_imp_subformS (x2 ++ A --> B :: x4, l0)).
            unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl.
            pose (replace_n_imp_subformLF (x2 ++ A --> B :: x4) A B). repeat rewrite n_imp_subformLF_dist_app in e. simpl in e.
            repeat rewrite replace_app. simpl. repeat rewrite replace_app in e. simpl in e. destruct (eq_dec_form (A --> B) (A --> B)).
            2: exfalso ; auto.
            assert (0 < count_occ eq_dec_form (x2 ++ A --> B :: x4) (A --> B)). apply count_occ_In. apply in_or_app ; right ; simpl ; auto.
            lia.
            pose (IH _ J1 (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) leaf1). simpl in s. destruct s ; simpl ; auto.
            exists (replace (A --> B) B x). clear p0.
            exists x0.
            repeat split ; auto ; simpl. apply Permutation_PermutationT.
            pose (Permutation_replace (x2 ++ A --> B :: x4) (x ++ Γ0 ++ A --> B :: Γ1) (A --> B) B).
            assert (replace (A --> B) B x ++ Γ0 ++ B :: Γ1 = replace (A --> B) B (x ++ Γ0 ++ A --> B :: Γ1)).
            repeat rewrite replace_app. simpl. destruct (eq_dec_form (A --> B) (A --> B)) ; auto. 2: exfalso ; auto.
            pose (notin_replace Γ0). pose (notin_replace Γ1). rewrite e0. rewrite e1. auto.
            1-2: intro ; apply n ; apply in_or_app ; auto. rewrite H1. apply p0 ; apply Permutation_PermutationT ; auto.
            intros C HC. apply in_or_app. apply in_replace in HC. destruct HC. simpl ; destruct H1 ; auto.
            apply i0 in H1. apply in_app_or in H1 ; destruct H1 ; auto.
            inversion H1 ; [ exfalso ; subst ; auto | auto]. intro. assert (size (A --> B) = size B). rewrite H1 ; auto. simpl in H3 ; lia.
            destruct p1. exists x1 ; split ; auto. apply (mult_ImpL_R _ _ A B) ; simpl ; auto.
       * assert (J1: n_imp_subformS (x2 ++ B :: x4, l0) < n_imp_subformS (x2 ++ A --> B :: x4, l0)).
         unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl. lia.
         pose (IH _ J1 (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) leaf1). simpl in s. destruct s ; simpl ; auto.
        exists x. clear p0. exists x0. repeat split ; auto ; simpl. apply Permutation_PermutationT.
        pose (@Permutation_app_inv _ x2 x4 (x ++ Γ0) Γ1 (A --> B)). repeat rewrite <- app_assoc in p0.
        pose (Permutation_elt x2 x4 (x ++ Γ0) Γ1 B). repeat rewrite <- app_assoc in p1. apply p1.
        apply p0. apply Permutation_PermutationT ; auto.
        intros C HC. apply in_or_app ; simpl. pose (i0 _ HC). apply in_app_or in i4 ; destruct i4 ; auto. inversion H1 ; subst ; auto.
        exfalso ; auto.
        destruct p1. exists x1 ; split ; auto. eapply ImpRule_Canopy. right. apply (ImpLRule_I A B x2 x4 [] l0).
        simpl. apply InT_cons ; apply InT_eq. auto. }
Qed.

Lemma Canopy_nodupseq_perm : forall s leaf, InT leaf (Canopy (nodupseq s)) ->
        (existsT2 s0, InT s0 (Canopy s) * (PermutationTS (nodupseq s0) (nodupseq leaf))).
Proof.
intros. pose (Canopy_nodupseq_perm_gen s (nodupseq s) leaf). apply s0 ; auto.
destruct (nodupseq_id s). destruct p. destruct s1. destruct s1. destruct p0. destruct p0.
exists x0 ; exists x1 ; repeat split ; auto ; simpl.
- destruct p. destruct p0. apply Permutation_PermutationT in p,p0. simpl in p0.
  apply Permutation_PermutationT. apply perm_trans with (l':=(x0 ++ fst x)) ; auto.
  apply Permutation_app_head ; auto.
- destruct p. destruct p0. apply Permutation_PermutationT in p2,p1. simpl in p2.
  apply Permutation_PermutationT. apply perm_trans with (l':=(x1 ++ snd x)) ; auto.
  apply Permutation_app_head ; auto.
- intros A HA. destruct s ; simpl in *. destruct p. apply i0 in HA. apply Permutation_PermutationT in p.
  simpl in p. apply Permutation_in with (l:= fst x) ; auto.
- intros A HA. destruct s ; simpl in *. destruct p. apply i in HA. apply Permutation_PermutationT in p1.
  simpl in p1. apply Permutation_in with (l:= snd x) ; auto.
Qed.


