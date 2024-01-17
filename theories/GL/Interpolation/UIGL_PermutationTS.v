Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import general_export.

Require Import GLS_export.

Require Import UIGL_Def_measure.
Require Import UIGL_Canopy.
Require Import UIGL_irred_short.
Require Import UIGL_PermutationT.
Require Import UIGL_LexSeq.
Require Import UIGL_basics.

Definition PermutationTS (s sp : Seq) := (PermutationT (fst s) (fst sp)) * (PermutationT (snd s) (snd sp)).

Theorem PermutationTS_sym : forall s sp, PermutationTS s sp -> PermutationTS sp s.
Proof.
unfold PermutationTS. intros. destruct H. apply Permutation_PermutationT in p.
apply Permutation_PermutationT in p0. split.
1-2: apply Permutation_PermutationT ; apply Permutation_sym ; auto.
Qed.

Theorem PermutationT_XBoxed_list : forall l0 l1, PermutationT l0 l1 -> PermutationT (XBoxed_list l0) (XBoxed_list l1).
Proof.
induction 1 ; simpl ; intuition.
- apply Permutation_PermutationT ; apply Permutation_refl.
- apply Permutation_PermutationT ; repeat apply perm_skip ; apply Permutation_PermutationT ; auto.
- apply Permutation_PermutationT. epose (Permutation_app_swap_app (_ :: [_]) (_ :: [_])). simpl in p. apply p.
- apply permT_trans with (l':=(XBoxed_list l')) ; auto.
Qed.

Theorem PermutationT_top_boxes : forall l0 l1, PermutationT l0 l1 -> PermutationT (top_boxes l0) (top_boxes l1).
Proof.
induction 1.
- apply Permutation_PermutationT ; apply Permutation_refl.
- destruct x ; simpl ; auto. apply Permutation_PermutationT ; repeat apply perm_skip ; apply Permutation_PermutationT ; auto.
- destruct x ; destruct y ; simpl ; apply Permutation_PermutationT ; try apply Permutation_refl. apply perm_swap.
- apply permT_trans with (l':=(top_boxes l')) ; auto.
Qed.

Theorem PermutationTS_prv_hpadm : forall s (D: GLS_prv s),
          forall sp, PermutationTS s sp -> existsT2 (D0: GLS_prv sp), derrec_height D0 <= derrec_height D.
Proof.
intros s D. remember (derrec_height D) as n. revert Heqn. revert D. revert s. revert n.
(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall (s : Seq) (D : GLS_prv s),
x = derrec_height D -> forall sp : Seq, PermutationTS s sp -> existsT2 D0 : GLS_prv sp, derrec_height D0 <= x)).
apply s. clear s. intros n IH.
(* Now we do the actual proof-theoretical work. *)
intros s0 D0. destruct D0.
- intros. inversion f.
- intros hei sp Perm. simpl in hei.
  inversion g ; subst.
  + inversion H ; subst.
     assert (GLS_rules [] sp). apply IdP. destruct sp. destruct Perm. simpl in *. apply Permutation_PermutationT in p, p0.
     assert (InT (# P) l0). apply In_InT. apply (Permutation_in _ p0). apply in_or_app ; right ; apply in_eq.
     assert (InT (# P) l). apply In_InT. apply (Permutation_in _ p). apply in_or_app ; right ; apply in_eq.
     apply InT_split in H0. apply InT_split in H1. destruct H0. destruct s. destruct H1. destruct s. subst ; apply IdPRule_I.
     pose (dlNil GLS_rules (fun _ : Seq => False)).
     epose (@derI _ _ (fun _ : Seq => False) _ _ X d0). exists d1. simpl. lia.
  + inversion H ; subst.
     assert (GLS_rules [] sp). apply BotL. destruct sp. destruct Perm. simpl in *. apply Permutation_PermutationT in p.
     assert (InT Bot l). apply In_InT. apply (Permutation_in _ p). apply in_or_app ; right ; apply in_eq.
     apply InT_split in H0. destruct H0. destruct s. subst ; apply BotLRule_I.
     pose (dlNil GLS_rules (fun _ : Seq => False)).
     epose (@derI _ _ (fun _ : Seq => False) _ _ X d0). exists d1. simpl. lia.
  + inversion H ; subst. destruct sp. destruct Perm. simpl in *. apply Permutation_PermutationT in p0.
     assert (InT (A --> B) l0). apply In_InT. apply (Permutation_in _ p0). apply in_or_app ; right ; apply in_eq.
     apply InT_split in H0. destruct H0. destruct s. subst.
     assert (GLS_rules [(A :: l, x ++ B :: x0)] (l, x ++ A --> B :: x0)). apply ImpR. eapply (ImpRRule_I _ _ []).
     assert (dersrec_height d = dersrec_height d). auto. pose (dersrec_derrec_height d H0). destruct s ; subst.
     assert (J0: derrec_height x1 < S (dersrec_height d)). lia.
     assert (J1: derrec_height x1 = derrec_height x1). auto.
     assert (J2: PermutationTS (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) (A :: l, x ++ B :: x0)).
     split ; simpl ; apply Permutation_PermutationT ; apply Permutation_PermutationT in p.
     apply Permutation_sym. apply Permutation_cons_app ; auto. apply Permutation_sym ; auto.
     apply Permutation_elt. apply Permutation_app_inv in p0 ; auto.
     pose (IH _ J0 _ _ J1 _ J2). destruct s. pose (dlCons x2 (dlNil _ _)).
     epose (@derI _ _ (fun _ : Seq => False) _ _ X d0). exists d1. simpl. lia.
  + inversion H ; subst. destruct sp. destruct Perm. simpl in *. apply Permutation_PermutationT in p0 , p.
     assert (InT (A --> B) l). apply In_InT. apply (Permutation_in _ p). apply in_or_app ; right ; apply in_eq.
     apply InT_split in H0. destruct H0. destruct s. subst.
     assert (GLS_rules [(x ++ x0, A :: l0);(x ++ B :: x0, l0)] (x ++ A --> B :: x0, l0)). apply ImpL. eapply (ImpLRule_I _ _ x x0 []).
     assert (dersrec_height d = dersrec_height d). auto. pose (dersrec_derrec2_height d H0). destruct s ; subst. destruct s.
     assert (J0: derrec_height x1 < S (dersrec_height d)). lia.
     assert (J1: derrec_height x1 = derrec_height x1). auto.
     assert (J2: PermutationTS (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) (x ++ x0, A :: l0)).
     split ; simpl ; apply Permutation_PermutationT.
     apply Permutation_app_inv in p ; auto.
     apply Permutation_sym. apply Permutation_cons_app ; auto. apply Permutation_sym ; auto.
     pose (IH _ J0 _ _ J1 _ J2). destruct s.
     assert (J3: derrec_height x2 < S (dersrec_height d)). lia.
     assert (J4: derrec_height x2 = derrec_height x2). auto.
     assert (J5: PermutationTS (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) (x ++ B :: x0, l0)).
     split ; simpl ; apply Permutation_PermutationT ; auto.
     apply Permutation_elt. apply Permutation_app_inv in p ; auto.
     pose (IH _ J3 _ _ J4 _ J5). destruct s. pose (dlCons x4 (dlNil _ _)). pose (dlCons x3 d0).
     epose (@derI _ _ (fun _ : Seq => False) _ _ X d1). exists d2. simpl. lia.
  + inversion X ; subst. destruct sp. destruct Perm. simpl in *. apply Permutation_PermutationT in p0 , p.
     assert (InT (Box A) l0). apply In_InT. apply (Permutation_in _ p0). apply in_or_app ; right ; apply in_eq.
     apply InT_split in H0. destruct H0. destruct s. subst.
     assert (GLS_rules [(XBoxed_list (top_boxes l) ++ [Box A], [A])] (l, x ++ Box A :: x0)). apply GLR. apply GLRRule_I.
     apply is_Boxed_list_top_boxes. apply nobox_gen_ext_top_boxes.
     assert (dersrec_height d = dersrec_height d). auto. pose (dersrec_derrec_height d H0). destruct s ; subst.
     assert (J0: derrec_height x1 < S (dersrec_height d)). lia.
     assert (J1: derrec_height x1 = derrec_height x1). auto.
     assert (J2: PermutationTS (XBoxed_list BΓ ++ [Box A], [A]) (XBoxed_list (top_boxes l) ++ [Box A], [A])).
     split ; simpl ; apply Permutation_PermutationT. 2: apply Permutation_refl.
     apply Permutation_app. 2: apply Permutation_refl.
     pose (nobox_gen_ext_top_boxes_identity X0 H). rewrite e0. apply Permutation_PermutationT.
     apply PermutationT_XBoxed_list. apply PermutationT_top_boxes ; apply Permutation_PermutationT ; auto.
     pose (IH _ J0 _ _ J1 _ J2). destruct s. pose (dlCons x2 (dlNil _ _)).
     epose (@derI _ _ (fun _ : Seq => False) _ _ X1 d0). exists d1. simpl. lia.
Qed.

Theorem PermutationTS_prv : forall s sp, PermutationTS s sp -> GLS_prv s -> GLS_prv sp.
Proof.
intros. destruct (PermutationTS_prv_hpadm _ X _ H) ; auto.
Qed.

Theorem PermutationTS_restr_list_prop_snd : forall s sp p A, PermutationTS s sp -> InT A (restr_list_prop p (snd s)) -> InT A (restr_list_prop p (snd sp)).
Proof.
unfold PermutationTS. intros. destruct H. apply Permutation_PermutationT in p0, p1.
apply InT_In in H0. apply In_InT. unfold restr_list_prop in *. apply in_remove in H0 ; destruct H0.
apply in_in_remove ; auto. apply In_list_prop_LF_bis in H. destruct H. apply list_prop_LF_In ; auto.
apply (Permutation_in _ p1 i).
Qed.

Theorem PermutationTS_restr_list_prop_fst : forall s sp p A, PermutationTS s sp -> InT A (restr_list_prop p (fst s)) -> InT A (restr_list_prop p (fst sp)).
Proof.
unfold PermutationTS. intros. destruct H. apply Permutation_PermutationT in p0, p1.
apply InT_In in H0. apply In_InT. unfold restr_list_prop in *. apply in_remove in H0 ; destruct H0.
apply in_in_remove ; auto. apply In_list_prop_LF_bis in H. destruct H. apply list_prop_LF_In ; auto.
apply (Permutation_in _ p0 i).
Qed.

Theorem PermutationTS_GLR_prems : forall s sp, PermutationTS s sp ->
            (forall ps, InT ps (GLR_prems s) -> (existsT2 psp, PermutationTS ps psp * InT psp (GLR_prems sp))).
Proof.
intros. unfold GLR_prems in H0. destruct (finite_GLR_premises_of_S s). simpl in H0.
apply InT_flatten_list_InT_elem in H0. destruct H0. destruct p0. apply p in i0. inversion i0 ; subst.
destruct sp. destruct H. simpl in *. apply Permutation_PermutationT in p0, p1.
assert (InT (Box A) l0). apply In_InT. apply (Permutation_in _ p1). apply in_or_app ; right ; apply in_eq.
apply InT_split in H. destruct H. destruct s. subst.
exists (XBoxed_list (top_boxes l) ++ [Box A], [A]). inversion i ; subst. 2: inversion H1. split.
split ; simpl ; apply Permutation_PermutationT.  2: apply Permutation_refl.
apply Permutation_app. 2: apply Permutation_refl.
pose (nobox_gen_ext_top_boxes_identity X H0). rewrite e. apply Permutation_PermutationT.
apply PermutationT_XBoxed_list. apply PermutationT_top_boxes ; apply Permutation_PermutationT ; auto.
unfold GLR_prems. destruct (finite_GLR_premises_of_S (l, x0 ++ Box A :: x1)). simpl.
apply InT_trans_flatten_list with (bs:=[(XBoxed_list (top_boxes l) ++ [Box A], [A])]).
apply InT_eq. apply p2. apply GLRRule_I.
apply is_Boxed_list_top_boxes. apply nobox_gen_ext_top_boxes.
Qed.

Theorem PermutationTS_is_init : forall s sp, PermutationTS s sp -> (is_init s -> is_init sp).
Proof.
unfold PermutationTS. intros. destruct H. apply Permutation_PermutationT in p, p0. destruct s. destruct sp.
simpl in *. inversion X. inversion H.
- inversion H0 ; subst.
  assert (InT (# P) l2). apply In_InT. apply (Permutation_in _ p0). apply in_or_app ; right ; apply in_eq.
  apply InT_split in H1. destruct H1. destruct s. subst.
  assert (InT (# P) l1). apply In_InT. apply (Permutation_in _ p). apply in_or_app ; right ; apply in_eq.
  apply InT_split in H1. destruct H1. destruct s. subst. left. left. apply IdPRule_I.
- inversion H0 ; subst.
  assert (InT (Box A) l2). apply In_InT. apply (Permutation_in _ p0). apply in_or_app ; right ; apply in_eq.
  apply InT_split in H1. destruct H1. destruct s. subst.
  assert (InT (Box A) l1). apply In_InT. apply (Permutation_in _ p). apply in_or_app ; right ; apply in_eq.
  apply InT_split in H1. destruct H1. destruct s. subst. left. right. apply IdBRule_I.
- inversion H ; subst.
  assert (InT (Bot) l1). apply In_InT. apply (Permutation_in _ p). apply in_or_app ; right ; apply in_eq.
  apply InT_split in H0. destruct H0. destruct s. subst. right. apply BotLRule_I.
Qed.

Theorem PermutationTS_critic : forall s sp, PermutationTS s sp -> (critical_Seq s -> critical_Seq sp).
Proof.
unfold PermutationTS. intros. destruct H. apply Permutation_PermutationT in p, p0. destruct s. destruct sp.
simpl in *. unfold critical_Seq in * ; simpl in *. intros A HA. apply in_app_or in HA ; destruct HA.
- assert (InT A l). apply In_InT. apply (Permutation_in _ (Permutation_sym p)) ; auto.
  apply H0. apply in_or_app ; left ; apply InT_In ; auto.
- assert (InT A l0). apply In_InT. apply (Permutation_in _ (Permutation_sym p0)) ; auto.
  apply H0. apply in_or_app ; right ; apply InT_In ; auto.
Qed.

Theorem Permutation_subform_boxesLF : forall l0 l1, Permutation l0 l1 ->
    (forall A, In A (subform_boxesLF l0) -> In A (subform_boxesLF l1)).
Proof.
induction 1 ; simpl ; intuition.
- apply in_app_or in H0. apply in_or_app. destruct H0 ; auto. right.
  apply In_remove_list_In_list_not_In_remove_list in H0. destruct H0.
  apply not_removed_remove_list ; auto.
- apply in_app_or in H. destruct H ; auto. apply remove_list_is_in. apply in_or_app ; auto.
  apply In_remove_list_In_list_not_In_remove_list in H. destruct H.
  apply in_app_or in H. destruct H ; auto. apply in_or_app ; auto.
  apply In_remove_list_In_list_not_In_remove_list in H. destruct H.
  apply remove_list_is_in. apply remove_list_is_in ; auto.
Qed.

Theorem PermutationTS_usable_boxes : forall s sp, PermutationTS s sp ->
    (forall A, InT A (usable_boxes s) -> InT A (usable_boxes sp)).
Proof.
unfold PermutationTS. intros. destruct H. apply Permutation_PermutationT in p, p0. destruct s. destruct sp.
simpl in *. unfold usable_boxes in *. simpl in *. apply InT_In in H0. apply In_InT.
apply In_remove_list_In_list_not_In_remove_list in H0. destruct H0.
apply not_removed_remove_list ; auto.
unfold subform_boxesS in * ; simpl in *. apply in_or_app.
apply in_app_or in H. destruct H. left.
apply Permutation_subform_boxesLF with (l0:=l) ; auto.
right. apply In_remove_list_In_list_not_In_remove_list in H. destruct H.
apply not_removed_remove_list.
apply Permutation_subform_boxesLF with (l0:=l0) ; auto.
intro. apply H1.
apply Permutation_subform_boxesLF with (l0:=l1) ; auto. apply Permutation_sym ; auto.
intro. apply H0. pose (in_top_boxes _ _ H1). repeat destruct s.
destruct p1. clear e0 ; subst. apply is_box_in_top_boxes. 2: eexists ; auto.
apply top_boxes_incl_list in H1. apply (Permutation_in _ (Permutation_sym p) H1).
Qed.

Theorem PermutationTS_Canopy : forall s sp, PermutationTS s sp ->
      (forall sc, InT sc (Canopy s) -> existsT2 spc, InT spc (Canopy sp) * PermutationTS sc spc).
Proof.
  intros s0 ; induction on s0 as IH with measure (n_imp_subformS s0).
  intros s1 perm sp InClos.
  pose (fold_Canopy _ _ InClos). destruct s ; subst ; auto.
  - exists s1. split ; auto. apply Canopy_critical in InClos. apply critical_Seq_InT_Canopy.
    apply (PermutationTS_critic _ _ perm) ; auto.
  - destruct s. destruct p. unfold inv_prems in i. apply InT_flatten_list_InT_elem in i. destruct i.
    destruct p. destruct (finite_ImpRules_premises_of_S s0). simpl in i1.
    apply p in i1. destruct i1. inversion i1 ; subst.
    (* x0 is obtained via ImpR. *)
    + inversion i ; subst. 2: inversion H0.  assert (InT (A --> B) (snd s1)).
       apply In_InT. apply Permutation_in with (l:=Δ0 ++ A --> B :: Δ1). destruct perm ; simpl in * ; auto.
       apply Permutation_PermutationT in p1 ; auto. apply in_or_app ; right ; apply in_eq.
       apply InT_split in H. destruct H. destruct s. subst.
       assert (J1: n_imp_subformS (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) < n_imp_subformS (Γ0 ++ Γ1, Δ0 ++ A --> B :: Δ1)).
       unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
       assert (J2: PermutationTS (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) (A :: fst s1, x ++ B :: x0)).
       unfold PermutationTS. destruct perm ; simpl in * ; split. apply Permutation_PermutationT. apply Permutation_sym.
       apply Permutation_cons_app ; apply Permutation_sym ; auto. apply Permutation_PermutationT in p0 ; auto.
       apply Permutation_PermutationT. apply Permutation_PermutationT in p1. rewrite e in p1.
       apply Permutation_app_inv in p1. apply Permutation_elt ; auto.
       pose (IH _ J1 _ J2 _ i0). destruct s. destruct p0. exists x2 ; split ; auto.
       assert (ImpRRule [(A :: fst s1, x ++ B :: x0)] s1 + ImpLRule [(A :: fst s1, x ++ B :: x0)] s1).
       left. destruct s1. epose (ImpRRule_I _ _ [] _ _ _). simpl in * ; subst ; simpl in *. apply i3.
       assert (InT (A :: fst s1, x ++ B :: x0) [(A :: fst s1, x ++ B :: x0)]). apply InT_eq.
       pose (ImpRule_Canopy _ _ H _ H0). apply i3 ; auto.
    + inversion i1 ; subst. assert (InT (A --> B) (fst s1)). apply In_InT. apply Permutation_in with (l:=Γ0 ++ A --> B :: Γ1). destruct perm ; simpl in * ; auto.
       apply Permutation_PermutationT in p0 ; auto. apply in_or_app ; right ; apply in_eq.
       apply InT_split in H. destruct H. destruct s. inversion i ; subst.
       (* x is the left premise via ImpL. *)
       * assert (J1: n_imp_subformS (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) < n_imp_subformS (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)).
         unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
         assert (J2: PermutationTS (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) (x0 ++ x2, A :: snd s1)).
         unfold PermutationTS. destruct perm ; simpl in * ; split.
         apply Permutation_PermutationT. apply Permutation_PermutationT in p0. rewrite e in p0.
         apply Permutation_app_inv in p0 ; auto.
         apply Permutation_PermutationT. apply Permutation_sym.
         apply Permutation_cons_app ; apply Permutation_sym ; auto. apply Permutation_PermutationT in p1 ; auto.
         pose (IH _ J1 _ J2 _ i0). destruct s. destruct p0. exists x ; split ; auto.
         assert (ImpRRule [(x0 ++ x2, A :: snd s1);(x0 ++ B :: x2, snd s1)] s1 + ImpLRule [(x0 ++ x2, A :: snd s1);(x0 ++ B :: x2, snd s1)] s1).
         right. destruct s1. epose (ImpLRule_I _ _ _ _ [] _). simpl in * ; subst ; simpl in *. apply i3.
         assert (InT (x0 ++ x2, A :: snd s1) [(x0 ++ x2, A :: snd s1); (x0 ++ B :: x2, snd s1)]). apply InT_eq.
         pose (ImpRule_Canopy _ _ H _ H0). apply i3 ; auto.
       (* x is the right premise via ImpL. *)
       * inversion H0 ; subst. 2: inversion H1.
         assert (J1: n_imp_subformS (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) < n_imp_subformS (Γ0 ++ A --> B :: Γ1, Δ0 ++ Δ1)).
         unfold n_imp_subformS ; simpl ; repeat rewrite n_imp_subformLF_dist_app ; simpl ; lia.
         assert (J2: PermutationTS (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) (x0 ++ B :: x2, snd s1)).
         unfold PermutationTS. destruct perm ; simpl in * ; split.
         apply Permutation_PermutationT. apply Permutation_PermutationT in p0. rewrite e in p0.
         apply Permutation_app_inv in p0 ; auto. apply Permutation_elt ; auto.
         apply Permutation_PermutationT ; apply Permutation_PermutationT in p1 ; auto.
         pose (IH _ J1 _ J2 _ i0). destruct s. destruct p0. exists x ; split ; auto.
         assert (ImpRRule [(x0 ++ x2, A :: snd s1);(x0 ++ B :: x2, snd s1)] s1 + ImpLRule [(x0 ++ x2, A :: snd s1);(x0 ++ B :: x2, snd s1)] s1).
         right. destruct s1. epose (ImpLRule_I _ _ _ _ [] _). simpl in * ; subst ; simpl in *. apply i3.
         assert (InT (x0 ++ B :: x2, snd s1) [(x0 ++ x2, A :: snd s1); (x0 ++ B :: x2, snd s1)]). apply InT_cons ; apply InT_eq.
         pose (ImpRule_Canopy _ _ H _ H1). apply i3 ; auto.
Qed.

Lemma PermutationT_nodupseq : forall l0 l1, PermutationT l0 l1 -> PermutationT (nodup eq_dec_form l0) (nodup eq_dec_form l1).
Proof.
intros. apply Permutation_PermutationT. apply Permutation_PermutationT in H.
revert H. revert l1. revert l0.
epose (@Permutation_ind_bis _ (fun l0 l1 => Permutation (nodup eq_dec_form l0) (nodup eq_dec_form l1))).
apply p ; clear p ; intros.
- simpl. apply perm_nil.
- simpl. destruct (in_dec eq_dec_form x l). destruct (in_dec eq_dec_form x l') ; auto.
  exfalso. apply n. apply (Permutation_in _ H) ; auto. destruct (in_dec eq_dec_form x l') ; auto.
  exfalso. apply n. apply Permutation_sym in H. apply (Permutation_in _ H) ; auto.
- simpl. destruct (eq_dec_form x y) ; subst ; simpl. destruct (eq_dec_form y y). 2: exfalso ; auto.
  destruct (in_dec eq_dec_form y l) ; auto. destruct (in_dec eq_dec_form y l') ; auto.
  exfalso. apply n. apply (Permutation_in _ H) ; auto. destruct (in_dec eq_dec_form y l') ; auto.
  exfalso. apply n. apply Permutation_sym in H. apply (Permutation_in _ H) ; auto.
  destruct (in_dec eq_dec_form y l). destruct (in_dec eq_dec_form x l). destruct (eq_dec_form y x).
  exfalso ; auto. destruct (in_dec eq_dec_form x l'). destruct (in_dec eq_dec_form y l') ; auto.
  exfalso. apply n1. apply (Permutation_in _ H) ; auto. exfalso. apply n1. apply (Permutation_in _ H) ; auto.
  destruct (eq_dec_form y x). exfalso ; auto. destruct (in_dec eq_dec_form x l').
  exfalso. apply n0. apply Permutation_sym in H. apply (Permutation_in _ H) ; auto.
  destruct (in_dec eq_dec_form y l'). apply perm_skip ; auto. exfalso.
  apply n3. apply (Permutation_in _ H) ; auto. destruct (in_dec eq_dec_form x l).
  destruct (eq_dec_form y x). exfalso ; auto. destruct (in_dec eq_dec_form x l').
  destruct (in_dec eq_dec_form y l') ; auto. exfalso. apply n0. apply Permutation_sym in H. apply (Permutation_in _ H) ; auto.
  exfalso. apply n2. apply (Permutation_in _ H) ; auto. destruct (eq_dec_form y x).
  exfalso ; auto. destruct (in_dec eq_dec_form x l'). exfalso. apply n1. apply Permutation_sym in H. apply (Permutation_in _ H) ; auto.
  destruct (in_dec eq_dec_form y l'). exfalso. apply n0. apply Permutation_sym in H. apply (Permutation_in _ H) ; auto.
  pose (@Permutation_cons_app _ (x :: nodup eq_dec_form l) [x] (nodup eq_dec_form l') y). simpl in p. apply p.
  clear p. apply perm_skip ; auto.
- apply (perm_trans H0 H2) ; auto.
Qed.


