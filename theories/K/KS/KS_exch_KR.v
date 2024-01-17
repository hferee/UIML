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

Lemma KR_app_list_exchL : forall s se ps,
  (@list_exch_L s se) ->
  (KRRule [ps] s) ->
  (existsT2 pse,
    (KRRule [pse] se) *
    (@list_exch_L ps pse)).
Proof.
intros s se ps exch RA. inversion RA. inversion exch. rewrite <- H1 in H2.
inversion H2. subst.
pose (@nobox_gen_ext_exch_L (Δ0 ++ Box A :: Δ1) [A] BΓ (Γ1 ++ Γ2 ++ Γ3 ++ Γ4 ++ Γ5) (Γ1 ++ Γ4 ++ Γ3 ++ Γ2 ++ Γ5) X exch).
destruct s. destruct p. inversion l.
exists (unboxed_list (Γ0 ++ Γ8 ++ Γ7 ++ Γ6 ++ Γ9), [A]). split.
- apply KRRule_I.
  * unfold is_Boxed_list. intros. apply in_exch_list in H4. subst. apply H0 in H4.
    assumption.
  * subst. assumption.
- repeat rewrite unbox_app_distrib. repeat rewrite <- app_assoc. apply list_exch_LI.
Qed.

Lemma KR_app_list_exchR : forall s se ps,
  (@list_exch_R s se) ->
  (KRRule [ps] s) ->
  (existsT2 pse,
    (KRRule [pse] se) *
    (@list_exch_R ps pse)).
Proof.
intros s se ps exch RA. inversion RA. inversion exch. rewrite <- H1 in H2.
inversion H2. exists (unboxed_list BΓ, [A]). split.
- pose (partition_1_element2 Δ2 Δ3 Δ4 Δ5 Δ6 Δ0 Δ1 (Box A) H6). destruct s0.
  + repeat destruct s0. repeat destruct p. subst. assert (E : (Δ0 ++ Box A :: x0) ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6 = Δ0 ++ Box A :: (x0 ++ Δ5 ++ Δ4 ++ Δ3 ++ Δ6)).
    repeat rewrite <- app_assoc. reflexivity. rewrite E. apply KRRule_I.
    * assumption.
    * assumption.
  + destruct s0.
    * repeat destruct s0. repeat destruct p. subst. assert (E: Δ2 ++ Δ5 ++ Δ4 ++ (x ++ Box A :: x0) ++ Δ6 = (Δ2 ++ Δ5 ++ Δ4 ++ x) ++ Box A :: x0 ++ Δ6).
      repeat rewrite <- app_assoc. reflexivity. rewrite E. apply KRRule_I.
      { assumption. }
      { assumption. }
    * destruct s0.
      { repeat destruct s0. repeat destruct p. subst. assert (E: Δ2 ++ Δ5 ++ (x ++ Box A :: x0) ++ Δ3 ++ Δ6 = (Δ2 ++ Δ5 ++ x) ++ Box A :: x0 ++ Δ3 ++ Δ6).
        repeat rewrite <- app_assoc. reflexivity. rewrite E. apply KRRule_I.
        - assumption.
        - assumption. }
      { destruct s0.
        - repeat destruct s0. repeat destruct p. subst. assert (E: Δ2 ++ (x ++ Box A :: x0) ++ Δ4 ++ Δ3 ++ Δ6 = (Δ2 ++ x) ++ Box A :: x0 ++ Δ4 ++ Δ3 ++ Δ6).
          repeat rewrite <- app_assoc. reflexivity. rewrite E. apply KRRule_I.
          + assumption.
          + assumption.
        - repeat destruct s0. repeat destruct p. subst. assert (E: Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ x ++ Box A :: Δ1 = (Δ2 ++ Δ5 ++ Δ4 ++ Δ3 ++ x) ++ Box A :: Δ1).
          repeat rewrite <- app_assoc. reflexivity. rewrite E. apply KRRule_I.
          + assumption.
          + assumption. }
- apply list_exch_R_id.
Qed.
